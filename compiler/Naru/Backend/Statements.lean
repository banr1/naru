import Naru.Backend.Model

/-!
# Statements backend — Core IR → Lean(`generated/Statements`)

spec 宣言(predicate / condition / regime / property / claim / claim bundle)だけを Lean に落とす。
runtime 宣言は Model backend(`Backend/Model.lean`)の仕事で、ここでは出力しない。

出力の規則(Model backend と同じく決定的: 表の反復順に依存せず、ソースの順と名前の順だけで並べる):
- naru モジュール `A.B` に spec 宣言があれば Lean モジュール `Statements.A.B`(ファイル `Statements/A/B.lean`)。
  宣言は `Statements.A.B.name` と完全修飾で参照する。runtime 宣言への参照は `Model.A.B.name`(生成 Model を
  `import Model.A.B` する)。spec モジュール同士の参照は `import Statements.X.Y`(循環は E017)。
  生成 Statements が import するのは `NaruStd`・生成 Model・他の生成 Statements だけで、Proofs は決して import しない
  (IDEAL.md「不変条件」の依存方向 Model ← Statements ← Proofs)。
- predicate / condition / regime / property / claim → `def Statements.A.B.name (params) : Prop := …`。本体の Bool の式を
  Prop に読み替える: `&&` → `∧`、`||` → `∨`、`!` → `¬`、`implies` → `→`、`==` → `=`、`<` 等 → `<`(Nat / Int / String)か
  `Ord.compare a b = Ordering.lt` 等(他の `order` 型)、`forall x: T { … }` → `∀ («x» : T), …`、`exists` → `∃`、
  `true` / `false` → `True` / `False`、spec 宣言の呼出しはその Prop、それ以外の Bool の値(fn の呼出し・stdlib の
  `all` / `any` / `contains`・欄・局所名)は `(e) = true`。`if` は条件が Bool の値なら `if c = true then … else …`、
  条件が Prop(量化・spec の呼出しを含む)なら `(c → a) ∧ (¬ c → b)`。`let` は値の `let`(Bool で Prop を含む値なら
  `let x : Prop := …`)。`match` は腕の本体を Prop にし、ガードは `(g → b) ∧ (¬ g → REST)`。
  値の位置(fn の実引数・欄・コレクションの要素 …)の式は Model backend と同じ Lean(`emitE`)。
  再帰する spec 宣言(`Totality` が受理したもの)は Model と同じ `if _h' :` / `match _hm' :` / `_ + m` で分岐の事実を証明に残し、
  `termination_by` / `decreasing_by` を付ける。
- claim bundle → `structure Statements.A.B.name : Prop where`。項目 `label: claim` は欄
  `label : ∀ (params of the claim), Statements.X.claim params`(仮引数が無ければ `Statements.X.claim`)、入れ子の bundle は
  `label : Statements.X.bundle`。欄の名前は項目のラベル(claim surface。C9 はこの欄名を数える)。
- `input` は Model と同じく Lean の宣言にならない。それを(推移的に)使う spec 宣言は先頭に引数 `name'` を持ち、呼出しで引き回す。
  claim bundle は項目が使う input の和を引数に持つ。
- 生成ファイルの先頭 5 行は Model と同じヘッダ(コンパイラ版・stdlib 版・ソース hash・単位 hash)。

既知の制限: Bool の値が要る位置(fn の実引数・`let` の値・コレクション)に量化や spec 宣言の呼出し(Prop)を書くと Lean が拒否する
(Prop は Bool に戻せない)。spec 宣言の中では Prop は論理演算・`if` の条件・`match` のガード・`let` の Prop の束縛にだけ置く。
`∀` / `∃` は Lean の型の全要素を回るので、`Set` / `Table` を含む型(`NaruStd.Set` は昇順・重複なしのリストだが、その不変条件は
型に入っていない)の量化は正規化されていない表現も含む(SYNTAX.md「Statements backend」の既知の制限)。
本体の無い spec 宣言と解決できない claim bundle の項目は `False` に落ちるが、パーサ(本体必須)と E016 が退けるので到達しない。
-/

namespace Naru.Backend.Statements
open Std
open Naru.Backend.Model

/-! ## 名前 -/

/-- 大域の修飾名 → Lean の完全修飾名(`Statements.A.B.name`)。 -/
def stmtName (key : String) : String :=
  "Statements." ++ ".".intercalate ((key.splitOn ".").map escSeg)

def stmtModule (name : List String) : String :=
  "Statements." ++ ".".intercalate (name.map escSeg)

def stmtPath (name : List String) : String :=
  "Statements/" ++ "/".intercalate name ++ ".lean"

def isSpecKey (env : Env) (k : String) : Bool :=
  match env.decls.get? k with
  | some d => d.phase == .spec
  | none => false

def isSpecDecl (d : Core.Decl) : Bool := d.phase == .spec

/-- Prop の文脈: いまの宣言が再帰するか(`if _h' :` が要る)と、`let` で Prop に束ねた局所名。 -/
structure PCtx where
  recursive : Bool
  propVars : List String := []

def PCtx.ectx (c : PCtx) : ECtx := { recursive := c.recursive }

/-- 束縛(lambda / 量化 / パターン / 値の `let`)が Prop の局所名を隠す。 -/
def PCtx.unbind (c : PCtx) (names : List String) : PCtx :=
  { c with propVars := c.propVars.filter fun n => !names.contains n }

partial def patVars : Core.Pat → List String
  | .bind n => [n]
  | .tuple ps | .builtin _ ps | .variant _ _ ps => ps.flatMap patVars
  | _ => []

/-! ## Prop と Bool の見分け -/

/-- Prop でしか表せない式か(量化・spec 宣言の参照・Prop に束ねた局所名を含む)。Bool の値として Lean に落とせない。 -/
partial def proppy (env : Env) (c : PCtx) : Core.Expr → Bool
  | .quant .. => true
  | .call k args => isSpecKey env k || args.any (proppy env c)
  | .global k => isSpecKey env k
  | .var n => c.propVars.contains n
  | .binop _ l r _ => proppy env c l || proppy env c r
  | .unop _ a => proppy env c a
  | .ite a b d => proppy env c a || proppy env c b || proppy env c d
  | .match_ s _ arms => proppy env c s || arms.any fun | .mk _ g b => (g.map (proppy env c)).getD false || proppy env c b
  | .let_ n _ v b => proppy env c v || proppy env (c.unbind [n]) b
  | .lambda ps b => proppy env (c.unbind (ps.map (·.1))) b
  | .callLocal f args => proppy env c f || args.any (proppy env c)
  | .method _ _ r args _ => proppy env c r || args.any (proppy env c)
  | .builtin _ args _ | .variant _ _ args | .tuple args | .list args _ => args.any (proppy env c)
  | .field r _ _ => proppy env c r
  | .record _ fs base => fs.any (fun (_, x) => proppy env c x) || (base.map (proppy env c)).getD false
  | .lit .. | .error => false

/-- Prop の位置で括弧が要らない形。 -/
def propAtom (env : Env) (c : PCtx) : Core.Expr → Bool
  | .lit (.bool _) _ => true
  | .var n => c.propVars.contains n
  | .global k => isSpecKey env k && (env.inputs.getD k []).isEmpty
  | _ => false

/-- 比較を Prop にする。`Nat` / `Int` / `String` は Lean の `<` `≤` `>` `≥`、他の `order` 型は `Ord.compare`(Model と同じく
`Ord` だけで決める)。 -/
def compareProp (op : String) (t : TyV) (l r : String) : String :=
  if isDecideTy t then
    let lop := match op with
      | "<=" => "≤"
      | ">=" => "≥"
      | o => o
    s!"{l} {lop} {r}"
  else
    match op with
    | "<" => s!"Ord.compare {l} {r} = Ordering.lt"
    | "<=" => s!"Ord.compare {l} {r} ≠ Ordering.gt"
    | ">" => s!"Ord.compare {l} {r} = Ordering.gt"
    | _ => s!"Ord.compare {l} {r} ≠ Ordering.lt"

/-! ## 式(Prop の位置) -/

mutual

/-- Bool の式を Prop として出す(括弧なしの形)。値の位置の式は Model backend の `emitE` / `emitP`。 -/
partial def emitProp (env : Env) (c : PCtx) (ind : Nat) (e : Core.Expr) : String :=
  let vP (x : Core.Expr) : String := emitP env c.ectx ind x
  let asBool (x : Core.Expr) : String := s!"{vP x} = true"
  match e with
  | .lit (.bool true) _ => "True"
  | .lit (.bool false) _ => "False"
  | .var n => if c.propVars.contains n then localName n else asBool e
  | .global k =>
    if isSpecKey env k then app (stmtName k) ((env.inputs.getD k []).map inputBinder) else asBool e
  | .call k args =>
    if isSpecKey env k then app (stmtName k) ((env.inputs.getD k []).map inputBinder ++ args.map vP)
    else asBool e
  | .binop "&&" l r _ => s!"{propP env c ind l} ∧ {propP env c ind r}"
  | .binop "||" l r _ => s!"{propP env c ind l} ∨ {propP env c ind r}"
  | .binop "implies" l r _ => s!"{propP env c ind l} → {propP env c ind r}"
  | .binop "==" l r _ =>
    if proppy env c l || proppy env c r then s!"{propP env c ind l} ↔ {propP env c ind r}"
    else s!"{vP l} = {vP r}"
  | .binop "!=" l r _ =>
    if proppy env c l || proppy env c r then s!"¬ ({propP env c ind l} ↔ {propP env c ind r})"
    else s!"{vP l} ≠ {vP r}"
  | .binop op l r t =>
    if op == "<" || op == "<=" || op == ">" || op == ">=" then compareProp op t (vP l) (vP r)
    else asBool e
  | .unop "!" a => s!"¬ {propP env c ind a}"
  | .quant q bs b =>
    let qs := if q == .forall_ then "∀" else "∃"
    let binders := bs.map fun (n, t) => s!"({localName n} : {ty t})"
    s!"{qs} {" ".intercalate binders}, {emitProp env (c.unbind (bs.map (·.1))) ind b}"
  | .ite cond t el =>
    if proppy env c cond then
      let cs := propP env c ind cond
      s!"({cs} → {propP env c ind t}) ∧ (¬ {cs} → {propP env c ind el})"
    else
      let h := if c.recursive then "_h' : " else ""
      s!"if {h}{vP cond} = true then\n{indent (ind + 2)}{emitProp env c (ind + 2) t}\n{indent ind}else\n{indent (ind + 2)}{emitProp env c (ind + 2) el}"
  | .match_ s st arms => emitMatchProp env c ind s st arms
  | .let_ n t v b =>
    let name := if n == "_" then "_" else localName n
    match t with
    | .bool =>
      if proppy env c v then
        let c' := if n == "_" then c else { c with propVars := n :: c.propVars }
        s!"let {name} : Prop := {emitProp env c (ind + 2) v}\n{indent ind}{emitProp env c' ind b}"
      else
        s!"let {name} : Bool := {emitE env c.ectx (ind + 2) v}\n{indent ind}{emitProp env (c.unbind [n]) ind b}"
    | _ =>
      s!"let {name} : {ty t} := {emitE env c.ectx (ind + 2) v}\n{indent ind}{emitProp env (c.unbind [n]) ind b}"
  | _ => asBool e

/-- Prop の被演算子の位置(必要なら括弧で囲む)。 -/
partial def propP (env : Env) (c : PCtx) (ind : Nat) (e : Core.Expr) : String :=
  if propAtom env c e then emitProp env c ind e
  else "(" ++ emitProp env c (ind + 1) e ++ ")"

/-- `match` の Prop 版。腕の本体を Prop にする。Model backend の `emitMatch` と同じ構造:
- 再帰する宣言の中で `Nat` の局所変数を match し、ガードが無い: `match _hm' : v with` で等式を残し、bind / `_` の腕を
  `_ + m` に落とす(停止性の証明に `v ≥ m` が要る)。
- ガードがある: 最初のガード付き腕 i より前の腕はそのまま出し、`| _ =>` の中で `match s with | p_i => (g → b) ∧ (¬ g → REST)
  | _ => REST`(REST = i 以外の腕の match。`p_i` が必ず一致する形なら `| _ => REST` は出さない。前の腕が無ければ外側の match は
  出さない)。ガード 1 つにつき残りの腕が 2 回現れる。 -/
partial def emitMatchProp (env : Env) (c : PCtx) (ind : Nat) (s : Core.Expr) (st : TyV) (arms : List Core.Arm) : String :=
  let natVar : Option String := match s, st with
    | .var v, .nat => if c.recursive then some v else none
    | _, _ => none
  let hasGuard := arms.any fun | .mk _ g _ => g.isSome
  -- ガード付きの `Nat` の match は Model の `emitNatChain`(`if _h' :` の連鎖)に相当する形をまだ出さない(再帰 + ガード付き Nat match の
  -- spec 宣言は停止性の証明が通らないことがある: SYNTAX.md「Statements backend」)
  if hasGuard then emitMatchGuardedProp env c ind s st arms
  else emitMatchPlainProp env c ind s arms natVar

/-- ガード無しの match。`natVar` があれば(再帰する宣言の `Nat` の局所変数)、Model backend の `emitMatchPlain` と同じく
`match _hm' : v with`、bind / `_` の腕を `_ + m`、束縛名は `let k : Nat := v` の別名にする。 -/
partial def emitMatchPlainProp (env : Env) (c : PCtx) (ind : Nat) (s : Core.Expr) (arms : List Core.Arm)
    (natVar : Option String) : String := Id.run do
  let eq := if natVar.isSome then "_hm' : " else ""
  let mut out := s!"match {eq}{emitP env c.ectx ind s} with"
  let mut covered : List Nat := []
  for arm in arms do
    let .mk p _ b := arm
    let (ps, prefix_) : String × String := match natVar, p with
      | some v, .bind k =>
        let m := firstMissing covered
        (if m > 0 then s!"_ + {m}" else "_",
         if k == v then "" else s!"let {localName k} : Nat := {localName v}\n{indent (ind + 2)}")
      | some _, .wild =>
        let m := firstMissing covered
        (if m > 0 then s!"_ + {m}" else "_", "")
      | _, _ => (pat p, "")
    out := out ++ s!"\n{indent ind}| {ps} =>\n{indent (ind + 2)}{prefix_}{emitProp env (c.unbind (patVars p)) (ind + 2) b}"
    if let .lit (.nat k) := p then covered := k :: covered
  return out

/-- ガード付きの腕を持つ match(上の説明)。 -/
partial def emitMatchGuardedProp (env : Env) (c : PCtx) (ind : Nat) (s : Core.Expr) (st : TyV) (arms : List Core.Arm) : String := Id.run do
  let scrut := emitP env c.ectx ind s
  let mut lead : List Core.Arm := []
  let mut rest := arms
  while !rest.isEmpty do
    let .mk _ g _ := rest.head!
    if g.isSome then break
    lead := lead ++ [rest.head!]
    rest := rest.tail!
  let armStr (ind : Nat) (arm : Core.Arm) : String :=
    let .mk p _ b := arm
    s!"\n{indent ind}| {pat p} =>\n{indent (ind + 2)}{emitProp env (c.unbind (patVars p)) (ind + 2) b}"
  match rest with
  | [] => return s!"match {scrut} with" ++ "".intercalate (lead.map (armStr ind))
  | .mk p (some g) b :: after =>
    let tailInd := if lead.isEmpty then ind else ind + 2
    let c' := c.unbind (patVars p)
    let restArms := lead ++ after
    let restAt (i : Nat) : String :=
      if restArms.isEmpty then "False" else "(" ++ emitMatchProp env c (i + 1) s st restArms ++ ")"
    let gs := propP env c' (tailInd + 4) g
    let inner := s!"match {scrut} with\n{indent (tailInd + 2)}| {pat p} =>\n{indent (tailInd + 4)}({gs} → {propP env c' (tailInd + 4) b}) ∧ (¬ {gs} → {restAt (tailInd + 4)})"
      ++ (if irrefutable env p then "" else s!"\n{indent (tailInd + 2)}| _ =>\n{indent (tailInd + 4)}{restAt (tailInd + 4)}")
    if lead.isEmpty then return inner
    return s!"match {scrut} with" ++ "".intercalate (lead.map (armStr ind)) ++ s!"\n{indent ind}| _ =>\n{indent (ind + 2)}{inner}"
  | _ => return "False"

end

/-! ## 宣言 -/

/-- spec 宣言 1 つ。predicate / … / claim は `def … : Prop`、claim bundle は `structure … : Prop`。 -/
def emitSpecDecl (env : Env) (d : Core.Decl) : String :=
  match d with
  | .fn k _ kind params _ body =>
    let binders := inputBinders env k ++ params.map fun p => s!"({localName p.name} : {ty p.ty})"
    let sig := app s!"def {stmtName k}" binders ++ " : Prop :="
    let c : PCtx := { recursive := isRecursive env k }
    let b := match body with
      | some b => emitProp env c 2 b
      | none => "False"
    s!"-- naru {kind.describe}\n{sig}\n  {b}" ++ terminationClause env k params
  | .claimBundle k _ items =>
    let binders := inputBinders env k
    let fields := items.map fun (label, target) =>
      let field := match env.decls.get? target with
        | some (.fn tk _ _ params _ _) =>
          let names := params.map fun (p : Core.Param) => localName p.name
          let binders := params.map fun (p : Core.Param) => s!"({localName p.name} : {ty p.ty})"
          let call := app (stmtName tk) ((env.inputs.getD tk []).map inputBinder ++ names)
          if params.isEmpty then call
          else "∀ " ++ " ".intercalate binders ++ ", " ++ call
        | some (.claimBundle tk ..) => app (stmtName tk) ((env.inputs.getD tk []).map inputBinder)
        | _ => "False"
      s!"\n  {escSeg label} : {field}"
    s!"-- naru claim bundle\n" ++ app s!"structure {stmtName k}" binders ++ " : Prop where" ++ "".intercalate fields
  | _ => ""

/-- 成分を出力する。複数(相互再帰)なら `mutual … end`。 -/
def emitSpecGroup (env : Env) (g : List Core.Decl) : String :=
  match g with
  | [d] => emitSpecDecl env d
  | ds => s!"mutual\n\n" ++ "\n\n".intercalate (ds.map (emitSpecDecl env)) ++ "\n\nend"

/-! ## モジュール -/

/-- モジュールの spec 宣言(と、それが使う input の署名)が参照する他のモジュール: (runtime のモジュール, spec のモジュール)。
名前順、重複なし。 -/
def specModuleDeps (env : Env) (m : Core.Module) : List (List String) × List (List String) := Id.run do
  let mut rt : List (List String) := []
  let mut sp : List (List String) := []
  for d in m.decls do
    if !(isSpecDecl d) then continue
    let refs := d.refs ++ ((env.inputs.getD d.key []).flatMap fun ik =>
      match env.decls.get? ik with
      | some i => i.refs
      | none => [])
    for r in refs do
      if let some other := env.moduleOf.get? r then
        if isSpecKey env r then
          if other != m.name && !sp.contains other then sp := sp ++ [other]
        else
          if !rt.contains other then rt := rt ++ [other]
  return (rt.mergeSort fun a b => renderPath a ≤ renderPath b, sp.mergeSort fun a b => renderPath a ≤ renderPath b)

/-- Core のモジュール列から生成 Statements(`generated/` からの相対パス、内容)を作る。spec 宣言のあるモジュールだけ
ファイルになり、ルート `Statements.lean` がそれらを import する。同名のモジュールの検査は Model backend(先に走る)が行う。 -/
def emitStatements (mods : Array Core.Module) (recs : Array Totality.Recursion) (info : Meta) :
    Except Diagnostic (Array (String × String)) := do
  let env := buildEnv mods recs
  let specMods := mods.toList.filter fun m => m.decls.any isSpecDecl
  let deps := specMods.map fun m => (m.name, specModuleDeps env m)
  if let some cycle := findCycle (deps.map fun (n, (_, sp)) => (n, sp)) then
    let names := cycle.map fun n => s!"`{renderPath n}`"
    let first := specMods.find? (·.name == cycle.head!)
    throw { file := (first.map (·.file)).getD "", span := {}, code := Code.moduleStructure,
            msg := s!"spec declarations of modules refer to each other in a cycle ({" → ".intercalate names}); generated Lean modules import each other, so move the shared declarations into one module" }
  let mut files : Array (String × String) := #[]
  for m in specMods do
    let hash := (info.fileHashes.lookup m.file).getD ""
    let (rt, sp) := (deps.lookup m.name).getD ([], [])
    let imports := "import NaruStd\n" ++ "".intercalate (rt.map fun n => s!"import {leanModule n}\n") ++
      "".intercalate (sp.map fun n => s!"import {stmtModule n}\n")
    let groups := orderGroups env (m.decls.toList.filter isSpecDecl)
    let body := if groups.isEmpty then "" else "\n" ++ "\n\n".intercalate (groups.map (emitSpecGroup env)) ++ "\n"
    let content := header info m.file hash ++ imports ++
      s!"\n/-! naru module `{renderPath m.name}` ({m.file}): spec declarations (predicate / condition / regime / property / claim / claim bundle) -/\n" ++ body
    files := files.push (stmtPath m.name, content)
  let rootImports := "".intercalate (specMods.map fun m => s!"import {stmtModule m.name}\n")
  let root := header info "all sources" info.unitHash ++ rootImports ++
    "\n/-! Generated Statements: one Lean module per naru module that declares predicates / conditions / regimes / properties / claims / claim bundles. Imports only NaruStd and the generated Model (never Proofs). Build with `lake build Statements`. -/\n"
  files := files.push ("Statements.lean", root)
  return files

end Naru.Backend.Statements
