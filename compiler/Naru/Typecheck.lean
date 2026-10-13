import Std.Data.HashMap
import Naru.Ast
import Naru.Core
import Naru.Resolve

/-!
# 型検査・capability 検査・選択と順序の検査 — そして Core IR への elaboration

名前解決と phase 検査(`Resolve.lean`)を通った宣言の本体に型を付け、次を報告する。

- 型の不一致・推論できない型・値でないものの値としての使用 → E014
- 無い欄・無いメソッド・引数の数や名前の不一致 → E015
- claim bundle の項目が claim(または入れ子の claim bundle)でない → E016
- capability(eq / order)の無い型への `==` `!=` `<` `<=` `>` `>=`、
  eq / order を要する stdlib メソッド、`derive` した capability を欄が満たさない → E005
- Set からの無条件の選択(`choose` / `pick` / `first` / `find?` …) → **E003**
- 順序指定の無い Set → List 変換(`toList` / `by =` の無い `sort` / `fold` …) → **E004**
- runtime 宣言の中の量化(`forall` / `exists`) → E006

同時に Surface AST を Typed Core IR(`Core.lean`)に elaborate する。誤りが 1 つでもあれば Core は
backend に渡らない(`Driver.lean`)。型が要る位置(`let` / lambda の引数 / 空のコレクション / 比較の被演算子)で
宣言の終わりまでにメタ変数が残っていれば E014(「add a type annotation」)。

stdlib のメソッド表(`setSigs` / `listSigs` / …)がこのファイルの正本。naru で書いた stdlib ができるまでは
ここで型を与える。Lean の型クラスは露出せず、eq / order の要求はメソッド表の `caps` 列で表す。
推論は単一化(メタ変数)で行い、lambda の引数型は期待される型から取る。
-/

namespace Naru

namespace Typecheck
open Std

abbrev CExpr := Core.Expr
abbrev CPat := Core.Pat
abbrev CArm := Core.Arm

/-- record / state の欄、enum の variant。 -/
inductive TypeInfo where
  | record (fields : Array (String × TyV)) (derives : Array String)
  | enum (variants : Array (String × List TyV)) (derives : Array String)
deriving Inhabited

/-- fn / input / observer / predicate / … の署名。spec 宣言の戻り型は Bool(Prop 相当)。 -/
structure FnInfo where
  kind : DeclKind
  params : Array (String × TyV)
  ret : TyV
deriving Inhabited

structure Entry where
  file : String
  qualified : String
  decl : Decl
deriving Inhabited

inductive MemberKind where
  | field
  | method
deriving Inhabited, BEq, Repr, DecidableEq

/-- 型検査が解決した欄・stdlib メソッドの参照 1 つ(名前解決の索引 `Resolve.Ref` には無いもの。言語サーバーのホバー(C29)と
欄名のリネーム(C32)が引く)。`span` は欄名 / メソッド名のトークンの位置。型は宣言の終わり(`finishDecl`)に確定したもの。
欄は式の中の読み `r.f` と record literal の初期化 `R { f: … }`(`init`)の両方。 -/
structure MemberRef where
  file : String
  span : Span
  kind : MemberKind
  /-- 欄なら record / state の修飾名(大域表の鍵)、メソッドなら受け手の型の名前(`Set` / `List` / … stdlib の表の名前)。 -/
  owner : String
  /-- 欄なら record / state の表示名、メソッドなら `owner` と同じ。 -/
  ownerName : String
  name : String
  /-- 受け手の型。 -/
  recv : TyV
  /-- メソッドの仮引数(名前付きで渡せるものはその名前つき)。欄は空。 -/
  params : List (Option String × TyV) := []
  /-- 欄の型 / メソッドの戻り型。 -/
  ret : TyV
  /-- record literal の欄の初期化(`R { f: e }` の `f`)なら true。読み `r.f` とメソッドは false。 -/
  init : Bool := false
  /-- 初期化が略記(`R { f }`: 欄名と値の局所名 `f` が同じトークン)なら true。リネームはこの欄を `new: f` に展開する。 -/
  shorthand : Bool := false
deriving Inhabited

/-- 欄 / メソッドのアクセス(`r.name` / `r.name(…)`)1 つの受け手の型。名前が欄 / メソッドとして解決できたかに関わらず、受け手の型が決まった
時点で記録する(言語サーバーの補完(C31)が `.` の後の候補を受け手の型から作るのに引く: 途中まで書いた名前は解決しないので `members` には
残らない)。`span` は名前のトークンの位置。型は宣言の終わり(`finishDecl`)に確定したもの。 -/
structure AccessRef where
  file : String
  span : Span
  name : String
  recv : TyV
deriving Inhabited

structure St where
  /-- 単純名と修飾名の両方を鍵にする(`Resolve` と同じ)。 -/
  decls : HashMap String Entry := {}
  /-- 鍵は修飾名。 -/
  types : HashMap String TypeInfo := {}
  /-- 鍵は修飾名。 -/
  fns : HashMap String FnInfo := {}
  subst : HashMap Nat TyV := {}
  nextMeta : Nat := 0
  diags : Array Diagnostic := #[]
  /-- いま検査中の宣言で、終わりまでに型が確定していなければならない位置(残れば E014)。 -/
  pending : Array (Span × TyV × String) := #[]
  /-- いま検査中の宣言で、終わりに capability を要求する位置(`Set.of` / `Set.singleton` の要素の `eq` など。
  要素の型が後から決まるので、宣言の終わりに zonk してから検査する。満たさなければ E005)。 -/
  pendingCaps : Array (Span × String × TyV × String) := #[]
  /-- 解決した欄・stdlib メソッドの参照(出現順。C29)。 -/
  members : Array MemberRef := #[]
  /-- `members` のうち型を確定済み(`finishDecl`)の個数。 -/
  membersDone : Nat := 0
  /-- 欄 / メソッドのアクセスの受け手の型(出現順。C31)。 -/
  accesses : Array AccessRef := #[]
  /-- `accesses` のうち型を確定済み(`finishDecl`)の個数。 -/
  accessesDone : Nat := 0

abbrev M := StateM St

instance [Inhabited α] : Inhabited (M α) := ⟨pure default⟩

structure Ctx where
  file : String
  declKind : DeclKind
  declName : String
  locals : List (String × TyV)
  /-- Prop の位置(spec 宣言の本体と、その論理構造(`&&` / `||` / `!` / `implies` の被演算子、`if` の条件と分岐、`match` の
  ガードと腕の本体、`let` の値と続き、量化の本体)の中)。ここでは Bool の式が Prop(量化・spec 宣言の呼出し)でもよい。
  それ以外(fn / メソッドの実引数・欄・コレクションの要素・lambda の本体・scrutinee・算術と比較の被演算子 …)は値の位置で、
  Prop でしか表せない式は E014(C35。Statements backend は Prop を Bool に戻せない)。runtime 宣言では常に false。 -/
  propPos : Bool := false
  /-- spec 宣言の Prop の位置で `let` が Prop に束ねた局所名(Statements backend は `let x : Prop := …` に落とす)。値の位置では使えない。 -/
  propVars : List String := []
  /-- 値の位置の説明(E014 の文面)。 -/
  valueWhat : String := ""

/-- 束縛は同名の Prop の局所名を隠す。 -/
def Ctx.bind (ctx : Ctx) (binds : List (String × TyV)) : Ctx :=
  { ctx with locals := binds ++ ctx.locals, propVars := ctx.propVars.filter fun n => !binds.any (·.1 == n) }

/-- 値の位置(Bool の値が要る。Prop は E014)。 -/
def Ctx.value (ctx : Ctx) (what : String) : Ctx := { ctx with propPos := false, valueWhat := what }

/-- Prop の位置(量化の本体)。 -/
def Ctx.prop (ctx : Ctx) : Ctx := { ctx with propPos := true }

def reportAt (file : String) (span : Span) (code msg : String) : M Unit :=
  modify fun s => { s with diags := s.diags.push { file, span, code, msg } }

def report (ctx : Ctx) (span : Span) (code msg : String) : M Unit :=
  reportAt ctx.file span code msg

def fresh : M TyV := do
  let s ← get
  set { s with nextMeta := s.nextMeta + 1 }
  return .mvar s.nextMeta

/-- 宣言の終わりまでに `t` のメタ変数が解けていなければ E014 を `span` に報告する。 -/
def need (span : Span) (t : TyV) (what : String) : M Unit :=
  modify fun s => { s with pending := s.pending.push (span, t, what) }

/-- 宣言の終わりに `t`(zonk 後)が capability `cap` を持つことを要求する(無ければ E005 を `span` に報告)。 -/
def deferCap (span : Span) (cap : String) (t : TyV) (what : String) : M Unit :=
  modify fun s => { s with pendingCaps := s.pendingCaps.push (span, cap, t, what) }

/-! ## 単一化 -/

partial def zonk (t : TyV) : M TyV := do
  match t with
  | .mvar n =>
    match (← get).subst.get? n with
    | some t' => zonk t'
    | none => return t
  | .option a => return .option (← zonk a)
  | .result a e => return .result (← zonk a) (← zonk e)
  | .list a => return .list (← zonk a)
  | .set a => return .set (← zonk a)
  | .table k v => return .table (← zonk k) (← zonk v)
  | .tuple ts => return .tuple (← ts.mapM zonk)
  | .fn ps r => return .fn (← ps.mapM zonk) (← zonk r)
  | t => return t

partial def occurs (n : Nat) : TyV → Bool
  | .mvar m => n == m
  | .option a | .list a | .set a => occurs n a
  | .result a e | .table a e => occurs n a || occurs n e
  | .tuple ts => ts.any (occurs n)
  | .fn ps r => ps.any (occurs n) || occurs n r
  | _ => false

partial def hasMeta : TyV → Bool
  | .mvar _ => true
  | .option a | .list a | .set a => hasMeta a
  | .result a e | .table a e => hasMeta a || hasMeta e
  | .tuple ts => ts.any hasMeta
  | .fn ps r => ps.any hasMeta || hasMeta r
  | _ => false

def bindMeta (n : Nat) (t : TyV) : M Unit :=
  modify fun s => { s with subst := s.subst.insert n t }

/-- 単一化。成功なら true。`unknown` は何とでも単一化する(誤りの波及を抑える)。 -/
partial def unify (a b : TyV) : M Bool := do
  let a ← zonk a
  let b ← zonk b
  let all (xs ys : List TyV) : M Bool := do
    if xs.length != ys.length then return false
    (xs.zip ys).allM fun (x, y) => unify x y
  match a, b with
  | .unknown, _ | _, .unknown => return true
  | .mvar n, .mvar m =>
    if n != m then bindMeta n b
    return true
  | .mvar n, _ =>
    if occurs n b then return false
    bindMeta n b
    return true
  | _, .mvar m =>
    if occurs m a then return false
    bindMeta m a
    return true
  | .bool, .bool | .nat, .nat | .int, .int | .string, .string | .unit, .unit => return true
  | .option x, .option y | .list x, .list y | .set x, .set y => unify x y
  | .result x e, .result y f => do
    let r1 ← unify x y
    let r2 ← unify e f
    return r1 && r2
  | .table k v, .table k' v' => do
    let r1 ← unify k k'
    let r2 ← unify v v'
    return r1 && r2
  | .tuple xs, .tuple ys => all xs ys
  | .named k _, .named k' _ => return k == k'
  | .fn ps r, .fn qs s => do
    let r1 ← all ps qs
    let r2 ← unify r s
    return r1 && r2
  | _, _ => return false

/-- 期待される型と実際の型を単一化し、合わなければ E014。 -/
def expectTy (ctx : Ctx) (span : Span) (expected actual : TyV) : M Unit := do
  if !(← unify expected actual) then
    let e ← zonk expected
    let a ← zonk actual
    report ctx span Code.typeMismatch s!"expected `{e.render}`, found `{a.render}`"

/-! ## 大域表 -/

/-- 最長の接頭辞で宣言を探し、残りの区切りを返す(`Phase.Tick` → `Phase` と `[Tick]`)。 -/
def lookupEntry (segs : List String) : M (Option (Entry × List String)) := do
  let s ← get
  let mut k := segs.length
  while k > 0 do
    match s.decls.get? (renderPath (segs.take k)) with
    | some e => return some (e, segs.drop k)
    | none => k := k - 1
  return none

def collect (m : Module) : M Unit := do
  for d in m.decls do
    let e : Entry := { file := m.file, qualified := renderPath (m.name ++ [d.name]), decl := d }
    modify fun s => { s with decls := (s.decls.insert d.name e).insert e.qualified e }

/-- Surface の型を内部表現に変換する。型別名は展開する。引数の数の誤りと循環する別名は E014。
`allowFn`: 関数型 `(T1, T2) -> U` を(この位置の最外にだけ)許す。fn / observer / predicate … の仮引数と closure の
引数の型にだけ true。欄・variant・別名・戻り型・コレクションの中は first-order の値だけ(E014)。 -/
partial def convTy (ctx : Ctx) (ty : Ty) (depth : Nat := 0) (allowFn : Bool := false) : M TyV := do
  match ty with
  | .fn span params ret =>
    if !allowFn then
      report ctx span Code.typeMismatch
        "a function type `(T1, T2) -> U` can only be the type of a parameter of a fn / observer / predicate … or of a closure; fields, variants, aliases, return types, inputs and collections hold first-order values"
      return .unknown
    if params.size == 0 then
      report ctx span Code.typeMismatch "a function type needs at least one parameter (`() -> U` is just a value of type `U`)"
      return .unknown
    let ps ← params.toList.mapM (convTy ctx · depth)
    let r ← convTy ctx ret depth
    return .fn ps r
  | .tuple _ elems =>
    let ts ← elems.toList.mapM (convTy ctx · depth)
    return .tuple ts
  | .named span name args =>
    let argsV := (← args.toList.mapM (convTy ctx · depth)).toArray
    let arity (n : Nat) (mk : Array TyV → TyV) : M TyV := do
      if argsV.size != n then
        report ctx span Code.typeMismatch
          s!"`{renderPath name}` takes {n} type argument(s), found {argsV.size}"
        return .unknown
      return mk argsV
    match name with
    | ["Bool"] => arity 0 fun _ => .bool
    | ["Nat"] => arity 0 fun _ => .nat
    | ["Int"] => arity 0 fun _ => .int
    | ["String"] => arity 0 fun _ => .string
    | ["Unit"] => arity 0 fun _ => .unit
    | ["Option"] => arity 1 fun a => .option a[0]!
    | ["Result"] => arity 2 fun a => .result a[0]! a[1]!
    | ["List"] => arity 1 fun a => .list a[0]!
    | ["Set"] => arity 1 fun a => .set a[0]!
    | ["Table"] => arity 2 fun a => .table a[0]! a[1]!
    | _ =>
      match ← lookupEntry name with
      | some (e, []) =>
        match e.decl.kind with
        | .typeAlias =>
          if depth > 32 then
            report ctx span Code.typeMismatch s!"type alias `{e.decl.name}` is cyclic"
            return .unknown
          if argsV.size != 0 then
            report ctx span Code.typeMismatch s!"type `{e.decl.name}` takes no type arguments"
          match e.decl.aliasOf with
          | some t => convTy { ctx with file := e.file } t (depth + 1)
          | none => return .unknown
        | .record | .state | .enum =>
          if argsV.size != 0 then
            report ctx span Code.typeMismatch s!"type `{e.decl.name}` takes no type arguments"
          return .named e.qualified e.decl.name
        | k =>
          -- 通常は Resolve が E013 で止めている。ここに来ても黙らない(unknown は診断の後にだけ作る)
          report ctx span Code.notAType s!"`{e.decl.name}` is a {k.describe}, not a type"
          return .unknown
      | some (e, rest) =>
        report ctx span Code.unresolved
          s!"cannot find type `{renderPath name}`: `{e.decl.name}` has no member type `{renderPath rest}`"
        return .unknown
      | none =>
        report ctx span Code.unresolved s!"cannot find type `{renderPath name}` in this scope"
        return .unknown

def declCtx (m : Module) (d : Decl) : Ctx :=
  { file := m.file, declKind := d.kind, declName := d.name, locals := [] }

def isFnLike : DeclKind → Bool
  | .fn | .input | .observer | .predicate | .condition | .regime | .property | .claim => true
  | _ => false

/-- Lean が record / enum ごとに自動生成する名前。欄・variant には使えない(E012)。 -/
def leanGenerated : List String :=
  ["mk", "rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn", "binductionOn",
   "ibelow", "toCtorIdx", "ofNat", "ctorIdx", "sizeOf", "sizeOf_spec", "inj", "injEq", "ctorElimType"]

def checkMemberName (ctx : Ctx) (span : Span) (what name owner : String) : M Unit := do
  if leanGenerated.contains name then
    report ctx span Code.duplicate
      s!"{what} `{name}` of `{owner}` is reserved: Lean generates a declaration of that name for every record / enum"

/-- 宣言の署名(欄・variant・引数・戻り型)を内部表現にして表に入れる。 -/
def buildInfo (m : Module) (d : Decl) : M Unit := do
  let ctx := declCtx m d
  let q := renderPath (m.name ++ [d.name])
  match d.kind with
  | .record | .state =>
    let mut fs : Array (String × TyV) := #[]
    for f in d.fields do
      if fs.any (·.1 == f.name) then
        report ctx f.span Code.arity s!"field `{f.name}` is declared twice in `{d.name}`"
      checkMemberName ctx f.span "field" f.name d.name
      fs := fs.push (f.name, ← convTy ctx f.ty)
    modify fun s => { s with types := s.types.insert q (.record fs d.derives) }
  | .enum =>
    let mut vs : Array (String × List TyV) := #[]
    for v in d.variants do
      if vs.any (·.1 == v.name) then
        report ctx v.span Code.arity s!"variant `{v.name}` is declared twice in `{d.name}`"
      checkMemberName ctx v.span "variant" v.name d.name
      vs := vs.push (v.name, ← v.args.toList.mapM (convTy ctx))
    modify fun s => { s with types := s.types.insert q (.enum vs d.derives) }
  | .typeAlias =>
    if let some t := d.aliasOf then
      let _ ← convTy ctx t
  | k =>
    if isFnLike k then
      let mut ps : Array (String × TyV) := #[]
      for p in d.params do
        if ps.any (·.1 == p.name) then
          report ctx p.span Code.arity s!"parameter `{p.name}` is declared twice in `{d.name}`"
        -- 関数型の仮引数は fn / observer / spec 宣言にだけ(input は環境が与える first-order の値)
        ps := ps.push (p.name, ← convTy ctx p.ty (allowFn := k != .input))
      let ret ← match d.ret with
        | some t => convTy ctx t
        | none => pure .bool
      modify fun s => { s with fns := s.fns.insert q { kind := k, params := ps, ret } }

/-! ## コンテナ越しの再帰型(E019) -/

/-- record / enum の欄・variant の型が指す型と、コンテナ(Option / List / Set / Table / Result / tuple)の中かどうか。 -/
def typeEdges (info : TypeInfo) : List (String × Bool) :=
  let tys : List TyV := match info with
    | .record fs _ => fs.toList.map (·.2)
    | .enum vs _ => vs.toList.flatMap (·.2)
  tys.flatMap fun t => match t with
    | .named k _ => if k.startsWith "$" then [] else [(k, false)]
    | t => t.namedKeys.map fun k => (k, true)

/-- 型 `start` から欄を辿って届く型(1 辺以上)。 -/
partial def reachTypes (start : String) : M (List String) := do
  let types := (← get).types
  let rec go (todo seen : List String) : List String :=
    match todo with
    | [] => seen
    | x :: rest =>
      let next := match types.get? x with
        | some info => (typeEdges info).map (·.1) |>.filter fun y => !seen.contains y
        | none => []
      go (next ++ rest) (seen ++ next)
  let init := match types.get? start with
    | some info => ((typeEdges info).map (·.1)).eraseDups
    | none => []
  return go init init

/-- コンテナ越しに自分(または自分に戻る型)を参照する record / enum は E019。
Lean の `deriving DecidableEq` / `Ord` は入れ子の帰納型(nested inductive)に使えないので、backend が落とせない。 -/
def checkNestedRecursion (m : Module) (d : Decl) : M Unit := do
  if !(d.kind == .record || d.kind == .state || d.kind == .enum) then return
  let ctx := declCtx m d
  let q := renderPath (m.name ++ [d.name])
  let some info := (← get).types.get? q | return
  for (k, nested) in typeEdges info do
    if !nested then continue
    if k == q || (← reachTypes k).contains q then
      let other := if k == q then "itself" else s!"`{((k.splitOn ".").getLast!)}` (which refers back to `{d.name}`)"
      report ctx d.span Code.nestedRecursion
        s!"{d.kind.describe} `{d.name}` refers to {other} inside a container type (Option / List / Set / Table / Result / tuple); recursion must go through a direct field or variant argument — split the type into mutually recursive enums or use an id instead"
      return

/-! ## capability -/

/-- 型が capability を持つか。`none` = まだ分からない(メタ変数・不明)。 -/
partial def hasCap (cap : String) (t : TyV) : M (Option Bool) := do
  let t ← zonk t
  let all (ts : List TyV) : M (Option Bool) := do
    let mut r : Option Bool := some true
    for x in ts do
      match ← hasCap cap x with
      | some true => pure ()
      | some false => return some false
      | none => r := none
    return r
  match cap, t with
  | _, .unknown | _, .mvar _ => return none
  | _, .named k _ =>
    match (← get).types.get? k with
    | some (.record _ ds) | some (.enum _ ds) => return some (ds.contains cap)
    | none => return none
  | "eq", .bool | "eq", .nat | "eq", .int | "eq", .string | "eq", .unit => return some true
  | "eq", .option a | "eq", .list a | "eq", .set a => all [a]
  | "eq", .result a e | "eq", .table a e => all [a, e]
  | "eq", .tuple ts => all ts
  | "order", .bool | "order", .nat | "order", .int | "order", .string => return some true
  | "order", .option a | "order", .list a => all [a]
  | "order", .tuple ts => all ts
  | _, _ => return some false

def requireCap (ctx : Ctx) (span : Span) (cap : String) (t : TyV) (what : String) : M Unit := do
  match ← hasCap cap t with
  | some false =>
    let tz ← zonk t
    report ctx span Code.missingCapability
      s!"{what} requires the `{cap}` capability on `{tz.render}`; add `derive {cap}` to its declaration"
  | _ => pure ()

/-! ## stdlib メソッド表 -/

/-- メソッド表の型変数。受け手の型引数で束縛する(`T` / `K` / `V` / `E`)か、呼出しごとに fresh(`U`)。 -/
def tv (n : String) : TyV := .named ("$" ++ n) n

def vT := tv "T"
def vU := tv "U"
def vK := tv "K"
def vV := tv "V"
def vE := tv "E"

structure Sig where
  /-- 引数。名前を持つものは `name = e` で渡せる(位置でも可)。 -/
  params : List (Option String × TyV) := []
  ret : TyV
  /-- 要求する capability と、その対象の型。 -/
  caps : List (String × TyV) := []

def pred : TyV := .fn [vT] .bool

/-- `Set<T>`。順序を持たない。要素を 1 つ取る操作は `findUnique?` / `minBy?` / `maxBy?` だけ、
List 化は `sort(by = …)` だけ(IDEAL.md「言語の意味論」)。
`minBy?` / `maxBy?` / `sort` は鍵が同じ要素を要素自身の順序で決めるので、要素にも `order` を要求する。 -/
def setSigs : List (String × Sig) :=
  [ ("size", { ret := .nat }),
    ("isEmpty", { ret := .bool }),
    ("contains", { params := [(none, vT)], ret := .bool, caps := [("eq", vT)] }),
    ("insert", { params := [(none, vT)], ret := .set vT, caps := [("eq", vT)] }),
    ("remove", { params := [(none, vT)], ret := .set vT, caps := [("eq", vT)] }),
    ("union", { params := [(none, .set vT)], ret := .set vT, caps := [("eq", vT)] }),
    ("inter", { params := [(none, .set vT)], ret := .set vT, caps := [("eq", vT)] }),
    ("diff", { params := [(none, .set vT)], ret := .set vT, caps := [("eq", vT)] }),
    ("subset", { params := [(none, .set vT)], ret := .bool, caps := [("eq", vT)] }),
    ("filter", { params := [(none, pred)], ret := .set vT }),
    ("map", { params := [(none, .fn [vT] vU)], ret := .set vU, caps := [("eq", vU)] }),
    -- 各要素の集合の和集合(`Finset.biUnion`)。和集合は可換なので要素の順序に依存しない(E004 の対象ではない)
    ("flatMap", { params := [(none, .fn [vT] (.set vU))], ret := .set vU, caps := [("eq", vU)] }),
    ("any", { params := [(none, pred)], ret := .bool }),
    ("all", { params := [(none, pred)], ret := .bool }),
    ("findUnique?", { params := [(none, pred)], ret := .option vT }),
    ("minBy?", { params := [(none, .fn [vT] vU)], ret := .option vT,
                 caps := [("order", vU), ("order", vT)] }),
    ("maxBy?", { params := [(none, .fn [vT] vU)], ret := .option vT,
                 caps := [("order", vU), ("order", vT)] }),
    ("sort", { params := [(some "by", .fn [vT] vU)], ret := .list vT,
               caps := [("order", vU), ("order", vT)] }),
    -- 可換な集約: 和は要素の順序に依存しないので Set から直接取れる(E004 の対象ではない)
    ("sum", { params := [(none, .fn [vT] .nat)], ret := .nat }) ]

/-- Set から要素を無条件に選ぶ操作(E003)。どれが返るかが集合の内部順序に依存する。 -/
def setChoiceMethods : List String :=
  ["choose", "pick", "first", "first?", "head", "head?", "last", "last?", "find?", "get?",
   "any?", "take", "drop"]

/-- Set を順序の指定なしに並べる操作(E004)。 -/
def setOrderMethods : List String :=
  ["toList", "fold", "foldl", "foldr", "reduce", "enumerate", "zip", "join"]

def listSigs : List (String × Sig) :=
  [ ("size", { ret := .nat }),
    ("isEmpty", { ret := .bool }),
    ("contains", { params := [(none, vT)], ret := .bool, caps := [("eq", vT)] }),
    ("push", { params := [(none, vT)], ret := .list vT }),
    ("append", { params := [(none, .list vT)], ret := .list vT }),
    ("head?", { ret := .option vT }),
    ("last?", { ret := .option vT }),
    ("get?", { params := [(none, .nat)], ret := .option vT }),
    ("find?", { params := [(none, pred)], ret := .option vT }),
    ("filter", { params := [(none, pred)], ret := .list vT }),
    ("map", { params := [(none, .fn [vT] vU)], ret := .list vU }),
    -- 各要素の List の連結(`List.flatMap`)。List は順序を持つので E004 とは無関係
    ("flatMap", { params := [(none, .fn [vT] (.list vU))], ret := .list vU }),
    -- `Some` を返した要素だけを残す(`List.filterMap`)
    ("filterMap", { params := [(none, .fn [vT] (.option vU))], ret := .list vU }),
    ("any", { params := [(none, pred)], ret := .bool }),
    ("all", { params := [(none, pred)], ret := .bool }),
    ("count", { params := [(none, pred)], ret := .nat }),
    ("fold", { params := [(none, vU), (none, .fn [vU, vT] vU)], ret := vU }),
    ("sort", { params := [(some "by", .fn [vT] vU)], ret := .list vT, caps := [("order", vU)] }),
    ("minBy?", { params := [(none, .fn [vT] vU)], ret := .option vT, caps := [("order", vU)] }),
    ("maxBy?", { params := [(none, .fn [vT] vU)], ret := .option vT, caps := [("order", vU)] }),
    ("reverse", { ret := .list vT }),
    ("take", { params := [(none, .nat)], ret := .list vT }),
    ("drop", { params := [(none, .nat)], ret := .list vT }),
    ("sum", { params := [(none, .fn [vT] .nat)], ret := .nat }),
    ("toSet", { ret := .set vT, caps := [("eq", vT)] }) ]

def optionSigs : List (String × Sig) :=
  [ ("isSome", { ret := .bool }),
    ("isNone", { ret := .bool }),
    ("getOr", { params := [(none, vT)], ret := vT }),
    ("map", { params := [(none, .fn [vT] vU)], ret := .option vU }),
    ("andThen", { params := [(none, .fn [vT] (.option vU))], ret := .option vU }),
    ("filter", { params := [(none, pred)], ret := .option vT }) ]

def resultSigs : List (String × Sig) :=
  [ ("isOk", { ret := .bool }),
    ("isErr", { ret := .bool }),
    ("ok?", { ret := .option vT }) ]

def tableSigs : List (String × Sig) :=
  [ ("size", { ret := .nat }),
    ("isEmpty", { ret := .bool }),
    ("get?", { params := [(none, vK)], ret := .option vV, caps := [("eq", vK)] }),
    ("getOr", { params := [(none, vK), (none, vV)], ret := vV, caps := [("eq", vK)] }),
    ("contains", { params := [(none, vK)], ret := .bool, caps := [("eq", vK)] }),
    ("insert", { params := [(none, vK), (none, vV)], ret := .table vK vV, caps := [("eq", vK)] }),
    ("remove", { params := [(none, vK)], ret := .table vK vV, caps := [("eq", vK)] }),
    ("keys", { ret := .set vK, caps := [("eq", vK)] }),
    ("entries", { ret := .set (.tuple [vK, vV]), caps := [("eq", vK), ("eq", vV)] }),
    -- 鍵を保って値だけを写す(`fun k => f (t k)`)。鍵の順序で正規化された表なので要素の順序に依存しない
    ("mapValues", { params := [(none, .fn [vV] vU)], ret := .table vK vU, caps := [("eq", vK)] }) ]

def natSigs : List (String × Sig) :=
  [ ("min", { params := [(none, .nat)], ret := .nat }),
    ("max", { params := [(none, .nat)], ret := .nat }),
    ("toInt", { ret := .int }) ]

def intSigs : List (String × Sig) :=
  [ ("min", { params := [(none, .int)], ret := .int }),
    ("max", { params := [(none, .int)], ret := .int }),
    ("abs", { ret := .nat }),
    -- 床除算(`-7.fdiv(2) == -4`。除数 0 なら 0)と、負を 0 に切り上げる Nat 化
    ("fdiv", { params := [(none, .int)], ret := .int }),
    ("toNat", { ret := .nat }) ]

def stringSigs : List (String × Sig) :=
  [ ("size", { ret := .nat }),
    ("append", { params := [(none, .string)], ret := .string }) ]

/-- 受け手の型から、型の名前・束縛する型変数・メソッド表を引く。 -/
def sigsFor : TyV → Option (String × List (String × TyV) × List (String × Sig))
  | .set t => some ("Set", [("$T", t)], setSigs)
  | .list t => some ("List", [("$T", t)], listSigs)
  | .option t => some ("Option", [("$T", t)], optionSigs)
  | .result t e => some ("Result", [("$T", t), ("$E", e)], resultSigs)
  | .table k v => some ("Table", [("$K", k), ("$V", v)], tableSigs)
  | .nat => some ("Nat", [], natSigs)
  | .int => some ("Int", [], intSigs)
  | .string => some ("String", [], stringSigs)
  | _ => none

partial def collectVars (t : TyV) (acc : List String) : List String :=
  match t with
  | .named k _ => if k.startsWith "$" && !acc.contains k then k :: acc else acc
  | .option a | .list a | .set a => collectVars a acc
  | .result a b | .table a b => collectVars b (collectVars a acc)
  | .tuple ts => ts.foldl (fun a x => collectVars x a) acc
  | .fn ps r => collectVars r (ps.foldl (fun a x => collectVars x a) acc)
  | _ => acc

partial def substVars (env : List (String × TyV)) : TyV → TyV
  | .named k d => match env.lookup k with
    | some t => t
    | none => .named k d
  | .option a => .option (substVars env a)
  | .result a b => .result (substVars env a) (substVars env b)
  | .list a => .list (substVars env a)
  | .set a => .set (substVars env a)
  | .table a b => .table (substVars env a) (substVars env b)
  | .tuple ts => .tuple (ts.map (substVars env))
  | .fn ps r => .fn (ps.map (substVars env)) (substVars env r)
  | t => t

/-- 署名の型変数を、受け手から束縛したものはその型に、残りは fresh なメタ変数に置き換える。 -/
def instSig (bound : List (String × TyV)) (sig : Sig) :
    M (List (Option String × TyV) × TyV × List (String × TyV)) := do
  let tys := sig.ret :: sig.params.map (·.2) ++ sig.caps.map (·.2)
  let vars := tys.foldl (fun acc t => collectVars t acc) []
  let mut env := bound
  for v in vars do
    if (env.lookup v).isNone then env := (v, ← fresh) :: env
  let ps := sig.params.map fun (n, t) => (n, substVars env t)
  let caps := sig.caps.map fun (c, t) => (c, substVars env t)
  return (ps, substVars env sig.ret, caps)

def litTy : Lit → TyV
  | .nat _ => .nat
  | .str _ => .string
  | .bool _ => .bool
  | .unit => .unit

def argExpr : Arg → Expr
  | .pos e => e
  | .named _ e => e

def describeCallee : Expr → String
  | .var _ segs => s!"`{renderPath segs}`"
  | _ => "this call"

def choiceMsg (what : String) : String :=
  s!"{what} selects an element without a condition; which element is returned is not deterministic. Use `findUnique?`, `minBy?` / `maxBy?`, or `sort(by = …)` and then index the List"

def orderMsg (what : String) : String :=
  s!"{what} turns a Set into an ordered sequence without saying which order; use `sort(by = …)` to make the order explicit"

def isCatchAllPat : Pattern → Bool
  | .wild _ | .bind .. => true
  | _ => false

/-- match の腕の形(E018)。(1) 最後の腕にガードがあると、ガードが偽のときどの腕も一致しない。
(2) Nat / Int / String はリテラルでは覆えないので、ガードの無い `_` か束縛の腕が要る。
他の型の網羅性は backend が出す Lean の match が検査する。 -/
def checkMatchShape (ctx : Ctx) (span : Span) (st : TyV) (arms : Array Arm) : M Unit := do
  if let some (.mk _ (some g) _) := arms.back? then
    report ctx g.span Code.matchShape
      "the last arm of a `match` must not have a guard: when the guard is false, no arm matches. Add an unconditional arm after it"
  match ← zonk st with
  | .nat | .int | .string =>
    let hasCatchAll := arms.any fun
      | .mk p none _ => isCatchAllPat p
      | _ => false
    if !hasCatchAll then
      report ctx span Code.matchShape
        s!"a `match` on `{(← zonk st).render}` needs an unconditional `_` or variable arm: literals cannot cover every value"
  | _ => pure ()

/-- ブロックの束縛を `let_` の入れ子にする。 -/
def mkLets (binds : List (String × TyV × CExpr)) (tail : CExpr) : CExpr :=
  binds.foldr (fun (n, t, v) body => .let_ n t v body) tail

/-! ## Prop と Bool の境界(C35)

spec 宣言の Bool の式のうち、量化・spec 宣言の呼出し・Prop に束ねた局所名を含むものは Lean の Prop にしかならない
(Statements backend の `proppy` と同じ規則)。それを実行可能な Bool の値が要る位置(fn / メソッドの実引数・欄・コレクションの
要素・lambda の本体・scrutinee・算術 / 比較の被演算子 …)に書くと、backend は `(∀ …) = true` のような Lean が拒否する形しか
出せない。量化を実行する機能も classical な判定も naru に無いので(IDEAL.md)、ここで E014 にして生成に進ませない。 -/

partial def patVarsOf : CPat → List String
  | .bind n => [n]
  | .tuple ps | .builtin _ ps | .variant _ _ ps => ps.flatMap patVarsOf
  | _ => []

/-- Prop でしか表せない Core の式か。`isSpec` は修飾名が spec 宣言か、`propVars` は Prop に束ねた局所名。 -/
partial def proppy (isSpec : String → Bool) (propVars : List String) : CExpr → Bool
  | .quant .. => true
  | .call k args => isSpec k || args.any (proppy isSpec propVars)
  | .global k => isSpec k
  | .var n => propVars.contains n
  | .binop _ l r _ => proppy isSpec propVars l || proppy isSpec propVars r
  | .unop _ a => proppy isSpec propVars a
  | .ite a b d => proppy isSpec propVars a || proppy isSpec propVars b || proppy isSpec propVars d
  | .match_ s _ arms =>
    proppy isSpec propVars s || arms.any fun
      | .mk p g b =>
        let pv := propVars.filter fun n => !(patVarsOf p).contains n
        (g.map (proppy isSpec pv)).getD false || proppy isSpec pv b
  | .let_ n _ v b => proppy isSpec propVars v || proppy isSpec (propVars.filter (· != n)) b
  | .lambda ps b => proppy isSpec (propVars.filter fun n => !ps.any (·.1 == n)) b
  | .callLocal f args => proppy isSpec propVars f || args.any (proppy isSpec propVars)
  | .method _ _ r args _ => proppy isSpec propVars r || args.any (proppy isSpec propVars)
  | .builtin _ args _ | .variant _ _ args | .tuple args | .list args _ => args.any (proppy isSpec propVars)
  | .field r _ _ => proppy isSpec propVars r
  | .record _ fs base => fs.any (fun (_, x) => proppy isSpec propVars x) || (base.map (proppy isSpec propVars)).getD false
  | .lit .. | .error => false

/-- いまの大域表で、修飾名が spec 宣言か。 -/
def specKeyPred : M (String → Bool) := do
  let fns := (← get).fns
  return fun k => ((fns.get? k).map (·.kind.phase == .spec)).getD false

def shortKey (k : String) : String := (k.splitOn ".").getLast!

/-- 値の位置に置かれた Prop の文面(根になった式の種類で言い分ける)。 -/
def propAsValueMsg (ctx : Ctx) (c : CExpr) : String :=
  let what := if ctx.valueWhat.isEmpty then "this position" else ctx.valueWhat
  let subject := match c with
    | .quant q .. => s!"`{if q == Quant.forall_ then "forall" else "exists"}` is a proposition"
    | .call k _ | .global k => s!"`{shortKey k}` is a spec declaration, so `{shortKey k}(…)` is a proposition"
    | .var n => s!"`{n}` is bound to a proposition by `let`"
    | _ => "this expression is a proposition (it contains a quantifier or a call of a spec declaration)"
  s!"{subject}, not a Bool value, but {what} needs a Bool value (a proposition cannot be computed; naru does not decide quantifiers or spec declarations). Keep it in the logical structure of the declaration (`&&` / `||` / `!` / `implies`, the condition of `if`, the guard of `match`, a Bool `let`) or iterate a finite collection with `all` / `any` / `filter` instead"

/-- 値の位置(spec 宣言の `propPos = false`)で Prop でしか表せない式を E014 にする。報告した式は `.error` に置き換えて、
外側の式まで Prop と判定される波及を止める(根になった式だけを 1 度報告する)。 -/
def valueGuard (ctx : Ctx) (span : Span) (c : CExpr) : M CExpr := do
  if ctx.propPos || ctx.declKind.phase != .spec then return c
  if !proppy (← specKeyPred) ctx.propVars c then return c
  report ctx span Code.typeMismatch (propAsValueMsg ctx c)
  return .error

/-- Prop の位置の `let` / `e;` / `==` の被演算子: Bool 以外の型の式が Prop に依存していれば(`if P(x) \{ 1 } else \{ 2 }` の
ように Prop の条件で値を選ぶ)E014。Bool の Prop なら true を返す(`let` はその名前を Prop として束ねる)。 -/
def propValueCheck (ctx : Ctx) (span : Span) (what : String) (t : TyV) (c : CExpr) : M Bool := do
  if !(ctx.propPos && ctx.declKind.phase == .spec) then return false
  if !proppy (← specKeyPred) ctx.propVars c then return false
  match ← zonk t with
  | .bool => return true
  | tz =>
    report ctx span Code.typeMismatch
      s!"{what} is a value of type `{tz.render}` that depends on a proposition (a quantifier or a call of a spec declaration decides it), but only a Bool expression can be a proposition; a proposition cannot select a value — move the `if` / `match` on the proposition to the logical structure of the declaration"
    return false

/-- 欄 / メソッドのアクセスの受け手の型を索引に残す(C31。名前が解決できるかに関わらず)。 -/
def recordAccess (ctx : Ctx) (span : Span) (name : String) (recv : TyV) : M Unit :=
  modify fun s => { s with accesses := s.accesses.push { file := ctx.file, span, name, recv } }

/-! ## 式 -/

mutual

/-- 式の型を推論し、Core に elaborate する。誤りは報告して `unknown` / `.error` を返す。
値の位置に Prop でしか表せない式があれば E014(`valueGuard`。C35)。 -/
partial def infer (ctx : Ctx) (e : Expr) : M (TyV × CExpr) := do
  let (t, c) ← inferCore ctx e
  return (t, ← valueGuard ctx e.span c)

/-- 期待される型に対して検査し、Core に elaborate する(`checkCore` + `valueGuard`)。 -/
partial def check (ctx : Ctx) (e : Expr) (expected : TyV) : M CExpr := do
  valueGuard ctx e.span (← checkCore ctx e expected)

partial def inferCore (ctx : Ctx) (e : Expr) : M (TyV × CExpr) := do
  match e with
  | .lit _ l => return (litTy l, .lit l (litTy l))
  | .var span segs => inferVar ctx span segs
  | .call span f args => inferCall ctx span f args
  | .field span r name => inferField ctx span r name
  | .method span r name args =>
    -- `x.f(args)` は、`f` がユーザ宣言の大域名なら `f(x, args)` の糖衣(UFCS。Resolve と同じ規則)
    if (ctx.locals.lookup name).isNone then
      if let some (_, []) ← lookupEntry [name] then
        return ← inferCall ctx span (.var span [name]) (#[.pos r] ++ args)
    inferMethod ctx span r name args
  | .binop span op l r => inferBinop ctx span op l r
  | .unop _ "!" a =>
    let c ← check ctx a .bool
    return (.bool, .unop "!" c)
  | .unop _ "-" a =>
    match a with
    | .lit _ (.nat n) => return (.int, .unop "-" (.lit (.nat n) .int))
    | _ =>
      let c ← check (ctx.value "the operand of `-`") a .int
      return (.int, .unop "-" c)
  | .unop _ op a =>
    let (t, c) ← infer (ctx.value s!"the operand of `{op}`") a
    return (t, .unop op c)
  | .ite _ c t el =>
    -- 条件と分岐は外側の位置を引き継ぐ(Prop の位置なら Prop の条件 `(c → a) ∧ (¬ c → b)` になる)
    let cc ← check ctx c .bool
    let (tt, ct) ← infer ctx t
    let ce ← check ctx el tt
    return (tt, .ite cc ct ce)
  | .matchE span s arms =>
    let (st, cs) ← infer (ctx.value "the value matched on") s
    if arms.isEmpty then
      report ctx span Code.typeMismatch "`match` needs at least one arm"
      return (.unknown, .error)
    let mut rt : Option TyV := none
    let mut carms : List CArm := []
    for arm in arms do
      let .mk pat guard body := arm
      let (binds, cp) ← checkPat ctx st pat
      let c := ctx.bind binds
      let cg ← match guard with
        | some g => pure (some (← check c g .bool))
        | none => pure none
      let cb ← match rt with
        | none =>
          let (t, cb) ← infer c body
          rt := some t
          pure cb
        | some t => check c body t
      carms := carms ++ [.mk cp cg cb]
    checkMatchShape ctx span st arms
    return (rt.getD .unknown, .match_ cs st carms)
  | .block _ stmts tail =>
    let (c, binds) ← inferStmts ctx stmts
    match tail with
    | some t =>
      let (tt, ct) ← infer c t
      return (tt, mkLets binds ct)
    | none => return (.unit, mkLets binds (.lit .unit .unit))
  | .recordLit span name fields base => inferRecordLit ctx span name fields base
  | .listLit span elems =>
    let m ← fresh
    let cs ← elems.toList.mapM (check (ctx.value "an element of a list") · m)
    need span m "this list's elements"
    return (.list m, .list cs m)
  | .tupleLit _ elems =>
    let rs ← elems.toList.mapM (infer (ctx.value "a component of a tuple"))
    return (.tuple (rs.map (·.1)), .tuple (rs.map (·.2)))
  | .lambda _ params body =>
    let mut ps : List TyV := []
    let mut binds : List (String × TyV) := []
    for p in params do
      let t ← match p.ty with
        | some a => convTy ctx a (allowFn := true)
        | none =>
          let m ← fresh
          need p.span m s!"parameter `{p.name}` of this closure"
          pure m
      ps := ps ++ [t]
      binds := binds ++ [(p.name, t)]
    -- closure は計算される値(stdlib の `all` / `any` / `filter` … が実行する)なので、本体は値の位置
    let (r, cb) ← infer ((ctx.bind binds).value "the result of a closure") body
    return (.fn ps r, .lambda binds cb)
  | .quant span q binders body =>
    if ctx.declKind.phase == .runtime then
      let qn := if q == .forall_ then "forall" else "exists"
      report ctx span Code.infiniteQuantification
        s!"`{qn}` quantifies over a possibly infinite domain and cannot be evaluated in a runtime declaration ({ctx.declKind.describe} `{ctx.declName}`); iterate a finite collection (`all` / `any` / `filter`) instead"
    let mut binds : List (String × TyV) := []
    for b in binders do
      let t ← match b.ty with
        | some a => convTy ctx a
        | none =>
          let m ← fresh
          need b.span m s!"`{b.name}` bound by this quantifier"
          pure m
      binds := binds ++ [(b.name, t)]
    let cb ← check (ctx.bind binds).prop body .bool
    return (.bool, .quant q binds cb)

/-- 期待される型に対して検査し、Core に elaborate する。lambda・分岐・ブロック・リストには期待を内側へ伝える。 -/
partial def checkCore (ctx : Ctx) (e : Expr) (expected : TyV) : M CExpr := do
  match e with
  | .lambda span params body =>
    match ← zonk expected with
    | .fn ps r =>
      if ps.length != params.size then
        report ctx span Code.typeMismatch
          s!"this closure takes {params.size} parameter(s), but {ps.length} expected"
        return .error
      let mut binds : List (String × TyV) := []
      for (p, t) in params.toList.zip ps do
        if let some a := p.ty then
          let at_ ← convTy ctx a (allowFn := true)
          expectTy ctx p.span t at_
        binds := binds ++ [(p.name, t)]
      let cb ← check ((ctx.bind binds).value "the result of a closure") body r
      return .lambda binds cb
    | _ =>
      let (t, c) ← inferCore ctx e
      expectTy ctx span expected t
      return c
  | .ite _ c t el =>
    let cc ← check ctx c .bool
    let ct ← check ctx t expected
    let ce ← check ctx el expected
    return .ite cc ct ce
  | .matchE span s arms =>
    let (st, cs) ← infer (ctx.value "the value matched on") s
    if arms.isEmpty then
      report ctx span Code.typeMismatch "`match` needs at least one arm"
      return .error
    let mut carms : List CArm := []
    for arm in arms do
      let .mk pat guard body := arm
      let (binds, cp) ← checkPat ctx st pat
      let c := ctx.bind binds
      let cg ← match guard with
        | some g => pure (some (← check c g .bool))
        | none => pure none
      let cb ← check c body expected
      carms := carms ++ [.mk cp cg cb]
    checkMatchShape ctx span st arms
    return .match_ cs st carms
  | .lit span (.nat n) =>
    -- 数値リテラルは Nat だが、Int が期待される位置では Int として読む
    match ← zonk expected with
    | .int => return .lit (.nat n) .int
    | _ =>
      expectTy ctx span expected .nat
      return .lit (.nat n) .nat
  | .block span stmts tail =>
    let (c, binds) ← inferStmts ctx stmts
    match tail with
    | some t => return mkLets binds (← check c t expected)
    | none =>
      expectTy ctx span expected .unit
      return mkLets binds (.lit .unit .unit)
  | .listLit span elems =>
    match ← zonk expected with
    | .list t =>
      let cs ← elems.toList.mapM (check (ctx.value "an element of a list") · t)
      return .list cs t
    | _ =>
      let (t, c) ← inferCore ctx e
      expectTy ctx span expected t
      return c
  | _ =>
    let (t, c) ← inferCore ctx e
    expectTy ctx e.span expected t
    return c

/-- ブロックの文。束縛(名前・型・値)の列と、束縛後の文脈を返す。`e;` 文は名前 `_`。 -/
partial def inferStmts (ctx : Ctx) (stmts : Array Stmt) : M (Ctx × List (String × TyV × CExpr)) := do
  let mut c := ctx
  let mut binds : List (String × TyV × CExpr) := []
  for st in stmts do
    match st with
    | .letS span name ty val =>
      -- Prop の位置では値も Prop の位置(`let all = forall …;` は Prop の束縛)。値の位置では値の位置のまま
      let (t, cv) ← match ty with
        | some a =>
          let at_ ← convTy c a (allowFn := true)
          let cv ← check c val at_
          pure (at_, cv)
        | none =>
          let (t, cv) ← infer c val
          need span t s!"`{name}`"
          pure (t, cv)
      let isProp ← propValueCheck c val.span s!"the value of `{name}`" t cv
      binds := binds ++ [(name, t, cv)]
      c := c.bind [(name, t)]
      if isProp then c := { c with propVars := name :: c.propVars }
    | .exprS x =>
      let (t, cx) ← infer c x
      let _ ← propValueCheck c x.span "this expression statement" t cx
      binds := binds ++ [("_", t, cx)]
    | .inputS span name .. =>
      -- パーサは scenario の本体にしか作らない(scenario は `checkScenario` が読む)
      report c span Code.typeMismatch s!"`input {name}(…) = …;` can only appear at the head of a scenario"
    | .observeS span _ =>
      report c span Code.typeMismatch "`observe` can only appear in a scenario"
  return (c, binds)

partial def inferVar (ctx : Ctx) (span : Span) (segs : List String) : M (TyV × CExpr) := do
  match segs with
  | [] => return (.unknown, .error)
  | head :: rest =>
    if rest.isEmpty then
      if let some t := ctx.locals.lookup head then return (t, .var head)
    if Resolve.isBuiltinHead head then return ← inferBuiltin ctx span head rest
    match ← lookupEntry segs with
    | none => return (.unknown, .error)   -- E011 は Resolve が報告済み
    | some (e, rest') =>
      let k := e.decl.kind
      if isFnLike k then
        if !rest'.isEmpty then
          report ctx span Code.arity s!"`{e.decl.name}` has no member `{renderPath rest'}`"
          return (.unknown, .error)
        match (← get).fns.get? e.qualified with
        | some fi => return (.fn (fi.params.toList.map (·.2)) fi.ret, .global e.qualified)
        | none => return (.unknown, .error)
      else if k.isType then
        let prefixLen := segs.length - rest'.length
        let t ← convTy ctx (.named span (segs.take prefixLen) #[])
        match ← zonk t with
        | .named key d =>
          match (← get).types.get? key with
          | some (.enum vs _) =>
            match rest' with
            | [v] =>
              match vs.toList.lookup v with
              | some [] => return (.named key d, .variant key v [])
              | some argTys => return (.fn argTys (.named key d), .variant key v [])
              | none =>
                report ctx span Code.arity s!"enum `{d}` has no variant `{v}`"
                return (.unknown, .error)
            | [] =>
              report ctx span Code.typeMismatch s!"enum `{d}` cannot be used as a value; name one of its variants (`{d}.Variant`)"
              return (.unknown, .error)
            | _ =>
              report ctx span Code.arity s!"`{renderPath segs}` is not a variant of enum `{d}`"
              return (.unknown, .error)
          | _ =>
            report ctx span Code.typeMismatch s!"type `{d}` cannot be used as a value"
            return (.unknown, .error)
        | .unknown => return (.unknown, .error)   -- convTy が報告済み
        | tz =>
          -- 型別名が展開された型(`type Count = Nat` の `Count`)。黙らない(C35)
          report ctx span Code.typeMismatch s!"type `{e.decl.name}` (= `{tz.render}`) cannot be used as a value"
          return (.unknown, .error)
      else
        match k with
        | .claimBundle =>
          report ctx span Code.typeMismatch
            s!"claim bundle `{e.decl.name}` can only be referenced from another claim bundle"
        | _ =>
          report ctx span Code.typeMismatch s!"`{e.decl.name}` is a {k.describe}, not a value"
        return (.unknown, .error)

/-- 組み込みの構築子と静的関数(`Some` / `None` / `Ok` / `Err` / `Set.empty` …)。
値としての参照(引数なし)。呼出しは `inferCall` が引数を付ける。 -/
partial def inferBuiltin (ctx : Ctx) (span : Span) (head : String) (rest : List String) : M (TyV × CExpr) := do
  let name := renderPath (head :: rest)
  let ok (t : TyV) : M (TyV × CExpr) := return (t, .builtin name [] t)
  match head, rest with
  | "Some", [] =>
    let m ← fresh
    ok (.fn [m] (.option m))
  | "None", [] =>
    let m ← fresh
    need span m "`None`"
    ok (.option m)
  | "Ok", [] =>
    let m ← fresh
    let err ← fresh
    ok (.fn [m] (.result m err))
  | "Err", [] =>
    let m ← fresh
    let err ← fresh
    ok (.fn [err] (.result m err))
  | "choose", [] | "pick", [] =>
    report ctx span Code.choose (choiceMsg s!"`{head}`")
    return (.unknown, .error)
  | "sort", [] =>
    report ctx span Code.arity "`sort` must be called as `sort(xs, by = …)`"
    return (.unknown, .error)
  | "Set", ["empty"] =>
    let m ← fresh
    ok (.fn [] (.set m))
  | "Set", ["singleton"] =>
    let m ← fresh
    -- Set の要素は `eq`(正規化の順序)を要する。要素の型は実引数で決まるので宣言の終わりに検査する
    deferCap span "eq" m "`Set.singleton` (its element)"
    ok (.fn [m] (.set m))
  | "Set", ["of"] =>
    let m ← fresh
    deferCap span "eq" m "`Set.of` (its elements)"
    ok (.fn [.list m] (.set m))
  | "List", ["empty"] =>
    let m ← fresh
    ok (.fn [] (.list m))
  | "List", ["range"] => ok (.fn [.nat] (.list .nat))
  | "Table", ["empty"] =>
    let k ← fresh
    let v ← fresh
    ok (.fn [] (.table k v))
  | _, _ =>
    report ctx span Code.arity s!"`{name}` is not a known built-in"
    return (.unknown, .error)

/-- 呼出し。`sort(xs, by = …)` は `xs.sort(by = …)` の糖衣。呼出し先の Core の形
(fn の `global` / 組み込みの `builtin` / enum の `variant`)で、Core の呼出しの形を決める。 -/
partial def inferCall (ctx : Ctx) (span : Span) (f : Expr) (args : Array Arg) : M (TyV × CExpr) := do
  match f with
  | .var vsp ["sort"] =>
    match args.toList with
    | .pos recv :: rest => inferMethod ctx vsp recv "sort" rest.toArray
    | _ =>
      report ctx vsp Code.arity "`sort(xs, by = …)` needs the collection as its first argument"
      inferArgsLoosely ctx args
      return (.unknown, .error)
  | _ =>
    -- 呼出し先そのものは `valueGuard` に掛けない(spec 宣言の参照は呼出し全体として Prop になる)
    let (ft0, cf) ← inferCore ctx f
    let ft ← zonk ft0
    match ft with
    | .fn ps r =>
      let names ← calleeParamNames ctx f
      let params := match names with
        | some ns => (ns.zip ps).map fun (n, t) => (some n, t)
        | none => ps.map fun t => (none, t)
      let cargs ← matchArgs ctx span (describeCallee f) params args
      let call : CExpr := match cf with
        | .global key => .call key cargs.toList
        | .builtin name [] _ => .builtin name cargs.toList r
        | .variant key v [] => .variant key v cargs.toList
        | _ => .callLocal cf cargs.toList
      if let .builtin name _ _ := call then
        need span r s!"the result of `{name}`"
      return (r, call)
    | .unknown =>
      inferArgsLoosely ctx args
      return (.unknown, .error)
    | .mvar _ =>
      report ctx span Code.typeMismatch "cannot determine the type of the callee; add a type annotation"
      inferArgsLoosely ctx args
      return (.unknown, .error)
    | t =>
      report ctx span Code.typeMismatch s!"{describeCallee f} is not callable (its type is `{t.render}`)"
      inferArgsLoosely ctx args
      return (.unknown, .error)

/-- 呼出し先がユーザ宣言の fn 等なら、その引数名(名前付き引数のため)。局所名(関数型の仮引数・lambda)は
大域名を隠すので、名前付き引数は使えない。 -/
partial def calleeParamNames (ctx : Ctx) (f : Expr) : M (Option (List String)) := do
  match f with
  | .var _ segs =>
    match segs with
    | [head] =>
      if Resolve.isBuiltinHead head then return none
      if (ctx.locals.lookup head).isSome then return none
    | _ => pure ()
    match ← lookupEntry segs with
    | some (e, []) =>
      if isFnLike e.decl.kind then
        match (← get).fns.get? e.qualified with
        | some fi => return some (fi.params.toList.map (·.1))
        | none => return none
      else return none
    | _ => return none
  | _ => return none

/-- 既に誤りを報告した呼出しの実引数を、波及を抑えつつ検査する。その間に積まれた「型が要る位置」は捨てる
(誤りの後の lambda の引数などに余計な E014 を出さない)。 -/
partial def inferArgsLoosely (ctx : Ctx) (args : Array Arg) : M Unit := do
  let before := (← get).pending.size
  let beforeCaps := (← get).pendingCaps.size
  for a in args do
    let _ ← infer (ctx.value "an argument") (argExpr a)
  modify fun s => { s with pending := s.pending.extract 0 before, pendingCaps := s.pendingCaps.extract 0 beforeCaps }

/-- 実引数を仮引数に割り当てて検査する。位置引数は順に、名前付き引数は名前で。
仮引数の順に並んだ Core の実引数を返す(欠けた位置は `.error`)。 -/
partial def matchArgs (ctx : Ctx) (span : Span) (what : String)
    (params : List (Option String × TyV)) (args : Array Arg) : M (Array CExpr) := do
  let ps := params.toArray
  let mut slots : Array (Option Expr) := ps.map fun _ => none
  let mut pos := 0
  let mut sawNamed := false
  for a in args do
    match a with
    | .pos x =>
      if sawNamed then
        -- 位置引数は名前付き引数より前に置く(後ろに置くと、どの枠かが読めない)
        report ctx x.span Code.arity s!"positional argument to {what} after a named argument; put positional arguments first"
        let _ ← infer ctx x
      else if pos < ps.size then
        slots := slots.set! pos (some x)
        pos := pos + 1
      else
        report ctx x.span Code.arity s!"too many arguments to {what}: expected {ps.size}"
        let _ ← infer ctx x
    | .named n x =>
      sawNamed := true
      match ps.findIdx? (fun p => p.1 == some n) with
      | some i =>
        if slots[i]!.isSome then
          report ctx x.span Code.arity s!"argument `{n}` to {what} is given twice"
        slots := slots.set! i (some x)
      | none =>
        report ctx x.span Code.arity s!"{what} has no parameter named `{n}`"
        let _ ← infer ctx x
  let mut out : Array CExpr := #[]
  for i in [0:ps.size] do
    match slots[i]! with
    | some x =>
      let pname := match ps[i]!.1 with
        | some n => s!"the argument `{n}` of {what}"
        | none => s!"an argument of {what}"
      out := out.push (← check (ctx.value pname) x ps[i]!.2)
    | none =>
      let pname := match ps[i]!.1 with
        | some n => s!"`{n}`"
        | none => s!"#{i + 1}"
      report ctx span Code.arity s!"missing argument {pname} to {what}"
      out := out.push .error
  return out

partial def inferField (ctx : Ctx) (span : Span) (r : Expr) (name : String) : M (TyV × CExpr) := do
  let (rt0, cr) ← infer (ctx.value s!"the value before `.{name}`") r
  let rt ← zonk rt0
  recordAccess ctx span name rt
  match rt with
  | .named k d =>
    match (← get).types.get? k with
    | some (.record fs _) =>
      match fs.toList.lookup name with
      | some t =>
        let m : MemberRef :=
          { file := ctx.file, span := span, kind := .field, owner := k, ownerName := d, name := name, recv := rt, ret := t }
        modify fun s => { s with members := s.members.push m }
        return (t, .field cr k name)
      | none =>
        report ctx span Code.arity s!"record `{d}` has no field `{name}`"
        return (.unknown, .error)
    | some (.enum ..) =>
      report ctx span Code.arity s!"enum `{d}` has no field `{name}`"
      return (.unknown, .error)
    | none => return (.unknown, .error)
  | .unknown => return (.unknown, .error)
  | .mvar _ =>
    report ctx span Code.typeMismatch
      s!"cannot determine the type of the value before `.{name}`; add a type annotation"
    return (.unknown, .error)
  | t =>
    let hint := match sigsFor t with
      | some (_, _, sigs) => if (sigs.lookup name).isSome then s!" (did you mean `{name}()`?)" else ""
      | none => ""
    report ctx span Code.arity s!"type `{t.render}` has no field `{name}`{hint}"
    return (.unknown, .error)

/-- stdlib メソッドの呼出し。Set の選択(E003)と順序(E004)の検査はここ。 -/
partial def inferMethod (ctx : Ctx) (span : Span) (r : Expr) (name : String) (args : Array Arg) :
    M (TyV × CExpr) := do
  let (rt0, cr) ← infer (ctx.value s!"the receiver of `.{name}()`") r
  let rt ← zonk rt0
  recordAccess ctx span name rt
  match rt with
  | .unknown =>
    inferArgsLoosely ctx args
    return (.unknown, .error)
  | .mvar _ =>
    report ctx span Code.typeMismatch
      s!"cannot determine the type of the receiver of `.{name}()`; add a type annotation"
    inferArgsLoosely ctx args
    return (.unknown, .error)
  | _ =>
    if let .set _ := rt then
      if setChoiceMethods.contains name then
        report ctx span Code.choose (choiceMsg s!"`Set.{name}`")
        inferArgsLoosely ctx args
        return (.unknown, .error)
      if setOrderMethods.contains name then
        report ctx span Code.orderLoss (orderMsg s!"`Set.{name}`")
        inferArgsLoosely ctx args
        return (.unknown, .error)
      if name == "sort" && args.isEmpty then
        report ctx span Code.orderLoss (orderMsg "`Set.sort` without `by = …`")
        return (.unknown, .error)
    match sigsFor rt with
    | none =>
      let msg := match rt with
        | .named _ d => s!"`{d}` has no method `{name}`; declare a fn and call it as `{name}(x)` or `x.{name}()`"
        | t => s!"type `{t.render}` has no method `{name}`"
      report ctx span Code.arity msg
      inferArgsLoosely ctx args
      return (.unknown, .error)
    | some (tyName, bound, sigs) =>
      match sigs.lookup name with
      | none =>
        report ctx span Code.arity s!"`{tyName}` has no method `{name}`"
        inferArgsLoosely ctx args
        return (.unknown, .error)
      | some sig =>
        let (ps, ret, caps) ← instSig bound sig
        let cargs ← matchArgs ctx span s!"`{tyName}.{name}`" ps args
        for (cap, t) in caps do
          requireCap ctx span cap t s!"`{tyName}.{name}`"
        need span ret s!"the result of `{tyName}.{name}`"
        let m : MemberRef :=
          { file := ctx.file, span := span, kind := .method, owner := tyName, ownerName := tyName, name := name, recv := rt,
            params := ps, ret := ret }
        modify fun s => { s with members := s.members.push m }
        return (ret, .method tyName name cr cargs.toList rt)

/-- 二項演算の両辺を同じ型にする。左辺が数値リテラルなら右辺の型(Int かもしれない)に合わせる。 -/
partial def sameType (ctx : Ctx) (l r : Expr) : M (TyV × CExpr × CExpr) := do
  match l with
  | .lit _ (.nat _) =>
    let (rt, cr) ← infer ctx r
    let cl ← check ctx l rt
    return (rt, cl, cr)
  | _ =>
    let (lt, cl) ← infer ctx l
    let cr ← check ctx r lt
    return (lt, cl, cr)

partial def inferBinop (ctx : Ctx) (span : Span) (op : String) (l r : Expr) : M (TyV × CExpr) := do
  match op with
  | "&&" | "||" | "implies" =>
    let cl ← check ctx l .bool
    let cr ← check ctx r .bool
    return (.bool, .binop op cl cr .bool)
  | "==" | "!=" =>
    -- 被演算子は外側の位置を引き継ぐ: Prop の位置で両辺が Bool なら `↔`(Statements backend)。Bool 以外の型の
    -- 被演算子が Prop に依存していれば E014(`propValueCheck`)
    let (lt, cl, cr) ← sameType ctx l r
    requireCap ctx span "eq" lt s!"`{op}`"
    need span lt s!"the operands of `{op}`"
    let _ ← propValueCheck ctx l.span s!"the left operand of `{op}`" lt cl
    let _ ← propValueCheck ctx r.span s!"the right operand of `{op}`" lt cr
    return (.bool, .binop op cl cr lt)
  | "<" | "<=" | ">" | ">=" =>
    let (lt, cl, cr) ← sameType (ctx.value s!"an operand of `{op}`") l r
    requireCap ctx span "order" lt s!"`{op}`"
    need span lt s!"the operands of `{op}`"
    return (.bool, .binop op cl cr lt)
  | "+" | "-" | "*" | "/" | "%" =>
    let (lt, cl, cr) ← sameType (ctx.value s!"an operand of `{op}`") l r
    match ← zonk lt with
    | .nat => return (.nat, .binop op cl cr .nat)
    | .int => return (.int, .binop op cl cr .int)
    | .unknown => return (.unknown, .error)
    | .mvar _ =>
      need span lt s!"the operands of `{op}`"
      return (lt, .binop op cl cr lt)
    | t =>
      report ctx span Code.typeMismatch s!"`{op}` expects Nat or Int operands, found `{t.render}`"
      return (.unknown, .error)
  | _ =>
    let _ ← infer (ctx.value s!"an operand of `{op}`") l
    let _ ← infer (ctx.value s!"an operand of `{op}`") r
    return (.unknown, .error)

partial def inferRecordLit (ctx : Ctx) (span : Span) (name : List String)
    (fields : Array (String × Span × Expr)) (base : Option Expr) : M (TyV × CExpr) := do
  let t ← convTy ctx (.named span name #[])
  let vctx := ctx.value s!"a field of `{renderPath name}`"
  let loosely : M Unit := do
    for (_, _, x) in fields do
      let _ ← infer vctx x
    if let some b := base then
      let _ ← infer vctx b
  match ← zonk t with
  | .named k d =>
    match (← get).types.get? k with
    | some (.record fs _) =>
      let mut seen : List String := []
      let mut given : List (String × CExpr) := []
      for (fname, fsp, x) in fields do
        if seen.contains fname then
          report ctx x.span Code.arity s!"field `{fname}` is given twice in `{d}` literal"
        seen := fname :: seen
        match fs.toList.lookup fname with
        | some ft =>
          -- 欄名の位置も索引に残す(C32: 欄名のリネームが record literal の初期化も書き換える。略記 `R { f }` は欄名と値が同じトークン)
          let shorthand := match x with
            | .var sp [n] => sp == fsp && n == fname
            | _ => false
          let m : MemberRef :=
            { file := ctx.file, span := fsp, kind := .field, owner := k, ownerName := d, name := fname, recv := .named k d, ret := ft, init := true, shorthand }
          modify fun s => { s with members := s.members.push m }
          given := given ++ [(fname, ← check (ctx.value s!"the field `{fname}` of `{d}`") x ft)]
        | none =>
          report ctx x.span Code.arity s!"record `{d}` has no field `{fname}`"
          let _ ← infer vctx x
      let cbase ← match base with
        | some b => pure (some (← check (ctx.value s!"the base of the `{d}` update") b t))
        | none =>
          let missing := (fs.toList.filter fun (f, _) => !seen.contains f).map (·.1)
          if !missing.isEmpty then
            report ctx span Code.arity
              s!"missing field(s) {", ".intercalate (missing.map fun f => s!"`{f}`")} in `{d}` literal"
          pure none
      -- 欄は宣言の順に並べる(出力を決定的にする)
      let ordered := fs.toList.filterMap fun (f, _) => (given.lookup f).map fun c => (f, c)
      return (t, .record k ordered cbase)
    | some (.enum ..) =>
      report ctx span Code.typeMismatch s!"`{d}` is an enum, not a record"
      loosely
      return (.unknown, .error)
    | none =>
      -- 型表に無い名前付き型(到達しないはず)。黙らない(C35)
      report ctx span Code.typeMismatch s!"`{d}` is not a record; a record literal needs a record or state type"
      loosely
      return (.unknown, .error)
  | .unknown =>
    loosely   -- convTy が報告済み
    return (.unknown, .error)
  | tz =>
    -- 型別名が展開された型や組み込み型(`type Count = Nat` の `Count \{}`、`Nat \{ … }`)。黙らない(C35)
    report ctx span Code.typeMismatch
      s!"`{renderPath name}` is `{tz.render}`, not a record; a record literal `{renderPath name} \{ … }` needs a record or state type"
    loosely
    return (.unknown, .error)

/-- パターンを期待される型で検査し、束縛する名前と型、Core のパターンを返す。 -/
partial def checkPat (ctx : Ctx) (expected : TyV) (p : Pattern) : M (List (String × TyV) × CPat) := do
  match p with
  | .wild _ => return ([], .wild)
  | .bind _ n => return ([(n, expected)], .bind n)
  | .lit span l =>
    expectTy ctx span expected (litTy l)
    return ([], .lit l)
  | .tuple span elems =>
    let ms ← elems.toList.mapM fun _ => fresh
    expectTy ctx span expected (.tuple ms)
    let mut binds : List (String × TyV) := []
    let mut cps : List CPat := []
    for (q, m) in elems.toList.zip ms do
      let (bs, cp) ← checkPat ctx m q
      binds := bs ++ binds
      cps := cps ++ [cp]
    return (binds, .tuple cps)
  | .ctor span name args =>
    match name with
    | ["Some"] =>
      let m ← fresh
      expectTy ctx span expected (.option m)
      let (bs, cps) ← ctorArgs ctx span "Some" [m] args
      return (bs, .builtin "Some" cps)
    | ["None"] =>
      let m ← fresh
      expectTy ctx span expected (.option m)
      let (bs, cps) ← ctorArgs ctx span "None" [] args
      return (bs, .builtin "None" cps)
    | ["Ok"] =>
      let m ← fresh
      let err ← fresh
      expectTy ctx span expected (.result m err)
      let (bs, cps) ← ctorArgs ctx span "Ok" [m] args
      return (bs, .builtin "Ok" cps)
    | ["Err"] =>
      let m ← fresh
      let err ← fresh
      expectTy ctx span expected (.result m err)
      let (bs, cps) ← ctorArgs ctx span "Err" [err] args
      return (bs, .builtin "Err" cps)
    | _ =>
      match ← lookupEntry name with
      | some (e, [v]) =>
        if !e.decl.kind.isType then
          report ctx span Code.typeMismatch s!"`{renderPath name}` is not a constructor (expected `Enum.Variant`)"
          return ([], .wild)
        let t ← convTy ctx (.named span (name.take (name.length - 1)) #[])
        match ← zonk t with
        | .named key d =>
          match (← get).types.get? key with
          | some (.enum vs _) =>
            match vs.toList.lookup v with
            | some argTys =>
              expectTy ctx span expected t
              let (bs, cps) ← ctorArgs ctx span s!"{d}.{v}" argTys args
              return (bs, .variant key v cps)
            | none =>
              report ctx span Code.arity s!"enum `{d}` has no variant `{v}`"
              return ([], .wild)
          | _ =>
            report ctx span Code.typeMismatch s!"`{d}` is not an enum"
            return ([], .wild)
        | _ => return ([], .wild)
      | some (e, _) =>
        report ctx span Code.typeMismatch
          s!"`{renderPath name}` is not a constructor (expected `Enum.Variant`, found {e.decl.kind.describe} `{e.decl.name}`)"
        return ([], .wild)
      | none => return ([], .wild)   -- E011 は Resolve が報告済み

partial def ctorArgs (ctx : Ctx) (span : Span) (what : String) (tys : List TyV)
    (args : Array Pattern) : M (List (String × TyV) × List CPat) := do
  if tys.length != args.size then
    report ctx span Code.arity
      s!"`{what}` takes {tys.length} argument(s) in a pattern, found {args.size}"
    return ([], [])
  let mut binds : List (String × TyV) := []
  let mut cps : List CPat := []
  for (q, t) in args.toList.zip tys do
    let (bs, cp) ← checkPat ctx t q
    binds := bs ++ binds
    cps := cps ++ [cp]
  return (binds, cps)

end

/-! ## Core の型の確定(zonk) -/

mutual
partial def zonkExpr (e : CExpr) : M CExpr := do
  match e with
  | .lit l ty => return .lit l (← zonk ty)
  | .var _ | .global _ | .error => return e
  | .call k args => return .call k (← args.mapM zonkExpr)
  | .callLocal f args => return .callLocal (← zonkExpr f) (← args.mapM zonkExpr)
  | .method tn n recv args rt => return .method tn n (← zonkExpr recv) (← args.mapM zonkExpr) (← zonk rt)
  | .builtin n args ty => return .builtin n (← args.mapM zonkExpr) (← zonk ty)
  | .variant k v args => return .variant k v (← args.mapM zonkExpr)
  | .field r k n => return .field (← zonkExpr r) k n
  | .binop op l r ty => return .binop op (← zonkExpr l) (← zonkExpr r) (← zonk ty)
  | .unop op a => return .unop op (← zonkExpr a)
  | .ite c t el => return .ite (← zonkExpr c) (← zonkExpr t) (← zonkExpr el)
  | .match_ s st arms => return .match_ (← zonkExpr s) (← zonk st) (← arms.mapM zonkArm)
  | .let_ n ty v b => return .let_ n (← zonk ty) (← zonkExpr v) (← zonkExpr b)
  | .record k fs base =>
    let fs' ← fs.mapM fun (f, x) => do return (f, ← zonkExpr x)
    let base' ← match base with
      | some b => pure (some (← zonkExpr b))
      | none => pure none
    return .record k fs' base'
  | .list es ty => return .list (← es.mapM zonkExpr) (← zonk ty)
  | .tuple es => return .tuple (← es.mapM zonkExpr)
  | .lambda ps b =>
    let ps' ← ps.mapM fun (n, t) => do return (n, ← zonk t)
    return .lambda ps' (← zonkExpr b)
  | .quant q bs b =>
    let bs' ← bs.mapM fun (n, t) => do return (n, ← zonk t)
    return .quant q bs' (← zonkExpr b)

partial def zonkArm (a : CArm) : M CArm := do
  let .mk p g b := a
  let g' ← match g with
    | some x => pure (some (← zonkExpr x))
    | none => pure none
  return .mk p g' (← zonkExpr b)
end

/-- 宣言の終わり: 型が要る位置にメタ変数が残っていれば E014。 -/
def finishDecl (ctx : Ctx) : M Unit := do
  let pending := (← get).pending
  let pendingCaps := (← get).pendingCaps
  modify fun s => { s with pending := #[], pendingCaps := #[] }
  for (span, t, what) in pending do
    let t' ← zonk t
    if hasMeta t' then
      report ctx span Code.typeMismatch
        s!"cannot infer the type of {what} (`{t'.render}`); add a type annotation"
  -- 宣言の終わりに要素の型が決まった上で capability を検査する(決まっていなければ上の E014 が出ている)
  for (span, cap, t, what) in pendingCaps do
    requireCap ctx span cap t what
  -- この宣言で解決した欄・メソッドの参照の型を確定する(C29。メタ変数が残れば上の E014 が出ている)
  let mut ms := (← get).members
  for i in [(← get).membersDone:ms.size] do
    let m := ms[i]!
    let recv ← zonk m.recv
    let params ← m.params.mapM fun (n, t) => do return (n, ← zonk t)
    let ret ← zonk m.ret
    ms := ms.set! i { m with recv, params, ret }
  modify fun s => { s with members := ms, membersDone := ms.size }
  -- 受け手の型の索引(C31)も同じく確定する
  let mut as := (← get).accesses
  for i in [(← get).accessesDone:as.size] do
    let a := as[i]!
    as := as.set! i { a with recv := ← zonk a.recv }
  modify fun s => { s with accesses := as, accessesDone := as.size }

/-! ## 宣言 -/

/-- `derive` した capability を欄・variant の型が満たすか(E005)。 -/
def checkDerives (ctx : Ctx) (d : Decl) (q : String) : M Unit := do
  match (← get).types.get? q with
  | some (.record fs ds) =>
    for cap in ds do
      for (f, t) in fs do
        requireCap ctx d.span cap t s!"`derive {cap}` on `{d.name}` (field `{f}`)"
  | some (.enum vs ds) =>
    for cap in ds do
      for (v, ts) in vs do
        for t in ts do
          requireCap ctx d.span cap t s!"`derive {cap}` on `{d.name}` (variant `{v}`)"
  | none => pure ()

/-- scenario の本体。先頭の `input f(x) = e;` は環境の入力に値を与え(仮引数の型は `input` 宣言から取り、値は
その戻り型で検査する。同じ input を 2 度束縛すると E012、仮引数の数が違えば E015)、`let` は局所束縛、`observe e;` は
observer の呼出しだけを受理する(他は E014: simulation の出力は observer を通す — IDEAL.md)。 -/
def checkScenario (ctx : Ctx) (q : String) (d : Decl) (stmts : Array Stmt) : M Core.Decl := do
  let mut c := ctx
  let mut inputs : List (String × List (String × TyV) × CExpr) := []
  let mut out : List Core.ScenarioStmt := []
  for st in stmts do
    match st with
    | .inputS span name params val =>
      match ← lookupEntry [name] with
      | some (e, []) =>
        if e.decl.kind != .input then continue   -- E014 は Resolve が報告済み
        let some fi := (← get).fns.get? e.qualified | continue
        if inputs.any (·.1 == e.qualified) then
          report c span Code.duplicate s!"input `{name}` is given a value twice in scenario `{d.name}`"
        if params.size != fi.params.size then
          report c span Code.arity
            s!"input `{name}` takes {fi.params.size} parameter(s) ({", ".intercalate (fi.params.toList.map (·.1))}), but this binding names {params.size}"
          inferArgsLoosely c #[.pos val]
          continue
        for (p, psp) in params do
          if (params.filter (·.1 == p)).size > 1 then
            report c psp Code.arity s!"parameter `{p}` is named twice in the binding of input `{name}`"
        let binds : List (String × TyV) := (params.toList.zip fi.params.toList).map fun ((p, _), (_, t)) => (p, t)
        let cv ← check (c.bind binds) val fi.ret
        inputs := inputs ++ [(e.qualified, binds, cv)]
      | _ => continue   -- E011 / E014 は Resolve が報告済み
    | .letS span name ty val =>
      let (t, cv) ← match ty with
        | some a =>
          let at_ ← convTy c a (allowFn := true)
          let cv ← check c val at_
          pure (at_, cv)
        | none =>
          let (t, cv) ← infer c val
          need span t s!"`{name}`"
          pure (t, cv)
      out := out ++ [.let_ name t cv]
      c := c.bind [(name, t)]
    | .observeS span e =>
      let (t, ce) ← infer c e
      let calleeKind : Option DeclKind ← match ce with
        | .call k _ => pure ((← get).fns.get? k |>.map (·.kind))
        | _ => pure none
      match ce, calleeKind with
      | .error, _ => pure ()
      | _, some .observer => out := out ++ [.observe (renderExpr e) t ce]
      | .call k _, some kind =>
        report c span Code.typeMismatch
          s!"`observe` takes a call of an observer (`observe name(…);`), but `{(k.splitOn ".").getLast!}` is a {kind.describe}; simulation output goes through observers only"
      | _, _ =>
        report c span Code.typeMismatch
          "`observe` takes a call of an observer (`observe name(…);`); simulation output goes through observers only"
    | .exprS x =>
      -- パーサは scenario に作らないが、作られても `let _ = x;` と同じ
      let (t, cx) ← infer c x
      out := out ++ [.let_ "_" t cx]
  return .scenario q d.name inputs out

/-- 宣言を検査し、Core の宣言にする(`protocol` の殻など、Core に対応物が無い宣言は `none`)。 -/
def checkDecl (m : Module) (d : Decl) : M (Option Core.Decl) := do
  let ctx := declCtx m d
  let q := renderPath (m.name ++ [d.name])
  let out : Option Core.Decl ← match d.kind with
    | .record | .state =>
      checkDerives ctx d q
      match (← get).types.get? q with
      | some (.record fs _) =>
        pure (some (.record q d.name (d.kind == .state) fs.toList d.derives.toList))
      | _ => pure none
    | .enum =>
      checkDerives ctx d q
      match (← get).types.get? q with
      | some (.enum vs _) => pure (some (.enum q d.name vs.toList d.derives.toList))
      | _ => pure none
    | .typeAlias =>
      match d.aliasOf with
      | some t => pure (some (.typeAlias q d.name (← convTy ctx t)))
      | none => pure none
    | .scenario =>
      match d.body with
      | some (.block _ stmts _) => pure (some (← checkScenario ctx q d stmts))
      | _ => pure none
    | .claimBundle =>
      let mut items : List (String × String) := []
      for (item, e) in d.items do
        match e with
        | .var span segs =>
          match ← lookupEntry segs with
          | some (en, []) =>
            if en.decl.kind != .claim && en.decl.kind != .claimBundle then
              report ctx span Code.notAClaim
                s!"item `{item}` of claim bundle `{d.name}` refers to {en.decl.kind.describe} `{en.decl.name}`; items must be claims (or nested claim bundles)"
            else
              items := items ++ [(item, en.qualified)]
          | some (en, _) =>
            report ctx span Code.notAClaim
              s!"item `{item}` of claim bundle `{d.name}` must name a claim, found member path under {en.decl.kind.describe} `{en.decl.name}`"
          | none => pure ()   -- E011 は Resolve が報告済み
        | _ =>
          report ctx e.span Code.notAClaim
            s!"item `{item}` of claim bundle `{d.name}` must be the name of a claim"
      pure (some (.claimBundle q d.name items))
    | k =>
      if isFnLike k then
        match (← get).fns.get? q with
        | some fi =>
          -- spec 宣言の本体は Prop の位置(C35)。runtime 宣言は値の位置のまま
          let c := { ctx with locals := fi.params.toList, propPos := k.phase == .spec }
          let cb ← match d.body with
            | some b => pure (some (← check c b fi.ret))
            | none => pure none
          let params := fi.params.toList.map fun (n, t) => ({ name := n, ty := t } : Core.Param)
          pure (some (.fn q d.name k params fi.ret cb))
        | none => pure none
      else pure none
  finishDecl ctx
  -- Core の型を確定する(メタ変数は上で E014 にしたので、残っていても backend には届かない)
  match out with
  | some (.typeAlias k n t) => return some (.typeAlias k n (← zonk t))
  | some (.record k n st fs ds) =>
    let fs' ← fs.mapM fun (f, t) => do return (f, ← zonk t)
    return some (.record k n st fs' ds)
  | some (.enum k n vs ds) =>
    let vs' ← vs.mapM fun (v, ts) => do return (v, ← ts.mapM zonk)
    return some (.enum k n vs' ds)
  | some (.fn k n kind ps ret body) =>
    let ps' ← ps.mapM fun p => do return ({ p with ty := ← zonk p.ty } : Core.Param)
    let body' ← match body with
      | some b => pure (some (← zonkExpr b))
      | none => pure none
    return some (.fn k n kind ps' (← zonk ret) body')
  | some (.scenario k n inputs stmts) =>
    let inputs' ← inputs.mapM fun (ik, ps, v) => do
      let ps' ← ps.mapM fun (p, t) => do return (p, ← zonk t)
      return (ik, ps', ← zonkExpr v)
    let stmts' ← stmts.mapM fun
      | .let_ nm t v => do return Core.ScenarioStmt.let_ nm (← zonk t) (← zonkExpr v)
      | .observe l t e => do return Core.ScenarioStmt.observe l (← zonk t) (← zonkExpr e)
    return some (.scenario k n inputs' stmts')
  | other => return other

/-- scenario は閉じていなければならない(E015): 本体(`let` / `observe`)が直接・間接に使う input はすべて先頭で
束縛され、input の束縛の値が使う input はそれより前に束縛されている。backend は閉じた scenario を引数なしの `def` に
落とし、`naru simulate` がそれを実行する。推移的な input の使用は Core の参照から fn / observer の不動点で求める
(backend の `buildEnv` と同じ)。 -/
def checkScenarioInputs (mods : Array Module) (cmods : Array Core.Module) : M Unit := do
  let all := cmods.toList.flatMap fun m => m.decls.toList
  let inputKeys := (all.filter fun d => d.kind == .input).map (·.key)
  let fnKeys := (all.filter fun d => match d with
    | .fn _ _ k _ _ (some _) => k == .fn || k == .observer
    | _ => false).map (·.key)
  let direct (refs : List String) : List String := refs.filter inputKeys.contains
  let mut table : List (String × List String) := fnKeys.map fun k => (k, [])
  let mut changed := true
  let mut guard := all.length + 1
  while changed && guard > 0 do
    guard := guard - 1
    changed := false
    let mut next : List (String × List String) := []
    for (k, cur) in table do
      let refs := match all.find? (·.key == k) with
        | some d => d.refs
        | none => []
      let via := (refs.filter fnKeys.contains).flatMap fun g => (table.lookup g).getD []
      let merged := (direct refs ++ via).foldl (init := cur) fun acc x => if acc.contains x then acc else acc ++ [x]
      if merged.length != cur.length then changed := true
      next := next ++ [(k, merged)]
    table := next
  let usedBy (refs : List String) : List String :=
    (direct refs ++ (refs.filter fnKeys.contains).flatMap fun g => (table.lookup g).getD []).eraseDups
  let short (k : String) : String := (k.splitOn ".").getLast!
  for cm in cmods do
    let some sm := mods.find? (·.name == cm.name) | continue
    for d in cm.decls do
      let .scenario _ name inputs stmts := d | continue
      let some sd := sm.decls.find? (fun x => x.kind == .scenario && x.name == name) | continue
      let ctx : Ctx := { file := sm.file, declKind := .scenario, declName := name, locals := [] }
      let bindSpans : Array Span := match sd.body with
        | some (.block _ ss _) => ss.filterMap fun
          | .inputS sp .. => some sp
          | _ => none
        | _ => #[]
      let mut bound : List String := []
      let mut i := 0
      for (ik, _, v) in inputs do
        for u in usedBy v.refs do
          if !bound.contains u then
            report ctx (bindSpans.getD i sd.span) Code.arity
              s!"the value given to input `{short ik}` in scenario `{name}` uses input `{short u}` (directly or through the functions it calls), which is bound later or not at all; bind `{short u}` before `{short ik}`"
        bound := bound ++ [ik]
        i := i + 1
      for u in usedBy (stmts.flatMap Core.ScenarioStmt.refs) do
        if !bound.contains u then
          let hint := match (← get).fns.get? u with
            | some fi => s!"input {short u}({", ".intercalate (fi.params.toList.map fun (p : String × TyV) => p.1)}) = …;"
            | none => s!"input {short u}(…) = …;"
          report ctx sd.span Code.arity
            s!"scenario `{name}` uses input `{short u}` (directly or through the functions it calls) but gives it no value; bind it at the head of the scenario: `{hint}`"

end Typecheck

/-- コンパイル単位全体の型検査・capability 検査・選択/順序の検査と、Core IR への elaboration。
診断(空なら合格)と Core のモジュール列、解決した欄・stdlib メソッドの参照の索引(C29)、欄 / メソッドのアクセスの受け手の型の索引(C31)を返す。
名前解決(`resolveAll`)が通った後に呼ぶ。 -/
def typecheckAll (mods : Array Module) :
    Array Diagnostic × Array Core.Module × Array Typecheck.MemberRef × Array Typecheck.AccessRef :=
  let run : Typecheck.M (Array Core.Module) := do
    for m in mods do Typecheck.collect m
    for m in mods do
      for d in m.decls do Typecheck.buildInfo m d
    for m in mods do
      for d in m.decls do Typecheck.checkNestedRecursion m d
    let mut out : Array Core.Module := #[]
    for m in mods do
      let mut decls : Array Core.Decl := #[]
      for d in m.decls do
        if let some cd ← Typecheck.checkDecl m d then decls := decls.push cd
      out := out.push { file := m.file, name := m.name, decls }
    Typecheck.checkScenarioInputs mods out
    return out
  let (cmods, st) := run.run {}
  (st.diags, cmods, st.members, st.accesses)

end Naru
