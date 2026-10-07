import Std.Data.HashMap
import Naru.Ast
import Naru.Resolve

/-!
# 型検査・capability 検査・選択と順序の検査

名前解決と phase 検査(`Resolve.lean`)を通った宣言の本体に型を付け、次を報告する。

- 型の不一致・推論できない型・値でないものの値としての使用 → E014
- 無い欄・無いメソッド・引数の数や名前の不一致 → E015
- claim bundle の項目が claim(または入れ子の claim bundle)でない → E016
- capability(eq / order)の無い型への `==` `!=` `<` `<=` `>` `>=`、
  eq / order を要する stdlib メソッド、`derive` した capability を欄が満たさない → E005
- Set からの無条件の選択(`choose` / `pick` / `first` / `find?` …) → **E003**
- 順序指定の無い Set → List 変換(`toList` / `by =` の無い `sort` / `fold` …) → **E004**
- runtime 宣言の中の量化(`forall` / `exists`) → E006

stdlib のメソッド表(`setSigs` / `listSigs` / …)がこのファイルの正本。naru で書いた stdlib ができるまでは
ここで型を与える。Lean の型クラスは露出せず、eq / order の要求はメソッド表の `caps` 列で表す。
推論は単一化(メタ変数)で行い、lambda の引数型は期待される型から取る。
-/

namespace Naru

/-- 内部の型表現。Surface の `Ty` を解決・展開したもの。 -/
inductive TyV where
  | bool | nat | int | string | unit
  | option (t : TyV)
  | result (t e : TyV)
  | list (t : TyV)
  | set (t : TyV)
  | table (k v : TyV)
  | tuple (ts : List TyV)
  /-- record / state / enum。`key` は大域表の鍵(修飾名)、`display` は表示名。
  `$T` のように `$` で始まる key はメソッド表の型変数。 -/
  | named (key display : String)
  | fn (params : List TyV) (ret : TyV)
  /-- 推論用のメタ変数。 -/
  | mvar (n : Nat)
  /-- 既に報告した誤りの波及を抑えるための「不明」。何とでも単一化する。 -/
  | unknown
deriving Inhabited

partial def TyV.render : TyV → String
  | .bool => "Bool"
  | .nat => "Nat"
  | .int => "Int"
  | .string => "String"
  | .unit => "Unit"
  | .option t => s!"Option<{t.render}>"
  | .result t e => s!"Result<{t.render}, {e.render}>"
  | .list t => s!"List<{t.render}>"
  | .set t => s!"Set<{t.render}>"
  | .table k v => s!"Table<{k.render}, {v.render}>"
  | .tuple ts => "(" ++ ", ".intercalate (ts.map TyV.render) ++ ")"
  | .named _ d => d
  | .fn ps r => "(" ++ ", ".intercalate (ps.map TyV.render) ++ ") -> " ++ r.render
  | .mvar n => s!"?{n}"
  | .unknown => "_"

namespace Typecheck
open Std

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

abbrev M := StateM St

instance [Inhabited α] : Inhabited (M α) := ⟨pure default⟩

structure Ctx where
  file : String
  declKind : DeclKind
  declName : String
  locals : List (String × TyV)

def Ctx.bind (ctx : Ctx) (binds : List (String × TyV)) : Ctx :=
  { ctx with locals := binds ++ ctx.locals }

def reportAt (file : String) (span : Span) (code msg : String) : M Unit :=
  modify fun s => { s with diags := s.diags.push { file, span, code, msg } }

def report (ctx : Ctx) (span : Span) (code msg : String) : M Unit :=
  reportAt ctx.file span code msg

def fresh : M TyV := do
  let s ← get
  set { s with nextMeta := s.nextMeta + 1 }
  return .mvar s.nextMeta

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

/-- Surface の型を内部表現に変換する。型別名は展開する。引数の数の誤りと循環する別名は E014。 -/
partial def convTy (ctx : Ctx) (ty : Ty) (depth : Nat := 0) : M TyV := do
  match ty with
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
      fs := fs.push (f.name, ← convTy ctx f.ty)
    modify fun s => { s with types := s.types.insert q (.record fs d.derives) }
  | .enum =>
    let mut vs : Array (String × List TyV) := #[]
    for v in d.variants do
      if vs.any (·.1 == v.name) then
        report ctx v.span Code.arity s!"variant `{v.name}` is declared twice in `{d.name}`"
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
        ps := ps.push (p.name, ← convTy ctx p.ty)
      let ret ← match d.ret with
        | some t => convTy ctx t
        | none => pure .bool
      modify fun s => { s with fns := s.fns.insert q { kind := k, params := ps, ret } }

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
    ("any", { params := [(none, pred)], ret := .bool }),
    ("all", { params := [(none, pred)], ret := .bool }),
    ("findUnique?", { params := [(none, pred)], ret := .option vT }),
    ("minBy?", { params := [(none, .fn [vT] vU)], ret := .option vT,
                 caps := [("order", vU), ("order", vT)] }),
    ("maxBy?", { params := [(none, .fn [vT] vU)], ret := .option vT,
                 caps := [("order", vU), ("order", vT)] }),
    ("sort", { params := [(some "by", .fn [vT] vU)], ret := .list vT,
               caps := [("order", vU), ("order", vT)] }) ]

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
    ("entries", { ret := .set (.tuple [vK, vV]), caps := [("eq", vK), ("eq", vV)] }) ]

def natSigs : List (String × Sig) :=
  [ ("min", { params := [(none, .nat)], ret := .nat }),
    ("max", { params := [(none, .nat)], ret := .nat }),
    ("toInt", { ret := .int }) ]

def intSigs : List (String × Sig) :=
  [ ("min", { params := [(none, .int)], ret := .int }),
    ("max", { params := [(none, .int)], ret := .int }),
    ("abs", { ret := .nat }) ]

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

/-! ## 式 -/

mutual

/-- 式の型を推論する。誤りは報告して `unknown` を返す。 -/
partial def infer (ctx : Ctx) (e : Expr) : M TyV := do
  match e with
  | .lit _ l => return litTy l
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
    check ctx a .bool
    return .bool
  | .unop _ "-" a =>
    match a with
    | .lit _ (.nat _) => return .int
    | _ =>
      check ctx a .int
      return .int
  | .unop _ _ a => infer ctx a
  | .ite _ c t el =>
    check ctx c .bool
    let tt ← infer ctx t
    check ctx el tt
    return tt
  | .matchE span s arms =>
    let st ← infer ctx s
    if arms.isEmpty then
      report ctx span Code.typeMismatch "`match` needs at least one arm"
      return .unknown
    let mut rt : Option TyV := none
    for arm in arms do
      let .mk pat guard body := arm
      let binds ← checkPat ctx st pat
      let c := ctx.bind binds
      if let some g := guard then check c g .bool
      match rt with
      | none => rt := some (← infer c body)
      | some t => check c body t
    return rt.getD .unknown
  | .block _ stmts tail =>
    let c ← inferStmts ctx stmts
    match tail with
    | some t => infer c t
    | none => return .unit
  | .recordLit span name fields base => inferRecordLit ctx span name fields base
  | .listLit _ elems =>
    let m ← fresh
    for x in elems do check ctx x m
    return .list m
  | .tupleLit _ elems =>
    let ts ← elems.toList.mapM (infer ctx)
    return .tuple ts
  | .lambda _ params body =>
    let mut ps : List TyV := []
    let mut binds : List (String × TyV) := []
    for p in params do
      let t ← match p.ty with
        | some a => convTy ctx a
        | none => fresh
      ps := ps ++ [t]
      binds := binds ++ [(p.name, t)]
    let r ← infer (ctx.bind binds) body
    return .fn ps r
  | .quant span q binders body =>
    if ctx.declKind.phase == .runtime then
      let qn := if q == .forall_ then "forall" else "exists"
      report ctx span Code.infiniteQuantification
        s!"`{qn}` quantifies over a possibly infinite domain and cannot be evaluated in a runtime declaration ({ctx.declKind.describe} `{ctx.declName}`); iterate a finite collection (`all` / `any` / `filter`) instead"
    let mut binds : List (String × TyV) := []
    for b in binders do
      let t ← match b.ty with
        | some a => convTy ctx a
        | none => fresh
      binds := binds ++ [(b.name, t)]
    check (ctx.bind binds) body .bool
    return .bool

/-- 期待される型に対して検査する。lambda・分岐・ブロック・リストには期待を内側へ伝える。 -/
partial def check (ctx : Ctx) (e : Expr) (expected : TyV) : M Unit := do
  match e with
  | .lambda span params body =>
    match ← zonk expected with
    | .fn ps r =>
      if ps.length != params.size then
        report ctx span Code.typeMismatch
          s!"this closure takes {params.size} parameter(s), but {ps.length} expected"
        return
      let mut binds : List (String × TyV) := []
      for (p, t) in params.toList.zip ps do
        if let some a := p.ty then
          let at_ ← convTy ctx a
          expectTy ctx p.span t at_
        binds := binds ++ [(p.name, t)]
      check (ctx.bind binds) body r
    | _ =>
      let t ← infer ctx e
      expectTy ctx span expected t
  | .ite _ c t el =>
    check ctx c .bool
    check ctx t expected
    check ctx el expected
  | .matchE span s arms =>
    let st ← infer ctx s
    if arms.isEmpty then
      report ctx span Code.typeMismatch "`match` needs at least one arm"
    for arm in arms do
      let .mk pat guard body := arm
      let binds ← checkPat ctx st pat
      let c := ctx.bind binds
      if let some g := guard then check c g .bool
      check c body expected
  | .lit span (.nat _) =>
    -- 数値リテラルは Nat だが、Int が期待される位置では Int として読む
    match ← zonk expected with
    | .int => pure ()
    | _ => expectTy ctx span expected .nat
  | .block span stmts tail =>
    let c ← inferStmts ctx stmts
    match tail with
    | some t => check c t expected
    | none => expectTy ctx span expected .unit
  | .listLit span elems =>
    match ← zonk expected with
    | .list t => for x in elems do check ctx x t
    | _ =>
      let t ← infer ctx e
      expectTy ctx span expected t
  | _ =>
    let t ← infer ctx e
    expectTy ctx e.span expected t

partial def inferStmts (ctx : Ctx) (stmts : Array Stmt) : M Ctx := do
  let mut c := ctx
  for st in stmts do
    match st with
    | .letS _ name ty val =>
      let t ← match ty with
        | some a =>
          let at_ ← convTy c a
          check c val at_
          pure at_
        | none => infer c val
      c := c.bind [(name, t)]
    | .exprS x =>
      let _ ← infer c x
  return c

partial def inferVar (ctx : Ctx) (span : Span) (segs : List String) : M TyV := do
  match segs with
  | [] => return .unknown
  | head :: rest =>
    if rest.isEmpty then
      if let some t := ctx.locals.lookup head then return t
    if Resolve.isBuiltinHead head then return ← inferBuiltin ctx span head rest
    match ← lookupEntry segs with
    | none => return .unknown   -- E011 は Resolve が報告済み
    | some (e, rest') =>
      let k := e.decl.kind
      if isFnLike k then
        if !rest'.isEmpty then
          report ctx span Code.arity s!"`{e.decl.name}` has no member `{renderPath rest'}`"
          return .unknown
        match (← get).fns.get? e.qualified with
        | some fi => return .fn (fi.params.toList.map (·.2)) fi.ret
        | none => return .unknown
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
              | some [] => return .named key d
              | some argTys => return .fn argTys (.named key d)
              | none =>
                report ctx span Code.arity s!"enum `{d}` has no variant `{v}`"
                return .unknown
            | [] =>
              report ctx span Code.typeMismatch s!"enum `{d}` cannot be used as a value; name one of its variants (`{d}.Variant`)"
              return .unknown
            | _ =>
              report ctx span Code.arity s!"`{renderPath segs}` is not a variant of enum `{d}`"
              return .unknown
          | _ =>
            report ctx span Code.typeMismatch s!"type `{d}` cannot be used as a value"
            return .unknown
        | _ => return .unknown
      else
        match k with
        | .claimBundle =>
          report ctx span Code.typeMismatch
            s!"claim bundle `{e.decl.name}` can only be referenced from another claim bundle"
        | _ =>
          report ctx span Code.typeMismatch s!"`{e.decl.name}` is a {k.describe}, not a value"
        return .unknown

/-- 組み込みの構築子と静的関数(`Some` / `None` / `Ok` / `Err` / `Set.empty` …)。 -/
partial def inferBuiltin (ctx : Ctx) (span : Span) (head : String) (rest : List String) : M TyV := do
  match head, rest with
  | "Some", [] =>
    let m ← fresh
    return .fn [m] (.option m)
  | "None", [] =>
    let m ← fresh
    return .option m
  | "Ok", [] =>
    let m ← fresh
    let err ← fresh
    return .fn [m] (.result m err)
  | "Err", [] =>
    let m ← fresh
    let err ← fresh
    return .fn [err] (.result m err)
  | "choose", [] | "pick", [] =>
    report ctx span Code.choose (choiceMsg s!"`{head}`")
    return .unknown
  | "sort", [] =>
    report ctx span Code.arity "`sort` must be called as `sort(xs, by = …)`"
    return .unknown
  | "Set", ["empty"] =>
    let m ← fresh
    return .fn [] (.set m)
  | "Set", ["singleton"] =>
    let m ← fresh
    return .fn [m] (.set m)
  | "Set", ["of"] =>
    let m ← fresh
    return .fn [.list m] (.set m)
  | "List", ["empty"] =>
    let m ← fresh
    return .fn [] (.list m)
  | "List", ["range"] => return .fn [.nat] (.list .nat)
  | "Table", ["empty"] =>
    let k ← fresh
    let v ← fresh
    return .fn [] (.table k v)
  | _, _ =>
    report ctx span Code.arity s!"`{renderPath (head :: rest)}` is not a known built-in"
    return .unknown

/-- 呼出し。`sort(xs, by = …)` は `xs.sort(by = …)` の糖衣。 -/
partial def inferCall (ctx : Ctx) (span : Span) (f : Expr) (args : Array Arg) : M TyV := do
  match f with
  | .var vsp ["sort"] =>
    match args.toList with
    | .pos recv :: rest => inferMethod ctx vsp recv "sort" rest.toArray
    | _ =>
      report ctx vsp Code.arity "`sort(xs, by = …)` needs the collection as its first argument"
      inferArgsLoosely ctx args
      return .unknown
  | _ =>
    let ft ← zonk (← infer ctx f)
    match ft with
    | .fn ps r =>
      let names ← calleeParamNames f
      let params := match names with
        | some ns => (ns.zip ps).map fun (n, t) => (some n, t)
        | none => ps.map fun t => (none, t)
      matchArgs ctx span (describeCallee f) params args
      return r
    | .unknown =>
      inferArgsLoosely ctx args
      return .unknown
    | .mvar _ =>
      report ctx span Code.typeMismatch "cannot determine the type of the callee; add a type annotation"
      inferArgsLoosely ctx args
      return .unknown
    | t =>
      report ctx span Code.typeMismatch s!"{describeCallee f} is not callable (its type is `{t.render}`)"
      inferArgsLoosely ctx args
      return .unknown

/-- 呼出し先がユーザ宣言の fn 等なら、その引数名(名前付き引数のため)。 -/
partial def calleeParamNames (f : Expr) : M (Option (List String)) := do
  match f with
  | .var _ segs =>
    match segs with
    | [head] => if Resolve.isBuiltinHead head then return none
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

partial def inferArgsLoosely (ctx : Ctx) (args : Array Arg) : M Unit := do
  for a in args do
    let _ ← infer ctx (argExpr a)

/-- 実引数を仮引数に割り当てて検査する。位置引数は順に、名前付き引数は名前で。 -/
partial def matchArgs (ctx : Ctx) (span : Span) (what : String)
    (params : List (Option String × TyV)) (args : Array Arg) : M Unit := do
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
  for i in [0:ps.size] do
    match slots[i]! with
    | some x => check ctx x ps[i]!.2
    | none =>
      let pname := match ps[i]!.1 with
        | some n => s!"`{n}`"
        | none => s!"#{i + 1}"
      report ctx span Code.arity s!"missing argument {pname} to {what}"

partial def inferField (ctx : Ctx) (span : Span) (r : Expr) (name : String) : M TyV := do
  let rt ← zonk (← infer ctx r)
  match rt with
  | .named k d =>
    match (← get).types.get? k with
    | some (.record fs _) =>
      match fs.toList.lookup name with
      | some t => return t
      | none =>
        report ctx span Code.arity s!"record `{d}` has no field `{name}`"
        return .unknown
    | some (.enum ..) =>
      report ctx span Code.arity s!"enum `{d}` has no field `{name}`"
      return .unknown
    | none => return .unknown
  | .unknown => return .unknown
  | .mvar _ =>
    report ctx span Code.typeMismatch
      s!"cannot determine the type of the value before `.{name}`; add a type annotation"
    return .unknown
  | t =>
    let hint := match sigsFor t with
      | some (_, _, sigs) => if (sigs.lookup name).isSome then s!" (did you mean `{name}()`?)" else ""
      | none => ""
    report ctx span Code.arity s!"type `{t.render}` has no field `{name}`{hint}"
    return .unknown

/-- stdlib メソッドの呼出し。Set の選択(E003)と順序(E004)の検査はここ。 -/
partial def inferMethod (ctx : Ctx) (span : Span) (r : Expr) (name : String) (args : Array Arg) :
    M TyV := do
  let rt ← zonk (← infer ctx r)
  match rt with
  | .unknown =>
    inferArgsLoosely ctx args
    return .unknown
  | .mvar _ =>
    report ctx span Code.typeMismatch
      s!"cannot determine the type of the receiver of `.{name}()`; add a type annotation"
    inferArgsLoosely ctx args
    return .unknown
  | _ =>
    if let .set _ := rt then
      if setChoiceMethods.contains name then
        report ctx span Code.choose (choiceMsg s!"`Set.{name}`")
        inferArgsLoosely ctx args
        return .unknown
      if setOrderMethods.contains name then
        report ctx span Code.orderLoss (orderMsg s!"`Set.{name}`")
        inferArgsLoosely ctx args
        return .unknown
      if name == "sort" && args.isEmpty then
        report ctx span Code.orderLoss (orderMsg "`Set.sort` without `by = …`")
        return .unknown
    match sigsFor rt with
    | none =>
      let msg := match rt with
        | .named _ d => s!"`{d}` has no method `{name}`; declare a fn and call it as `{name}(x)` or `x.{name}()`"
        | t => s!"type `{t.render}` has no method `{name}`"
      report ctx span Code.arity msg
      inferArgsLoosely ctx args
      return .unknown
    | some (tyName, bound, sigs) =>
      match sigs.lookup name with
      | none =>
        report ctx span Code.arity s!"`{tyName}` has no method `{name}`"
        inferArgsLoosely ctx args
        return .unknown
      | some sig =>
        let (ps, ret, caps) ← instSig bound sig
        matchArgs ctx span s!"`{tyName}.{name}`" ps args
        for (cap, t) in caps do
          requireCap ctx span cap t s!"`{tyName}.{name}`"
        return ret

/-- 二項演算の両辺を同じ型にする。左辺が数値リテラルなら右辺の型(Int かもしれない)に合わせる。 -/
partial def sameType (ctx : Ctx) (l r : Expr) : M TyV := do
  match l with
  | .lit _ (.nat _) =>
    let rt ← infer ctx r
    check ctx l rt
    return rt
  | _ =>
    let lt ← infer ctx l
    check ctx r lt
    return lt

partial def inferBinop (ctx : Ctx) (span : Span) (op : String) (l r : Expr) : M TyV := do
  match op with
  | "&&" | "||" | "implies" =>
    check ctx l .bool
    check ctx r .bool
    return .bool
  | "==" | "!=" =>
    let lt ← sameType ctx l r
    requireCap ctx span "eq" lt s!"`{op}`"
    return .bool
  | "<" | "<=" | ">" | ">=" =>
    let lt ← sameType ctx l r
    requireCap ctx span "order" lt s!"`{op}`"
    return .bool
  | "+" | "-" | "*" | "/" | "%" =>
    let lt ← sameType ctx l r
    match ← zonk lt with
    | .nat => return .nat
    | .int => return .int
    | .unknown => return .unknown
    | .mvar _ => return lt
    | t =>
      report ctx span Code.typeMismatch s!"`{op}` expects Nat or Int operands, found `{t.render}`"
      return .unknown
  | _ =>
    let _ ← infer ctx l
    let _ ← infer ctx r
    return .unknown

partial def inferRecordLit (ctx : Ctx) (span : Span) (name : List String)
    (fields : Array (String × Expr)) (base : Option Expr) : M TyV := do
  let t ← convTy ctx (.named span name #[])
  let loosely : M Unit := do
    for (_, x) in fields do
      let _ ← infer ctx x
    if let some b := base then
      let _ ← infer ctx b
  match ← zonk t with
  | .named k d =>
    match (← get).types.get? k with
    | some (.record fs _) =>
      let mut seen : List String := []
      for (fname, x) in fields do
        if seen.contains fname then
          report ctx x.span Code.arity s!"field `{fname}` is given twice in `{d}` literal"
        seen := fname :: seen
        match fs.toList.lookup fname with
        | some ft => check ctx x ft
        | none =>
          report ctx x.span Code.arity s!"record `{d}` has no field `{fname}`"
          let _ ← infer ctx x
      match base with
      | some b => check ctx b t
      | none =>
        let missing := (fs.toList.filter fun (f, _) => !seen.contains f).map (·.1)
        if !missing.isEmpty then
          report ctx span Code.arity
            s!"missing field(s) {", ".intercalate (missing.map fun f => s!"`{f}`")} in `{d}` literal"
      return t
    | some (.enum ..) =>
      report ctx span Code.typeMismatch s!"`{d}` is an enum, not a record"
      loosely
      return .unknown
    | none =>
      loosely
      return .unknown
  | _ =>
    loosely
    return .unknown

/-- パターンを期待される型で検査し、束縛する名前と型を返す。 -/
partial def checkPat (ctx : Ctx) (expected : TyV) (p : Pattern) : M (List (String × TyV)) := do
  match p with
  | .wild _ => return []
  | .bind _ n => return [(n, expected)]
  | .lit span l =>
    expectTy ctx span expected (litTy l)
    return []
  | .tuple span elems =>
    let ms ← elems.toList.mapM fun _ => fresh
    expectTy ctx span expected (.tuple ms)
    let mut binds : List (String × TyV) := []
    for (q, m) in elems.toList.zip ms do
      binds := (← checkPat ctx m q) ++ binds
    return binds
  | .ctor span name args =>
    match name with
    | ["Some"] =>
      let m ← fresh
      expectTy ctx span expected (.option m)
      ctorArgs ctx span "Some" [m] args
    | ["None"] =>
      let m ← fresh
      expectTy ctx span expected (.option m)
      ctorArgs ctx span "None" [] args
    | ["Ok"] =>
      let m ← fresh
      let err ← fresh
      expectTy ctx span expected (.result m err)
      ctorArgs ctx span "Ok" [m] args
    | ["Err"] =>
      let m ← fresh
      let err ← fresh
      expectTy ctx span expected (.result m err)
      ctorArgs ctx span "Err" [err] args
    | _ =>
      match ← lookupEntry name with
      | some (e, [v]) =>
        if !e.decl.kind.isType then
          report ctx span Code.typeMismatch s!"`{renderPath name}` is not a constructor (expected `Enum.Variant`)"
          return []
        let t ← convTy ctx (.named span (name.take (name.length - 1)) #[])
        match ← zonk t with
        | .named key d =>
          match (← get).types.get? key with
          | some (.enum vs _) =>
            match vs.toList.lookup v with
            | some argTys =>
              expectTy ctx span expected t
              ctorArgs ctx span s!"{d}.{v}" argTys args
            | none =>
              report ctx span Code.arity s!"enum `{d}` has no variant `{v}`"
              return []
          | _ =>
            report ctx span Code.typeMismatch s!"`{d}` is not an enum"
            return []
        | _ => return []
      | some (e, _) =>
        report ctx span Code.typeMismatch
          s!"`{renderPath name}` is not a constructor (expected `Enum.Variant`, found {e.decl.kind.describe} `{e.decl.name}`)"
        return []
      | none => return []   -- E011 は Resolve が報告済み

partial def ctorArgs (ctx : Ctx) (span : Span) (what : String) (tys : List TyV)
    (args : Array Pattern) : M (List (String × TyV)) := do
  if tys.length != args.size then
    report ctx span Code.arity
      s!"`{what}` takes {tys.length} argument(s) in a pattern, found {args.size}"
    return []
  let mut binds : List (String × TyV) := []
  for (q, t) in args.toList.zip tys do
    binds := (← checkPat ctx t q) ++ binds
  return binds

end

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

def checkDecl (m : Module) (d : Decl) : M Unit := do
  let ctx := declCtx m d
  let q := renderPath (m.name ++ [d.name])
  match d.kind with
  | .record | .state | .enum => checkDerives ctx d q
  | .scenario =>
    if let some b := d.body then
      let _ ← infer ctx b
  | .claimBundle =>
    for (item, e) in d.items do
      match e with
      | .var span segs =>
        match ← lookupEntry segs with
        | some (en, []) =>
          if en.decl.kind != .claim && en.decl.kind != .claimBundle then
            report ctx span Code.notAClaim
              s!"item `{item}` of claim bundle `{d.name}` refers to {en.decl.kind.describe} `{en.decl.name}`; items must be claims (or nested claim bundles)"
        | some (en, _) =>
          report ctx span Code.notAClaim
            s!"item `{item}` of claim bundle `{d.name}` must name a claim, found member path under {en.decl.kind.describe} `{en.decl.name}`"
        | none => pure ()   -- E011 は Resolve が報告済み
      | _ =>
        report ctx e.span Code.notAClaim
          s!"item `{item}` of claim bundle `{d.name}` must be the name of a claim"
  | k =>
    if isFnLike k then
      let some fi := (← get).fns.get? q | return
      let c := { ctx with locals := fi.params.toList }
      if let some b := d.body then check c b fi.ret

end Typecheck

/-- コンパイル単位全体の型検査・capability 検査・選択/順序の検査。診断を返す(空なら合格)。
名前解決(`resolveAll`)が通った後に呼ぶ。 -/
def typecheckAll (mods : Array Module) : Array Diagnostic :=
  let run : Typecheck.M Unit := do
    for m in mods do Typecheck.collect m
    for m in mods do
      for d in m.decls do Typecheck.buildInfo m d
    for m in mods do
      for d in m.decls do Typecheck.checkDecl m d
  let ((), st) := run.run {}
  st.diags

end Naru
