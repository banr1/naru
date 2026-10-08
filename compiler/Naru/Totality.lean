import Std.Data.HashMap
import Std.Data.HashSet
import Naru.Ast
import Naru.Typecheck

/-!
# 計算可能性検査(停止性)— E002

型検査を通った宣言の本体から fn 間の呼出しグラフを作り、再帰のサイクルごとに
「停止性を確認できる形」であることを検査する。確認できなければ **E002**。

IDEAL.md「言語の意味論」: 再帰は構造的再帰・明示 fuel・有限集合の反復のみ。
有限集合の反復は stdlib のメソッド(`all` / `any` / `filter` / `fold` …)で、ユーザの再帰ではないので
ここでは扱わない。ユーザの再帰は次の 2 つの形だけを受理する。

- **構造的再帰**: 仮引数(またはそれより小さい値)を `match` して、構築子パターンの中で束縛した値を
  再帰呼出しの同じ測度の位置に渡す(`Tree.Node(l, _, r) => sum(l) + sum(r)`)。
- **明示 fuel**: `Nat` の仮引数 `n`(またはパターンで付けた別名)を、`n ≥ k` が分かる分岐の中で `n - k`(k ≥ 1)として渡す。
  分かる分岐は `if n == 0 { … } else { ここ }`、`if n > 0 { ここ }`、`n != 0`、`n >= k`、`k < n`、否定・`&&`・`||`、
  `else if` の連鎖(`n ≥ k` が分かっていて `n != k` なら `n ≥ k + 1`)、
  `match n { 0 => …, k => ここ }`(ガードの無いリテラルの腕が 0 から連続して覆った値の次が下限)、腕のガード。

サイクルの全員に測度(仮引数の位置)を 1 つずつ割り当て、サイクル内のすべての呼出しで
「呼出し先の測度の実引数が呼出し元の測度より厳密に小さい」ことを要求する(相互再帰も同じ規則)。
関数を値として参照する(`let g = f`)経路はその引数が読めないので、サイクル内では常に E002。

保守的な検査なので、Lean が受理できる再帰でも E002 になることがある
(`let k = n - 1;` を経由する・record の欄に再帰する・lambda の中から再帰する、など)。
検査を緩めるのではなく、書き方を上の形に寄せる。
-/

namespace Naru.Totality
open Std Typecheck

/-- 型検査の段が作った表(名前 → 宣言、修飾名 → 署名)。 -/
structure Tables where
  decls : HashMap String Entry
  fns : HashMap String FnInfo

/-- 呼出し点。 -/
structure CallSite where
  caller : String
  callee : String
  span : Span
  /-- `(呼出し先の仮引数の位置, 呼出し元の仮引数の位置)`: その実引数が呼出し元の仮引数より厳密に小さい。 -/
  decreases : List (Nat × Nat) := []
  /-- 呼出しではなく値としての参照(引数が読めない)。 -/
  bare : Bool := false
deriving Inhabited

/-- 本体を走査するときの文脈。 -/
structure Env where
  tb : Tables
  callerQ : String
  /-- 局所名(大域名を隠す)。 -/
  locals : List String
  /-- 局所名 → (仮引数の位置, 厳密に小さいか)。`false` は仮引数そのものか、その別名。 -/
  rel : List (String × Nat × Bool)
  /-- 仮引数の位置 → この経路で分かっている下限(`n ≥ k`)。 -/
  bounds : List (Nat × Nat)
  paramTys : Array TyV

abbrev W := StateM (Array CallSite)

instance [Inhabited α] : Inhabited (W α) := ⟨pure default⟩

def Env.isLocal (env : Env) (x : String) : Bool := env.locals.contains x

/-- 名前を束縛する。同名の既存の関係(仮引数・別名・部分項)は隠れる。 -/
def Env.bind (env : Env) (names : List (String × Option (Nat × Bool))) : Env :=
  let ns := names.map (·.1)
  let kept := env.rel.filter fun (n, _, _) => !ns.contains n
  let added := names.filterMap fun (n, r) => r.map fun (i, s) => (n, i, s)
  { env with locals := ns ++ env.locals, rel := added ++ kept }

def Env.boundOf (env : Env) (i : Nat) : Nat := (env.bounds.lookup i).getD 0

def Env.addBounds (env : Env) (bs : List (Nat × Nat)) : Env :=
  bs.foldl (init := env) fun e (i, k) =>
    if k > e.boundOf i then { e with bounds := (i, k) :: e.bounds.filter (·.1 != i) } else e

def Env.isNatParam (env : Env) (i : Nat) : Bool :=
  match env.paramTys[i]? with
  | some .nat => true
  | _ => false

/-- `x` が `Nat` の仮引数(またはその別名)なら、その位置。 -/
def natParamOf (env : Env) : Expr → Option Nat
  | .var _ [x] =>
    if !env.isLocal x then none
    else (env.rel.find? fun (n, i, strict) => n == x && !strict && env.isNatParam i).map (·.2.1)
  | _ => none

def natLit : Expr → Option Nat
  | .lit _ (.nat k) => some k
  | _ => none

def flipOp : String → String
  | ">" => "<"
  | "<" => ">"
  | ">=" => "<="
  | "<=" => ">="
  | op => op

/-- 条件 `c` が真(`whenTrue`)/ 偽のときに分かる、Nat 仮引数の下限。 -/
partial def boundsOf (env : Env) (c : Expr) (whenTrue : Bool) : List (Nat × Nat) :=
  match c with
  | .unop _ "!" a => boundsOf env a (!whenTrue)
  | .binop _ "&&" a b => if whenTrue then boundsOf env a true ++ boundsOf env b true else []
  | .binop _ "||" a b => if whenTrue then [] else boundsOf env a false ++ boundsOf env b false
  | .binop _ op l r =>
    -- (仮引数, 比較, リテラル) に正規化する。リテラルが左なら比較を反転
    let norm : Option (Nat × String × Nat) :=
      match natParamOf env l, natLit r with
      | some i, some k => some (i, op, k)
      | _, _ =>
        match natLit l, natParamOf env r with
        | some k, some i => some (i, flipOp op, k)
        | _, _ => none
    match norm with
    | none => []
    | some (i, op, k) =>
      match op, whenTrue with
      | "==", true => if k ≥ 1 then [(i, k)] else []
      | "==", false | "!=", true =>
        -- n ≠ k: k = 0 なら n ≥ 1。既に n ≥ k が分かっていれば(`else if n == 1` の連鎖)n ≥ k + 1
        if k == 0 then [(i, 1)] else if env.boundOf i ≥ k then [(i, k + 1)] else []
      | "!=", false => if k ≥ 1 then [(i, k)] else []
      | ">", true => [(i, k + 1)]
      | ">=", true => [(i, k)]
      | "<", false => [(i, k)]
      | "<=", false => [(i, k + 1)]
      | _, _ => []
  | _ => []

/-- `covered` に含まれない最小の自然数(`[0, 1]` → 2、`[1]` → 0)。 -/
def firstMissing (covered : List Nat) : Nat := Id.run do
  let mut k := 0
  for _ in [0:covered.length + 1] do
    if covered.contains k then k := k + 1 else return k
  return k

/-- パターンが束縛する名前と、構築子の中(= 厳密な部分項)かどうか。 -/
partial def patBinders (p : Pattern) (under : Bool) : List (String × Bool) :=
  match p with
  | .wild _ | .lit .. => []
  | .bind _ n => [(n, under)]
  | .ctor _ _ args => args.toList.flatMap (patBinders · true)
  | .tuple _ elems => elems.toList.flatMap (patBinders · under)

/-- 実引数 `arg` がそれより厳密に小さい、呼出し元の仮引数の位置。 -/
def smallerThan (env : Env) (arg : Expr) : List Nat :=
  match arg with
  | .var _ [x] =>
    if !env.isLocal x then []
    else env.rel.filterMap fun (n, i, strict) => if n == x && strict then some i else none
  | .binop _ "-" (.var _ [x]) (.lit _ (.nat k)) =>
    -- fuel: `n - k`(k ≥ 1)は、この経路で `n ≥ k` が分かっているときだけ小さい(Nat の減算は 0 で止まる)
    if k == 0 || !env.isLocal x then []
    else env.rel.filterMap fun (n, i, strict) =>
      if n == x && !strict && env.isNatParam i && env.boundOf i ≥ k then some i else none
  | _ => []

/-- 経路が fn 等(本体を持ちうる宣言)を指すなら、修飾名と署名。 -/
def lookupFn (tb : Tables) (segs : List String) : Option (String × FnInfo) :=
  match tb.decls.get? (renderPath segs) with
  | some e =>
    if isFnLike e.decl.kind then (tb.fns.get? e.qualified).map fun fi => (e.qualified, fi) else none
  | none => none

/-- 値の位置の経路が指す fn(局所名が大域名を隠す規則は型検査と同じ)。 -/
def calleeOf (env : Env) (segs : List String) : Option (String × FnInfo) :=
  match segs with
  | [x] => if env.isLocal x then none else lookupFn env.tb segs
  | _ => lookupFn env.tb segs

/-- 実引数を仮引数の位置に並べる(名前付きは仮引数名で)。数や名前の誤りは型検査が報告済み。 -/
def arrange (fi : FnInfo) (args : List Arg) : Array (Option Expr) := Id.run do
  let mut slots : Array (Option Expr) := fi.params.map fun _ => none
  let mut pos := 0
  for a in args do
    match a with
    | .pos e =>
      if pos < slots.size then
        slots := slots.set! pos (some e)
        pos := pos + 1
    | .named n e =>
      if let some i := fi.params.findIdx? (·.1 == n) then
        slots := slots.set! i (some e)
  return slots

def record (env : Env) (span : Span) (callee : String) (fi : FnInfo) (args : List Arg) : W Unit := do
  let slots := arrange fi args
  let mut dec : List (Nat × Nat) := []
  for j in [0:slots.size] do
    if let some (some e) := slots[j]? then
      for i in smallerThan env e do
        dec := dec ++ [(j, i)]
  modify (·.push { caller := env.callerQ, callee, span, decreases := dec })

/-- 本体を走査して呼出し点を集める。 -/
partial def walk (env : Env) : Expr → W Unit
  | .lit .. => pure ()
  | .var span segs => do
    if let some (q, _) := calleeOf env segs then
      modify (·.push { caller := env.callerQ, callee := q, span, bare := true })
  | .call span f args => do
    match f with
    | .var _ segs =>
      match calleeOf env segs with
      | some (q, fi) => record env span q fi args.toList
      | none => walk env f
    | _ => walk env f
    for a in args do walk env (argExpr a)
  | .field _ r _ => walk env r
  | .method span r name args => do
    -- `x.f(args)` は `f` がユーザ宣言なら `f(x, args)`(UFCS。型検査と同じ規則)
    if !env.isLocal name then
      if let some (q, fi) := lookupFn env.tb [name] then
        record env span q fi (.pos r :: args.toList)
    walk env r
    for a in args do walk env (argExpr a)
  | .binop _ _ l r => do
    walk env l
    walk env r
  | .unop _ _ a => walk env a
  | .ite _ c t el => do
    walk env c
    walk (env.addBounds (boundsOf env c true)) t
    walk (env.addBounds (boundsOf env c false)) el
  | .matchE _ s arms => do
    walk env s
    -- 被検査式が仮引数(またはその別名・部分項)なら、腕のパターンが束縛する名前はその部分項
    let scrut : Option (Nat × Bool) := match s with
      | .var _ [x] =>
        if env.isLocal x then (env.rel.find? (·.1 == x)).map (fun (_, i, st) => (i, st)) else none
      | _ => none
    -- ガードの無いリテラルの腕が覆った値。ガード付きの腕は(ガードが偽なら)値を次の腕に落とすので数えない
    let mut covered : List Nat := []
    for arm in arms do
      let .mk pat guard body := arm
      let names := (patBinders pat false).map fun (n, under) =>
        (n, scrut.map fun (i, strict) => (i, under || strict))
      let mut e := env.bind names
      -- `match n { 0 => …, 1 => …, k => ここ }`: 0 から連続して覆われた値は束縛 / ワイルドカードの腕には来ない
      -- → その次の値が下限(`0` だけなら n ≥ 1、`0` と `1` なら n ≥ 2)
      if let some (i, false) := scrut then
        match pat with
        | .bind .. | .wild _ =>
          let lb := firstMissing covered
          if lb > 0 then e := e.addBounds [(i, lb)]
        | _ => pure ()
      if let some g := guard then
        walk e g
        e := e.addBounds (boundsOf e g true)
      walk e body
      if guard.isNone then
        if let .lit _ (.nat k) := pat then covered := k :: covered
  | .block _ stmts tail => do
    let mut e := env
    for st in stmts do
      match st with
      | .letS _ name _ val =>
        walk e val
        e := e.bind [(name, none)]
      | .exprS x => walk e x
      | .inputS _ _ params val => walk (e.bind (params.toList.map fun (p, _) => (p, none))) val
      | .observeS _ x => walk e x
    if let some t := tail then walk e t
  | .recordLit _ _ fields base => do
    for (_, x) in fields do walk env x
    if let some b := base then walk env b
  | .listLit _ es | .tupleLit _ es => do
    for x in es do walk env x
  | .lambda _ params body =>
    walk (env.bind (params.toList.map fun p => (p.name, none))) body
  | .quant _ _ binders body =>
    walk (env.bind (binders.toList.map fun b => (b.name, none))) body

/-- 呼出しグラフの節点(本体を持つ fn 等)。 -/
structure FnNode where
  q : String
  name : String
  kind : DeclKind
  file : String
  span : Span
  nparams : Nat
deriving Inhabited

def collectSites (tb : Tables) (mods : Array Module) : Array FnNode × Array CallSite := Id.run do
  let mut nodes : Array FnNode := #[]
  let mut sites : Array CallSite := #[]
  for m in mods do
    for d in m.decls do
      if !isFnLike d.kind then continue
      let some b := d.body | continue
      let q := renderPath (m.name ++ [d.name])
      let some fi := tb.fns.get? q | continue
      nodes := nodes.push
        { q, name := d.name, kind := d.kind, file := m.file, span := d.span, nparams := fi.params.size }
      let mut rel : List (String × Nat × Bool) := []
      for i in [0:fi.params.size] do
        rel := rel ++ [(fi.params[i]!.1, i, false)]
      let env : Env :=
        { tb, callerQ := q, locals := fi.params.toList.map (·.1), rel, bounds := [],
          paramTys := fi.params.map (·.2) }
      let ((), s) := (walk env b).run #[]
      sites := sites ++ s
  return (nodes, sites)

def adjacency (sites : Array CallSite) : HashMap String (List String) :=
  sites.foldl (init := {}) fun m s =>
    let cur := m.getD s.caller []
    if cur.contains s.callee then m else m.insert s.caller (s.callee :: cur)

partial def reachGo (adj : HashMap String (List String)) : List String → HashSet String → HashSet String
  | [], seen => seen
  | x :: rest, seen =>
    let next := (adj.getD x []).filter fun y => !seen.contains y
    reachGo adj (next ++ rest) (next.foldl (·.insert ·) seen)

/-- `start` から 1 回以上の呼出しで届く節点。 -/
def reachFrom (adj : HashMap String (List String)) (start : String) : HashSet String :=
  let init := adj.getD start []
  reachGo adj init (init.foldl (·.insert ·) {})

/-- 割り当て済みの測度のもとで、両端が割り当て済みの辺がすべて厳密に減るか。 -/
def edgesOk (edges : Array CallSite) (acc : List (String × Nat)) : Bool :=
  edges.all fun s =>
    match acc.lookup s.caller, acc.lookup s.callee with
    | some i, some j => !s.bare && s.decreases.contains (j, i)
    | _, _ => true

/-- サイクルの各関数に測度(仮引数の位置)を割り当てる探索。予算(状態)が尽きたら失敗。 -/
partial def search (edges : Array CallSite) (members : List FnNode) (acc : List (String × Nat)) :
    StateM Nat (Option (List (String × Nat))) := do
  match members with
  | [] => return some acc
  | f :: rest =>
    for i in [0:f.nparams] do
      let budget ← get
      if budget == 0 then return none
      set (budget - 1)
      let acc' := (f.q, i) :: acc
      if edgesOk edges acc' then
        if let some r ← search edges rest acc' then return some r
    return none

def hint : String :=
  "naru accepts only structural recursion (recurse on a value bound by a `match` pattern of a parameter) and explicit fuel (a `Nat` parameter `n` passed as `n - 1` under a guard such as `if n == 0 { … } else { … }`); every call around the cycle must make the same measure smaller"

/-- 受理した再帰のサイクル(強連結成分)。backend が `mutual` ブロックと `termination_by` を作るのに使う。 -/
structure Recursion where
  /-- 成分の fn の修飾名(宣言の順)。 -/
  members : List String
  /-- fn の修飾名 → 測度に選んだ仮引数の位置。 -/
  measures : List (String × Nat)
deriving Inhabited

def analyze (nodes : Array FnNode) (sites : Array CallSite) : Array Diagnostic × Array Recursion := Id.run do
  let adj := adjacency sites
  let mut done : HashSet String := {}
  let mut diags : Array Diagnostic := #[]
  let mut recs : Array Recursion := #[]
  for f in nodes do
    if done.contains f.q then continue
    let r := reachFrom adj f.q
    if !r.contains f.q then continue
    -- f は再帰する。サイクル(強連結成分)= f から届き、かつ f に届く節点
    let members := nodes.toList.filter fun g =>
      g.q == f.q || (r.contains g.q && (reachFrom adj g.q).contains f.q)
    for g in members do done := done.insert g.q
    let mq := members.map (·.q)
    let edges := sites.filter fun s => mq.contains s.caller && mq.contains s.callee
    let (res, _) := (search edges members []).run 100000
    if let some assignment := res then
      recs := recs.push { members := mq, measures := mq.filterMap fun q => (assignment.lookup q).map (q, ·) }
      continue
    for g in members do
      let site := edges.find? (·.caller == g.q)
      let span := (site.map (·.span)).getD g.span
      let shape :=
        if members.length == 1 then "calls itself"
        else
          let others := (members.filter (·.q != g.q)).map fun m => s!"`{m.name}`"
          s!"is part of a recursion cycle with {", ".intercalate others}"
      let bareNote :=
        if site.any (·.bare) then "; here it is passed around as a value, which hides its arguments — call it directly" else ""
      diags := diags.push
        { file := g.file, span, code := Code.nonTotal,
          msg := s!"{g.kind.describe} `{g.name}` {shape}, but no argument is shown to get smaller on every recursive call{bareNote}. {hint}" }
  return (diags, recs)

end Totality

/-- コンパイル単位全体の停止性検査(E002)。型検査(`typecheckAll`)が通った後に呼ぶ。
診断(空なら合格)と、受理した再帰のサイクル(backend 用)を返す。 -/
def totalityAll (mods : Array Module) : Array Diagnostic × Array Totality.Recursion :=
  let build : Typecheck.M Unit := do
    for m in mods do Typecheck.collect m
    for m in mods do
      for d in m.decls do Typecheck.buildInfo m d
  let ((), st) := build.run {}
  let tb : Totality.Tables := { decls := st.decls, fns := st.fns }
  let (nodes, sites) := Totality.collectSites tb mods
  Totality.analyze nodes sites

end Naru
