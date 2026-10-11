import NaruSem.SurfaceEval
import NaruSem.Call

/-!
# 関数・input の保存対象の Surface AST の意味論と適格性(IDEAL.md C54、用語「関数・input の保存対象」)

C48 の Surface AST の保存対象(`Surface.lean` / `SurfaceEval.lean`)を土台に、構文解析の出力のうち **呼出し**(`Naru.Expr.call`: 呼出し先は名前の経路、
実引数は位置引数と名前付き引数)と **UFCS**(`recv.f(args)` が大域の宣言 `f` の呼出し `f(recv, args)` になる糖衣)を加えた AST の意味論を、
frontend(名前解決・型検査・elaboration)から独立に定める。既存の `Surf.*` の定義は変えず、呼出しを含む AST のための定義をここに並置する
(名前空間 `NaruSem.Surf.Call`)。Core 側の対応は `Call.lean`。

- **宣言表 `Table`**: 名前と呼出し先の対応 `resolve`(経路 → 修飾名: 修飾名そのもの、または宣言の単純名(コンパイル単位で一意))と、修飾名の署名 `sig`
  (`DeclSig`: fn / input は仮引数の名前と型と戻り型、spec 宣言は仮引数の名前と型)。宣言群から作る(`tableOf`: 解決は宣言群全体の名前で、署名は
  依存順でそれより前の宣言だけ)。局所名は大域名を隠す(`headBound`: 呼出し先の経路の頭が束縛されていれば呼出しではなく対象外。UFCS も局所名 `f` があれば
  適用しない。コンパイラの名前解決と同じ規則)。
- **実引数の順序**: 位置引数は仮引数の先頭から順に、名前付き引数は仮引数の名前で(`arrange`: 名前付きの後の位置引数、無い名前、二重の指定、不足、過剰は
  `none`。コンパイラの `matchArgs` と同じ規則)。実引数は構文解析の順に型付け・評価してから並べ替える(構造的再帰のため。評価は純粋なので順序は意味に
  関与しない)。
- **束縛文脈と環境**: この層では runtime の式も spec の束縛文脈 `SCtx`(名前 → 値の型か命題)と環境 `SEnv` の上で読む。runtime の式は値の束縛だけを
  参照し(`.var` は `.val t` のときだけ型を持つ)、命題の束縛名も局所名として大域名を隠す(値の位置で命題に束ねた名前を呼出し先と取り違えない)。
  fn の本体の文脈は仮引数(すべて値)。
- **型付け・意味**: `wtR T Γ e`(runtime)/ `wtS T Γ e`(spec)/ `eval T Φ ρ e` / `Sem T Φ Ψ ρ e P` は `Surface.lean` / `SurfaceEval.lean` の定義に呼出しと UFCS の
  場合を加えたもの。`Φ : Call.FEnv`(fn の意味と input の解釈)と `Ψ : Call.PEnv`(spec 宣言の意味)は Core 側と共有する(鍵 → 値の列 → 値 / 命題)。
  fn / input の呼出しは値、spec 宣言の呼出しは命題(runtime から呼べない)。論理の位置の Bool の呼出しは「結果が true である」という命題(`callVal` / `ufcsVal`)、
  spec 宣言の呼出しはその宣言の意味に実引数の値を渡したもの(`callSpec` / `ufcsSpec`)。命題を Bool に戻す規則は無い。
- **宣言群**: `Decl`(モジュール名・種別・名前・位置・仮引数・戻り型・本体)の列 `Prog`。`wtProg` は依存順(呼出し先が前)に鍵と単純名の重複なく各宣言が
  適格(fn は本体が戻り型、spec 宣言は本体が論理の位置の型、input は本体なし)であること。`interp I P` は input の解釈 `I` から始めて fn / spec 宣言の
  本体の意味を順に環境に足す(`Call.Interp` と同じ構成。本体はそれより前の宣言の表と環境で読む)。

意味が定まること(全域性・一意性・存在)の証明は後続の周回(`SurfaceCallTotality.lean`)。実際の構文解析の出力との一致は `SurfaceCallQuote.lean`。
-/

namespace NaruSem.Surf.Call
open Naru

/-! ## 宣言表 -/

/-- 呼出し先の署名: 仮引数の名前と型(名前付き引数のため)と、fn / input の戻り型。 -/
inductive DeclSig where
  | fn (params : List (String × NaruSem.Ty)) (ret : NaruSem.Ty)
  | input (params : List (String × NaruSem.Ty)) (ret : NaruSem.Ty)
  | spec (params : List (String × NaruSem.Ty))
deriving DecidableEq, Repr

def DeclSig.params : DeclSig → List (String × NaruSem.Ty)
  | .fn ps _ | .input ps _ | .spec ps => ps

/-- Core 側の署名(名前を落とす)。 -/
def DeclSig.toSig : DeclSig → NaruSem.Call.Sig
  | .fn ps t => .fn (ps.map (·.2)) t
  | .input ps t => .input (ps.map (·.2)) t
  | .spec ps => .spec (ps.map (·.2))

/-- 値の位置で呼べる署名(fn / input): 仮引数と戻り型。 -/
def DeclSig.value? : DeclSig → Option (List (String × NaruSem.Ty) × NaruSem.Ty)
  | .fn ps t => some (ps, t)
  | .input ps t => some (ps, t)
  | .spec _ => none

def DeclSig.spec? : DeclSig → Option (List (String × NaruSem.Ty))
  | .spec ps => some ps
  | _ => none

/-- 宣言表: 名前の経路の解決(→ 修飾名)と修飾名の署名。 -/
structure Table where
  resolve : List String → Option String
  sig : String → Option DeclSig

/-- 表の Core 側の署名の文脈。 -/
def Table.Δ (T : Table) : NaruSem.Call.SigEnv := fun k => (T.sig k).map DeclSig.toSig

/-- 経路が spec 宣言に解決するか。 -/
def isSpecPath (T : Table) (path : List String) : Bool :=
  match T.resolve path with
  | some k => ((T.sig k).bind DeclSig.spec?).isSome
  | none => false

/-- 経路の頭が局所名に束ねられているか(局所名は大域名を隠す)。 -/
def headBound {β : Type} (f : String → Option β) : List String → Bool
  | [x] => (f x).isSome
  | _ => false

/-- UFCS: `recv.m(args)` が大域の宣言 `m` の呼出しになる条件 — `m` が局所名でなく、宣言に解決する。 -/
def ufcs {β : Type} (T : Table) (f : String → Option β) (m : String) : Bool :=
  (f m).isNone && (T.resolve [m]).isSome

/-! ## 実引数の並べ替え -/

/-- 名前付き引数のある実引数の列を仮引数の順に並べる: 位置引数は先頭から順に、名前付き引数は名前で。名前付きの後の位置引数・無い名前・
二重の指定・過剰は `none`。`slots` は仮引数ごとの枡、`i` は次の位置引数の枡、`sawNamed` は名前付き引数を見たか。 -/
def assign {α : Type} (params : List (String × NaruSem.Ty)) :
    List (Option String × α) → Nat → Bool → List (Option α) → Option (List (Option α))
  | [], _, _, slots => some slots
  | (none, v) :: rest, i, sawNamed, slots =>
    if sawNamed then none
    else if i < slots.length then assign params rest (i + 1) false (slots.set i (some v)) else none
  | (some n, v) :: rest, i, _, slots =>
    match params.findIdx? (fun p => p.1 == n) with
    | some j =>
      match slots[j]? with
      | some none => assign params rest i true (slots.set j (some v))
      | _ => none
    | none => none

/-- すべての枡が埋まっていればその列。 -/
def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | some v :: rest => (allSome rest).map (v :: ·)
  | none :: _ => none

/-- 実引数(構文解析の順。名前付きは名前つき)を仮引数の順の列にする。 -/
def arrange {α : Type} (params : List (String × NaruSem.Ty)) (args : List (Option String × α)) : Option (List α) :=
  (assign params args 0 false (params.map fun _ => none)).bind allSome

/-! ## 対象の式 -/

mutual

/-- 対象の式(構文解析の出力の部分集合。位置情報つき)。`Surface.lean` の `Surf.Expr` に呼出しを加え、メソッドの実引数を名前付きも許す列にしたもの。 -/
inductive Expr where
  | lit (span : Span) (l : Lit)
  | var (span : Span) (name : List String)
  /-- `f(args)` / `A.B.f(args)`。対象は呼出し先が名前の経路のもの。 -/
  | call (span : Span) (callee : Expr) (args : List Arg)
  /-- `recv.name(args)`: 大域の宣言 `name` があれば UFCS の呼出し、なければ Nat の `min` / `max`(位置引数 1 つ)。 -/
  | method (span : Span) (recv : Expr) (name : String) (args : List Arg)
  | binop (span : Span) (op : String) (lhs rhs : Expr)
  | unop (span : Span) (op : String) (arg : Expr)
  | ite (span : Span) (cond thn els : Expr)
  | matchE (span : Span) (scrut : Expr) (arms : List Arm)
  | block (span : Span) (stmts : List Stmt) (tail : Option Expr)
  | quant (span : Span) (q : Quant) (binders : List Binder) (body : Expr)

/-- 実引数: 位置引数か名前付き引数。 -/
inductive Arg where
  | pos (e : Expr)
  | named (name : String) (e : Expr)

inductive Arm where
  | mk (pat : Pat) (guard : Option Expr) (body : Expr)

inductive Stmt where
  | letS (span : Span) (name : String) (ty : Option Ty) (val : Expr)

end

instance : Inhabited Expr := ⟨.lit {} .unit⟩
instance : Inhabited Arg := ⟨.pos default⟩
instance : Inhabited Arm := ⟨.mk (.wild {}) none default⟩
instance : Inhabited Stmt := ⟨.letS {} "" none default⟩

mutual

/-- 構文解析の型への埋め込み(構築子ごとに同じ構築子へ)。 -/
def Expr.toAst : Expr → Naru.Expr
  | .lit sp l => .lit sp l
  | .var sp n => .var sp n
  | .call sp f args => .call sp f.toAst (argsToAst args).toArray
  | .method sp r n args => .method sp r.toAst n (argsToAst args).toArray
  | .binop sp op l r => .binop sp op l.toAst r.toAst
  | .unop sp op a => .unop sp op a.toAst
  | .ite sp c t e => .ite sp c.toAst t.toAst e.toAst
  | .matchE sp s arms => .matchE sp s.toAst (armsToAst arms).toArray
  | .block sp stmts tail =>
    .block sp (stmtsToAst stmts).toArray (match tail with | some e => some e.toAst | none => none)
  | .quant sp q bs b => .quant sp q (bs.map Binder.toAst).toArray b.toAst

def argsToAst : List Arg → List Naru.Arg
  | [] => []
  | .pos e :: rest => .pos e.toAst :: argsToAst rest
  | .named n e :: rest => .named n e.toAst :: argsToAst rest

def armsToAst : List Arm → List Naru.Arm
  | [] => []
  | a :: rest => a.toAst :: armsToAst rest

def Arm.toAst : Arm → Naru.Arm
  | .mk p g b => .mk p.toAst (match g with | some g => some g.toAst | none => none) b.toAst

def stmtsToAst : List Stmt → List Naru.Stmt
  | [] => []
  | s :: rest => s.toAst :: stmtsToAst rest

def Stmt.toAst : Stmt → Naru.Stmt
  | .letS sp x ty v => .letS sp x (ty.map Ty.toAst) v.toAst

end

/-- `match` の網羅性(`Surface.lean` と同じ規則)。 -/
def exhaustiveFrom (t : NaruSem.Ty) (sawT sawF : Bool) : List Arm → Bool
  | [] => false
  | .mk p none _ :: rest =>
    match p with
    | .wild _ | .bind _ _ => true
    | .lit _ (.bool true) => (t = .bool && sawF) || exhaustiveFrom t true sawF rest
    | .lit _ (.bool false) => (t = .bool && sawT) || exhaustiveFrom t sawT true rest
    | _ => exhaustiveFrom t sawT sawF rest
  | .mk _ (some _) _ :: rest => exhaustiveFrom t sawT sawF rest

def exhaustive (t : NaruSem.Ty) (arms : List Arm) : Bool := exhaustiveFrom t false false arms

/-! ## 呼出しの型 -/

/-- 呼出し先の経路と(構文解析の順の)実引数の型から、fn / input の呼出しの型。 -/
def callTy (T : Table) (path : List String) (tys : List (Option String × NaruSem.Ty)) : Option NaruSem.Ty :=
  match T.resolve path with
  | some k =>
    match (T.sig k).bind DeclSig.value? with
    | some (ps, t) => if arrange ps tys = some (ps.map (·.2)) then some t else none
    | none => none
  | none => none

/-- spec の位置の呼出しの型: fn / input は値、spec 宣言は命題。 -/
def callTyS (T : Table) (path : List String) (tys : List (Option String × NaruSem.Ty)) : Option STy :=
  match T.resolve path with
  | some k =>
    match T.sig k with
    | some (.fn ps t) => if arrange ps tys = some (ps.map (·.2)) then some (.val t) else none
    | some (.input ps t) => if arrange ps tys = some (ps.map (·.2)) then some (.val t) else none
    | some (.spec ps) => if arrange ps tys = some (ps.map (·.2)) then some .prop else none
    | none => none
  | none => none

/-! ## runtime の型付けと対象範囲 -/

mutual

/-- runtime の式の型付け(対象範囲の判定を兼ねる)。文脈は `SCtx`: 局所名は値の束縛だけ参照できる(命題の束縛名も大域名を隠す)。 -/
def wtR (T : Table) (Γ : SCtx) : Expr → Option NaruSem.Ty
  | .lit _ (.nat _) => some .nat
  | .lit _ (.bool _) => some .bool
  | .var _ [x] => match Γ x with | some (.val t) => some t | _ => none
  | .call _ (.var _ path) args =>
    if headBound Γ path then none
    else
      match wtArgs T Γ args with
      | some tys => callTy T path tys
      | none => none
  | .binop _ op l r =>
    match BinOp.ofString? op, wtR T Γ l, wtR T Γ r with
    | some k, some tl, some tr => binopResult k tl tr
    | _, _, _ => none
  | .unop _ op a =>
    if op = "!" then
      match wtR T Γ a with
      | some .bool => some .bool
      | _ => none
    else none
  | .method _ r m args =>
    if ufcs T Γ m then
      match wtR T Γ r, wtArgs T Γ args with
      | some tr, some tys => callTy T [m] ((none, tr) :: tys)
      | _, _ => none
    else
      match args with
      | [.pos a] =>
        match NatMethod.ofString? m, wtR T Γ r, wtR T Γ a with
        | some _, some .nat, some .nat => some .nat
        | _, _, _ => none
      | _ => none
  | .ite _ c t e =>
    match wtR T Γ c, wtR T Γ t, wtR T Γ e with
    | some .bool, some tt, some te => if tt = te then some tt else none
    | _, _, _ => none
  | .matchE _ s arms =>
    match wtR T Γ s with
    | some ts => if exhaustive ts arms then wtArmsR T Γ ts arms else none
    | none => none
  | .block _ stmts (some e) =>
    match wtStmtsR T Γ stmts with
    | some Γ' => wtR T Γ' e
    | none => none
  | _ => none

/-- 実引数の列の型(構文解析の順。名前付きは名前つき)。 -/
def wtArgs (T : Table) (Γ : SCtx) : List Arg → Option (List (Option String × NaruSem.Ty))
  | [] => some []
  | .pos e :: rest =>
    match wtR T Γ e, wtArgs T Γ rest with
    | some t, some tys => some ((none, t) :: tys)
    | _, _ => none
  | .named n e :: rest =>
    match wtR T Γ e, wtArgs T Γ rest with
    | some t, some tys => some ((some n, t) :: tys)
    | _, _ => none

def wtStmtsR (T : Table) (Γ : SCtx) : List Stmt → Option SCtx
  | [] => some Γ
  | .letS _ x ty v :: rest =>
    match wtR T Γ v with
    | some tv =>
      match annot ty tv with
      | some t => wtStmtsR T (Γ.ext x (.val t)) rest
      | none => none
    | none => none

def wtArmsR (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) : List Arm → Option NaruSem.Ty
  | [] => none
  | arm :: rest =>
    match wtArmR T Γ ts arm, rest with
    | none, _ => none
    | some t1, [] => some t1
    | some t1, _ :: _ =>
      match wtArmsR T Γ ts rest with
      | some t2 => if t1 = t2 then some t1 else none
      | none => none

def wtArmR (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) : Arm → Option NaruSem.Ty
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none => wtR T (Γ.extVals bs) b
      | some g =>
        match wtR T (Γ.extVals bs) g with
        | some .bool => wtR T (Γ.extVals bs) b
        | _ => none

end

/-! ## spec の型付けと対象範囲 -/

def stmtsCtxP (Γ : SCtx) : List Stmt → SCtx
  | [] => Γ
  | .letS _ x _ _ :: rest => stmtsCtxP (Γ.ext x (.val .nat)) rest

mutual

/-- spec の式が命題でしか表せないか(量化、命題に束ねた局所名、spec 宣言の呼出しを含む)。 -/
def proppyS (T : Table) (Γ : SCtx) : Expr → Bool
  | .quant .. => true
  | .var _ [x] => match Γ x with | some .prop => true | _ => false
  | .call _ (.var _ path) args => (!headBound Γ path && isSpecPath T path) || proppyArgs T Γ args
  | .method _ r m args => (ufcs T Γ m && isSpecPath T [m]) || proppyS T Γ r || proppyArgs T Γ args
  | .block _ stmts tail =>
    proppyStmts T Γ stmts || (match tail with | some e => proppyS T (stmtsCtxP Γ stmts) e | none => false)
  | .ite _ c t e => proppyS T Γ c || proppyS T Γ t || proppyS T Γ e
  | .binop _ _ l r => proppyS T Γ l || proppyS T Γ r
  | .unop _ _ a => proppyS T Γ a
  | .matchE _ s arms => proppyS T Γ s || proppyArms T Γ arms
  | _ => false

def proppyArgs (T : Table) (Γ : SCtx) : List Arg → Bool
  | [] => false
  | .pos e :: rest => proppyS T Γ e || proppyArgs T Γ rest
  | .named _ e :: rest => proppyS T Γ e || proppyArgs T Γ rest

def proppyStmts (T : Table) (Γ : SCtx) : List Stmt → Bool
  | [] => false
  | .letS _ x _ v :: rest => proppyS T Γ v || proppyStmts T (Γ.ext x (.val .nat)) rest

def proppyArms (T : Table) (Γ : SCtx) : List Arm → Bool
  | [] => false
  | .mk p g b :: rest =>
    let Γ' := match p with
      | .bind _ x => Γ.ext x (.val .nat)
      | _ => Γ
    (match g with | some g => proppyS T Γ' g | none => false) || proppyS T Γ' b || proppyArms T Γ rest

end

mutual

/-- spec の式の型付け。値を要求する位置(算術・比較・Nat の等値の被演算子、`min` / `max`、scrutinee、値の `let` の値、実引数)は `wtR T Γ`。 -/
def wtS (T : Table) (Γ : SCtx) : Expr → Option STy
  | .lit _ (.nat _) => some (.val .nat)
  | .lit _ (.bool _) => some (.val .bool)
  | .var _ [x] => Γ x
  | .call _ (.var _ path) args =>
    if headBound Γ path then none
    else
      match wtArgs T Γ args with
      | some tys => callTyS T path tys
      | none => none
  | .ite _ c t e =>
    match wtS T Γ c, wtS T Γ t, wtS T Γ e with
    | some tc, some tt, some te =>
      match tc.join tt with
      | some j => j.join te
      | none => none
    | _, _, _ => none
  | .binop _ op l r =>
    match BinOp.ofString? op with
    | some (.logic _) =>
      match wtS T Γ l, wtS T Γ r with
      | some tl, some tr => tl.join tr
      | _, _ => none
    | some (.eq _) =>
      if wtR T Γ l = some .nat ∧ wtR T Γ r = some .nat then some (.val .bool)
      else
        match wtS T Γ l, wtS T Γ r with
        | some tl, some tr => tl.join tr
        | _, _ => none
    | some (.cmp _) =>
      match wtR T Γ l, wtR T Γ r with
      | some tl, some tr => if tl = tr then some (.val .bool) else none
      | _, _ => none
    | some (.arith _) =>
      match wtR T Γ l, wtR T Γ r with
      | some .nat, some .nat => some (.val .nat)
      | _, _ => none
    | none => none
  | .unop _ op a =>
    if op = "!" then
      match wtS T Γ a with
      | some t => if t.isForm then some t else none
      | none => none
    else none
  | .method _ r m args =>
    if ufcs T Γ m then
      match wtR T Γ r, wtArgs T Γ args with
      | some tr, some tys => callTyS T [m] ((none, tr) :: tys)
      | _, _ => none
    else
      match args with
      | [.pos a] =>
        match NatMethod.ofString? m, wtR T Γ r, wtR T Γ a with
        | some _, some .nat, some .nat => some (.val .nat)
        | _, _, _ => none
      | _ => none
  | .matchE _ s arms =>
    match wtR T Γ s with
    | some ts => if exhaustive ts arms then wtArmsS T Γ ts arms else none
    | none => none
  | .block _ stmts (some e) =>
    match wtStmtsS T Γ stmts with
    | some Γ' => wtS T Γ' e
    | none => none
  | .quant _ _ bs b =>
    match bs with
    | [] => none
    | _ =>
      match SCtx.extBinders Γ bs with
      | some Γ' =>
        match wtS T Γ' b with
        | some t => if t.isForm then some .prop else none
        | none => none
      | none => none
  | _ => none

def wtStmtsS (T : Table) (Γ : SCtx) : List Stmt → Option SCtx
  | [] => some Γ
  | .letS _ x ty v :: rest =>
    if proppyS T Γ v then
      if annotProp ty then
        match wtS T Γ v with
        | some .prop => wtStmtsS T (Γ.ext x .prop) rest
        | _ => none
      else none
    else
      match wtR T Γ v with
      | some tv =>
        match annot ty tv with
        | some t => wtStmtsS T (Γ.ext x (.val t)) rest
        | none => none
      | none => none

def wtArmsS (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) : List Arm → Option STy
  | [] => none
  | arm :: rest =>
    match wtArmS T Γ ts arm, rest with
    | none, _ => none
    | some t1, [] => some t1
    | some t1, _ :: _ =>
      match wtArmsS T Γ ts rest with
      | some t2 => t1.join t2
      | none => none

def wtArmS (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) : Arm → Option STy
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none =>
        match wtS T (Γ.extVals bs) b with
        | some t => if t.isForm then some t else none
        | none => none
      | some g =>
        match wtS T (Γ.extVals bs) g, wtS T (Γ.extVals bs) b with
        | some tg, some tb => tg.join tb
        | _, _ => none

end

/-! ## runtime の意味 -/

/-- 呼出し先の経路と(構文解析の順の)実引数の値から、環境の関数に仮引数の順の値を渡す。鍵が無い・署名が fn / input でない・関数が無い・
並べ替えられないときは `none`。 -/
def callVal (T : Table) (Φ : NaruSem.Call.FEnv) (path : List String) (vals : List (Option String × Val)) : Option Val :=
  match T.resolve path with
  | some k =>
    match (T.sig k).bind DeclSig.value?, Φ k with
    | some (ps, _), some f =>
      match arrange ps vals with
      | some vs => f vs
      | none => none
    | _, _ => none
  | none => none

mutual

/-- runtime の式の意味。環境は `SEnv`(値の束縛だけを参照する)。`none` は行き詰まり。 -/
def eval (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) : Expr → Option Val
  | .lit _ (.nat n) => some (.nat n)
  | .lit _ (.bool b) => some (.bool b)
  | .var _ [x] => match ρ x with | some (.val v) => some v | _ => none
  | .call _ (.var _ path) args =>
    if headBound ρ path then none
    else
      match evalArgs T Φ ρ args with
      | some vals => callVal T Φ path vals
      | none => none
  | .binop _ op l r =>
    match BinOp.ofString? op, eval T Φ ρ l, eval T Φ ρ r with
    | some k, some a, some b => k.apply a b
    | _, _, _ => none
  | .unop _ op a =>
    if op = "!" then
      match eval T Φ ρ a with
      | some (.bool x) => some (.bool (!x))
      | _ => none
    else none
  | .method _ r m args =>
    if ufcs T ρ m then
      match eval T Φ ρ r, evalArgs T Φ ρ args with
      | some v, some vals => callVal T Φ [m] ((none, v) :: vals)
      | _, _ => none
    else
      match args with
      | [.pos a] =>
        match NatMethod.ofString? m, eval T Φ ρ r, eval T Φ ρ a with
        | some k, some (.nat x), some (.nat y) => some (.nat (k.eval x y))
        | _, _, _ => none
      | _ => none
  | .ite _ c t e =>
    match eval T Φ ρ c with
    | some (.bool true) => eval T Φ ρ t
    | some (.bool false) => eval T Φ ρ e
    | _ => none
  | .matchE _ s arms =>
    match eval T Φ ρ s with
    | some v => evalArms T Φ ρ v arms
    | none => none
  | .block _ stmts (some e) =>
    match evalStmts T Φ ρ stmts with
    | some ρ' => eval T Φ ρ' e
    | none => none
  | _ => none

/-- 実引数の列の評価(構文解析の順。名前付きは名前つき)。 -/
def evalArgs (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) : List Arg → Option (List (Option String × Val))
  | [] => some []
  | .pos e :: rest =>
    match eval T Φ ρ e, evalArgs T Φ ρ rest with
    | some v, some vals => some ((none, v) :: vals)
    | _, _ => none
  | .named n e :: rest =>
    match eval T Φ ρ e, evalArgs T Φ ρ rest with
    | some v, some vals => some ((some n, v) :: vals)
    | _, _ => none

def evalStmts (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) : List Stmt → Option SEnv
  | [] => some ρ
  | .letS _ x _ v :: rest =>
    match eval T Φ ρ v with
    | some w => evalStmts T Φ (ρ.ext x (.val w)) rest
    | none => none

def evalArms (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (v : Val) : List Arm → Option Val
  | [] => none
  | .mk p g b :: rest =>
    match matchPat p v with
    | none => evalArms T Φ ρ v rest
    | some bs =>
      match g with
      | none => eval T Φ (ρ.extVals bs) b
      | some g =>
        match eval T Φ (ρ.extVals bs) g with
        | some (.bool true) => eval T Φ (ρ.extVals bs) b
        | some (.bool false) => evalArms T Φ ρ v rest
        | _ => none

end

def Eval (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (e : Expr) (v : Val) : Prop := eval T Φ ρ e = some v

/-! ## spec の意味 -/

/-- spec の式の意味。`Sem T Φ Ψ ρ e P`: 表 `T`、runtime の呼出し先 `Φ`、spec 宣言の意味 `Ψ`、環境 `ρ` の下で論理の位置の式 `e` の意味は命題 `P`。 -/
inductive Sem (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) : SEnv → Expr → Prop → Prop where
  | lit {ρ : SEnv} {sp : Span} {b : Bool} : Sem T Φ Ψ ρ (.lit sp (.bool b)) (b = true)
  | varVal {ρ : SEnv} {sp : Span} {x : String} {b : Bool} (h : ρ x = some (.val (.bool b))) : Sem T Φ Ψ ρ (.var sp [x]) (b = true)
  | varProp {ρ : SEnv} {sp : Span} {x : String} {P : Prop} (h : ρ x = some (.prop P)) : Sem T Φ Ψ ρ (.var sp [x]) P
  /-- fn / input の呼出し(論理の位置): 実引数を評価して仮引数の順に並べ、Bool の結果を「true である」という命題に写す。 -/
  | callVal {ρ : SEnv} {sp vsp : Span} {path : List String} {args : List Arg} {k : String} {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
      {f : List Val → Option Val} {vals : List (Option String × Val)} {vs : List Val} {b : Bool}
      (hs : headBound ρ path = false) (hr : T.resolve path = some k) (hd : (T.sig k).bind DeclSig.value? = some (ps, t)) (hf : Φ k = some f)
      (ha : evalArgs T Φ ρ args = some vals) (harr : arrange ps vals = some vs) (hv : f vs = some (.bool b)) :
      Sem T Φ Ψ ρ (.call sp (.var vsp path) args) (b = true)
  /-- spec 宣言の呼出し: その宣言の意味に仮引数の順の実引数の値を渡す。 -/
  | callSpec {ρ : SEnv} {sp vsp : Span} {path : List String} {args : List Arg} {k : String} {ps : List (String × NaruSem.Ty)}
      {F : List Val → Prop} {vals : List (Option String × Val)} {vs : List Val}
      (hs : headBound ρ path = false) (hr : T.resolve path = some k) (hd : T.sig k = some (.spec ps)) (hF : Ψ k = some F)
      (ha : evalArgs T Φ ρ args = some vals) (harr : arrange ps vals = some vs) :
      Sem T Φ Ψ ρ (.call sp (.var vsp path) args) (F vs)
  /-- UFCS の fn / input の呼出し `recv.m(args)` = `m(recv, args)`。 -/
  | ufcsVal {ρ : SEnv} {sp : Span} {r : Expr} {m : String} {args : List Arg} {k : String} {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
      {f : List Val → Option Val} {v : Val} {vals : List (Option String × Val)} {vs : List Val} {b : Bool}
      (hu : ufcs T ρ m = true) (hr : T.resolve [m] = some k) (hd : (T.sig k).bind DeclSig.value? = some (ps, t)) (hf : Φ k = some f)
      (hrv : eval T Φ ρ r = some v) (ha : evalArgs T Φ ρ args = some vals) (harr : arrange ps ((none, v) :: vals) = some vs)
      (hv : f vs = some (.bool b)) :
      Sem T Φ Ψ ρ (.method sp r m args) (b = true)
  /-- UFCS の spec 宣言の呼出し。 -/
  | ufcsSpec {ρ : SEnv} {sp : Span} {r : Expr} {m : String} {args : List Arg} {k : String} {ps : List (String × NaruSem.Ty)}
      {F : List Val → Prop} {v : Val} {vals : List (Option String × Val)} {vs : List Val}
      (hu : ufcs T ρ m = true) (hr : T.resolve [m] = some k) (hd : T.sig k = some (.spec ps)) (hF : Ψ k = some F)
      (hrv : eval T Φ ρ r = some v) (ha : evalArgs T Φ ρ args = some vals) (harr : arrange ps ((none, v) :: vals) = some vs) :
      Sem T Φ Ψ ρ (.method sp r m args) (F vs)
  | logic {ρ : SEnv} {sp : Span} {op : String} {k : LogicOp} {l r : Expr} {P Q : Prop}
      (hk : BinOp.ofString? op = some (.logic k)) (hl : Sem T Φ Ψ ρ l P) (hr : Sem T Φ Ψ ρ r Q) :
      Sem T Φ Ψ ρ (.binop sp op l r) (k.prop P Q)
  | eqNat {ρ : SEnv} {sp : Span} {op : String} {k : EqOp} {l r : Expr} {a b : Nat}
      (hk : BinOp.ofString? op = some (.eq k)) (hl : eval T Φ ρ l = some (.nat a)) (hr : eval T Φ ρ r = some (.nat b)) :
      Sem T Φ Ψ ρ (.binop sp op l r) (k.propNat a b)
  | eqForm {ρ : SEnv} {sp : Span} {op : String} {k : EqOp} {l r : Expr} {P Q : Prop}
      (hk : BinOp.ofString? op = some (.eq k)) (hl : Sem T Φ Ψ ρ l P) (hr : Sem T Φ Ψ ρ r Q) :
      Sem T Φ Ψ ρ (.binop sp op l r) (k.propIff P Q)
  | cmpNat {ρ : SEnv} {sp : Span} {op : String} {k : CmpOp} {l r : Expr} {a b : Nat}
      (hk : BinOp.ofString? op = some (.cmp k)) (hl : eval T Φ ρ l = some (.nat a)) (hr : eval T Φ ρ r = some (.nat b)) :
      Sem T Φ Ψ ρ (.binop sp op l r) (k.propNat a b)
  | cmpBool {ρ : SEnv} {sp : Span} {op : String} {k : CmpOp} {l r : Expr} {a b : Bool}
      (hk : BinOp.ofString? op = some (.cmp k)) (hl : eval T Φ ρ l = some (.bool a)) (hr : eval T Φ ρ r = some (.bool b)) :
      Sem T Φ Ψ ρ (.binop sp op l r) (k.evalBool a b = true)
  | not {ρ : SEnv} {sp : Span} {a : Expr} {P : Prop} (h : Sem T Φ Ψ ρ a P) : Sem T Φ Ψ ρ (.unop sp "!" a) (¬ P)
  | ite {ρ : SEnv} {sp : Span} {c t e : Expr} {C P Q : Prop} (hc : Sem T Φ Ψ ρ c C) (ht : Sem T Φ Ψ ρ t P) (he : Sem T Φ Ψ ρ e Q) :
      Sem T Φ Ψ ρ (.ite sp c t e) ((C → P) ∧ (¬ C → Q))
  | blockTail {ρ : SEnv} {sp : Span} {e : Expr} {P : Prop} (h : Sem T Φ Ψ ρ e P) : Sem T Φ Ψ ρ (.block sp [] (some e)) P
  | blockLetVal {ρ : SEnv} {sp lsp : Span} {x : String} {ty : Option Ty} {v : Expr} {rest : List Stmt} {tail : Option Expr}
      {w : Val} {Q : Prop}
      (hp : proppyS T ρ.ctx v = false) (hv : eval T Φ ρ v = some w) (hb : Sem T Φ Ψ (ρ.ext x (.val w)) (.block sp rest tail) Q) :
      Sem T Φ Ψ ρ (.block sp (.letS lsp x ty v :: rest) tail) Q
  | blockLetProp {ρ : SEnv} {sp lsp : Span} {x : String} {ty : Option Ty} {v : Expr} {rest : List Stmt} {tail : Option Expr}
      {P Q : Prop}
      (hp : proppyS T ρ.ctx v = true) (hv : Sem T Φ Ψ ρ v P) (hb : Sem T Φ Ψ (ρ.ext x (.prop P)) (.block sp rest tail) Q) :
      Sem T Φ Ψ ρ (.block sp (.letS lsp x ty v :: rest) tail) Q
  | matchSkip {ρ : SEnv} {sp : Span} {s : Expr} {p : Pat} {g : Option Expr} {b : Expr} {rest : List Arm} {v : Val} {P : Prop}
      (hs : eval T Φ ρ s = some v) (hp : matchPat p v = none) (hr : Sem T Φ Ψ ρ (.matchE sp s rest) P) :
      Sem T Φ Ψ ρ (.matchE sp s (.mk p g b :: rest)) P
  | matchHit {ρ : SEnv} {sp : Span} {s : Expr} {p : Pat} {b : Expr} {rest : List Arm} {v : Val} {bs : List (String × Val)} {P : Prop}
      (hs : eval T Φ ρ s = some v) (hp : matchPat p v = some bs) (hb : Sem T Φ Ψ (ρ.extVals bs) b P) :
      Sem T Φ Ψ ρ (.matchE sp s (.mk p none b :: rest)) P
  | matchGuard {ρ : SEnv} {sp : Span} {s : Expr} {p : Pat} {g b : Expr} {rest : List Arm} {v : Val} {bs : List (String × Val)}
      {G P R : Prop}
      (hs : eval T Φ ρ s = some v) (hp : matchPat p v = some bs) (hg : Sem T Φ Ψ (ρ.extVals bs) g G)
      (hb : Sem T Φ Ψ (ρ.extVals bs) b P) (hr : Sem T Φ Ψ ρ (.matchE sp s rest) R) :
      Sem T Φ Ψ ρ (.matchE sp s (.mk p (some g) b :: rest)) ((G → P) ∧ (¬ G → R))
  | quantNil {ρ : SEnv} {sp : Span} {q : Quant} {b : Expr} {P : Prop} (h : Sem T Φ Ψ ρ b P) : Sem T Φ Ψ ρ (.quant sp q [] b) P
  | forallCons {ρ : SEnv} {sp bsp : Span} {x : String} {ty : Ty} {t : NaruSem.Ty} {bs : List Binder} {b : Expr} {F : t.carrier → Prop}
      (ht : ty.toTy? = some t)
      (h : ∀ a : t.carrier, Sem T Φ Ψ (ρ.ext x (.val (Val.of t a))) (.quant sp .forall_ bs b) (F a)) :
      Sem T Φ Ψ ρ (.quant sp .forall_ ({ name := x, ty := some ty, span := bsp } :: bs) b) (∀ a, F a)
  | existsCons {ρ : SEnv} {sp bsp : Span} {x : String} {ty : Ty} {t : NaruSem.Ty} {bs : List Binder} {b : Expr} {F : t.carrier → Prop}
      (ht : ty.toTy? = some t)
      (h : ∀ a : t.carrier, Sem T Φ Ψ (ρ.ext x (.val (Val.of t a))) (.quant sp .exists_ bs b) (F a)) :
      Sem T Φ Ψ ρ (.quant sp .exists_ ({ name := x, ty := some ty, span := bsp } :: bs) b) (∃ a, F a)

/-! ## 宣言群 -/

/-- 対象の宣言(Surface): モジュール名・種別・名前・位置・仮引数・戻り型の注釈・本体(input は本体なし)。 -/
structure Decl where
  module : List String
  kind : DeclKind
  name : String
  span : Span
  params : List Param
  ret : Option Ty
  body : Option Expr

/-- 修飾名(モジュール名 + 単純名)。 -/
def Decl.key (d : Decl) : String := renderPath (d.module ++ [d.name])

/-- 構文解析の宣言への埋め込み(モジュール名は別に照合する)。 -/
def Decl.toAst (d : Decl) : Naru.Decl :=
  { kind := d.kind, name := d.name, span := d.span, params := (d.params.map Param.toAst).toArray, ret := d.ret.map Ty.toAst,
    body := d.body.map Expr.toAst }

/-- 宣言の署名: 仮引数の注釈がすべて Nat / Bool で、fn / input は戻り型が Nat / Bool、spec 宣言は戻り型が無い。それ以外は `none`(対象外)。 -/
def Decl.sig? (d : Decl) : Option DeclSig :=
  match paramsCtx d.params with
  | none => none
  | some ps =>
    match d.kind, d.ret with
    | .fn, some rτ => (rτ.toTy?).map (.fn ps)
    | .input, some rτ => (rτ.toTy?).map (.input ps)
    | k, none => if k.phase = .spec then some (.spec ps) else none
    | _, _ => none

/-- 宣言群: 依存順(呼出し先が前)に並べた宣言の列。 -/
abbrev Prog := List Decl

/-- 名前の解決(宣言群全体の名前で): 修飾名そのもの、または単純名(宣言の名前。コンパイル単位で一意)。 -/
def resolveIn (P : Prog) (path : List String) : Option String :=
  let s := renderPath path
  if P.any (fun d => d.key == s) then some s
  else
    match path with
    | [x] => (P.find? (fun d => d.name == x)).map Decl.key
    | _ => none

/-- 署名の表(与えた宣言だけ)。 -/
def sigsOf (P : Prog) (k : String) : Option DeclSig := (P.find? (fun d => d.key == k)).bind Decl.sig?

/-- 宣言群 `all` の名前で解決し、`seen`(それより前の宣言)の署名だけを持つ表。 -/
def tableOf (all seen : Prog) : Table := { resolve := resolveIn all, sig := sigsOf seen }

/-- 宣言 1 つの適格性(表 `T` = それより前の宣言の署名): fn は本体が戻り型の型、spec 宣言は本体が論理の位置の型、input は本体なし。 -/
def wtDecl (T : Table) (d : Decl) : Bool :=
  match d.sig?, d.body with
  | some (.fn ps t), some b => decide (wtR T (NaruSem.Call.paramSCtx ps) b = some t)
  | some (.input _ _), none => true
  | some (.spec ps), some b =>
    match wtS T (NaruSem.Call.paramSCtx ps) b with
    | some τ => τ.isForm
    | none => false
  | _, _ => false

/-- 宣言群の適格性: 前から順に、鍵も単純名も未使用で(重複なし)、本体がそれまでの署名だけで適格(呼出し先は前の宣言: 非循環)。 -/
def wtProgFrom (all : Prog) : Prog → Prog → Bool
  | _, [] => true
  | seen, d :: rest =>
    (sigsOf seen d.key).isNone && seen.all (fun e => e.name != d.name) && wtDecl (tableOf all seen) d && wtProgFrom all (seen ++ [d]) rest

def wtProg (P : Prog) : Bool := wtProgFrom P [] P

/-- 宣言群の意味: runtime の呼出し先(fn の意味と input の解釈)と spec 宣言の意味。署名は表が持つ。 -/
structure Interp where
  Φ : NaruSem.Call.FEnv
  Ψ : NaruSem.Call.PEnv

/-- 宣言 1 つの意味を足す(本体はそれより前の宣言の表 `tableOf all seen` と環境で読む)。 -/
def Interp.step (all seen : Prog) (m : Interp) (d : Decl) : Interp :=
  let T := tableOf all seen
  match d.sig?, d.body with
  | some (.fn ps _), some b =>
    { m with Φ := m.Φ.ext d.key fun vs =>
        match NaruSem.Call.bindParams ps vs with
        | some ρ => eval T m.Φ (NaruSem.Call.Env.toSEnv ρ) b
        | none => none }
  | some (.spec ps), some b =>
    { m with Ψ := m.Ψ.ext d.key fun vs =>
        ∃ ρ, NaruSem.Call.bindParams ps vs = some ρ ∧ ∃ P, Sem T m.Φ m.Ψ (NaruSem.Call.Env.toSEnv ρ) b P ∧ P }
  | _, _ => m

def interpFrom (all : Prog) : Prog → Interp → Prog → Interp
  | _, m, [] => m
  | seen, m, d :: rest => interpFrom all (seen ++ [d]) (Interp.step all seen m d) rest

/-- 宣言群の意味(input の解釈 `I` の下で)。 -/
def interp (I : NaruSem.Call.FEnv) (P : Prog) : Interp := interpFrom P [] { Φ := I, Ψ := NaruSem.Call.PEnv.empty } P

/-- input の解釈が宣言群の input の署名を守る。 -/
def RespectsInputs (I : NaruSem.Call.FEnv) (P : Prog) : Prop :=
  ∀ d ∈ P, ∀ ps t, d.sig? = some (.input ps t) →
    ∃ f, I d.key = some f ∧ ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) → ∃ v, f vs = some v ∧ v.ty = t

end NaruSem.Surf.Call
