import NaruSem.SurfaceCallTotality
import NaruSem.Lower

/-!
# 呼出しを含む runtime の Surface AST → Core の対応

`lower` は frontend から独立した構造的変換。宣言表が名前と署名を決め、
位置・名前付き引数を仮引数順に並べ、UFCS の受け手を先頭の位置引数にする。
局所の命題束縛も大域名を隠すため文脈は `SCtx` のまま使う。
実際の AST / Core の一致は `naru_test semantics` が現在の17 fnで検査する。
これは変換の一致の段階であり、任意の式・環境の意味保存定理、宣言群の意味の合成、
spec の変換と双方向同値はまだ備えない。独立意味論の定義は変更しない。
-/

namespace NaruSem.Surf.Call
open Naru

/-- 大域名と値の署名を解決し、実引数を仮引数順にした Core の呼出し。 -/
def lowerCall (T : Table) (path : List String)
    (args : List (Option String × Core.Expr)) : Option Core.Expr :=
  match T.resolve path with
  | some k =>
    match (T.sig k).bind DeclSig.value? with
    | some (ps, _) => (arrange ps args).map (Core.Expr.call k)
    | none => none
  | none => none

/-- 呼出し先・署名・引数列の各対応証拠から Core の呼出しの形が決まる。 -/
theorem lowerCall_eq {T : Table} {path : List String} {k : String}
    {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
    {args : List (Option String × Core.Expr)} {cs : List Core.Expr}
    (hr : T.resolve path = some k) (hs : (T.sig k).bind DeclSig.value? = some (ps, t))
    (ha : arrange ps args = some cs) : lowerCall T path args = some (.call k cs) := by
  simp only [lowerCall, hr, hs, ha, Option.map_some]

mutual

/-- runtime の独立 lowering。型の注釈は独立した `wtR` から補う。 -/
def lower (T : Table) (Γ : SCtx) : Expr → Option Core.Expr
  | .lit _ (.nat n) => some (.lit (.nat n) .nat)
  | .lit _ (.bool b) => some (.lit (.bool b) .bool)
  | .var _ [x] => some (.var x)
  | .call _ (.var _ path) args =>
    if headBound Γ path then none
    else (lowerArgs T Γ args).bind (lowerCall T path)
  | .binop _ op l r =>
    match wtR T Γ l, lower T Γ l, lower T Γ r with
    | some tl, some cl, some cr => some (.binop op cl cr tl.toTyV)
    | _, _, _ => none
  | .unop _ op a =>
    if op = "!" then (lower T Γ a).map (Core.Expr.unop "!") else none
  | .method _ r m args =>
    if ufcs T Γ m then
      match lower T Γ r, lowerArgs T Γ args with
      | some cr, some cs => lowerCall T [m] ((none, cr) :: cs)
      | _, _ => none
    else
      match args with
      | [.pos a] =>
        match NatMethod.ofString? m, lower T Γ r, lower T Γ a with
        | some _, some cr, some ca => some (.method "Nat" m cr [ca] .nat)
        | _, _, _ => none
      | _ => none
  | .ite _ c t e =>
    match lower T Γ c, lower T Γ t, lower T Γ e with
    | some cc, some ct, some ce => some (.ite cc ct ce)
    | _, _, _ => none
  | .matchE _ s arms =>
    match wtR T Γ s, lower T Γ s with
    | some ts, some cs => (lowerArms T Γ ts arms).map (Core.Expr.match_ cs ts.toTyV)
    | _, _ => none
  | .block _ stmts (some e) =>
    match wtStmtsR T Γ stmts, lowerStmts T Γ stmts with
    | some Γ', some binds => (lower T Γ' e).map (Surf.mkLets binds)
    | _, _ => none
  | _ => none

/-- 構文解析順を保つ引数の変換。並べ替えは `lowerCall` で一度だけ行う。 -/
def lowerArgs (T : Table) (Γ : SCtx) : List Arg → Option (List (Option String × Core.Expr))
  | [] => some []
  | .pos e :: rest =>
    match lower T Γ e, lowerArgs T Γ rest with
    | some c, some cs => some ((none, c) :: cs)
    | _, _ => none
  | .named n e :: rest =>
    match lower T Γ e, lowerArgs T Γ rest with
    | some c, some cs => some ((some n, c) :: cs)
    | _, _ => none

def lowerStmts (T : Table) (Γ : SCtx) : List Stmt → Option (List (String × TyV × Core.Expr))
  | [] => some []
  | .letS _ x _ v :: rest =>
    match wtR T Γ v, lower T Γ v with
    | some tv, some cv =>
      (lowerStmts T (Γ.ext x (.val tv)) rest).map ((x, tv.toTyV, cv) :: ·)
    | _, _ => none

def lowerArms (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) : List Arm → Option (List Core.Arm)
  | [] => some []
  | arm :: rest =>
    match lowerArm T Γ ts arm, lowerArms T Γ ts rest with
    | some ca, some cas => some (ca :: cas)
    | _, _ => none

def lowerArm (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) : Arm → Option Core.Arm
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none => (lower T (Γ.extVals bs) b).map (Core.Arm.mk (Surf.lowerPat p) none)
      | some g =>
        match lower T (Γ.extVals bs) g, lower T (Γ.extVals bs) b with
        | some cg, some cb => some (.mk (Surf.lowerPat p) (some cg) cb)
        | _, _ => none

end
end NaruSem.Surf.Call
