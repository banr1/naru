import NaruSem.SurfaceCallLower
import NaruSem.LowerSpec

/-!
# 呼出しを含む spec の独立 lowering

論理の位置は `lowerS`、値の位置と実引数は runtime の `lower` / `lowerArgs`。
名前付き引数・UFCS を署名の仮引数順へ並べ、命題の let・量化・ガードを保つ。
現在の spec AST / 実Coreの一致を kernel 検査する。一般の型保存・全域性は
`SurfaceCallLowerSpecSound` で証明する。双方向同値、宣言群からの環境対応、
Surfaceから実生成Leanまでの合成はまだ証明しない。
-/

namespace NaruSem.Surf.Call
open Naru

/-- spec の位置では値と命題の両署名を呼べる。署名の無い呼出しは拒否する。 -/
def lowerCallS (T : Table) (path : List String)
    (args : List (Option String × Core.Expr)) : Option Core.Expr :=
  match T.resolve path with
  | some k =>
    match T.sig k with
    | some s => (arrange s.params args).map (Core.Expr.call k)
    | none => none
  | none => none

/-- どの phase でも、解決・署名・並べ替えが Core 呼出しの形を決める。 -/
theorem lowerCallS_eq {T : Table} {path : List String} {k : String}
    {s : DeclSig} {args : List (Option String × Core.Expr)} {cs : List Core.Expr}
    (hr : T.resolve path = some k) (hs : T.sig k = some s)
    (ha : arrange s.params args = some cs) : lowerCallS T path args = some (.call k cs) := by
  simp only [lowerCallS, hr, hs, ha, Option.map_some]

mutual

/-- spec の Surface AST → Core。論理の位置は `wtS` に導かれ、値を要求する位置は runtime の変換 `lower`。対象外の構文は `none`。 -/
def lowerS (T : Table) (Γ : SCtx) : Expr → Option Core.Expr
  | .lit _ (.nat n) => some (.lit (.nat n) .nat)
  | .lit _ (.bool b) => some (.lit (.bool b) .bool)
  | .var _ [x] => some (.var x)
  | .call _ (.var _ path) args =>
    if headBound Γ path then none
    else (lowerArgs T Γ args).bind (lowerCallS T path)
  | .ite _ c t e =>
    match lowerS T Γ c, lowerS T Γ t, lowerS T Γ e with
    | some cc, some ct, some ce => some (.ite cc ct ce)
    | _, _, _ => none
  | .binop _ op l r =>
    match BinOp.ofString? op with
    | some (.logic _) =>
      match lowerS T Γ l, lowerS T Γ r with
      | some cl, some cr => some (.binop op cl cr .bool)
      | _, _ => none
    | some (.eq _) =>
      -- 両辺が Nat の値なら値の等値(注釈 `.nat`)、そうでなければ論理の位置(注釈 `.bool`: Bool の値の等値か命題の同値)
      if wtR T Γ l = some .nat ∧ wtR T Γ r = some .nat then
        match lower T Γ l, lower T Γ r with
        | some cl, some cr => some (.binop op cl cr .nat)
        | _, _ => none
      else
        match lowerS T Γ l, lowerS T Γ r with
        | some cl, some cr => some (.binop op cl cr .bool)
        | _, _ => none
    | some (.cmp _) =>
      match wtR T Γ l, lower T Γ l, lower T Γ r with
      | some tl, some cl, some cr => some (.binop op cl cr tl.toTyV)
      | _, _, _ => none
    | some (.arith _) =>
      match lower T Γ l, lower T Γ r with
      | some cl, some cr => some (.binop op cl cr .nat)
      | _, _ => none
    | none => none
  | .unop _ op a =>
    if op = "!" then
      match lowerS T Γ a with
      | some ca => some (.unop "!" ca)
      | none => none
    else none
  | .method _ r m args =>
    if ufcs T Γ m then
      match lower T Γ r, lowerArgs T Γ args with
      | some cr, some cs => lowerCallS T [m] ((none, cr) :: cs)
      | _, _ => none
    else
      match args with
      | [.pos a] =>
        match NatMethod.ofString? m, lower T Γ r, lower T Γ a with
        | some _, some cr, some ca => some (.method "Nat" m cr [ca] .nat)
        | _, _, _ => none
      | _ => none
  | .matchE _ s arms =>
    match wtR T Γ s with
    | some ts =>
      match lower T Γ s, lowerArmsS T Γ ts arms with
      | some cs, some cas => some (.match_ cs ts.toTyV cas)
      | _, _ => none
    | none => none
  | .block _ stmts (some e) =>
    match wtStmtsS T Γ stmts, lowerStmtsS T Γ stmts with
    | some Γ', some binds =>
      match lowerS T Γ' e with
      | some c => some (Surf.mkLets binds c)
      | none => none
    | _, _ => none
  | .quant _ q bs b =>
    match SCtx.extBinders Γ bs, Surf.lowerBinders bs with
    | some Γ', some cbs =>
      match lowerS T Γ' b with
      | some cb => some (.quant q cbs cb)
      | none => none
    | _, _ => none
  | _ => none

/-- ブロックの `let` の列(spec)→ 束縛(名前・型・値)の列: 値が命題(`proppyS`)なら `lowerS` で注釈 `.bool`、そうでなければ `lower` で値の型。 -/
def lowerStmtsS (T : Table) (Γ : SCtx) : List Stmt → Option (List (String × TyV × Core.Expr))
  | [] => some []
  | .letS _ x _ v :: rest =>
    if proppyS T Γ v then
      match lowerS T Γ v with
      | some cv =>
        match lowerStmtsS T (Γ.ext x .prop) rest with
        | some binds => some ((x, .bool, cv) :: binds)
        | none => none
      | none => none
    else
      match wtR T Γ v, lower T Γ v with
      | some tv, some cv =>
        match lowerStmtsS T (Γ.ext x (.val tv)) rest with
        | some binds => some ((x, tv.toTyV, cv) :: binds)
        | none => none
      | _, _ => none

def lowerArmsS (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) : List Arm → Option (List Core.Arm)
  | [] => some []
  | arm :: rest =>
    match lowerArmS T Γ ts arm, lowerArmsS T Γ ts rest with
    | some ca, some cas => some (ca :: cas)
    | _, _ => none

def lowerArmS (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) : Arm → Option Core.Arm
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none =>
        match lowerS T (Γ.extVals bs) b with
        | some cb => some (.mk (Surf.lowerPat p) none cb)
        | none => none
      | some g =>
        match lowerS T (Γ.extVals bs) g, lowerS T (Γ.extVals bs) b with
        | some cg, some cb => some (.mk (Surf.lowerPat p) (some cg) cb)
        | _, _ => none

end

/-! ## 呼出しの局所合成

引数ごとの型・評価の対応を明示的に要求し、仮引数順に合成する。
全 spec 式からこれらの前提を導く一般の帰納保存はまだ含めない。
-/

/-- spec 署名と引数型の対応から Core 呼出しの命題型を導く。 -/
theorem lowerCallS_spec_wt {T : Table} {k : String} {Γ : SCtx}
    {ps : List (String × NaruSem.Ty)}
    {args : List (Option String × Core.Expr)} {tys : List (Option String × NaruSem.Ty)}
    {cs : List Core.Expr}
    (hs : T.sig k = some (.spec ps)) (hc : arrange ps args = some cs)
    (ht : args.map (mapArg (NaruSem.Call.wtR T.Δ Γ.vals)) = tys.map (mapArg some))
    (ha : arrange ps tys = some (ps.map (·.2))) :
    NaruSem.Call.wtS T.Δ Γ (.call k cs) = some .prop := by
  have hargs := arrange_wt ht hc ha
  simp only [NaruSem.Call.wtS, Table.Δ, hs, Option.map_some, DeclSig.toSig, hargs, ite_true]

/-- 同じ spec 解釈と引数評価の対応から、Core の呼出しの意味を合成する。 -/
theorem lowerCallS_spec_Sem {T : Table} {k : String}
    {ps : List (String × NaruSem.Ty)} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv} {ρ : SEnv}
    {args : List (Option String × Core.Expr)} {vals : List (Option String × Val)}
    {cs : List Core.Expr} {vs : List Val} {F : List Val → Prop}
    (hs : T.sig k = some (.spec ps)) (hc : arrange ps args = some cs)
    (he : args.map (mapArg (NaruSem.Call.eval Φ ρ.vals)) = vals.map (mapArg some))
    (hv : arrange ps vals = some vs) (hF : Ψ k = some F) :
    NaruSem.Call.Sem T.Δ Φ Ψ ρ (.call k cs) (F vs) := by
  apply NaruSem.Call.Sem.callSpec (vs := vs) (F := F)
  · simp only [NaruSem.Call.isSpecKey, specSig?_Δ hs, Option.isSome_some]
  · exact hF
  · exact arrange_eval he hc hv

/-- Bool 値を true である命題へ写す境界を、値の呼出しでも保つ。 -/
theorem lowerCallS_value_Sem {T : Table} {k : String}
    {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
    {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv} {ρ : SEnv}
    {args : List (Option String × Core.Expr)} {vals : List (Option String × Val)}
    {cs : List Core.Expr} {vs : List Val} {f : List Val → Option Val} {b : Bool}
    (hs : (T.sig k).bind DeclSig.value? = some (ps, t)) (hc : arrange ps args = some cs)
    (he : args.map (mapArg (NaruSem.Call.eval Φ ρ.vals)) = vals.map (mapArg some))
    (hv : arrange ps vals = some vs) (hf : Φ k = some f) (hb : f vs = some (.bool b)) :
    NaruSem.Call.Sem T.Δ Φ Ψ ρ (.call k cs) (b = true) := by
  apply NaruSem.Call.Sem.callVal (vs := vs) (f := f)
  · simp only [NaruSem.Call.isValueKey, valueSig?_Δ hs, Option.isSome_some]
  · exact hf
  · exact arrange_eval he hc hv
  · exact hb

end NaruSem.Surf.Call
