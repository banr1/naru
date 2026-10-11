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
/-! ## 引数の並べ替えと評価の合成

子式の評価が対応すれば、名前を保つ引数の写像と `arrange` の可換性から
呼出し先に届く値の対応を導く。任意の関数環境を扱い、行き詰まりも保持する。
これは呼出しの局所的な合成であり、全 Surface 式の保存の代用ではない。
-/

theorem allSome_some {α : Type} (xs : List α) :
    allSome (xs.map some) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, allSome, ih, Option.map_some]

/-- Core の引数評価は各式の部分評価の列を成功値の列にまとめる。 -/
theorem evalArgs_allSome (Φ : NaruSem.Call.FEnv) (ρ : Env) (cs : List Core.Expr) :
    NaruSem.Call.evalArgs Φ ρ cs = allSome (cs.map (NaruSem.Call.eval Φ ρ)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [NaruSem.Call.evalArgs_cons, List.map_cons, ih]
    cases NaruSem.Call.eval Φ ρ c with
    | none => rfl
    | some v =>
      simp only [allSome]
      cases allSome (cs.map (NaruSem.Call.eval Φ ρ)) <;> rfl

/-- 同じ名前を持つ各実引数の成功評価は、仮引数順へ並べても対応する。 -/
theorem arrange_eval {Φ : NaruSem.Call.FEnv} {ρ : Env}
    {ps : List (String × NaruSem.Ty)} {args : List (Option String × Core.Expr)}
    {vals : List (Option String × Val)} {cs : List Core.Expr} {vs : List Val}
    (he : args.map (mapArg (NaruSem.Call.eval Φ ρ)) = vals.map (mapArg some))
    (hc : arrange ps args = some cs) (hv : arrange ps vals = some vs) :
    NaruSem.Call.evalArgs Φ ρ cs = some vs := by
  have h := congrArg (arrange ps) he
  rw [arrange_map, arrange_map, hc, hv] at h
  simp only [Option.map_some, Option.some.injEq] at h
  rw [evalArgs_allSome, h, allSome_some]

theorem wtArgs_of_map {Δ : NaruSem.Call.SigEnv} {Γ : Ctx} {cs : List Core.Expr} {ts : List NaruSem.Ty}
    (h : cs.map (NaruSem.Call.wtR Δ Γ) = ts.map some) :
    NaruSem.Call.wtArgs Δ Γ cs ts = true := by
  induction cs generalizing ts with
  | nil => cases ts <;> simp_all [NaruSem.Call.wtArgs_nil]
  | cons c cs ih =>
    cases ts with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at h
    | cons t ts =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [NaruSem.Call.wtArgs_cons, h.1, ih h.2]
      simp

/-- 引数ごとの型とその名前が対応すれば、仮引数順の Core 引数も型が合う。 -/
theorem arrange_wt {Δ : NaruSem.Call.SigEnv} {Γ : Ctx}
    {ps : List (String × NaruSem.Ty)} {args : List (Option String × Core.Expr)}
    {tys : List (Option String × NaruSem.Ty)} {cs : List Core.Expr}
    (ht : args.map (mapArg (NaruSem.Call.wtR Δ Γ)) = tys.map (mapArg some))
    (hc : arrange ps args = some cs) (ha : arrange ps tys = some (ps.map (·.2))) :
    NaruSem.Call.wtArgs Δ Γ cs (ps.map (·.2)) = true := by
  have h := congrArg (arrange ps) ht
  rw [arrange_map, arrange_map, hc, ha] at h
  simp only [Option.map_some, Option.some.injEq] at h
  exact wtArgs_of_map h

/-- 解決した値の署名と引数の型対応から Core 呼出しの適格性を導く。 -/
theorem lowerCall_wt {T : Table} {k : String} {Γ : Ctx}
    {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
    {args : List (Option String × Core.Expr)} {tys : List (Option String × NaruSem.Ty)}
    {cs : List Core.Expr}
    (hs : (T.sig k).bind DeclSig.value? = some (ps, t))
    (hc : arrange ps args = some cs)
    (ht : args.map (mapArg (NaruSem.Call.wtR T.Δ Γ)) = tys.map (mapArg some))
    (ha : arrange ps tys = some (ps.map (·.2))) :
    NaruSem.Call.wtR T.Δ Γ (.call k cs) = some t := by
  simp only [NaruSem.Call.wtR, valueSig?_Δ hs, arrange_wt ht hc ha, ite_true]

/-- 呼出し先・署名・実引数の対応から、独立 lowering の呼出し評価が一致する。
関数が無い、または関数自身が `none` を返す場合も同じ結果となる。 -/
theorem lowerCall_eval {T : Table} {path : List String} {k : String}
    {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
    {Φ : NaruSem.Call.FEnv} {ρ : Env}
    {args : List (Option String × Core.Expr)} {vals : List (Option String × Val)}
    {cs : List Core.Expr} {vs : List Val}
    (hr : T.resolve path = some k) (hs : (T.sig k).bind DeclSig.value? = some (ps, t))
    (hc : arrange ps args = some cs)
    (he : args.map (mapArg (NaruSem.Call.eval Φ ρ)) = vals.map (mapArg some))
    (hv : arrange ps vals = some vs) :
    lowerCall T path args = some (.call k cs) ∧
      NaruSem.Call.eval Φ ρ (.call k cs) = callVal T Φ path vals := by
  refine ⟨lowerCall_eq hr hs hc, ?_⟩
  have ha := arrange_eval he hc hv
  simp only [NaruSem.Call.eval, ha, callVal, hr, hs]
  cases Φ k <;> simp only [hv] <;> rfl

/-- 子引数の対応を実際の Surface 呼出しへ合成する。局所名による隠蔽も検査する。 -/
theorem lower_call_eval {T : Table} {Γ : SCtx} {ρ : SEnv} {Φ : NaruSem.Call.FEnv}
    {sp sf : Span} {path : List String} {args : List Arg} {k : String}
    {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
    {cargs : List (Option String × Core.Expr)} {vals : List (Option String × Val)}
    {cs : List Core.Expr} {vs : List Val}
    (hg : headBound Γ path = false) (hρ : headBound ρ path = false)
    (hr : T.resolve path = some k) (hs : (T.sig k).bind DeclSig.value? = some (ps, t))
    (hl : lowerArgs T Γ args = some cargs) (hc : arrange ps cargs = some cs)
    (he : cargs.map (mapArg (NaruSem.Call.eval Φ ρ.vals)) = vals.map (mapArg some))
    (ha : evalArgs T Φ ρ args = some vals) (hv : arrange ps vals = some vs) :
    lower T Γ (.call sp (.var sf path) args) = some (.call k cs) ∧
      eval T Φ ρ (.call sp (.var sf path) args) = NaruSem.Call.eval Φ ρ.vals (.call k cs) := by
  obtain ⟨hlc, hec⟩ := lowerCall_eval hr hs hc he hv
  constructor
  · rw [lower.eq_def]
    simp only [hg, Bool.false_eq_true, ite_false, hl, Option.bind_some, hlc]
  · rw [eval.eq_def]
    simp only [hρ, Bool.false_eq_true, ite_false, ha]
    exact hec.symm

/-- UFCS は受け手を先頭の位置引数にして同じ呼出し合成を使う。 -/
theorem lower_ufcs_eval {T : Table} {Γ : SCtx} {ρ : SEnv} {Φ : NaruSem.Call.FEnv}
    {sp : Span} {r : Expr} {m k : String} {args : List Arg}
    {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
    {cr : Core.Expr} {rv : Val}
    {cargs : List (Option String × Core.Expr)} {vals : List (Option String × Val)}
    {cs : List Core.Expr} {vs : List Val}
    (hg : ufcs T Γ m = true) (hρ : ufcs T ρ m = true)
    (hr : T.resolve [m] = some k) (hs : (T.sig k).bind DeclSig.value? = some (ps, t))
    (hlr : lower T Γ r = some cr) (hl : lowerArgs T Γ args = some cargs)
    (hc : arrange ps ((none, cr) :: cargs) = some cs)
    (her : NaruSem.Call.eval Φ ρ.vals cr = some rv)
    (he : cargs.map (mapArg (NaruSem.Call.eval Φ ρ.vals)) = vals.map (mapArg some))
    (har : eval T Φ ρ r = some rv) (ha : evalArgs T Φ ρ args = some vals)
    (hv : arrange ps ((none, rv) :: vals) = some vs) :
    lower T Γ (.method sp r m args) = some (.call k cs) ∧
      eval T Φ ρ (.method sp r m args) = NaruSem.Call.eval Φ ρ.vals (.call k cs) := by
  have he' : ((none, cr) :: cargs).map (mapArg (NaruSem.Call.eval Φ ρ.vals)) =
      ((none, rv) :: vals).map (mapArg some) := by
    simp only [List.map_cons, mapArg, her, he]
  obtain ⟨hlc, hec⟩ := lowerCall_eval hr hs hc he' hv
  constructor
  · rw [lower.eq_def]
    simp only [hg, ite_true, hlr, hl, hlc]
  · rw [eval.eq_def]
    simp only [hρ, ite_true, har, ha]
    exact hec.symm


/-! ## ブロックの束縛列の合成

呼出しを含む Core の評価・型付けで束縛列を読む。子式と後続列の対応は
明示した合成前提であり、全式の帰納保存を仮定せずに証明したとはしない。
-/

/-- 呼出しの署名を保持した Core 束縛列の型付け。 -/
def wtBinds (Δ : NaruSem.Call.SigEnv) (Γ : Ctx) :
    List (String × TyV × Core.Expr) → Option Ctx
  | [] => some Γ
  | (x, ty, v) :: rest =>
    match NaruSem.Call.wtR Δ Γ v, TyV.toTy? ty with
    | some tv, some ta => if tv = ta then wtBinds Δ (Γ.ext x tv) rest else none
    | _, _ => none

/-- 同じ関数・input環境を使い、前から順に束縛する。失敗は後続へ進めない。 -/
def evalBinds (Φ : NaruSem.Call.FEnv) (ρ : Env) :
    List (String × TyV × Core.Expr) → Option Env
  | [] => some ρ
  | (x, _, v) :: rest =>
    match NaruSem.Call.eval Φ ρ v with
    | some w => evalBinds Φ (ρ.ext x w) rest
    | none => none

/-- 型付けされた束縛列と末尾式から、入れ子のletの適格性を合成する。 -/
theorem wtR_mkLets {Δ : NaruSem.Call.SigEnv} {Γ Γ' : Ctx}
    {binds : List (String × TyV × Core.Expr)} (hb : wtBinds Δ Γ binds = some Γ')
    {c : Core.Expr} {t : NaruSem.Ty} (hc : NaruSem.Call.wtR Δ Γ' c = some t) :
    NaruSem.Call.wtR Δ Γ (Surf.mkLets binds c) = some t := by
  induction binds generalizing Γ with
  | nil =>
    simp only [wtBinds, Option.some.injEq] at hb
    subst hb
    simpa using hc
  | cons b rest ih =>
    obtain ⟨x, ty, v⟩ := b
    simp only [wtBinds] at hb
    cases hv : NaruSem.Call.wtR Δ Γ v with
    | none => simp [hv] at hb
    | some tv =>
      cases hty : TyV.toTy? ty with
      | none => simp [hv, hty] at hb
      | some ta =>
        simp only [hv, hty] at hb
        split at hb
        · rename_i heq
          subst heq
          simp only [Surf.mkLets_cons, NaruSem.Call.wtR, hv, hty, ite_true]
          exact ih hb
        · cases hb

/-- 任意の束縛列・環境についてCoreの入れ子のletと順次評価が一致する。 -/
theorem eval_mkLets (Φ : NaruSem.Call.FEnv) (ρ : Env)
    (binds : List (String × TyV × Core.Expr)) (c : Core.Expr) :
    NaruSem.Call.eval Φ ρ (Surf.mkLets binds c) =
      match evalBinds Φ ρ binds with
      | some ρ' => NaruSem.Call.eval Φ ρ' c
      | none => none := by
  induction binds generalizing ρ with
  | nil => simp [evalBinds]
  | cons b rest ih =>
    obtain ⟨x, ty, v⟩ := b
    simp only [Surf.mkLets_cons, NaruSem.Call.eval, evalBinds]
    cases NaruSem.Call.eval Φ ρ v <;> simp [ih]

/-- 子式と後続束縛列の対応をlet一つへ合成する。失敗も両側で一致する。 -/
theorem lowerStmts_cons_eval {T : Table} {Φ : NaruSem.Call.FEnv} {ρ : SEnv}
    {sp : Span} {x : String} {ty : Option Ty} {v : Expr} {cv : Core.Expr}
    {cty : TyV} {rest : List Stmt} {binds : List (String × TyV × Core.Expr)}
    (hv : eval T Φ ρ v = NaruSem.Call.eval Φ ρ.vals cv)
    (hb : ∀ w, (evalStmts T Φ (ρ.ext x (.val w)) rest).map SEnv.vals =
      evalBinds Φ (ρ.vals.ext x w) binds) :
    (evalStmts T Φ ρ (.letS sp x ty v :: rest)).map SEnv.vals =
      evalBinds Φ ρ.vals ((x, cty, cv) :: binds) := by
  rw [evalStmts_cons, hv]
  simp only [evalBinds]
  cases NaruSem.Call.eval Φ ρ.vals cv with
  | none => rfl
  | some w => exact hb w

/-- 束縛列と末尾式の対応から、独立loweringのブロック評価を合成する。 -/
theorem lower_block_eval {T : Table} {Γ Γ' : SCtx} {Φ : NaruSem.Call.FEnv}
    {sp : Span} {stmts : List Stmt} {e : Expr}
    {binds : List (String × TyV × Core.Expr)} {c : Core.Expr}
    (hΓ : wtStmtsR T Γ stmts = some Γ')
    (hl : lowerStmts T Γ stmts = some binds) (hc : lower T Γ' e = some c)
    (hb : ∀ ρ, (evalStmts T Φ ρ stmts).map SEnv.vals = evalBinds Φ ρ.vals binds)
    (he : ∀ ρ, eval T Φ ρ e = NaruSem.Call.eval Φ ρ.vals c) :
    lower T Γ (.block sp stmts (some e)) = some (Surf.mkLets binds c) ∧
      ∀ ρ, eval T Φ ρ (.block sp stmts (some e)) =
        NaruSem.Call.eval Φ ρ.vals (Surf.mkLets binds c) := by
  constructor
  · rw [lower.eq_def]
    simp only [hΓ, hl, hc, Option.map_some]
  · intro ρ
    rw [eval.eq_def, eval_mkLets, ← hb ρ]
    simp only
    cases evalStmts T Φ ρ stmts with
    | none => rfl
    | some ρ' => exact he ρ'

end NaruSem.Surf.Call
