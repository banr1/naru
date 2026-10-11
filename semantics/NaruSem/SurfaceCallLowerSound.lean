import NaruSem.SurfaceCallLower

/-!
# 呼出しを含む runtime lowering の全域性・適格性・評価保存

Surface の型付けの 5-way 相互帰納法により、適格な runtime 式、その
引数列、let 列、腕列、腕の独立 lowering が存在し、Core の型付けを保つ。
後半では同じ帰納法から、整形環境の下の runtime 評価保存を証明する。
関数環境は Surface と Core で共通であり、宣言表の署名を守ることを要求する。
-/

namespace NaruSem.Surf.Call
open Naru

private theorem vals_ext (Γ : SCtx) (x : String) (t : NaruSem.Ty) :
    (Γ.ext x (.val t)).vals = Γ.vals.ext x t := by
  funext y
  by_cases h : y = x <;> simp [SCtx.vals, SCtx.ext, Ctx.ext, h]

private theorem vals_extVals (Γ : SCtx) (bs : List (String × NaruSem.Ty)) :
    (Γ.extVals bs).vals = Γ.vals.extPat bs := by
  induction bs generalizing Γ with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨x, t⟩ := b
    change ((Γ.ext x (.val t)).extVals rest).vals =
      (Γ.vals.ext x t).extPat rest
    rw [ih, vals_ext]

/-- 型のついた名前保持付き実引数を並べると、Core 引数列も存在する。 -/
theorem arrange_core_total {Δ : NaruSem.Call.SigEnv} {Γ : Ctx}
    {ps : List (String × NaruSem.Ty)} {args : List (Option String × Core.Expr)}
    {tys : List (Option String × NaruSem.Ty)}
    (ht : args.map (mapArg (NaruSem.Call.wtR Δ Γ)) = tys.map (mapArg some))
    (ha : arrange ps tys = some (ps.map (·.2))) :
    ∃ cs, arrange ps args = some cs ∧
      NaruSem.Call.wtArgs Δ Γ cs (ps.map (·.2)) = true := by
  have h := congrArg (arrange ps) ht
  rw [arrange_map, arrange_map, ha] at h
  cases hc : arrange ps args with
  | none => rw [hc] at h; cases h
  | some cs => exact ⟨cs, rfl, arrange_wt ht hc ha⟩

/-- 呼出し先を解決できる適格な型列と、各子引数の型保存から呼出しを合成する。 -/
private theorem lowerCall_typed {T : Table} {Γ : SCtx}
    {path : List String} {tys : List (Option String × NaruSem.Ty)}
    {args : List (Option String × Core.Expr)} {t : NaruSem.Ty}
    (ht : args.map (mapArg (NaruSem.Call.wtR T.Δ Γ.vals)) = tys.map (mapArg some))
    (h : callTy T path tys = some t) :
    ∃ c, lowerCall T path args = some c ∧ NaruSem.Call.wtR T.Δ Γ.vals c = some t := by
  simp only [callTy] at h
  cases hr : T.resolve path with
  | none => simp [hr] at h
  | some k =>
    simp only [hr] at h
    cases hs : (T.sig k).bind DeclSig.value? with
    | none => simp [hs] at h
    | some pt =>
      obtain ⟨ps, t₀⟩ := pt
      simp only [hs] at h
      split at h
      · rename_i ha
        cases h
        obtain ⟨cs, hc, _⟩ := arrange_core_total ht ha
        exact ⟨.call k cs, lowerCall_eq hr hs hc, lowerCall_wt hs hc ht ha⟩
      · cases h

/-- 式・let列・腕列・腕・実引数の5つの lowering は、Surface の適格性を保つ。 -/
theorem lower_typed_all (T : Table) :
    (∀ (Γ : SCtx) (e : Expr), ∀ t, wtR T Γ e = some t →
      ∃ c, lower T Γ e = some c ∧ NaruSem.Call.wtR T.Δ Γ.vals c = some t) ∧
    (∀ (Γ : SCtx) (stmts : List Stmt), ∀ Γ', wtStmtsR T Γ stmts = some Γ' →
      ∃ binds, lowerStmts T Γ stmts = some binds ∧ wtBinds T.Δ Γ.vals binds = some Γ'.vals) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arms : List Arm), ∀ t,
      wtArmsR T Γ ts arms = some t → ∃ cas, lowerArms T Γ ts arms = some cas ∧
        NaruSem.Call.wtArmsR T.Δ Γ.vals ts cas = some t) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arm : Arm), ∀ t,
      wtArmR T Γ ts arm = some t → ∃ ca, lowerArm T Γ ts arm = some ca ∧
        NaruSem.Call.wtArmR T.Δ Γ.vals ts ca = some t) ∧
    (∀ (Γ : SCtx) (args : List Arg), ∀ tys, wtArgs T Γ args = some tys →
      ∃ cs, lowerArgs T Γ args = some cs ∧
        cs.map (mapArg (NaruSem.Call.wtR T.Δ Γ.vals)) = tys.map (mapArg some)) := by
  apply wtR.mutual_induct T
  · intro Γ _ n t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨_, rfl, rfl⟩
  · intro Γ _ b t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨_, rfl, rfl⟩
  · intro Γ _ x t hx t' ht
    simp only [wtR, hx, Option.some.injEq] at ht
    subst ht
    exact ⟨.var x, rfl, by simp [NaruSem.Call.wtR, SCtx.vals, hx]⟩
  · intro Γ _ x hno t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht
         · rename_i t' hx
           exact (hno t' hx).elim
         · cases ht)
  · intro Γ _ _ path args hb t ht
    simp [wtR, hb] at ht
  · intro Γ _ _ path args hnb tys hargs ih5 t ht
    simp only [Bool.not_eq_true] at hnb
    simp only [wtR, hnb, Bool.false_eq_true, ite_false, hargs] at ht
    obtain ⟨cs, hcs, hwcs⟩ := ih5 tys hargs
    obtain ⟨c, hc, hw⟩ := lowerCall_typed hwcs ht
    refine ⟨c, ?_, hw⟩
    rw [lower.eq_def]
    simp [hnb, hcs, hc]
  · intro Γ _ _ path args hnb hargs _ t ht
    simp only [Bool.not_eq_true] at hnb
    simp [wtR, hnb, hargs] at ht
  · intro Γ _ op l r k tl tr hr hl hk ihl ihr t ht
    simp only [wtR, hk, hl, hr] at ht
    obtain ⟨cl, hcl, hwl⟩ := ihl tl hl
    obtain ⟨cr, hcr, hwr⟩ := ihr tr hr
    refine ⟨.binop op cl cr tl.toTyV, by simp [lower, hl, hcl, hcr], ?_⟩
    simp only [NaruSem.Call.wtR, hk, hwl, hwr, TyV.toTy?_toTyV]
    exact Surf.binopResult_result ht
  · intro Γ _ op l r hno _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  · intro Γ _ a ha iha t ht
    simp only [wtR, ha, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨ca, hca, hwa⟩ := iha .bool ha
    exact ⟨.unop "!" ca, by simp [lower, hca], by simp [NaruSem.Call.wtR, hwa]⟩
  · intro Γ _ a hno _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  · intro Γ _ op a hne t ht
    simp [wtR, hne] at ht
  · intro Γ _ r m args hu tr tys hargs hr ihr ih5 t ht
    rw [wtR.eq_def] at ht
    simp only [hu, ite_true, hr, hargs] at ht
    obtain ⟨cr, hcr, hwr⟩ := ihr tr hr
    obtain ⟨cs, hcs, hwcs⟩ := ih5 tys hargs
    have htys : ((none, cr) :: cs).map (mapArg (NaruSem.Call.wtR T.Δ Γ.vals)) =
        ((none, tr) :: tys).map (mapArg some) := by
      simp only [List.map_cons, mapArg, hwr, hwcs]
    obtain ⟨c, hc, hw⟩ := lowerCall_typed htys ht
    refine ⟨c, ?_, hw⟩
    rw [lower.eq_def]
    simp [hu, hcr, hcs, hc]
  · intro Γ _ r m args hu hno _ _ t ht
    rw [wtR.eq_def] at ht
    simp only [hu, ite_true] at ht
    cases hwr : wtR T Γ r with
    | none => simp at ht
    | some tr =>
      cases hwa : wtArgs T Γ args with
      | none => simp at ht
      | some tys => exact (hno tr tys hwr hwa).elim
  · intro Γ _ r m hnu a k ha hr hm ihr iha t ht
    simp only [Bool.not_eq_true] at hnu
    simp only [wtR, hnu, Bool.false_eq_true, ite_false, hm, hr, ha, Option.some.injEq] at ht
    subst ht
    obtain ⟨cr, hcr, hwr⟩ := ihr .nat hr
    obtain ⟨ca, hca, hwa⟩ := iha .nat ha
    exact ⟨.method "Nat" m cr [ca] .nat, by simp [lower, hnu, hm, hcr, hca],
      by simp [NaruSem.Call.wtR, hm, hwr, hwa]⟩
  · intro Γ _ r m hnu a hno _ _ t ht
    simp only [Bool.not_eq_true] at hnu
    rw [wtR.eq_def] at ht
    simp only [hnu, Bool.false_eq_true, ite_false] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  · intro Γ _ r m args hnu hne t ht
    simp only [Bool.not_eq_true] at hnu
    simp only [wtR, hnu, Bool.false_eq_true, ite_false] at ht
    cases args with
    | nil => simp at ht
    | cons a rest =>
      cases a with
      | named n e => simp at ht
      | pos e =>
        cases rest with
        | nil => exact (hne e rfl).elim
        | cons b rest' => simp at ht
  · intro Γ _ c t e te hte hc htt ihc iht ihe t' ht'
    simp only [wtR, hc, htt, hte, ite_true, Option.some.injEq] at ht'
    subst ht'
    obtain ⟨cc, hcc, hwc⟩ := ihc .bool hc
    obtain ⟨ct, hct, hwt⟩ := iht te htt
    obtain ⟨ce, hce, hwe⟩ := ihe te hte
    exact ⟨.ite cc ct ce, by simp [lower, hcc, hct, hce], by simp [NaruSem.Call.wtR, hwc, hwt, hwe]⟩
  · intro Γ _ c t e tt te hte htt hc hne _ _ _ t' ht'
    simp [wtR, hc, htt, hte, hne] at ht'
  · intro Γ _ c t e hno _ _ _ t' ht'
    simp only [wtR] at ht'
    first
      | (cases ht'; done)
      | (split at ht' <;> simp_all)
  · intro Γ _ s arms ta hs hex ihs iharms t ht
    simp only [wtR, hs, hex, ite_true] at ht
    obtain ⟨cs, hcs, hws⟩ := ihs ta hs
    obtain ⟨cas, hcas, hwas⟩ := iharms t ht
    exact ⟨.match_ cs ta.toTyV cas, by simp [lower, hs, hcs, hcas], lower_match_wt hcas hex hws hwas⟩
  · intro Γ _ s arms ta hs hne _ t ht
    simp [wtR, hs, hne] at ht
  · intro Γ _ s arms hs _ t ht
    simp [wtR, hs] at ht
  · intro Γ _ stmts e Γ' hst ihst ihe t ht
    simp only [wtR, hst] at ht
    obtain ⟨binds, hlb, hwb⟩ := ihst Γ' hst
    obtain ⟨c, hc, hw⟩ := ihe t ht
    exact ⟨Surf.mkLets binds c, by simp [lower, hst, hlb, hc], wtR_mkLets hwb hw⟩
  · intro Γ _ stmts e hst _ t ht
    simp [wtR, hst] at ht
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 t ht
    rw [wtR.eq_def] at ht
    split at ht
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ _ rfl).elim
      | exact (h7 _ _ _ _ rfl).elim
      | exact (h8 _ _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | exact (h10 _ _ _ rfl).elim
      | (cases ht; done)
  · intro Γ ts p g b hp t ht
    rw [wtArmR_mk, hp] at ht
    simp at ht
  · intro Γ ts p b bts hp ihb t ht
    rw [wtArmR_mk, hp] at ht
    simp only at ht
    obtain ⟨cb, hcb, hwb⟩ := ihb t ht
    refine ⟨.mk (Surf.lowerPat p) none cb, by rw [lowerArm.eq_1, hp]; simp [hcb], ?_⟩
    rw [NaruSem.Call.wtArmR.eq_1, Surf.wtPat_lower, hp]
    simpa only [vals_extVals] using hwb
  · intro Γ ts p b bts hp g hg ihg ihb t ht
    rw [wtArmR_mk, hp] at ht
    simp only [hg] at ht
    obtain ⟨cg, hcg, hwg⟩ := ihg .bool hg
    obtain ⟨cb, hcb, hwb⟩ := ihb t ht
    refine ⟨.mk (Surf.lowerPat p) (some cg) cb, by rw [lowerArm.eq_1, hp]; simp [hcg, hcb], ?_⟩
    rw [NaruSem.Call.wtArmR.eq_1, Surf.wtPat_lower, hp]
    simp only [vals_extVals] at hwg hwb
    simp only [hwg]
    exact hwb
  · intro Γ ts p b bts hp g hno _ t ht
    rw [wtArmR_mk, hp] at ht
    simp only at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  · intro Γ tys h
    rw [wtArgs.eq_1, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  · intro Γ e rest tr tys hrest he ihe ihrest tys' h
    rw [wtArgs_pos] at h
    simp only [he, hrest, Option.some.injEq] at h
    subst h
    obtain ⟨c, hc, hwc⟩ := ihe tr he
    obtain ⟨cs, hcs, hwcs⟩ := ihrest tys hrest
    exact ⟨(none, c) :: cs, by simp [lowerArgs, hc, hcs], by simp [mapArg, hwc, hwcs]⟩
  · intro Γ e rest hno _ _ tys h
    rw [wtArgs_pos] at h
    cases hwe : wtR T Γ e with
    | none => simp [hwe] at h
    | some tr =>
      cases hwr : wtArgs T Γ rest with
      | none => simp [hwe, hwr] at h
      | some tys' => exact (hno tr tys' hwe hwr).elim
  · intro Γ n e rest tr tys hrest he ihe ihrest tys' h
    rw [wtArgs_named] at h
    simp only [he, hrest, Option.some.injEq] at h
    subst h
    obtain ⟨c, hc, hwc⟩ := ihe tr he
    obtain ⟨cs, hcs, hwcs⟩ := ihrest tys hrest
    exact ⟨(some n, c) :: cs, by simp [lowerArgs, hc, hcs], by simp [mapArg, hwc, hwcs]⟩
  · intro Γ n e rest hno _ _ tys h
    rw [wtArgs_named] at h
    cases hwe : wtR T Γ e with
    | none => simp [hwe] at h
    | some tr =>
      cases hwr : wtArgs T Γ rest with
      | none => simp [hwe, hwr] at h
      | some tys' => exact (hno tr tys' hwe hwr).elim
  · intro Γ ts t ht
    simp [wtArmsR] at ht
  · intro Γ ts arm rest h _ t ht
    simp [wtArmsR, h] at ht
  · intro Γ ts arm t1 h1 ih4 t ht
    simp only [wtArmsR, h1, Option.some.injEq] at ht
    subst ht
    obtain ⟨ca, hca, hwa⟩ := ih4 t1 h1
    refine ⟨[ca], by simp [lowerArms, hca], ?_⟩
    rw [NaruSem.Call.wtArmsR.eq_def]
    simp [hwa]
  · intro Γ ts arm head tail t2 h2 h1 ih4 ih3 t ht
    rw [wtArmsR.eq_def] at ht
    simp only [h1, h2, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨ca, hca, hwa⟩ := ih4 t2 h1
    obtain ⟨cas, hcas, hwas⟩ := ih3 t2 h2
    refine ⟨ca :: cas, by rw [lowerArms.eq_2, hca, hcas], ?_⟩
    cases cas with
    | nil =>
      rw [NaruSem.Call.wtArmsR.eq_def] at hwas
      simp at hwas
    | cons ca' cas' =>
      rw [NaruSem.Call.wtArmsR.eq_def]
      simp [hwa, hwas]
  · intro Γ ts arm t1 head tail h1 t2 hne h2 _ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2, hne] at ht
  · intro Γ ts arm t1 head tail h1 h2 _ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2] at ht
  · intro Γ Γ' h
    simp only [wtStmtsR, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  · intro Γ _ x ty v rest ta hv t hann ihv ihrest Γ' h
    simp only [wtStmtsR, hv, hann] at h
    have ht : t = ta := annot_eq hann
    subst ht
    obtain ⟨cv, hcv, hwv⟩ := ihv t hv
    obtain ⟨binds, hlb, hwb⟩ := ihrest Γ' h
    refine ⟨(x, t.toTyV, cv) :: binds, by simp [lowerStmts, hv, hcv, hlb], ?_⟩
    simp only [wtBinds, hwv, TyV.toTy?_toTyV, ite_true]
    simpa only [vals_ext] using hwb
  · intro Γ _ x ty v rest ta hv hann _ Γ' h
    simp [wtStmtsR, hv, hann] at h
  · intro Γ _ x ty v rest hv _ Γ' h
    simp [wtStmtsR, hv] at h

/-- 適格な任意の runtime Surface 式は lowering が存在し、同じ型を持つ。 -/
theorem lower_typed {T : Table} {Γ : SCtx} {e : Expr} {t : NaruSem.Ty}
    (h : wtR T Γ e = some t) :
    ∃ c, lower T Γ e = some c ∧ NaruSem.Call.wtR T.Δ Γ.vals c = some t :=
  (lower_typed_all T).1 Γ e t h

/-- 呼出しを含む適格な runtime 式の lowering は全域。 -/
theorem lower_total {T : Table} {Γ : SCtx} {e : Expr} {t : NaruSem.Ty}
    (h : wtR T Γ e = some t) : ∃ c, lower T Γ e = some c := by
  obtain ⟨c, hc, _⟩ := lower_typed h
  exact ⟨c, hc⟩

/-- 独立 lowering に成功した適格な式の Core は同じ型を持つ。 -/
theorem lower_wt {T : Table} {Γ : SCtx} {e : Expr} {t : NaruSem.Ty}
    (h : wtR T Γ e = some t) {c : Core.Expr} (hl : lower T Γ e = some c) :
    NaruSem.Call.wtR T.Δ Γ.vals c = some t := by
  obtain ⟨c', hc', hw⟩ := lower_typed h
  rw [hl] at hc'
  cases hc'
  exact hw

/-- 全5構文群の runtime 評価保存。文脈と環境、共通関数環境は整形。 -/
theorem lower_eval_all (T : Table) :
    (∀ (Γ : SCtx) (e : Expr) (Φ : NaruSem.Call.FEnv) (ρ : SEnv),
      Γ = ρ.ctx → Φ.Respects T.Δ → ∀ t, wtR T Γ e = some t →
      ∀ c, lower T Γ e = some c → eval T Φ ρ e = NaruSem.Call.eval Φ ρ.vals c) ∧
    (∀ (Γ : SCtx) (stmts : List Stmt) (Φ : NaruSem.Call.FEnv) (ρ : SEnv),
      Γ = ρ.ctx → Φ.Respects T.Δ → ∀ Γ', wtStmtsR T Γ stmts = some Γ' →
      ∀ binds, lowerStmts T Γ stmts = some binds →
      ∃ ρ', evalStmts T Φ ρ stmts = some ρ' ∧ Γ' = ρ'.ctx ∧
        evalBinds Φ ρ.vals binds = some ρ'.vals) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arms : List Arm) (Φ : NaruSem.Call.FEnv) (ρ : SEnv),
      Γ = ρ.ctx → Φ.Respects T.Δ → ∀ t, wtArmsR T Γ ts arms = some t →
      ∀ v, v.ty = ts → ∀ cas, lowerArms T Γ ts arms = some cas →
        evalArms T Φ ρ v arms = NaruSem.Call.evalArms Φ ρ.vals v cas) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arm : Arm) (Φ : NaruSem.Call.FEnv) (ρ : SEnv),
      Γ = ρ.ctx → Φ.Respects T.Δ → ∀ t, wtArmR T Γ ts arm = some t →
      ∀ ca, lowerArm T Γ ts arm = some ca → ∀ v, v.ty = ts → ∀ rest crest,
        evalArms T Φ ρ v rest = NaruSem.Call.evalArms Φ ρ.vals v crest →
        evalArms T Φ ρ v (arm :: rest) = NaruSem.Call.evalArms Φ ρ.vals v (ca :: crest)) ∧
    (∀ (Γ : SCtx) (args : List Arg) (Φ : NaruSem.Call.FEnv) (ρ : SEnv),
      Γ = ρ.ctx → Φ.Respects T.Δ → ∀ tys, wtArgs T Γ args = some tys →
      ∀ cs, lowerArgs T Γ args = some cs → ∃ vals, evalArgs T Φ ρ args = some vals ∧
        cs.map (mapArg (NaruSem.Call.eval Φ ρ.vals)) = vals.map (mapArg some)) := by
  apply wtR.mutual_induct T
  · intro Γ _ n Φ ρ hΓ hΦ t ht c hl
    simp [lower] at hl
    subst c
    rfl
  · intro Γ _ b Φ ρ hΓ hΦ t ht c hl
    simp [lower] at hl
    subst c
    rfl
  · intro Γ _ x tv hx Φ ρ hΓ hΦ t ht c hl
    simp [lower] at hl
    subst c
    simp only [eval, NaruSem.Call.eval, SEnv.vals]
    cases ρ x <;> rfl
  · intro Γ _ x hno Φ ρ hΓ hΦ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht
         · rename_i t' hx
           exact (hno t' hx).elim
         · cases ht)
  · intro Γ _ _ path args hb Φ ρ hΓ hΦ t ht
    simp [wtR, hb] at ht
  · intro Γ _ _ path args hnb tys hargs ih5 Φ ρ hΓ hΦ t ht c hl
    simp only [Bool.not_eq_true] at hnb
    simp only [wtR, hnb, Bool.false_eq_true, ite_false, hargs] at ht
    obtain ⟨cs, hcs, hwcs⟩ := (lower_typed_all T).2.2.2.2 Γ args tys hargs
    obtain ⟨vals, ha, he⟩ := ih5 Φ ρ hΓ hΦ tys hargs cs hcs
    obtain ⟨vals', ha', hvt⟩ := evalArgs_total hargs Φ ρ hΓ hΦ
    rw [ha] at ha'; cases ha'
    simp only [callTy] at ht
    cases hr : T.resolve path with
    | none => simp [hr] at ht
    | some k =>
      simp only [hr] at ht
      cases hs : (T.sig k).bind DeclSig.value? with
      | none => simp [hs] at ht
      | some pt =>
        obtain ⟨ps, tr⟩ := pt
        simp only [hs] at ht
        split at ht
        · rename_i harr
          obtain ⟨cargs, hc, _⟩ := arrange_core_total hwcs harr
          obtain ⟨vs, hv, _⟩ := arrange_vals hvt harr
          have hρ : headBound ρ path = false := by rw [← headBound_ctx, ← hΓ]; exact hnb
          obtain ⟨hl', he'⟩ := lower_call_eval hnb hρ hr hs hcs hc he ha hv
          rw [hl] at hl'; cases hl'
          exact he'
        · cases ht
  · intro Γ _ _ path args hnb hargs _ Φ ρ hΓ hΦ t ht
    simp only [Bool.not_eq_true] at hnb
    simp [wtR, hnb, hargs] at ht
  · intro Γ _ op l r k tl tr hr htL hk ihl ihr Φ ρ hΓ hΦ t ht c hl
    obtain ⟨cl, hcl⟩ := lower_total htL
    obtain ⟨cr, hcr⟩ := lower_total hr
    simp [lower, htL, hcl, hcr] at hl
    subst c
    rw [eval.eq_def, NaruSem.Call.eval.eq_def]
    simp only [ihl Φ ρ hΓ hΦ tl htL cl hcl, ihr Φ ρ hΓ hΦ tr hr cr hcr]
    rfl
  · intro Γ _ op l r hno _ _ Φ ρ hΓ hΦ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  · intro Γ _ a ha iha Φ ρ hΓ hΦ t ht c hl
    obtain ⟨ca, hca⟩ := lower_total ha
    simp [lower, hca] at hl
    subst c
    rw [eval.eq_def, NaruSem.Call.eval.eq_def]
    simp only [ite_true, iha Φ ρ hΓ hΦ .bool ha ca hca]
    rfl
  · intro Γ _ a hno _ Φ ρ hΓ hΦ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  · intro Γ _ op a hne Φ ρ hΓ hΦ t ht
    simp [wtR, hne] at ht
  · intro Γ _ r m args hu tr tys hargs hr ihr ih5 Φ ρ hΓ hΦ t ht c hl
    rw [wtR.eq_def] at ht
    simp only [hu, ite_true, hr, hargs] at ht
    obtain ⟨cr, hcr, hwr⟩ := lower_typed hr
    obtain ⟨cs, hcs, hwcs⟩ := (lower_typed_all T).2.2.2.2 Γ args tys hargs
    obtain ⟨vals, ha, he⟩ := ih5 Φ ρ hΓ hΦ tys hargs cs hcs
    obtain ⟨vals', ha', hvt⟩ := evalArgs_total hargs Φ ρ hΓ hΦ
    rw [ha] at ha'; cases ha'
    obtain ⟨rv, har, hrt⟩ := eval_total hr Φ ρ hΓ hΦ
    have her : NaruSem.Call.eval Φ ρ.vals cr = some rv := by
      rw [← ihr Φ ρ hΓ hΦ tr hr cr hcr]; exact har
    have hwcs' : ((none, cr) :: cs).map (mapArg (NaruSem.Call.wtR T.Δ Γ.vals)) =
        ((none, tr) :: tys).map (mapArg some) := by simp [mapArg, hwr, hwcs]
    have hvt' : ((none, rv) :: vals).map (mapArg Val.ty) = (none, tr) :: tys := by
      simp [mapArg, hrt, hvt]
    have huρ : ufcs T ρ m = true := by rw [← ufcs_ctx, ← hΓ]; exact hu
    simp only [callTy] at ht
    cases hres : T.resolve [m] with
    | none => simp [hres] at ht
    | some k =>
      simp only [hres] at ht
      cases hs : (T.sig k).bind DeclSig.value? with
      | none => simp [hs] at ht
      | some pt =>
        obtain ⟨ps, tret⟩ := pt
        simp only [hs] at ht
        split at ht
        · rename_i harr
          obtain ⟨cargs, hc, _⟩ := arrange_core_total hwcs' harr
          obtain ⟨vs, hv, _⟩ := arrange_vals hvt' harr
          obtain ⟨hl', he'⟩ := lower_ufcs_eval hu huρ hres hs hcr hcs hc her he har ha hv
          rw [hl] at hl'; cases hl'
          exact he'
        · cases ht
  · intro Γ _ r m args hu hno _ _ Φ ρ hΓ hΦ t ht
    rw [wtR.eq_def] at ht
    simp only [hu, ite_true] at ht
    cases hwr : wtR T Γ r with
    | none => simp at ht
    | some tr =>
      cases hwa : wtArgs T Γ args with
      | none => simp at ht
      | some tys => exact (hno tr tys hwr hwa).elim
  · intro Γ _ r m hnu a k ha hr hm ihr iha Φ ρ hΓ hΦ t ht c hl
    simp only [Bool.not_eq_true] at hnu
    obtain ⟨cr, hcr⟩ := lower_total hr
    obtain ⟨ca, hca⟩ := lower_total ha
    rw [lower.eq_def] at hl
    simp [hnu, hm, hcr, hca] at hl
    subst c
    have hnuρ : ufcs T ρ m = false := by rw [← ufcs_ctx, ← hΓ]; exact hnu
    rw [eval.eq_def, NaruSem.Call.eval.eq_def]
    simp only [hnuρ, Bool.false_eq_true, ite_false, hm,
      ihr Φ ρ hΓ hΦ .nat hr cr hcr, iha Φ ρ hΓ hΦ .nat ha ca hca, ite_true]
    rfl
  · intro Γ _ r m hnu a hno _ _ Φ ρ hΓ hΦ t ht
    simp only [Bool.not_eq_true] at hnu
    rw [wtR.eq_def] at ht
    simp only [hnu, Bool.false_eq_true, ite_false] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  · intro Γ _ r m args hnu hne Φ ρ hΓ hΦ t ht
    simp only [Bool.not_eq_true] at hnu
    simp only [wtR, hnu, Bool.false_eq_true, ite_false] at ht
    cases args with
    | nil => simp at ht
    | cons a rest =>
      cases a with
      | named n e => simp at ht
      | pos e =>
        cases rest with
        | nil => exact (hne e rfl).elim
        | cons b rest' => simp at ht
  · intro Γ _ cond thn els te hte hc htt ihc iht ihe Φ ρ hΓ hΦ t ht c hl
    obtain ⟨cc, hcc⟩ := lower_total hc
    obtain ⟨ct, hct⟩ := lower_total htt
    obtain ⟨ce, hce⟩ := lower_total hte
    simp [lower, hcc, hct, hce] at hl
    subst c
    rw [eval.eq_def, NaruSem.Call.eval.eq_def]
    simp only [ihc Φ ρ hΓ hΦ .bool hc cc hcc,
      iht Φ ρ hΓ hΦ te htt ct hct, ihe Φ ρ hΓ hΦ te hte ce hce]
    rfl
  · intro Γ _ c t e tt te hte htt hc hne _ _ _ Φ ρ hΓ hΦ t' ht'
    simp [wtR, hc, htt, hte, hne] at ht'
  · intro Γ _ c t e hno _ _ _ Φ ρ hΓ hΦ t' ht'
    simp only [wtR] at ht'
    first
      | (cases ht'; done)
      | (split at ht' <;> simp_all)
  · intro Γ _ s arms ts hs hex ihs iharms Φ ρ hΓ hΦ t ht c hl
    simp only [wtR, hs, hex, ite_true] at ht
    obtain ⟨cs, hcs⟩ := lower_total hs
    obtain ⟨cas, hcas, _⟩ := (lower_typed_all T).2.2.1 Γ ts arms t ht
    simp [lower, hs, hcs, hcas] at hl
    subst c
    obtain ⟨v, hv, hvt⟩ := eval_total hs Φ ρ hΓ hΦ
    have he := ihs Φ ρ hΓ hΦ ts hs cs hcs
    simp only [eval, NaruSem.Call.eval, ← he, hv]
    exact iharms Φ ρ hΓ hΦ t ht v hvt cas hcas
  · intro Γ _ s arms ta hs hne _ Φ ρ hΓ hΦ t ht
    simp [wtR, hs, hne] at ht
  · intro Γ _ s arms hs _ Φ ρ hΓ hΦ t ht
    simp [wtR, hs] at ht
  · intro Γ _ stmts e Γ' hst ihst ihe Φ ρ hΓ hΦ t ht c hl
    simp only [wtR, hst] at ht
    obtain ⟨binds, hlb, _⟩ := (lower_typed_all T).2.1 Γ stmts Γ' hst
    obtain ⟨ce, hce⟩ := lower_total ht
    simp [lower, hst, hlb, hce] at hl
    subst c
    obtain ⟨ρ', heval, hΓ', hbind⟩ := ihst Φ ρ hΓ hΦ Γ' hst binds hlb
    rw [eval.eq_def, eval_mkLets]
    simp only [heval, hbind]
    exact ihe Φ ρ' hΓ' hΦ t ht ce hce
  · intro Γ _ stmts e hst _ Φ ρ hΓ hΦ t ht
    simp [wtR, hst] at ht
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 Φ ρ hΓ hΦ t ht
    rw [wtR.eq_def] at ht
    split at ht
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ _ rfl).elim
      | exact (h7 _ _ _ _ rfl).elim
      | exact (h8 _ _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | exact (h10 _ _ _ rfl).elim
      | (cases ht; done)
  · intro Γ ts p g b hp Φ ρ hΓ hΦ t ht
    rw [wtArmR_mk, hp] at ht
    simp at ht
  · intro Γ ts p b bts hp ihb Φ ρ hΓ hΦ t ht ca hl v hv rest crest hrest
    rw [wtArmR_mk, hp] at ht
    simp only  at ht
    apply lowerArm_eval hp hl
    · intro bs cb hm hcb
      have hΓ' : Γ.extVals bts = (ρ.extVals bs).ctx := by
        rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
      rw [← SEnv.vals_extVals]
      exact ihb Φ (ρ.extVals bs) hΓ' hΦ t ht cb hcb
    · intro guard cg bs hg; cases hg
    · exact hrest
  · intro Γ ts p b bts hp g hg ihg ihb Φ ρ hΓ hΦ t ht ca hl v hv rest crest hrest
    rw [wtArmR_mk, hp] at ht
    simp only [hg] at ht
    apply lowerArm_eval hp hl
    · intro bs cb hm hcb
      have hΓ' : Γ.extVals bts = (ρ.extVals bs).ctx := by
        rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
      rw [← SEnv.vals_extVals]
      exact ihb Φ (ρ.extVals bs) hΓ' hΦ t ht cb hcb
    · intro guard cg bs hguard hm hcg
      cases hguard
      have hΓ' : Γ.extVals bts = (ρ.extVals bs).ctx := by
        rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
      rw [← SEnv.vals_extVals]
      exact ihg Φ (ρ.extVals bs) hΓ' hΦ .bool hg cg hcg
    · exact hrest
  · intro Γ ts p b bts hp g hno _ Φ ρ hΓ hΦ t ht
    rw [wtArmR_mk, hp] at ht
    simp only at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  · intro Γ Φ ρ hΓ hΦ tys ht cs hl
    simp [lowerArgs] at hl
    subst cs
    exact ⟨[], rfl, rfl⟩
  · intro Γ e rest tr tys hrest he ihe ihrest Φ ρ hΓ hΦ tys' ht cs hl
    obtain ⟨ce, hce⟩ := lower_total he
    obtain ⟨cr, hcr, _⟩ := (lower_typed_all T).2.2.2.2 Γ rest tys hrest
    simp [lowerArgs, hce, hcr] at hl
    subst cs
    obtain ⟨v, hv, _⟩ := eval_total he Φ ρ hΓ hΦ
    obtain ⟨vals, hvals, hmap⟩ := ihrest Φ ρ hΓ hΦ tys hrest cr hcr
    have heval := ihe Φ ρ hΓ hΦ tr he ce hce
    refine ⟨(none, v) :: vals, by simp [evalArgs_pos, hv, hvals], ?_⟩
    simp [mapArg, ← heval, hv, hmap]
  · intro Γ e rest hno _ _ Φ ρ hΓ hΦ tys h
    rw [wtArgs_pos] at h
    cases hwe : wtR T Γ e with
    | none => simp [hwe] at h
    | some tr =>
      cases hwr : wtArgs T Γ rest with
      | none => simp [hwe, hwr] at h
      | some tys' => exact (hno tr tys' hwe hwr).elim
  · intro Γ n e rest tr tys hrest he ihe ihrest Φ ρ hΓ hΦ tys' ht cs hl
    obtain ⟨ce, hce⟩ := lower_total he
    obtain ⟨cr, hcr, _⟩ := (lower_typed_all T).2.2.2.2 Γ rest tys hrest
    simp [lowerArgs, hce, hcr] at hl
    subst cs
    obtain ⟨v, hv, _⟩ := eval_total he Φ ρ hΓ hΦ
    obtain ⟨vals, hvals, hmap⟩ := ihrest Φ ρ hΓ hΦ tys hrest cr hcr
    have heval := ihe Φ ρ hΓ hΦ tr he ce hce
    refine ⟨(some n, v) :: vals, by simp [evalArgs_named, hv, hvals], ?_⟩
    simp [mapArg, ← heval, hv, hmap]
  · intro Γ n e rest hno _ _ Φ ρ hΓ hΦ tys h
    rw [wtArgs_named] at h
    cases hwe : wtR T Γ e with
    | none => simp [hwe] at h
    | some tr =>
      cases hwr : wtArgs T Γ rest with
      | none => simp [hwe, hwr] at h
      | some tys' => exact (hno tr tys' hwe hwr).elim
  · intro Γ ts Φ ρ hΓ hΦ t ht
    simp [wtArmsR] at ht
  · intro Γ ts arm rest h _ Φ ρ hΓ hΦ t ht
    simp [wtArmsR, h] at ht
  · intro Γ ts arm t1 h1 ih4 Φ ρ hΓ hΦ t ht v hv cas hl
    simp only [wtArmsR, h1, Option.some.injEq] at ht
    subst t
    obtain ⟨ca, hca, _⟩ := (lower_typed_all T).2.2.2.1 Γ ts arm t1 h1
    simp [lowerArms, hca] at hl
    subst cas
    exact ih4 Φ ρ hΓ hΦ t1 h1 ca hca v hv [] [] rfl
  · intro Γ ts arm head tail t2 h2 h1 ih4 ih3 Φ ρ hΓ hΦ t ht v hv cas hl
    obtain ⟨ca, hca, _⟩ := (lower_typed_all T).2.2.2.1 Γ ts arm t2 h1
    obtain ⟨crest, hcrest, _⟩ := (lower_typed_all T).2.2.1 Γ ts (head :: tail) t2 h2
    rw [lowerArms.eq_2, hca, hcrest] at hl
    cases hl
    exact ih4 Φ ρ hΓ hΦ t2 h1 ca hca v hv _ _ (ih3 Φ ρ hΓ hΦ t2 h2 v hv crest hcrest)
  · intro Γ ts arm t1 head tail h1 t2 hne h2 _ _ Φ ρ hΓ hΦ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2, hne] at ht
  · intro Γ ts arm t1 head tail h1 h2 _ _ Φ ρ hΓ hΦ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2] at ht
  · intro Γ Φ ρ hΓ hΦ Γ' ht binds hl
    simp [wtStmtsR] at ht
    subst Γ'
    simp [lowerStmts] at hl
    subst binds
    exact ⟨ρ, rfl, hΓ, rfl⟩
  · intro Γ _ x ty v rest ta hv t hann ihv ihrest Φ ρ hΓ hΦ Γ' ht binds hl
    simp only [wtStmtsR, hv, hann] at ht
    have heq : t = ta := annot_eq hann
    subst t
    obtain ⟨cv, hcv⟩ := lower_total hv
    obtain ⟨restb, hrestb, _⟩ := (lower_typed_all T).2.1 (Γ.ext x (.val ta)) rest Γ' ht
    simp [lowerStmts, hv, hcv, hrestb] at hl
    subst binds
    obtain ⟨w, hw, hwt⟩ := eval_total hv Φ ρ hΓ hΦ
    have hΓw : Γ.ext x (.val ta) = (ρ.ext x (.val w)).ctx := by
      rw [SEnv.ctx_ext, hΓ]; simp [SVal.ty, hwt]
    obtain ⟨ρ', heval, hΓ', hbind⟩ := ihrest Φ (ρ.ext x (.val w)) hΓw hΦ Γ' ht restb hrestb
    refine ⟨ρ', by simp [evalStmts_cons, hw, heval], hΓ', ?_⟩
    have he := ihv Φ ρ hΓ hΦ ta hv cv hcv
    simp only [evalBinds, ← he, hw]
    simpa only [SEnv.vals_ext_val] using hbind
  · intro Γ _ x ty v rest ta hv hann _ Φ ρ hΓ hΦ Γ' h
    simp [wtStmtsR, hv, hann] at h
  · intro Γ _ x ty v rest hv _ Φ ρ hΓ hΦ Γ' h
    simp [wtStmtsR, hv] at h
/-- 適格な runtime Surface 式の lowering は、整形環境の下で評価を保つ。 -/
theorem lower_eval {T : Table} {Γ : SCtx} {e : Expr} {t : NaruSem.Ty}
    {c : Core.Expr} {Φ : NaruSem.Call.FEnv} {ρ : SEnv}
    (h : wtR T Γ e = some t) (hl : lower T Γ e = some c)
    (hΓ : Γ = ρ.ctx) (hΦ : Φ.Respects T.Δ) :
    eval T Φ ρ e = NaruSem.Call.eval Φ ρ.vals c :=
  (lower_eval_all T).1 Γ e Φ ρ hΓ hΦ t h c hl

/-- 適格な let 列は、出力環境の値部分と文脈を保持する。 -/
theorem lowerStmts_eval {T : Table} {Γ Γ' : SCtx} {stmts : List Stmt}
    {binds : List (String × TyV × Core.Expr)} {Φ : NaruSem.Call.FEnv} {ρ : SEnv}
    (h : wtStmtsR T Γ stmts = some Γ') (hl : lowerStmts T Γ stmts = some binds)
    (hΓ : Γ = ρ.ctx) (hΦ : Φ.Respects T.Δ) :
    (evalStmts T Φ ρ stmts).map SEnv.vals = evalBinds Φ ρ.vals binds := by
  obtain ⟨ρ', he, _, hb⟩ := (lower_eval_all T).2.1 Γ stmts Φ ρ hΓ hΦ Γ' h binds hl
  simp only [he, Option.map_some, hb]

/-- 適格な実引数列の名前と各評価値は、並べ替え前の Core 列と対応する。 -/
theorem lowerArgs_eval {T : Table} {Γ : SCtx} {args : List Arg}
    {tys : List (Option String × NaruSem.Ty)} {cs : List (Option String × Core.Expr)}
    {Φ : NaruSem.Call.FEnv} {ρ : SEnv}
    (h : wtArgs T Γ args = some tys) (hl : lowerArgs T Γ args = some cs)
    (hΓ : Γ = ρ.ctx) (hΦ : Φ.Respects T.Δ) :
    ∃ vals, evalArgs T Φ ρ args = some vals ∧
      cs.map (mapArg (NaruSem.Call.eval Φ ρ.vals)) = vals.map (mapArg some) :=
  (lower_eval_all T).2.2.2.2 Γ args Φ ρ hΓ hΦ tys h cs hl

/-- 適格な腕列は型の合う scrutinee 値について評価を保つ。 -/
theorem lowerArms_eval_wt {T : Table} {Γ : SCtx} {ts t : NaruSem.Ty}
    {arms : List Arm} {cas : List Core.Arm} {Φ : NaruSem.Call.FEnv} {ρ : SEnv}
    (h : wtArmsR T Γ ts arms = some t) (hl : lowerArms T Γ ts arms = some cas)
    (hΓ : Γ = ρ.ctx) (hΦ : Φ.Respects T.Δ) {v : Val} (hv : v.ty = ts) :
    evalArms T Φ ρ v arms = NaruSem.Call.evalArms Φ ρ.vals v cas :=
  (lower_eval_all T).2.2.1 Γ ts arms Φ ρ hΓ hΦ t h v hv cas hl

/-- 適格な単一腕は、対応する任意の後続評価を保持する。 -/
theorem lowerArm_eval_wt {T : Table} {Γ : SCtx} {ts t : NaruSem.Ty}
    {arm : Arm} {ca : Core.Arm} {Φ : NaruSem.Call.FEnv} {ρ : SEnv}
    (h : wtArmR T Γ ts arm = some t) (hl : lowerArm T Γ ts arm = some ca)
    (hΓ : Γ = ρ.ctx) (hΦ : Φ.Respects T.Δ) {v : Val} (hv : v.ty = ts)
    {rest : List Arm} {crest : List Core.Arm}
    (hr : evalArms T Φ ρ v rest = NaruSem.Call.evalArms Φ ρ.vals v crest) :
    evalArms T Φ ρ v (arm :: rest) = NaruSem.Call.evalArms Φ ρ.vals v (ca :: crest) :=
  (lower_eval_all T).2.2.2.1 Γ ts arm Φ ρ hΓ hΦ t h ca hl v hv rest crest hr

end NaruSem.Surf.Call
