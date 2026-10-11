import NaruSem.SurfaceCallLower

/-!
# 呼出しを含む runtime lowering の全域性と適格性

Surface の型付けの 5-way 相互帰納法により、適格な runtime 式、その
引数列、let 列、腕列、腕の独立 lowering が存在し、Core の型付けを保つ。
評価の意味保存はこの定理の結論には含めない。
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

end NaruSem.Surf.Call
