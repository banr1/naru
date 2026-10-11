import NaruSem.SurfaceCallLowerSound

/-! Runtime typing excludes proposition-only expressions. The observation context may
change value types, but cannot turn a typed value name into a proposition. -/

namespace NaruSem.Call
open Naru

/-- A value context cannot read a name classified as a proposition. -/
def ValueScope (Γ : Ctx) (Γ₀ : SCtx) : Prop :=
  ∀ x t, Γ x = some t → Γ₀ x ≠ some .prop

theorem ValueScope.ext {Γ : Ctx} {Γ₀ : SCtx} (h : ValueScope Γ Γ₀) (x : String) (t t₀ : Ty) :
    ValueScope (Γ.ext x t) (Γ₀.ext x (.val t₀)) := by
  intro y u hy
  by_cases he : y = x
  · simp [SCtx.ext, he]
  · simp only [Ctx.ext, he, ite_false] at hy
    simpa only [SCtx.ext, he, ite_false] using h y u hy

theorem ValueScope.pat {Γ : Ctx} {Γ₀ : SCtx} (h : ValueScope Γ Γ₀)
    {ts : Ty} {p : Core.Pat} {bs : List (String × Ty)} (hp : wtPat ts p = some bs) :
    ValueScope (Γ.extPat bs) (match p with | .bind x => Γ₀.ext x (.val .nat) | _ => Γ₀) := by
  cases p with
  | wild =>
    simp only [wtPat, Option.some.injEq] at hp
    subst bs
    exact h
  | bind x =>
    simp only [wtPat, Option.some.injEq] at hp
    subst bs
    exact h.ext x ts .nat
  | lit l =>
    cases l <;> simp only [wtPat] at hp
    all_goals first
      | (cases hp; done)
      | (split at hp <;> first | (cases hp; exact h) | (cases hp; done))
  | tuple _ | builtin _ _ | variant _ _ _ => simp [wtPat] at hp

theorem wtArgs_members {Δ : SigEnv} {Γ : Ctx} {args : List Core.Expr} {ps : List Ty}
    (h : wtArgs Δ Γ args ps = true) : ∀ a ∈ args, ∃ t, wtR Δ Γ a = some t := by
  induction args generalizing ps with
  | nil => simp
  | cons a as ih =>
    cases ps with
    | nil => simp [wtArgs] at h
    | cons t ts =>
      rw [wtArgs_cons] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨t, h.1⟩
      · exact ih h.2 e he

theorem wtArmsR_members {Δ : SigEnv} {Γ : Ctx} {ts t : Ty} {arms : List Core.Arm}
    (h : wtArmsR Δ Γ ts arms = some t) : ∀ a ∈ arms, ∃ u, wtArmR Δ Γ ts a = some u := by
  induction arms generalizing t with
  | nil => simp
  | cons a as ih =>
    rw [wtArmsR.eq_def] at h
    cases ha : wtArmR Δ Γ ts a with
    | none => simp [ha] at h
    | some u =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨u, ha⟩
      · cases as with
        | nil => simp at hb
        | cons a' rest =>
          simp only [ha] at h
          cases hr : wtArmsR Δ Γ ts (a' :: rest) with
          | none => simp [hr] at h
          | some v => exact ih hr b hb

/-- Simultaneous exclusion for expressions, arm lists, and argument lists. -/
theorem proppyS_false_of_wtR_all (Δ : SigEnv) :
    (∀ (Γ₀ : SCtx) (e : Core.Expr), ∀ Γ, ValueScope Γ Γ₀ → ∀ t,
      wtR Δ Γ e = some t → proppyS Δ Γ₀ e = false) ∧
    (∀ (Γ₀ : SCtx) (arms : List Core.Arm), ∀ Γ, ValueScope Γ Γ₀ → ∀ ts,
      (∀ a ∈ arms, ∃ t, wtArmR Δ Γ ts a = some t) → proppyArms Δ Γ₀ arms = false) ∧
    (∀ (Γ₀ : SCtx) (args : List Core.Expr), ∀ Γ, ValueScope Γ Γ₀ →
      (∀ a ∈ args, ∃ t, wtR Δ Γ a = some t) → proppyArgs Δ Γ₀ args = false) := by
  apply proppyS.mutual_induct
  · intro Γ₀ q bs b Γ _ t hw
    simp [wtR] at hw
  · intro Γ₀ x hx Γ hv t hw
    simp only [wtR] at hw
    exact (hv x t hw hx).elim
  · intro Γ₀ x hx Γ _ t _
    simp [proppyS]
  · intro Γ₀ k args ih Γ hv t hw
    simp only [wtR] at hw
    cases hk : valueSig? Δ k with
    | none => simp [hk] at hw
    | some pt =>
      rcases pt with ⟨ps, u⟩
      simp only [hk] at hw
      split at hw
      · rename_i ha
        have hs : isSpecKey Δ k = false := by
          cases hspec : isSpecKey Δ k with
          | false => rfl
          | true => exact (not_value_and_spec (isValueKey_of_valueSig? hk) hspec).elim
        simp only [proppyS, hs, Bool.false_or]
        exact ih Γ hv (wtArgs_members ha)
      · cases hw
  · intro Γ₀ x ty v b ihv ihb Γ hv t hw
    simp only [wtR] at hw
    cases hvt : wtR Δ Γ v <;> cases hty : TyV.toTy? ty <;> simp only [hvt, hty] at hw
    all_goals first | (cases hw; done) | skip
    rename_i tv ta
    split at hw
    · simp only [proppyS, ihv Γ hv tv hvt, Bool.false_or]
      exact ihb _ (hv.ext x tv .nat) t hw
    · cases hw
  · intro Γ₀ c a b ihc iha ihb Γ hv t hw
    simp only [wtR] at hw
    cases hc : wtR Δ Γ c <;> cases ha : wtR Δ Γ a <;> cases hb : wtR Δ Γ b <;> simp only [hc, ha, hb] at hw
    all_goals first | (cases hw; done) | skip
    rename_i tc ta tb
    cases tc <;> simp only at hw
    · cases hw
    · simp only [proppyS, ihc Γ hv .bool hc, iha Γ hv ta ha, ihb Γ hv tb hb, Bool.false_or]
  · intro Γ₀ op l r ty ihl ihr Γ hv t hw
    simp only [wtR] at hw
    cases hk : BinOp.ofString? op <;> cases hl : wtR Δ Γ l <;> cases hr : wtR Δ Γ r <;>
      cases ht : TyV.toTy? ty <;> simp only [hk, hl, hr, ht] at hw
    all_goals first | (cases hw; done) | skip
    rename_i k tl tr ta
    simp only [proppyS, ihl Γ hv tl hl, ihr Γ hv tr hr, Bool.false_or]
  · intro Γ₀ op a iha Γ hv t hw
    simp only [wtR] at hw
    split at hw
    · cases ha : wtR Δ Γ a <;> simp only [ha] at hw
      · cases hw
      · rename_i ta
        cases ta <;> simp only at hw
        · cases hw
        · simp only [proppyS, iha Γ hv .bool ha]
    · cases hw
  · intro Γ₀ s st arms ihs ihas Γ hv t hw
    simp only [wtR] at hw
    cases hs : wtR Δ Γ s <;> cases ht : TyV.toTy? st <;> simp only [hs, ht] at hw
    all_goals first | (cases hw; done) | skip
    rename_i ts ta
    split at hw
    · simp only [proppyS, ihs Γ hv ts hs, Bool.false_or]
      exact ihas Γ hv ts (wtArmsR_members hw)
    · cases hw
  · intro Γ₀ tn m r a rt ihr iha Γ hv t hw
    simp only [wtR] at hw
    split at hw
    · cases hm : NatMethod.ofString? m <;> cases hr : wtR Δ Γ r <;> cases ha : wtR Δ Γ a <;>
        cases rt <;> simp only [hm, hr, ha] at hw
      all_goals first | (cases hw; done) | skip
      all_goals rename_i k tr ta
      all_goals cases tr <;> cases ta <;> simp only at hw
      all_goals first | (cases hw; done) | simp only [proppyS, ihr Γ hv .nat hr, iha Γ hv .nat ha, Bool.false_or]
    · cases hw
  · intro e Γ₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 Γ _ t _
    rw [proppyS.eq_def]
    split
    all_goals first
      | exact (h1 _ _ _ rfl).elim
      | exact (h2 _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ rfl).elim
      | exact (h6 _ _ _ _ rfl).elim
      | exact (h7 _ _ rfl).elim
      | exact (h8 _ _ _ rfl).elim
      | exact (h9 _ _ _ _ _ rfl).elim
      | rfl
  · intro Γ₀ Γ _ _
    rfl
  · intro Γ₀ a as iha ihas Γ hv hm
    obtain ⟨t, ht⟩ := hm a (List.mem_cons_self ..)
    simp only [proppyArgs, iha Γ hv t ht, Bool.false_or]
    exact ihas Γ hv (fun e he => hm e (List.mem_cons_of_mem _ he))
  · intro Γ₀ Γ _ ts _
    rfl
  · intro Γ₀ p g b rest Γp ihg ihb ihrest Γ hv ts hm
    have hΓp : Γp = (match p with | .bind x => Γ₀.ext x (.val .nat) | _ => Γ₀) := by cases p <;> rfl
    clear_value Γp
    subst hΓp
    obtain ⟨t, ht⟩ := hm (.mk p g b) (List.mem_cons_self ..)
    rw [wtArmR.eq_1] at ht
    cases hp : wtPat ts p with
    | none => simp [hp] at ht
    | some bs =>
      simp only [hp] at ht
      have hv' := hv.pat hp
      have hr : proppyArms Δ Γ₀ rest = false := ihrest Γ hv ts (fun e he => hm e (List.mem_cons_of_mem _ he))
      cases g with
      | none =>
        have hb := ihb (Γ.extPat bs) (by cases p <;> exact hv') t ht
        cases p <;> simp only [proppyArms, hb, hr, Bool.false_or]
      | some g =>
        cases hg : wtR Δ (Γ.extPat bs) g <;> simp only [hg] at ht
        · cases ht
        · rename_i tg
          cases tg <;> simp only at ht
          · cases ht
          · have hgg := ihg (Γ.extPat bs) (by cases p <;> exact hv') .bool hg
            have hb := ihb (Γ.extPat bs) (by cases p <;> exact hv') t ht
            cases p <;> simp only [proppyArms, hgg, hb, hr, Bool.false_or]

/-- Runtime typing excludes propositions in any context whose proposition names
are also propositions in the typing context. -/
theorem proppyS_false_of_wtR {Δ : SigEnv} {Γ Γ₀ : SCtx} {e : Core.Expr} {t : Ty}
    (h : wtR Δ Γ.vals e = some t)
    (hp : ∀ x, Γ₀ x = some .prop → Γ x = some .prop) : proppyS Δ Γ₀ e = false := by
  apply (proppyS_false_of_wtR_all Δ).1 Γ₀ e Γ.vals _ t h
  intro x u hx hprop
  have hh := hp x hprop
  simp [SCtx.vals, hh] at hx

end NaruSem.Call

namespace NaruSem.Surf.Call
open Naru

/-- Preserve local-name shadowing and do not create proposition bindings. Value
types may change because the proposition classifier uses a placeholder type. -/
def RuntimeScope (Γ Γ₀ : SCtx) : Prop :=
  (∀ x, (Γ₀ x).isSome = (Γ x).isSome) ∧
  (∀ x, Γ₀ x = some .prop → Γ x = some .prop)

theorem RuntimeScope.ext {Γ Γ₀ : SCtx} (h : RuntimeScope Γ Γ₀) (x : String) (t t₀ : NaruSem.Ty) :
    RuntimeScope (Γ.ext x (.val t)) (Γ₀.ext x (.val t₀)) := by
  constructor
  · intro y
    by_cases he : y = x
    · simp [SCtx.ext, he]
    · simpa only [SCtx.ext, he, ite_false] using h.1 y
  · intro y hy
    by_cases he : y = x
    · simp [SCtx.ext, he] at hy
    · simp only [SCtx.ext, he, ite_false] at hy ⊢
      exact h.2 y hy

theorem RuntimeScope.pat {Γ Γ₀ : SCtx} (h : RuntimeScope Γ Γ₀)
    {ts : NaruSem.Ty} {p : Pat} {bs : List (String × NaruSem.Ty)} (hp : wtPat ts p = some bs) :
    RuntimeScope (Γ.extVals bs) (match p with | .bind _ x => Γ₀.ext x (.val .nat) | _ => Γ₀) := by
  cases p with
  | wild _ =>
    simp only [wtPat, Option.some.injEq] at hp
    subst bs
    exact h
  | bind _ x =>
    simp only [wtPat, Option.some.injEq] at hp
    subst bs
    exact h.ext x ts .nat
  | lit _ l =>
    cases l <;> simp only [wtPat] at hp
    all_goals first
      | (cases hp; done)
      | (split at hp <;> first | (cases hp; exact h) | (cases hp; done))

theorem RuntimeScope.ufcs {Γ Γ₀ : SCtx} (h : RuntimeScope Γ Γ₀) (T : Table) (m : String) :
    ufcs T Γ₀ m = ufcs T Γ m := by
  have hm : (Γ₀ m).isNone = (Γ m).isNone := by
    have hd := h.1 m
    cases h₀ : Γ₀ m <;> cases h₁ : Γ m <;> simp_all
  simp only [NaruSem.Surf.Call.ufcs, hm]

theorem callTy_not_spec {T : Table} {path : List String} {tys : List (Option String × NaruSem.Ty)} {t : NaruSem.Ty}
    (h : callTy T path tys = some t) : isSpecPath T path = false := by
  cases hr : T.resolve path with
  | none => simp [callTy, hr] at h
  | some k =>
    cases hs : T.sig k with
    | none => simp [callTy, hr, hs] at h
    | some sig =>
      cases sig <;> simp_all [callTy, isSpecPath, DeclSig.value?, DeclSig.spec?]

/-- Expression carried by an actual argument, retaining its name in the caller. -/
def argExpr : Arg → Expr
  | .pos e | .named _ e => e

theorem wtArgs_members {T : Table} {Γ : SCtx} {args : List Arg} {tys : List (Option String × NaruSem.Ty)}
    (h : wtArgs T Γ args = some tys) : ∀ a ∈ args, ∃ t, wtR T Γ (argExpr a) = some t := by
  induction args generalizing tys with
  | nil => simp
  | cons a as ih =>
    cases a with
    | pos e | named n e =>
      first | rw [wtArgs_pos] at h | rw [wtArgs_named] at h
      cases he : wtR T Γ e <;> cases hr : wtArgs T Γ as <;> simp only [he, hr] at h
      all_goals first | (cases h; done) | skip
      rename_i t ts
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨t, he⟩
      · exact ih hr a ha

theorem wtArmsR_members {T : Table} {Γ : SCtx} {ts t : NaruSem.Ty} {arms : List Arm}
    (h : wtArmsR T Γ ts arms = some t) : ∀ a ∈ arms, ∃ u, wtArmR T Γ ts a = some u := by
  induction arms generalizing t with
  | nil => simp
  | cons a as ih =>
    rw [wtArmsR.eq_def] at h
    cases ha : wtArmR T Γ ts a with
    | none => simp [ha] at h
    | some u =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨u, ha⟩
      · cases as with
        | nil => simp at hb
        | cons a' rest =>
          simp only [ha] at h
          cases hr : wtArmsR T Γ ts (a' :: rest) with
          | none => simp [hr] at h
          | some v => exact ih hr b hb

/-- Simultaneous exclusion, including propagation of shadowing through blocks. -/
theorem proppyS_false_of_wtR_all (T : Table) :
    (∀ (Γ₀ : SCtx) (e : Expr), ∀ Γ, RuntimeScope Γ Γ₀ → ∀ t,
      wtR T Γ e = some t → proppyS T Γ₀ e = false) ∧
    (∀ (Γ₀ : SCtx) (arms : List Arm), ∀ Γ, RuntimeScope Γ Γ₀ → ∀ ts,
      (∀ a ∈ arms, ∃ t, wtArmR T Γ ts a = some t) → proppyArms T Γ₀ arms = false) ∧
    (∀ (Γ₀ : SCtx) (stmts : List Stmt), ∀ Γ, RuntimeScope Γ Γ₀ → ∀ Γ',
      wtStmtsR T Γ stmts = some Γ' →
      proppyStmts T Γ₀ stmts = false ∧ RuntimeScope Γ' (stmtsCtxP Γ₀ stmts)) ∧
    (∀ (Γ₀ : SCtx) (args : List Arg), ∀ Γ, RuntimeScope Γ Γ₀ →
      (∀ a ∈ args, ∃ t, wtR T Γ (argExpr a) = some t) → proppyArgs T Γ₀ args = false) := by
  apply proppyS.mutual_induct
  · intro Γ₀ sp q bs b Γ _ t hw
    simp [wtR] at hw
  · intro Γ₀ sp x hx Γ hv t hw
    have hh := hv.2 x hx
    simp [wtR, hh] at hw
  · intro Γ₀ sp x hx Γ _ t _
    simp [proppyS]
  · intro Γ₀ sp spf path args ih Γ hv t hw
    rw [wtR.eq_def] at hw
    simp only at hw
    split at hw
    · cases hw
    · cases ha : wtArgs T Γ args with
      | none => simp [ha] at hw
      | some tys =>
        simp only [ha] at hw
        have hs := callTy_not_spec hw
        simp only [proppyS, hs, Bool.and_false, Bool.false_or]
        exact ih Γ hv (wtArgs_members ha)
  · intro Γ₀ sp r m args ihr ihas Γ hv t hw
    rw [wtR.eq_def] at hw
    simp only at hw
    split at hw
    · rename_i hu
      cases hr : wtR T Γ r <;> cases ha : wtArgs T Γ args <;> simp only [hr, ha] at hw
      all_goals first | (cases hw; done) | skip
      rename_i tr tys
      have hs := callTy_not_spec hw
      simp only [proppyS, hs, Bool.and_false, Bool.false_or, ihr Γ hv tr hr]
      exact ihas Γ hv (wtArgs_members ha)
    · rename_i hu
      cases args with
      | nil => simp at hw
      | cons a rest =>
        cases a with
        | named _ _ => simp at hw
        | pos a =>
          cases rest with
          | cons _ _ => simp at hw
          | nil =>
            cases hm : NatMethod.ofString? m <;> cases hr : wtR T Γ r <;> cases ha : wtR T Γ a <;>
              simp only [hm, hr, ha] at hw
            all_goals first | (cases hw; done) | skip
            rename_i k tr ta
            cases tr <;> cases ta <;> simp only at hw
            all_goals first | (cases hw; done) | skip
            have hu₀ : ufcs T Γ₀ m = false := by
              rw [hv.ufcs]
              simpa only [Bool.not_eq_true] using hu
            have has : proppyArgs T Γ₀ [.pos a] = false := ihas Γ hv (by
              intro a' ha'
              simp only [List.mem_singleton] at ha'
              subst a'
              exact ⟨.nat, ha⟩)
            simp only [proppyS, hu₀, Bool.false_and, Bool.false_or, ihr Γ hv .nat hr, has]
  · intro Γ₀ sp stmts tail ihs ihe Γ hv t hw
    cases tail with
    | none => simp [wtR] at hw
    | some e =>
      simp only [wtR] at hw
      cases hst : wtStmtsR T Γ stmts with
      | none => simp [hst] at hw
      | some Γ' =>
        simp only [hst] at hw
        obtain ⟨hs, hv'⟩ := ihs Γ hv Γ' hst
        simp only [proppyS, hs, Bool.false_or]
        exact ihe Γ' hv' t hw
  · intro Γ₀ sp c a b ihc iha ihb Γ hv t hw
    simp only [wtR] at hw
    cases hc : wtR T Γ c <;> cases ha : wtR T Γ a <;> cases hb : wtR T Γ b <;>
      simp only [hc, ha, hb] at hw
    all_goals first | (cases hw; done) | skip
    rename_i tc ta tb
    cases tc <;> simp only at hw
    · cases hw
    · simp only [proppyS, ihc Γ hv .bool hc, iha Γ hv ta ha, ihb Γ hv tb hb, Bool.false_or]
  · intro Γ₀ sp op l r ihl ihr Γ hv t hw
    simp only [wtR] at hw
    cases hk : BinOp.ofString? op <;> cases hl : wtR T Γ l <;> cases hr : wtR T Γ r <;>
      simp only [hk, hl, hr] at hw
    all_goals first | (cases hw; done) | skip
    rename_i k tl tr
    simp only [proppyS, ihl Γ hv tl hl, ihr Γ hv tr hr, Bool.false_or]
  · intro Γ₀ sp op a iha Γ hv t hw
    simp only [wtR] at hw
    split at hw
    · cases ha : wtR T Γ a <;> simp only [ha] at hw
      · cases hw
      · rename_i ta
        cases ta <;> simp only at hw
        · cases hw
        · simp only [proppyS, iha Γ hv .bool ha]
    · cases hw
  · intro Γ₀ sp s arms ihs ihas Γ hv t hw
    simp only [wtR] at hw
    cases hs : wtR T Γ s <;> simp only [hs] at hw
    · cases hw
    · rename_i ts
      split at hw
      · simp only [proppyS, ihs Γ hv ts hs, Bool.false_or]
        exact ihas Γ hv ts (wtArmsR_members hw)
      · cases hw
  · intro e Γ₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 Γ _ t _
    rw [proppyS.eq_def]
    split
    all_goals first
      | exact (h1 _ _ _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ rfl).elim
      | exact (h6 _ _ _ _ rfl).elim
      | exact (h7 _ _ _ _ rfl).elim
      | exact (h8 _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | rfl
  · intro Γ₀ Γ _ _
    rfl
  · intro Γ₀ e rest ihe ihrest Γ hv hm
    obtain ⟨t, ht⟩ := hm (.pos e) (List.mem_cons_self ..)
    simp only [argExpr] at ht
    simp only [proppyArgs, ihe Γ hv t ht, Bool.false_or]
    exact ihrest Γ hv (fun a ha => hm a (List.mem_cons_of_mem _ ha))
  · intro Γ₀ n e rest ihe ihrest Γ hv hm
    obtain ⟨t, ht⟩ := hm (.named n e) (List.mem_cons_self ..)
    simp only [argExpr] at ht
    simp only [proppyArgs, ihe Γ hv t ht, Bool.false_or]
    exact ihrest Γ hv (fun a ha => hm a (List.mem_cons_of_mem _ ha))
  · intro Γ₀ Γ _ ts _
    rfl
  · intro Γ₀ p g b rest Γp ihg ihb ihrest Γ hv ts hm
    have hΓp : Γp = (match p with | .bind _ x => Γ₀.ext x (.val .nat) | _ => Γ₀) := by cases p <;> rfl
    clear_value Γp
    subst hΓp
    obtain ⟨t, ht⟩ := hm (.mk p g b) (List.mem_cons_self ..)
    rw [wtArmR_mk] at ht
    cases hp : wtPat ts p with
    | none => simp [hp] at ht
    | some bs =>
      simp only [hp] at ht
      have hv' := hv.pat hp
      have hr : proppyArms T Γ₀ rest = false := ihrest Γ hv ts (fun e he => hm e (List.mem_cons_of_mem _ he))
      cases g with
      | none =>
        have hb := ihb (Γ.extVals bs) (by cases p <;> exact hv') t ht
        cases p <;> simp only [proppyArms, hb, hr, Bool.false_or]
      | some g =>
        cases hg : wtR T (Γ.extVals bs) g <;> simp only [hg] at ht
        · cases ht
        · rename_i tg
          cases tg <;> simp only at ht
          · cases ht
          · have hgg := ihg (Γ.extVals bs) (by cases p <;> exact hv') .bool hg
            have hb := ihb (Γ.extVals bs) (by cases p <;> exact hv') t ht
            cases p <;> simp only [proppyArms, hgg, hb, hr, Bool.false_or]
  · intro Γ₀ Γ hv Γ' hw
    simp only [wtStmtsR, Option.some.injEq] at hw
    subst Γ'
    exact ⟨rfl, hv⟩
  · intro Γ₀ sp x ty v rest ihv ihr Γ hv Γ' hw
    rw [wtStmtsR.eq_2] at hw
    cases hvv : wtR T Γ v with
    | none => simp [hvv] at hw
    | some tv =>
      simp only [hvv] at hw
      cases hann : annot ty tv with
      | none => simp [hann] at hw
      | some ta =>
        simp only [hann] at hw
        obtain ⟨hr, hv'⟩ := ihr _ (hv.ext x ta .nat) Γ' hw
        exact ⟨by simp only [proppyStmts, ihv Γ hv tv hvv, hr, Bool.false_or], hv'⟩

/-- Runtime expressions remain value expressions under the same local-name
shadowing with no newly introduced proposition binding. -/
theorem proppyS_false_of_wtR {T : Table} {Γ Γ₀ : SCtx} {e : Expr} {t : NaruSem.Ty}
    (h : wtR T Γ e = some t)
    (hd : ∀ x, (Γ₀ x).isSome = (Γ x).isSome)
    (hp : ∀ x, Γ₀ x = some .prop → Γ x = some .prop) : proppyS T Γ₀ e = false :=
  (proppyS_false_of_wtR_all T).1 Γ₀ e Γ ⟨hd, hp⟩ t h

end NaruSem.Surf.Call
