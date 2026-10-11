import NaruSem.SurfaceCallLowerSpec
import NaruSem.SurfaceCallLowerSound
import NaruSem.SurfaceCallProppy

/-!
# 呼出しを含む spec lowering の全域性・型保存

式・let列・腕列・腕を同時に帰納し、値の位置では runtime の型保存を使う。
命題の構文区分の保存は、名前の可視性が同じで命題束縛を増やさない文脈に限る。
意味の双方向同値、宣言群から生成 Lean までの合成はここでは扱わない。
-/
namespace NaruSem.Surf.Call
open Naru

/-- 型付け文脈の名前の可視性を保ち、命題束縛を増やさない構文走査文脈。 -/
def ScopeView (Γ Γ₀ : SCtx) : Prop :=
  (∀ x, (Γ₀ x).isSome = (Γ x).isSome) ∧
  (∀ x, Γ₀ x = some .prop → Γ x = some .prop)

theorem ScopeView.refl (Γ : SCtx) : ScopeView Γ Γ := ⟨fun _ => rfl, fun _ h => h⟩

private theorem ScopeView.extVal {Γ Γ₀ : SCtx} (h : ScopeView Γ Γ₀)
    (x : String) (t : STy) : ScopeView (Γ.ext x t) (Γ₀.ext x (.val .nat)) := by
  constructor
  · intro y
    by_cases hy : y = x <;> simp [SCtx.ext, hy, h.1 y]
  · intro y hp
    by_cases hy : y = x
    · simp [SCtx.ext, hy] at hp
    · simpa [SCtx.ext, hy] using h.2 y (by simpa [SCtx.ext, hy] using hp)

private theorem ScopeView.headBound {Γ Γ₀ : SCtx} (h : ScopeView Γ Γ₀) (path : List String) :
    headBound Γ₀ path = headBound Γ path := by
  cases path <;> simp [NaruSem.Surf.Call.headBound, h.1]

private theorem ScopeView.ufcs {Γ Γ₀ : SCtx} (h : ScopeView Γ Γ₀) (T : Table) (m : String) :
    ufcs T Γ₀ m = ufcs T Γ m := by
  have hd := h.1 m
  unfold NaruSem.Surf.Call.ufcs
  cases h₀ : Γ₀ m <;> cases hΓ : Γ m <;> simp_all

private theorem ScopeView.pat {Γ Γ₀ : SCtx} (h : ScopeView Γ Γ₀)
    {ts : NaruSem.Ty} {p : Pat} {bs : List (String × NaruSem.Ty)}
    (hp : wtPat ts p = some bs) : ScopeView (Γ.extVals bs) (Surf.patCtxS Γ₀ p) := by
  cases p with
  | wild => simp only [wtPat, Option.some.injEq] at hp; subst bs; exact h
  | bind _ x =>
    simp only [wtPat, Option.some.injEq] at hp
    subst bs
    exact h.extVal x (.val ts)
  | lit _ l =>
    cases ts <;> cases l <;> simp [wtPat] at hp
    all_goals subst bs; exact h

private theorem proppyS_lower_runtime {T : Table} {Γ : SCtx} {e : Expr} {t : NaruSem.Ty}
    (h : wtR T Γ e = some t) {c : Core.Expr} (hc : lower T Γ e = some c)
    (Γ₀ : SCtx) (hv : ScopeView Γ Γ₀) :
    NaruSem.Call.proppyS T.Δ Γ₀ c = proppyS T Γ₀ e := by
  rw [proppyS_false_of_wtR h hv.1 hv.2,
    NaruSem.Call.proppyS_false_of_wtR (lower_wt h hc) hv.2]

private theorem proppyArgs_false {T : Table} {Γ : SCtx} {args : List Arg}
    {tys : List (Option String × NaruSem.Ty)} (h : wtArgs T Γ args = some tys)
    (Γ₀ : SCtx) (hv : ScopeView Γ Γ₀) : proppyArgs T Γ₀ args = false := by
  induction args generalizing tys with
  | nil => rfl
  | cons a rest ih =>
    cases a <;> rename_i e
    all_goals
      rw [wtArgs.eq_def] at h
      cases he : wtR T Γ e <;> simp only [he] at h
      · cases h
      · cases hr : wtArgs T Γ rest <;> simp only [hr] at h
        · cases h
        · simp [proppyArgs, proppyS_false_of_wtR he hv.1 hv.2, ih hr]

private theorem proppyCoreArgs_false {Δ : NaruSem.Call.SigEnv} {Γ Γ₀ : SCtx}
    {args : List Core.Expr} {ts : List NaruSem.Ty}
    (h : NaruSem.Call.wtArgs Δ Γ.vals args ts = true)
    (hv : ∀ x, Γ₀ x = some .prop → Γ x = some .prop) :
    NaruSem.Call.proppyArgs Δ Γ₀ args = false := by
  induction args generalizing ts with
  | nil => rfl
  | cons a rest ih =>
    cases ts with
    | nil => simp [NaruSem.Call.wtArgs] at h
    | cons t ts =>
      simp only [NaruSem.Call.wtArgs, Bool.and_eq_true, decide_eq_true_eq] at h
      simp [NaruSem.Call.proppyArgs,
        NaruSem.Call.proppyS_false_of_wtR h.1 hv, ih h.2]

private theorem lowerCallS_typed {T : Table} {Γ : SCtx}
    {path : List String} {tys : List (Option String × NaruSem.Ty)}
    {args : List (Option String × Core.Expr)} {τ : STy}
    (ht : args.map (mapArg (NaruSem.Call.wtR T.Δ Γ.vals)) = tys.map (mapArg some))
    (h : callTyS T path tys = some τ) :
    ∃ k s cs, T.resolve path = some k ∧ T.sig k = some s ∧
      lowerCallS T path args = some (.call k cs) ∧
      NaruSem.Call.wtS T.Δ Γ (.call k cs) = some τ ∧
      NaruSem.Call.wtArgs T.Δ Γ.vals cs (s.params.map (·.2)) = true := by
  simp only [callTyS] at h
  cases hr : T.resolve path with
  | none => simp [hr] at h
  | some k =>
    simp only [hr] at h
    cases hs : T.sig k with
    | none => simp [hs] at h
    | some s =>
      cases s <;> rename_i ps
      all_goals
        simp only [hs] at h
        split at h
        · rename_i ha
          obtain ⟨cs, hc, hw⟩ := arrange_core_total ht ha
          refine ⟨k, _, cs, rfl, hs, lowerCallS_eq hr hs hc, ?_, hw⟩
          simpa [NaruSem.Call.wtS, Table.Δ, hs, DeclSig.toSig, hw] using h
        · cases h

private theorem proppyCall_eq {T : Table} {Γ Γ₀ : SCtx} {path : List String}
    {k : String} {s : DeclSig} {cs : List Core.Expr}
    (hr : T.resolve path = some k) (hs : T.sig k = some s)
    (hw : NaruSem.Call.wtArgs T.Δ Γ.vals cs (s.params.map (·.2)) = true)
    (hv : ScopeView Γ Γ₀) :
    NaruSem.Call.proppyS T.Δ Γ₀ (.call k cs) = isSpecPath T path := by
  simp only [NaruSem.Call.proppyS, proppyCoreArgs_false hw hv.2, Bool.or_false]
  cases s <;> simp [NaruSem.Call.isSpecKey, NaruSem.Call.specSig?, Table.Δ,
    hs, DeclSig.toSig, DeclSig.spec?, NaruSem.Call.Sig.spec?, isSpecPath, hr]

private theorem proppyArms_cons (T : Table) (Γ : SCtx) (p : Pat)
    (g : Option Expr) (b : Expr) (rest : List Arm) :
    proppyArms T Γ (.mk p g b :: rest) =
      ((match g with | some g => proppyS T (Surf.patCtxS Γ p) g | none => false) ||
        proppyS T (Surf.patCtxS Γ p) b || proppyArms T Γ rest) := by
  cases p <;> cases g <;> rfl

private theorem proppyCoreArms_cons (Δ : NaruSem.Call.SigEnv) (Γ : SCtx) (p : Core.Pat)
    (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm) :
    NaruSem.Call.proppyArms Δ Γ (.mk p g b :: rest) =
      ((match g with | some g => NaruSem.Call.proppyS Δ (SCtx.patCtx Γ p) g | none => false) ||
        NaruSem.Call.proppyS Δ (SCtx.patCtx Γ p) b || NaruSem.Call.proppyArms Δ Γ rest) := by
  cases p <;> cases g <;> rfl

private theorem proppyArms_lowerPat_cons {T : Table} {Γ Γ₀ : SCtx}
    {ts : NaruSem.Ty} {p : Pat} {bs : List (String × NaruSem.Ty)}
    (hp : wtPat ts p = some bs) (hv : ScopeView Γ Γ₀)
    (g : Option Expr) (b : Expr) (cg : Option Core.Expr) (cb : Core.Expr)
    (hg : g.isSome = cg.isSome)
    (hb : ∀ Γ₁, ScopeView (Γ.extVals bs) Γ₁ → NaruSem.Call.proppyS T.Δ Γ₁ cb = proppyS T Γ₁ b)
    (hgg : ∀ g' cg', g = some g' → cg = some cg' → ∀ Γ₁,
      ScopeView (Γ.extVals bs) Γ₁ → NaruSem.Call.proppyS T.Δ Γ₁ cg' = proppyS T Γ₁ g')
    (rest : List Arm) (crest : List Core.Arm)
    (hrest : NaruSem.Call.proppyArms T.Δ Γ₀ crest = proppyArms T Γ₀ rest) :
    NaruSem.Call.proppyArms T.Δ Γ₀ (.mk (Surf.lowerPat p) cg cb :: crest) =
      proppyArms T Γ₀ (.mk p g b :: rest) := by
  have hv' := hv.pat hp
  rw [proppyCoreArms_cons, proppyArms_cons, Surf.patCtx_lower, hrest, hb _ hv']
  cases g with
  | none => cases cg <;> simp_all
  | some g' =>
    cases cg with
    | none => simp at hg
    | some cg' => simp only [hgg g' cg' rfl rfl _ hv']

theorem exhaustiveFrom_lowerPat_cons (ts : NaruSem.Ty) (p : Pat) (g : Option Expr) (b : Expr) (cg : Option Core.Expr) (cb : Core.Expr)
    (hg : g.isSome = cg.isSome) (rest : List Arm) (crest : List Core.Arm)
    (hrest : ∀ sawT sawF, exhaustiveFrom ts sawT sawF rest = NaruSem.exhaustiveFrom ts sawT sawF crest) (sawT sawF : Bool) :
    exhaustiveFrom ts sawT sawF (.mk p g b :: rest) = NaruSem.exhaustiveFrom ts sawT sawF (.mk (lowerPat p) cg cb :: crest) := by
  cases g with
  | some g =>
    cases cg with
    | none => simp at hg
    | some cg => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, hrest]
  | none =>
    cases cg with
    | some cg => simp at hg
    | none =>
      cases p with
      | wild => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat]
      | bind => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat]
      | lit _ l =>
        cases l with
        | bool lb => cases lb <;> simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
        | nat n => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
        | str s => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
        | unit => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]

/-- 全4構文群の spec lowering の全域性・型保存。命題区分は同じ名前スコープで保存する。 -/
theorem lowerS_typed_all (T : Table) :
    (∀ (Γ : SCtx) (e : Expr), ∀ τ, wtS T Γ e = some τ →
      ∃ c, lowerS T Γ e = some c ∧ NaruSem.Call.wtS T.Δ Γ c = some τ ∧
        ∀ Γ₀, ScopeView Γ Γ₀ → NaruSem.Call.proppyS T.Δ Γ₀ c = proppyS T Γ₀ e) ∧
    (∀ (Γ : SCtx) (stmts : List Stmt), ∀ Γ', wtStmtsS T Γ stmts = some Γ' →
      ∃ binds, lowerStmtsS T Γ stmts = some binds ∧
        (∀ c τ, NaruSem.Call.wtS T.Δ Γ' c = some τ → NaruSem.Call.wtS T.Δ Γ (Surf.mkLets binds c) = some τ) ∧
        ∀ Γ₀, ScopeView Γ Γ₀ → ∀ c e,
          (∀ Γ₁, ScopeView Γ' Γ₁ → NaruSem.Call.proppyS T.Δ Γ₁ c = proppyS T Γ₁ e) →
          NaruSem.Call.proppyS T.Δ Γ₀ (Surf.mkLets binds c) =
            (proppyStmts T Γ₀ stmts || proppyS T (stmtsCtxP Γ₀ stmts) e)) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arms : List Arm), ∀ τ, wtArmsS T Γ ts arms = some τ →
      ∃ cas, lowerArmsS T Γ ts arms = some cas ∧ NaruSem.Call.wtArmsS T.Δ Γ ts cas = some τ ∧
        (∀ sawT sawF, exhaustiveFrom ts sawT sawF arms = NaruSem.exhaustiveFrom ts sawT sawF cas) ∧
        ∀ Γ₀, ScopeView Γ Γ₀ → NaruSem.Call.proppyArms T.Δ Γ₀ cas = proppyArms T Γ₀ arms) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arm : Arm), ∀ p g b, arm = .mk p g b →
      ∀ τ, wtArmS T Γ ts arm = some τ →
      ∃ bs cg cb, wtPat ts p = some bs ∧
        lowerArmS T Γ ts arm = some (.mk (Surf.lowerPat p) cg cb) ∧
        NaruSem.Call.wtArmS T.Δ Γ ts (.mk (Surf.lowerPat p) cg cb) = some τ ∧
        g.isSome = cg.isSome ∧
        (∀ Γ₀, ScopeView (Γ.extVals bs) Γ₀ → NaruSem.Call.proppyS T.Δ Γ₀ cb = proppyS T Γ₀ b) ∧
        (∀ g' cg', g = some g' → cg = some cg' → ∀ Γ₀,
          ScopeView (Γ.extVals bs) Γ₀ → NaruSem.Call.proppyS T.Δ Γ₀ cg' = proppyS T Γ₀ g')) := by
  apply wtS.mutual_induct T
  -- 1. Nat のリテラル(値)
  · intro Γ _ n τ hτ
    simp only [wtS, Option.some.injEq] at hτ
    subst hτ
    refine ⟨.lit (.nat n) .nat, rfl, rfl, fun _ _ => rfl⟩
  -- 2. Bool のリテラル
  · intro Γ _ b τ hτ
    simp only [wtS, Option.some.injEq] at hτ
    subst hτ
    refine ⟨.lit (.bool b) .bool, rfl, rfl, fun _ _ => rfl⟩
  -- 3. 局所名
  · intro Γ _ x τ hτ
    simp only [wtS] at hτ
    refine ⟨.var x, rfl, by simpa [NaruSem.Call.wtS] using hτ, fun _ _ => rfl⟩
  · intro Γ _ _ path args hb τ hτ
    simp [wtS, hb] at hτ
  · intro Γ _ _ path args hnb tys hargs τ hτ
    simp only [Bool.not_eq_true] at hnb
    rw [wtS.eq_def] at hτ
    simp only [hnb, Bool.false_eq_true, ite_false, hargs] at hτ
    obtain ⟨cs, hcs, hwcs⟩ := (lower_typed_all T).2.2.2.2 Γ args tys hargs
    obtain ⟨k, s, cargs, hr, hs, hl, hw, hwa⟩ := lowerCallS_typed hwcs hτ
    refine ⟨.call k cargs, ?_, hw, ?_⟩
    · rw [lowerS.eq_def]
      simp [hnb, hcs, hl]
    · intro Γ₀ hv
      rw [proppyCall_eq hr hs hwa hv]
      simp only [proppyS, hv.headBound path, hnb, Bool.not_false, Bool.true_and,
        proppyArgs_false hargs Γ₀ hv, Bool.or_false]
  · intro Γ _ _ path args hnb hargs τ hτ
    simp only [Bool.not_eq_true] at hnb
    simp [wtS, hnb, hargs] at hτ
  -- 4. if(適格)
  · intro Γ _ c t e tc tt te hte htt hc j hj ihc iht ihe τ hτ
    simp only [wtS, hc, htt, hte, hj] at hτ
    obtain ⟨cc, hcc, hwc, hpc⟩ := ihc tc hc
    obtain ⟨ct, hct, hwt, hpt⟩ := iht tt htt
    obtain ⟨ce, hce, hwe, hpe⟩ := ihe te hte
    refine ⟨.ite cc ct ce, by simp [lowerS, hcc, hct, hce], ?_, ?_⟩
    · simp only [NaruSem.Call.wtS, hwc, hwt, hwe, hj]
      exact hτ
    · intro Γ₀ hv
      simp only [NaruSem.Call.proppyS, proppyS, hpc Γ₀ hv, hpt Γ₀ hv, hpe Γ₀ hv]
  -- 5. if(条件と then の結びが無い)
  · intro Γ _ c t e tc tt te hte htt hc hj _ _ _ τ hτ
    simp [wtS, hc, htt, hte, hj] at hτ
  -- 6. if(不適格)
  · intro Γ _ c t e hno _ _ _ τ hτ
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 7. 論理演算(適格)
  · intro Γ _ op l r k hk tl tr hr hl ihl ihr τ hτ
    simp only [wtS, hk, hl, hr] at hτ
    obtain ⟨cl, hcl, hwl, hpl⟩ := ihl tl hl
    obtain ⟨cr, hcr, hwr, hpr⟩ := ihr tr hr
    refine ⟨.binop op cl cr .bool, by simp [lowerS, hk, hcl, hcr], ?_, ?_⟩
    · simp only [NaruSem.Call.wtS, hk, TyV.toTy?, hwl, hwr]
      exact hτ
    · intro Γ₀ hv
      simp only [NaruSem.Call.proppyS, proppyS, hpl Γ₀ hv, hpr Γ₀ hv]
  -- 8. 論理演算(被演算子が不適格)
  · intro Γ _ op l r k hk hno _ _ τ hτ
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 9. == / !=(両辺が Nat の値: 値の等値、注釈 `.nat`)
  · intro Γ _ op l r k hk hnn τ hτ
    simp only [wtS, hk, hnn, and_self, ite_true, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨cl, hcl⟩ := lower_total hnn.1
    obtain ⟨cr, hcr⟩ := lower_total hnn.2
    refine ⟨.binop op cl cr .nat, ?_, ?_, ?_⟩
    · simp [lowerS, hk, hnn, hcl, hcr]
    · simp [NaruSem.Call.wtS, hk, TyV.toTy?, lower_wt hnn.1 hcl, lower_wt hnn.2 hcr]
    · intro Γ₀ hv
      simp only [NaruSem.Call.proppyS, proppyS, proppyS_lower_runtime hnn.1 hcl Γ₀ hv, proppyS_lower_runtime hnn.2 hcr Γ₀ hv]
  -- 10. == / !=(論理の位置、適格: 注釈 `.bool`)
  · intro Γ _ op l r k hk hnn tl tr hr hl ihl ihr τ hτ
    simp only [wtS, hk, hnn, ite_false, hl, hr] at hτ
    obtain ⟨cl, hcl, hwl, hpl⟩ := ihl tl hl
    obtain ⟨cr, hcr, hwr, hpr⟩ := ihr tr hr
    refine ⟨.binop op cl cr .bool, ?_, ?_, ?_⟩
    · simp [lowerS, hk, hnn, hcl, hcr]
    · simp only [NaruSem.Call.wtS, hk, TyV.toTy?, hwl, hwr]
      exact hτ
    · intro Γ₀ hv
      simp only [NaruSem.Call.proppyS, proppyS, hpl Γ₀ hv, hpr Γ₀ hv]
  -- 11. == / !=(論理の位置、被演算子が不適格)
  · intro Γ _ op l r k hk hnn hno _ _ τ hτ
    simp only [wtS, hk, hnn, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 12. 比較(適格: 注釈は被演算子の型)
  · intro Γ _ op l r k hk tr hr hl τ hτ
    simp [wtS, hk, hl, hr] at hτ
    subst hτ
    obtain ⟨cl, hcl⟩ := lower_total hl
    obtain ⟨cr, hcr⟩ := lower_total hr
    refine ⟨.binop op cl cr tr.toTyV, ?_, ?_, ?_⟩
    · simp [lowerS, hk, hl, hcl, hcr]
    · simp [NaruSem.Call.wtS, hk, lower_wt hl hcl, lower_wt hr hcr]
    · intro Γ₀ hv
      simp only [NaruSem.Call.proppyS, proppyS, proppyS_lower_runtime hl hcl Γ₀ hv, proppyS_lower_runtime hr hcr Γ₀ hv]
  -- 13. 比較(被演算子の型が違う)
  · intro Γ _ op l r k hk tl tr hr hl hne τ hτ
    simp [wtS, hk, hl, hr, hne] at hτ
  -- 14. 比較(被演算子が不適格)
  · intro Γ _ op l r k hk hno τ hτ
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 15. 算術(値)
  · intro Γ _ op l r k hk hr hl τ hτ
    simp only [wtS, hk, hl, hr, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨cl, hcl⟩ := lower_total hl
    obtain ⟨cr, hcr⟩ := lower_total hr
    refine ⟨.binop op cl cr .nat, ?_, ?_, ?_⟩
    · simp [lowerS, hk, hcl, hcr]
    · simp [NaruSem.Call.wtS, hk, TyV.toTy?, lower_wt hl hcl, lower_wt hr hcr]
    · intro Γ₀ hv
      simp only [NaruSem.Call.proppyS, proppyS, proppyS_lower_runtime hl hcl Γ₀ hv, proppyS_lower_runtime hr hcr Γ₀ hv]
  -- 16. 算術(被演算子が不適格)
  · intro Γ _ op l r k hk hno τ hτ
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 17. 対象外の演算子
  · intro Γ _ op l r hk τ hτ
    simp [wtS, hk] at hτ
  -- 18. `!`(適格)
  · intro Γ _ a j hj hjf iha τ hτ
    simp [wtS, hj, hjf] at hτ
    subst hτ
    obtain ⟨ca, hca, hwa, hpa⟩ := iha j hj
    refine ⟨.unop "!" ca, by simp [lowerS, hca], by simp [NaruSem.Call.wtS, hwa, hjf], ?_⟩
    · intro Γ₀ hv
      simp only [NaruSem.Call.proppyS, proppyS, hpa Γ₀ hv]
  -- 19. `!`(被演算子が論理の位置の型でない)
  · intro Γ _ a j hj hjf _ τ hτ
    simp [wtS, hj, hjf] at hτ
  -- 20. `!`(被演算子が不適格)
  · intro Γ _ a hj _ τ hτ
    simp [wtS, hj] at hτ
  -- 21. 対象外の単項演算子
  · intro Γ _ op a hne τ hτ
    simp [wtS, hne] at hτ
  · intro Γ _ r m args hu tr tys hargs hr τ hτ
    rw [wtS.eq_def] at hτ
    simp only [hu, ite_true, hr, hargs] at hτ
    obtain ⟨cr, hcr, hwr⟩ := lower_typed hr
    obtain ⟨cs, hcs, hwcs⟩ := (lower_typed_all T).2.2.2.2 Γ args tys hargs
    have htys : ((none, cr) :: cs).map (mapArg (NaruSem.Call.wtR T.Δ Γ.vals)) =
        ((none, tr) :: tys).map (mapArg some) := by
      simp only [List.map_cons, mapArg, hwr, hwcs]
    obtain ⟨k, s, cargs, hres, hs, hl, hw, hwa⟩ := lowerCallS_typed htys hτ
    refine ⟨.call k cargs, by simp [lowerS, hu, hcr, hcs, hl], hw, ?_⟩
    intro Γ₀ hv
    rw [proppyCall_eq hres hs hwa hv]
    simp [proppyS, hv.ufcs T m, hu, proppyArgs_false hargs Γ₀ hv,
      proppyS_false_of_wtR hr hv.1 hv.2]
  · intro Γ _ r m args hu hno τ hτ
    rw [wtS.eq_def] at hτ
    simp only [hu, ite_true] at hτ
    cases hr : wtR T Γ r with
    | none => simp at hτ
    | some tr =>
      cases ha : wtArgs T Γ args with
      | none => simp at hτ
      | some tys => exact (hno tr tys hr ha).elim
  · intro Γ _ r m hnu a k ha hr hm τ hτ
    simp only [Bool.not_eq_true] at hnu
    simp only [wtS, hnu, Bool.false_eq_true, ite_false, hm, hr, ha, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨cr, hcr⟩ := lower_total hr
    obtain ⟨ca, hca⟩ := lower_total ha
    refine ⟨.method "Nat" m cr [ca] .nat, ?_, ?_, ?_⟩
    · simp [lowerS, hnu, hm, hcr, hca]
    · simp [NaruSem.Call.wtS, hm, lower_wt hr hcr, lower_wt ha hca]
    · intro Γ₀ hv
      simp [NaruSem.Call.proppyS, proppyS, proppyArgs, hv.ufcs T m, hnu,
        proppyS_lower_runtime hr hcr Γ₀ hv, proppyS_lower_runtime ha hca Γ₀ hv]
  · intro Γ _ r m hnu a hno τ hτ
    simp only [Bool.not_eq_true] at hnu
    rw [wtS.eq_def] at hτ
    simp only [hnu, Bool.false_eq_true, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  · intro Γ _ r m args hnu hne τ hτ
    simp only [Bool.not_eq_true] at hnu
    rw [wtS.eq_def] at hτ
    simp only [hnu, Bool.false_eq_true, ite_false] at hτ
    cases args with
    | nil => simp at hτ
    | cons a rest =>
      cases a with
      | named n e => simp at hτ
      | pos e =>
        cases rest with
        | nil => exact (hne e rfl).elim
        | cons b rest' => simp at hτ
  -- 24. match(適格)
  · intro Γ _ s arms ta hs hex ih2 τ hτ
    simp only [wtS, hs, hex, ite_true] at hτ
    obtain ⟨cs, hcs⟩ := lower_total hs
    obtain ⟨cas, hcas, hwas, hexs, hpas⟩ := ih2 τ hτ
    refine ⟨.match_ cs ta.toTyV cas, ?_, ?_, ?_⟩
    · simp [lowerS, hs, hcs, hcas]
    · have hex' : NaruSem.exhaustive ta cas = true := by
        unfold NaruSem.exhaustive
        rw [← hexs]
        exact hex
      simp only [NaruSem.Call.wtS, lower_wt hs hcs, TyV.toTy?_toTyV, hex', Bool.and_true, decide_true, ite_true]
      exact hwas
    · intro Γ₀ hv
      simp only [NaruSem.Call.proppyS, proppyS, proppyS_lower_runtime hs hcs Γ₀ hv, hpas Γ₀ hv]
  -- 25. match(網羅しない)
  · intro Γ _ s arms ta hs hne τ hτ
    simp [wtS, hs, hne] at hτ
  -- 26. match(scrutinee が不適格)
  · intro Γ _ s arms hs τ hτ
    simp [wtS, hs] at hτ
  -- 27. ブロック(適格)
  · intro Γ sp stmts e Γ' hst ihst ihe τ hτ
    simp only [wtS, hst] at hτ
    obtain ⟨binds, hlb, hwb, hpb⟩ := ihst Γ' hst
    obtain ⟨c, hc, hw, hpc⟩ := ihe τ hτ
    refine ⟨Surf.mkLets binds c, by simp [lowerS, hst, hlb, hc], hwb c τ hw, ?_⟩
    · intro Γ₀ hv
      exact hpb Γ₀ hv c e hpc
  -- 28. ブロック(let の列が不適格)
  · intro Γ _ stmts e hst _ τ hτ
    simp [wtS, hst] at hτ
  -- 29. 量化(束縛なし: 対象外)
  · intro Γ _ q b τ hτ
    simp [wtS] at hτ
  -- 30. 量化(適格)
  · intro Γ sp q bs b Γ' hb j hj hjf hne ih τ hτ
    obtain ⟨cbs, hcbs, hcb, hlen⟩ := lowerBinders_sound bs hb
    obtain ⟨cb, hcb', hwb, _⟩ := ih j hj
    have hτ' : τ = .prop := by
      cases bs with
      | nil => exact (hne rfl).elim
      | cons bd rest =>
        simp [wtS, hb, hj, hjf] at hτ
        exact hτ.symm
    subst hτ'
    refine ⟨.quant q cbs cb, ?_, ?_, fun _ _ => rfl⟩
    · simp [lowerS, hb, hcbs, hcb']
    · cases bs with
      | nil => exact (hne rfl).elim
      | cons bd rest =>
        cases cbs with
        | nil => simp at hlen
        | cons cbd crest => simp [NaruSem.Call.wtS, hcb, hwb, hjf]
  -- 31. 量化(本体が論理の位置の型でない)
  · intro Γ _ q bs b Γ' hb j hj hjf hne _ τ hτ
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj, hjf] at hτ
  -- 32. 量化(本体が不適格)
  · intro Γ _ q bs b Γ' hb hj hne _ τ hτ
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj] at hτ
  -- 33. 量化(束縛の型が対象外)
  · intro Γ _ q bs b hb hne τ hτ
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb] at hτ
  -- 34. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 τ hτ
    rw [wtS.eq_def] at hτ
    split at hτ
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ _ _ rfl).elim
      | exact (h7 _ _ _ rfl).elim
      | exact (h8 _ _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | exact (h10 _ _ _ rfl).elim
      | exact (h11 _ _ _ _ rfl).elim
      | (cases hτ; done)
  -- 35. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp p' g' b' heq τ hτ
    cases heq
    rw [wtArmS.eq_1, hp] at hτ
    simp at hτ
  -- 36. 腕(ガード無し、適格)
  · intro Γ ts p b bs' hp j hj hjf ihb p' g' b' heq τ hτ
    cases heq
    rw [wtArmS.eq_1, hp] at hτ
    simp only [hj, hjf, ite_true, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨cb, hcb, hwb, hpb⟩ := ihb j hj
    refine ⟨bs', none, cb, hp, ?_, ?_, rfl, hpb, ?_⟩
    · rw [lowerArmS.eq_1, hp]
      simp [hcb]
    · rw [NaruSem.Call.wtArmS.eq_1, wtPat_lower, hp]
      simp [hwb, hjf]
    · intro g' cg' h
      cases h
  -- 37. 腕(ガード無し、本体が論理の位置の型でない)
  · intro Γ ts p b bs' hp j hj hjf _ p' g' b' heq τ hτ
    cases heq
    rw [wtArmS.eq_1, hp] at hτ
    simp [hj, hjf] at hτ
  -- 38. 腕(ガード無し、本体が不適格)
  · intro Γ ts p b bs' hp hj _ p' g' b' heq τ hτ
    cases heq
    rw [wtArmS.eq_1, hp] at hτ
    simp [hj] at hτ
  -- 39. 腕(ガード付き、適格)
  · intro Γ ts p b bs' hp g tl tr hb hg ihg ihb p' g' b' heq τ hτ
    cases heq
    rw [wtArmS.eq_1, hp] at hτ
    simp only [hg, hb] at hτ
    obtain ⟨cg, hcg, hwg, hpg⟩ := ihg tl hg
    obtain ⟨cb, hcb, hwb, hpb⟩ := ihb tr hb
    refine ⟨bs', some cg, cb, hp, ?_, ?_, rfl, hpb, ?_⟩
    · rw [lowerArmS.eq_1, hp]
      simp [hcg, hcb]
    · rw [NaruSem.Call.wtArmS.eq_1, wtPat_lower, hp]
      simp only [hwg, hwb]
      exact hτ
    · intro g'' cg'' h1 h2
      cases h1
      cases h2
      exact hpg
  -- 40. 腕(ガード付き、不適格)
  · intro Γ ts p b bs' hp g hno _ _ p' g' b' heq τ hτ
    cases heq
    rw [wtArmS.eq_1, hp] at hτ
    simp only at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 41. 腕の列(空)
  · intro Γ ts τ hτ
    simp [wtArmsS] at hτ
  -- 42. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h] at hτ
  -- 43. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 τ hτ
    obtain ⟨p, g, b⟩ := arm
    rw [wtArmsS.eq_def] at hτ
    simp only [h1, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨bs, cg, cb, hp, hca, hwa, hg, hpb, hpg⟩ := ih3 p g b rfl t1 h1
    refine ⟨[.mk (lowerPat p) cg cb], ?_, ?_, ?_, ?_⟩
    · rw [lowerArmsS.eq_2, hca]
      rfl
    · rw [NaruSem.Call.wtArmsS.eq_def]
      simp [hwa]
    · intro sawT sawF
      exact exhaustiveFrom_lowerPat_cons ts p g b cg cb hg [] [] (fun _ _ => rfl) sawT sawF
    · intro Γ₀ hv
      exact proppyArms_lowerPat_cons hp hv g b cg cb hg hpb hpg [] [] rfl
  -- 44. 腕の列(先頭の腕と残りがともに適格)
  · intro Γ ts arm t1 head tail h1 j hj ih3 ih2 τ hτ
    obtain ⟨p, g, b⟩ := arm
    rw [wtArmsS.eq_def] at hτ
    simp only [h1, hj] at hτ
    obtain ⟨bs, cg, cb, hp, hca, hwa, hg, hpb, hpg⟩ := ih3 p g b rfl t1 h1
    obtain ⟨cas, hcas, hwas, hexs, hpas⟩ := ih2 j hj
    refine ⟨.mk (lowerPat p) cg cb :: cas, ?_, ?_, ?_, ?_⟩
    · rw [lowerArmsS.eq_2, hca, hcas]
    · cases cas with
      | nil =>
        rw [NaruSem.Call.wtArmsS.eq_def] at hwas
        simp at hwas
      | cons ca' cas' =>
        rw [NaruSem.Call.wtArmsS.eq_def]
        simp only [hwa, hwas]
        exact hτ
    · intro sawT sawF
      exact exhaustiveFrom_lowerPat_cons ts p g b cg cb hg (head :: tail) cas hexs sawT sawF
    · intro Γ₀ hv
      exact proppyArms_lowerPat_cons hp hv g b cg cb hg hpb hpg (head :: tail) cas (hpas Γ₀ hv)
  -- 45. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h1, h2] at hτ
  -- 46. let の列(空)
  · intro Γ Γ' h
    simp only [wtStmtsS, Option.some.injEq] at h
    subst h
    refine ⟨[], rfl, fun c τ hc => by simpa using hc, ?_⟩
    · intro Γ₀ hv c e he
      exact he Γ₀ hv
  -- 47. let の列(命題に束ねる、適格)
  · intro Γ _ x ty v rest hp hann hv ihv ihrest Γ' h
    simp only [wtStmtsS, hp, hann, hv, ite_true] at h
    obtain ⟨cv, hcv, hwv, hpv⟩ := ihv .prop hv
    obtain ⟨binds, hlb, hwb, hpb⟩ := ihrest Γ' h
    refine ⟨(x, .bool, cv) :: binds, ?_, ?_, ?_⟩
    · rw [lowerStmtsS.eq_2]
      simp [hp, hcv, hlb]
    · intro c τ hc
      simp only [Surf.mkLets_cons, NaruSem.Call.wtS, TyV.toTy?, hpv Γ (ScopeView.refl Γ), hp, ite_true, hwv]
      exact hwb c τ hc
    · intro Γ₀ hv c e he
      rw [Surf.mkLets_cons]
      simp only [NaruSem.Call.proppyS, proppyStmts, stmtsCtxP, hpv Γ₀ hv, hpb (Γ₀.ext x (.val .nat)) (hv.extVal x _) c e he, Bool.or_assoc]
  -- 48. let の列(命題だが不適格)
  · intro Γ _ x ty v rest hp hann hno _ Γ' h
    simp only [wtStmtsS, hp, hann, ite_true] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 49. let の列(命題だが注釈が Bool でない)
  · intro Γ _ x ty v rest hp hann Γ' h
    simp [wtStmtsS, hp, hann] at h
  -- 50. let の列(値に束ねる、適格)
  · intro Γ _ x ty v rest hp ta hv t hann ihrest Γ' h
    simp only [Bool.not_eq_true] at hp
    simp only [wtStmtsS, hp, Bool.false_eq_true, ite_false, hv, hann] at h
    have ht : t = ta := annot_eq hann
    subst ht
    obtain ⟨cv, hcv⟩ := lower_total hv
    have hwv := lower_wt hv hcv
    have hpv : ∀ Γ₀ : SCtx, ScopeView Γ Γ₀ → NaruSem.Call.proppyS T.Δ Γ₀ cv = proppyS T Γ₀ v := proppyS_lower_runtime hv hcv
    obtain ⟨binds, hlb, hwb, hpb⟩ := ihrest Γ' h
    refine ⟨(x, t.toTyV, cv) :: binds, ?_, ?_, ?_⟩
    · rw [lowerStmtsS.eq_2]
      simp [hp, hv, hcv, hlb]
    · intro c τ hc
      cases t with
      | nat =>
        simp only [Surf.mkLets_cons, NaruSem.Call.wtS, Ty.toTyV, TyV.toTy?, hwv]
        exact hwb c τ hc
      | bool =>
        simp only [Surf.mkLets_cons, NaruSem.Call.wtS, Ty.toTyV, TyV.toTy?, hpv Γ (ScopeView.refl Γ), hp, Bool.false_eq_true, ite_false, hwv]
        exact hwb c τ hc
    · intro Γ₀ hv c e he
      rw [Surf.mkLets_cons]
      simp only [NaruSem.Call.proppyS, proppyStmts, stmtsCtxP, hpv Γ₀ hv, hpb (Γ₀.ext x (.val .nat)) (hv.extVal x _) c e he, Bool.or_assoc]
  -- 51. let の列(値に束ねる、注釈が合わない)
  · intro Γ _ x ty v rest hp ta hv hann Γ' h
    simp only [Bool.not_eq_true] at hp
    simp [wtStmtsS, hp, hv, hann] at h
  -- 52. let の列(値が不適格)
  · intro Γ _ x ty v rest hp hv Γ' h
    simp only [Bool.not_eq_true] at hp
    simp [wtStmtsS, hp, hv] at h

/-- 任意の適格な spec Surface 式の lowering は存在し、同じ spec 型を保つ。 -/
theorem lowerS_typed {T : Table} {Γ : SCtx} {e : Expr} {τ : STy}
    (h : wtS T Γ e = some τ) :
    ∃ c, lowerS T Γ e = some c ∧ NaruSem.Call.wtS T.Δ Γ c = some τ := by
  obtain ⟨c, hc, hw, _⟩ := (lowerS_typed_all T).1 Γ e τ h
  exact ⟨c, hc, hw⟩

/-- 適格な spec Surface 式の独立 lowering は全域。 -/
theorem lowerS_total {T : Table} {Γ : SCtx} {e : Expr} {τ : STy}
    (h : wtS T Γ e = some τ) : ∃ c, lowerS T Γ e = some c := by
  obtain ⟨c, hc, _⟩ := lowerS_typed h
  exact ⟨c, hc⟩

/-- 独立 lowering の結果の Core は元の Surface と同じ型を持つ。 -/
theorem lowerS_wt {T : Table} {Γ : SCtx} {e : Expr} {τ : STy}
    (h : wtS T Γ e = some τ) {c : Core.Expr} (hl : lowerS T Γ e = some c) :
    NaruSem.Call.wtS T.Δ Γ c = some τ := by
  obtain ⟨c', hc', hw⟩ := lowerS_typed h
  rw [hl] at hc'
  cases hc'
  exact hw

/-- 同じ名前スコープで命題束縛を増やさない走査文脈なら、命題区分を保存する。 -/
theorem proppyS_lowerS_view {T : Table} {Γ : SCtx} {e : Expr} {τ : STy}
    (h : wtS T Γ e = some τ) {c : Core.Expr} (hl : lowerS T Γ e = some c)
    (Γ₀ : SCtx) (hv : ScopeView Γ Γ₀) :
    NaruSem.Call.proppyS T.Δ Γ₀ c = proppyS T Γ₀ e := by
  obtain ⟨c', hc', _, hp⟩ := (lowerS_typed_all T).1 Γ e τ h
  rw [hl] at hc'
  cases hc'
  exact hp Γ₀ hv

/-- 型付けした文脈で、命題 let の区分は lowering 後も一致する。 -/
theorem proppyS_lowerS {T : Table} {Γ : SCtx} {e : Expr} {τ : STy}
    (h : wtS T Γ e = some τ) {c : Core.Expr} (hl : lowerS T Γ e = some c) :
    NaruSem.Call.proppyS T.Δ Γ c = proppyS T Γ e :=
  proppyS_lowerS_view h hl Γ (ScopeView.refl Γ)

end NaruSem.Surf.Call
