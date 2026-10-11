import NaruSem.SurfaceCallLowerSpecSem

/-! Nat / Bool 量化の局所合成の検体。本体の対応を個別に証明し、
任意の関数・命題解釈を保持する。全 spec 式や宣言群の保存は主張しない。 -/
namespace NaruSem.Surf.Call
open Naru

def quantSemTable : Table :=
  { resolve := fun p => if p = ["p"] then some "M.p" else none
    sig := fun k => if k = "M.p" then some (.spec []) else none }

def quantSemCtx : SCtx := SCtx.empty.ext "q" .prop
def quantSemEnv (Q : Prop) : SEnv := SEnv.empty.ext "q" (.prop Q)
def quantSemBinders : List Binder :=
  [{ name := "q", ty := some (.named {} ["Nat"] []), span := {} },
   { name := "q", ty := some (.named {} ["Bool"] []), span := {} }]
def quantSemCoreBinders : List (String × TyV) := [("q", .nat), ("q", .bool)]
def quantSemBody : Expr := .var {} ["q"]
def quantSemSurface (q : Quant) : Expr := .quant {} q quantSemBinders quantSemBody
def quantSemCore (q : Quant) : Core.Expr := .quant q quantSemCoreBinders (.var "q")
def quantSemBodyCtx : SCtx := (quantSemCtx.ext "q" (.val .nat)).ext "q" (.val .bool)

private theorem var_bridge (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (Γ : SCtx) (x : String) : SpecSemEquiv T Φ Ψ Γ (.var {} [x]) (.var x) := by
  intro ρ _ P
  constructor
  · intro hs
    refine ⟨P, ?_, Iff.rfl⟩
    cases hs with
    | varVal h => exact .varVal h
    | varProp h => exact .varProp h
  · intro hc
    refine ⟨P, ?_, Iff.rfl⟩
    cases hc with
    | varVal h => exact .varVal h
    | varProp h => exact .varProp h

theorem quant_sem_ctx (Q : Prop) : quantSemCtx = (quantSemEnv Q).ctx := by
  rw [quantSemEnv, SEnv.ctx_ext]
  rfl

theorem quant_sem_binders_lower :
    Surf.lowerBinders quantSemBinders = some quantSemCoreBinders := rfl

theorem quant_sem_binders_ctx :
    SCtx.extBinders quantSemCtx quantSemBinders = some quantSemBodyCtx := rfl

theorem quant_sem_wt (q : Quant) :
    wtS quantSemTable quantSemCtx (quantSemSurface q) = some .prop := rfl

theorem quant_sem_lower (q : Quant) :
    lowerS quantSemTable quantSemCtx (quantSemSurface q) = some (quantSemCore q) := rfl

/-- 全 Nat / Bool の二段量化を任意解釈で運ぶ。外側 Prop q は二度隠される。 -/
theorem quant_sem_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (q : Quant) (Q P : Prop) :
    Sem quantSemTable Φ Ψ (quantSemEnv Q) (quantSemSurface q) P ↔
      NaruSem.Call.Sem quantSemTable.Δ Φ Ψ (quantSemEnv Q) (quantSemCore q) P := by
  exact lowerS_quant_sem_iff quant_sem_binders_ctx quant_sem_binders_lower (by rfl)
    (by rfl) (quant_sem_lower q) (var_bridge _ _ _ _ "q") (quant_sem_ctx Q) P

/-- 証明書 API の forall 適用。本体の対応は独立に成立させる。 -/
theorem quant_sem_forall_equiv (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SpecSemEquiv quantSemTable Φ Ψ quantSemCtx
      (quantSemSurface .forall_) (quantSemCore .forall_) := by
  exact lowerS_quant_equiv quant_sem_binders_ctx quant_sem_binders_lower
    (var_bridge _ _ _ _ "q")

/-- 束縛列 API の exists 適用。有限入力の列挙に置き換えない。 -/
theorem quant_sem_exists_binders (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (Q P : Prop) :
    Sem quantSemTable Φ Ψ (quantSemEnv Q) (quantSemSurface .exists_) P ↔
      NaruSem.Call.Sem quantSemTable.Δ Φ Ψ (quantSemEnv Q) (quantSemCore .exists_) P := by
  exact lowerBinders_sem_iff quantSemBinders quant_sem_binders_lower quant_sem_binders_ctx
    (quant_sem_ctx Q) (var_bridge _ _ _ _ "q") {} .exists_ P

/-- 空の束縛も forall / exists とも本体の意味をそのまま保持する。 -/
theorem quant_sem_empty (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (ρ : SEnv) (x : String) (q : Quant) (P : Prop) :
    Sem T Φ Ψ ρ (.quant {} q [] (.var {} [x])) P ↔
      NaruSem.Call.Sem T.Δ Φ Ψ ρ (.quant q [] (.var x)) P := by
  exact lowerBinders_sem_iff [] rfl rfl rfl (var_bridge T Φ Ψ ρ.ctx x) {} q P

theorem quant_sem_forall_false (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (Q : Prop) :
    Sem quantSemTable Φ Ψ (quantSemEnv Q) (quantSemSurface .forall_) False ∧
      NaruSem.Call.Sem quantSemTable.Δ Φ Ψ (quantSemEnv Q) (quantSemCore .forall_) False := by
  have hs : Sem quantSemTable Φ Ψ (quantSemEnv Q) (quantSemSurface .forall_)
      (∀ (_ : Nat), ∀ b : Bool, b = true) := by
    apply Sem.forallCons (t := .nat) rfl
    intro n
    apply Sem.forallCons (t := .bool) rfl
    intro b
    exact .quantNil (.varVal (by rfl))
  have he : (∀ (_ : Nat), ∀ b : Bool, b = true) = False := by
    apply propext
    simp
  have hs' := he ▸ hs
  exact ⟨hs', (quant_sem_arbitrary Φ Ψ .forall_ Q False).mp hs'⟩

theorem quant_sem_exists_true (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (Q : Prop) :
    Sem quantSemTable Φ Ψ (quantSemEnv Q) (quantSemSurface .exists_) True ∧
      NaruSem.Call.Sem quantSemTable.Δ Φ Ψ (quantSemEnv Q) (quantSemCore .exists_) True := by
  have hs : Sem quantSemTable Φ Ψ (quantSemEnv Q) (quantSemSurface .exists_)
      (∃ (_ : Nat), ∃ b : Bool, b = true) := by
    apply Sem.existsCons (t := .nat) rfl
    intro n
    apply Sem.existsCons (t := .bool) rfl
    intro b
    exact .quantNil (.varVal (by rfl))
  have he : (∃ (_ : Nat), ∃ b : Bool, b = true) = True := by
    apply propext
    simp
  have hs' := he ▸ hs
  exact ⟨hs', (quant_sem_arbitrary Φ Ψ .exists_ Q True).mp hs'⟩

/-- 量化種別を取り違えても Core の型検査は通る。 -/
theorem quant_sem_wrong_wt (q : Quant) :
    NaruSem.Call.wtS quantSemTable.Δ quantSemCtx (quantSemCore q) = some .prop := rfl

/-- 同型であっても量化種別を交換した Core は実 lowering の出力ではない。 -/
theorem quant_sem_wrong_not_lower :
    lowerS quantSemTable quantSemCtx (quantSemSurface .forall_) ≠
      some (quantSemCore .exists_) ∧
    lowerS quantSemTable quantSemCtx (quantSemSurface .exists_) ≠
      some (quantSemCore .forall_) := by
  constructor <;> intro h <;> cases h

/-- forall を exists に誤 lowering すると False の意味を保存しない。 -/
theorem quant_sem_wrong_exists_not_preserved
    (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (Q : Prop) :
    ¬ (Sem quantSemTable Φ Ψ (quantSemEnv Q) (quantSemSurface .forall_) False ↔
      NaruSem.Call.Sem quantSemTable.Δ Φ Ψ (quantSemEnv Q) (quantSemCore .exists_) False) := by
  intro h
  have hc := h.mp (quant_sem_forall_false Φ Ψ Q).1
  exact (NaruSem.Call.Sem_unique hc (quant_sem_exists_true Φ Ψ Q).2).mpr True.intro

/-- exists を forall に誤 lowering しても True の意味を保存しない。 -/
theorem quant_sem_wrong_forall_not_preserved
    (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (Q : Prop) :
    ¬ (Sem quantSemTable Φ Ψ (quantSemEnv Q) (quantSemSurface .exists_) True ↔
      NaruSem.Call.Sem quantSemTable.Δ Φ Ψ (quantSemEnv Q) (quantSemCore .forall_) True) := by
  intro h
  have hc := h.mp (quant_sem_exists_true Φ Ψ Q).1
  exact (NaruSem.Call.Sem_unique (quant_sem_forall_false Φ Ψ Q).2 hc).mpr True.intro

def quantSemPred : Expr := .call {} (.var {} ["p"]) []

private theorem pred_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (Γ : SCtx) (hp : Γ "p" = none) :
    SpecSemEquiv quantSemTable Φ Ψ Γ quantSemPred (.call "M.p" []) := by
  intro ρ hΓ P
  have hρ : ρ "p" = none := by
    have hh : ρ.ctx "p" = none := by rw [← hΓ]; exact hp
    cases hhρ : ρ "p" <;> simp_all [SEnv.ctx]
  constructor
  · intro hs
    refine ⟨P, ?_, Iff.rfl⟩
    cases hs with
    | callVal _ hr hd _ _ _ _ =>
      simp [quantSemTable] at hr
      subst hr
      simp [quantSemTable, DeclSig.value?] at hd
    | callSpec _ hr hd hF ha harr =>
      simp [quantSemTable] at hr
      subst hr
      simp [quantSemTable] at hd
      subst hd
      simp [evalArgs] at ha
      subst ha
      change some [] = some _ at harr
      simp only [Option.some.injEq] at harr
      subst harr
      exact .callSpec rfl hF rfl
  · intro hc
    refine ⟨P, ?_, Iff.rfl⟩
    cases hc with
    | callVal hk _ _ _ =>
      simp [NaruSem.Call.isValueKey, NaruSem.Call.valueSig?, Table.Δ,
        quantSemTable, DeclSig.toSig, NaruSem.Call.Sig.value?] at hk
    | callSpec _ hF ha =>
      simp [NaruSem.Call.evalArgs] at ha
      subst ha
      exact .callSpec (by simp [headBound, hρ]) rfl rfl hF rfl rfl

/-- spec 呼出し本体も任意 Ψ で合成し、解釈が不在なら意味を補わない。 -/
theorem quant_sem_pred_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (q : Quant) (Q P : Prop) :
    Sem quantSemTable Φ Ψ (quantSemEnv Q) (.quant {} q quantSemBinders quantSemPred) P ↔
      NaruSem.Call.Sem quantSemTable.Δ Φ Ψ (quantSemEnv Q)
        (.quant q quantSemCoreBinders (.call "M.p" [])) P := by
  exact lowerS_quant_sem_iff quant_sem_binders_ctx quant_sem_binders_lower (by rfl) (by rfl)
    (by rfl) (pred_bridge Φ Ψ quantSemBodyCtx (by decide)) (quant_sem_ctx Q) P

private theorem pred_missing (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (P : Prop) :
    ¬ Sem quantSemTable Φ (fun _ => none) ρ quantSemPred P := by
  intro hs
  cases hs with
  | callVal _ hr hd _ _ _ _ =>
    simp [quantSemTable] at hr
    subst hr
    simp [quantSemTable, DeclSig.value?] at hd
  | callSpec _ _ _ hF _ _ => cases hF

/-- Nat / Bool の全範囲は非空。欠けた spec 解釈を vacuous な量化で補わない。 -/
theorem quant_sem_pred_missing (Φ : NaruSem.Call.FEnv) (q : Quant) (Q P : Prop) :
    (¬ Sem quantSemTable Φ (fun _ => none) (quantSemEnv Q)
      (.quant {} q quantSemBinders quantSemPred) P) ∧
    (¬ NaruSem.Call.Sem quantSemTable.Δ Φ (fun _ => none) (quantSemEnv Q)
      (.quant q quantSemCoreBinders (.call "M.p" [])) P) := by
  have hs : ¬ Sem quantSemTable Φ (fun _ => none) (quantSemEnv Q)
      (.quant {} q quantSemBinders quantSemPred) P := by
    intro h
    cases h with
    | forallCons ht h =>
      simp only [Ty.toTy?, Option.some.injEq] at ht
      cases ht
      have h0 : ∃ R, Sem quantSemTable Φ (fun _ => none)
          ((quantSemEnv Q).ext "q" (.val (.nat 0)))
          (.quant {} .forall_ quantSemBinders.tail quantSemPred) R := ⟨_, h (0 : Nat)⟩
      obtain ⟨R, h0⟩ := h0
      cases h0 with
      | forallCons ht h =>
        simp only [Ty.toTy?, Option.some.injEq] at ht
        cases ht
        have hf : ∃ R, Sem quantSemTable Φ (fun _ => none)
            (((quantSemEnv Q).ext "q" (.val (.nat 0))).ext "q" (.val (.bool false)))
            (.quant {} .forall_ [] quantSemPred) R := ⟨_, h false⟩
        obtain ⟨R, hf⟩ := hf
        cases hf with
        | quantNil hb => exact pred_missing Φ _ _ hb
    | existsCons ht h =>
      simp only [Ty.toTy?, Option.some.injEq] at ht
      cases ht
      have h0 : ∃ R, Sem quantSemTable Φ (fun _ => none)
          ((quantSemEnv Q).ext "q" (.val (.nat 0)))
          (.quant {} .exists_ quantSemBinders.tail quantSemPred) R := ⟨_, h (0 : Nat)⟩
      obtain ⟨R, h0⟩ := h0
      cases h0 with
      | existsCons ht h =>
        simp only [Ty.toTy?, Option.some.injEq] at ht
        cases ht
        have hf : ∃ R, Sem quantSemTable Φ (fun _ => none)
            (((quantSemEnv Q).ext "q" (.val (.nat 0))).ext "q" (.val (.bool false)))
            (.quant {} .exists_ [] quantSemPred) R := ⟨_, h false⟩
        obtain ⟨R, hf⟩ := hf
        cases hf with
        | quantNil hb => exact pred_missing Φ _ _ hb
  exact ⟨hs, fun hc => hs ((quant_sem_pred_arbitrary Φ _ q Q P).mpr hc)⟩

/-- 注釈なしの束縛は、表・量化種別・本体に依らず拒否する。 -/
theorem quant_sem_unannotated_rejected (T : Table) (Γ : SCtx) (q : Quant) (b : Expr) :
    Surf.lowerBinders [{ name := "x", ty := none, span := {} }] = none ∧
      lowerS T Γ (.quant {} q [{ name := "x", ty := none, span := {} }] b) = none := by
  exact ⟨rfl, rfl⟩

/-- 保存対象外 String 型の束縛を推測で Nat / Bool に落とさない。 -/
theorem quant_sem_unsupported_rejected (T : Table) (Γ : SCtx) (q : Quant) (b : Expr) :
    Surf.lowerBinders [{ name := "x", ty := some (.named {} ["String"] []), span := {} }] = none ∧
      lowerS T Γ (.quant {} q
        [{ name := "x", ty := some (.named {} ["String"] []), span := {} }] b) = none := by
  exact ⟨rfl, rfl⟩

end NaruSem.Surf.Call
