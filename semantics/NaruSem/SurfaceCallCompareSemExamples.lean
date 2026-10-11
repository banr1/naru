import NaruSem.SurfaceCallLowerSpecSem

/-! 比較・等値の局所保存の永続検体。Nat/Bool の全演算、入力呼出し、
命題変数と spec 呼出しを含む。命題の子対応は明示的に証明する。
全 spec 式の帰納保存や宣言群の完成は主張しない。 -/
namespace NaruSem.Surf.Call
open Naru

def compareSemTable : Table :=
  { resolve := fun p => if p = ["n"] then some "M.n" else
      if p = ["p"] then some "M.p" else none
    sig := fun k => if k = "M.n" then some (.input [] .nat) else
      if k = "M.p" then some (.spec []) else none }

def compareSemOp : CmpOp → String
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
def compareSemEqOp : EqOp → String
  | .eq => "==" | .ne => "!="
def compareSemLit : Val → Lit
  | .nat n => .nat n | .bool b => .bool b
def compareSemSurface (k : CmpOp) (a b : Val) : Expr :=
  .binop {} (compareSemOp k) (.lit {} (compareSemLit a)) (.lit {} (compareSemLit b))
def compareSemCore (k : CmpOp) (a b : Val) : Core.Expr :=
  .binop (compareSemOp k) (.lit (compareSemLit a) a.ty.toTyV) (.lit (compareSemLit b) b.ty.toTyV) a.ty.toTyV
def compareSemEqSurface (k : EqOp) (a b : Val) : Expr :=
  .binop {} (compareSemEqOp k) (.lit {} (compareSemLit a)) (.lit {} (compareSemLit b))
def compareSemEqCore (k : EqOp) (a b : Val) : Core.Expr :=
  .binop (compareSemEqOp k) (.lit (compareSemLit a) a.ty.toTyV) (.lit (compareSemLit b) b.ty.toTyV) a.ty.toTyV

private theorem cmp_parse (k : CmpOp) :
    BinOp.ofString? (compareSemOp k) = some (.cmp k) := by cases k <;> rfl
private theorem eq_parse (k : EqOp) :
    BinOp.ofString? (compareSemEqOp k) = some (.eq k) := by cases k <;> rfl

theorem compare_sem_nat_wt (k : CmpOp) (a b : Nat) :
    wtS compareSemTable SCtx.empty (compareSemSurface k (.nat a) (.nat b)) = some (.val .bool) := by
  cases k <;> rfl
theorem compare_sem_nat_lower (k : CmpOp) (a b : Nat) :
    lowerS compareSemTable SCtx.empty (compareSemSurface k (.nat a) (.nat b)) =
      some (compareSemCore k (.nat a) (.nat b)) := by cases k <;> rfl
theorem compare_sem_bool_wt (k : CmpOp) (a b : Bool) :
    wtS compareSemTable SCtx.empty (compareSemSurface k (.bool a) (.bool b)) = some (.val .bool) := by
  cases k <;> rfl
theorem compare_sem_bool_lower (k : CmpOp) (a b : Bool) :
    lowerS compareSemTable SCtx.empty (compareSemSurface k (.bool a) (.bool b)) =
      some (compareSemCore k (.bool a) (.bool b)) := by cases k <;> rfl
theorem compare_sem_eq_nat_wt (k : EqOp) (a b : Nat) :
    wtS compareSemTable SCtx.empty (compareSemEqSurface k (.nat a) (.nat b)) = some (.val .bool) := by
  cases k <;> rfl
theorem compare_sem_eq_nat_lower (k : EqOp) (a b : Nat) :
    lowerS compareSemTable SCtx.empty (compareSemEqSurface k (.nat a) (.nat b)) =
      some (compareSemEqCore k (.nat a) (.nat b)) := by cases k <;> rfl
theorem compare_sem_eq_bool_wt (k : EqOp) (a b : Bool) :
    wtS compareSemTable SCtx.empty (compareSemEqSurface k (.bool a) (.bool b)) = some (.val .bool) := by
  cases k <;> rfl
theorem compare_sem_eq_bool_lower (k : EqOp) (a b : Bool) :
    lowerS compareSemTable SCtx.empty (compareSemEqSurface k (.bool a) (.bool b)) =
      some (compareSemEqCore k (.bool a) (.bool b)) := by cases k <;> rfl

private theorem bool_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (b : Bool) : SpecSemEquiv compareSemTable Φ Ψ SCtx.empty
      (.lit {} (.bool b)) (.lit (.bool b) .bool) := by
  apply SpecSemEquiv.of_iff
  intro ρ _ P
  constructor <;> intro h <;> cases h <;> exact .lit

theorem compare_sem_nat_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects compareSemTable.Δ) (k : CmpOp) (a b : Nat)
    (ρ : SEnv) (hΓ : SCtx.empty = ρ.ctx) (P : Prop) :
    Sem compareSemTable Φ Ψ ρ (compareSemSurface k (.nat a) (.nat b)) P ↔
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemCore k (.nat a) (.nat b)) P := by
  exact lowerS_cmp_sem_iff (compare_sem_nat_wt k a b) (cmp_parse k)
    (by rfl) (by rfl) (by rfl) (by rfl) (compare_sem_nat_lower k a b) hΦ hΓ P

theorem compare_sem_bool_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects compareSemTable.Δ) (k : CmpOp) (a b : Bool)
    (ρ : SEnv) (hΓ : SCtx.empty = ρ.ctx) (P : Prop) :
    Sem compareSemTable Φ Ψ ρ (compareSemSurface k (.bool a) (.bool b)) P ↔
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemCore k (.bool a) (.bool b)) P := by
  exact lowerS_cmp_sem_iff (compare_sem_bool_wt k a b) (cmp_parse k)
    (by rfl) (by rfl) (by rfl) (by rfl) (compare_sem_bool_lower k a b) hΦ hΓ P

theorem compare_sem_eq_nat_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects compareSemTable.Δ) (k : EqOp) (a b : Nat)
    (ρ : SEnv) (hΓ : SCtx.empty = ρ.ctx) (P : Prop) :
    Sem compareSemTable Φ Ψ ρ (compareSemEqSurface k (.nat a) (.nat b)) P ↔
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemEqCore k (.nat a) (.nat b)) P := by
  exact lowerS_eqNat_sem_iff (compare_sem_eq_nat_wt k a b) (eq_parse k)
    (by rfl) (by rfl) (by rfl) (by rfl) (compare_sem_eq_nat_lower k a b) hΦ hΓ P

theorem compare_sem_eq_bool_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (k : EqOp) (a b : Bool) (ρ : SEnv) (hΓ : SCtx.empty = ρ.ctx) (P : Prop) :
    Sem compareSemTable Φ Ψ ρ (compareSemEqSurface k (.bool a) (.bool b)) P ↔
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemEqCore k (.bool a) (.bool b)) P := by
  exact lowerS_eqForm_sem_iff (compare_sem_eq_bool_wt k a b) (eq_parse k)
    (by simp [wtR, compareSemLit]) (by rfl) (by rfl) (compare_sem_eq_bool_lower k a b)
    (by intro ρ _ n h; cases h) (bool_bridge Φ Ψ a) (bool_bridge Φ Ψ b) hΓ P

theorem compare_sem_nat_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (k : CmpOp) (a b : Nat) (ρ : SEnv) :
    Sem compareSemTable Φ Ψ ρ (compareSemSurface k (.nat a) (.nat b)) (k.propNat a b) ∧
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemCore k (.nat a) (.nat b))
        (k.propNat a b) := ⟨.cmpNat (cmp_parse k) rfl rfl, .cmpNat (cmp_parse k) rfl rfl⟩
theorem compare_sem_bool_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (k : CmpOp) (a b : Bool) (ρ : SEnv) :
    Sem compareSemTable Φ Ψ ρ (compareSemSurface k (.bool a) (.bool b))
      (k.evalBool a b = true) ∧
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemCore k (.bool a) (.bool b))
        (k.evalBool a b = true) :=
  ⟨.cmpBool (cmp_parse k) rfl rfl, .cmpBool (cmp_parse k) rfl rfl⟩
theorem compare_sem_eq_nat_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (k : EqOp) (a b : Nat) (ρ : SEnv) :
    Sem compareSemTable Φ Ψ ρ (compareSemEqSurface k (.nat a) (.nat b)) (k.propNat a b) ∧
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemEqCore k (.nat a) (.nat b))
        (k.propNat a b) := ⟨.eqNat (eq_parse k) rfl rfl, .eqNat (eq_parse k) rfl rfl⟩
theorem compare_sem_eq_bool_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (k : EqOp) (a b : Bool) (ρ : SEnv) :
    Sem compareSemTable Φ Ψ ρ (compareSemEqSurface k (.bool a) (.bool b))
      (k.propIff (a = true) (b = true)) ∧
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemEqCore k (.bool a) (.bool b))
        (k.propIff (a = true) (b = true)) := ⟨.eqForm (eq_parse k) .lit .lit,
          .eqForm (eq_parse k) .lit .lit⟩

def compareSemCtx : SCtx := SCtx.empty.ext "q" .prop
def compareSemEnv (Q : Prop) : SEnv := SEnv.empty.ext "q" (.prop Q)
def compareSemPred : Expr := .call {} (.var {} ["p"]) []
def compareSemForm (k : EqOp) : Expr :=
  .binop {} (compareSemEqOp k) (.var {} ["q"]) compareSemPred
def compareSemCoreForm (k : EqOp) : Core.Expr :=
  .binop (compareSemEqOp k) (.var "q") (.call "M.p" []) .bool

private theorem name_absent (ρ : SEnv) (hΓ : compareSemCtx = ρ.ctx)
    (x : String) (hx : x ≠ "q") : ρ x = none := by
  have hp : ρ.ctx x = none := by rw [← hΓ]; simp [compareSemCtx, SCtx.ext, SCtx.empty, hx]
  cases h : ρ x <;> simp_all [SEnv.ctx]
private theorem prop_noNat (Φ : NaruSem.Call.FEnv) :
    ∀ ρ : SEnv, compareSemCtx = ρ.ctx → ∀ n,
      eval compareSemTable Φ ρ (.var {} ["q"]) ≠ some (.nat n) := by
  intro ρ hΓ n he
  have hq : ρ.ctx "q" = some .prop := by rw [← hΓ]; rfl
  cases hs : ρ "q" with
  | none => simp [eval, hs] at he
  | some s =>
    cases s with
    | prop P => simp [eval, hs] at he
    | val v =>
      have ht : SVal.ty (.val v) = .prop := by simpa [SEnv.ctx, hs] using hq
      cases v <;> cases ht
private theorem var_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SpecSemEquiv compareSemTable Φ Ψ compareSemCtx (.var {} ["q"]) (.var "q") := by
  apply SpecSemEquiv.of_iff
  intro ρ _ P
  constructor <;> intro h <;> cases h with
  | varVal h => exact .varVal h
  | varProp h => exact .varProp h
private theorem pred_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SpecSemEquiv compareSemTable Φ Ψ compareSemCtx compareSemPred (.call "M.p" []) := by
  apply SpecSemEquiv.of_iff
  intro ρ hΓ P
  constructor
  · intro hs
    cases hs with
    | callVal _ hr hd _ _ _ _ =>
      simp [compareSemTable] at hr
      subst hr
      simp [compareSemTable, DeclSig.value?] at hd
    | callSpec _ hr hd hF ha harr =>
      simp [compareSemTable] at hr
      subst hr
      simp [compareSemTable] at hd
      subst hd
      simp [evalArgs] at ha
      subst ha
      change some [] = some _ at harr
      simp only [Option.some.injEq] at harr
      subst harr
      exact .callSpec rfl hF rfl
  · intro hc
    cases hc with
    | callVal hk _ _ _ =>
      simp [NaruSem.Call.isValueKey, NaruSem.Call.valueSig?, Table.Δ,
        compareSemTable, DeclSig.toSig, NaruSem.Call.Sig.value?] at hk
    | callSpec _ hF ha =>
      simp [NaruSem.Call.evalArgs] at ha
      subst ha
      exact .callSpec (by simp [headBound, name_absent ρ hΓ "p" (by decide)])
        rfl rfl hF rfl rfl

theorem compare_sem_ctx (Q : Prop) : compareSemCtx = (compareSemEnv Q).ctx := by
  rw [compareSemEnv, SEnv.ctx_ext]
  rfl
theorem compare_sem_form_wt (k : EqOp) :
    wtS compareSemTable compareSemCtx (compareSemForm k) = some .prop := by cases k <;> rfl
theorem compare_sem_form_lower (k : EqOp) :
    lowerS compareSemTable compareSemCtx (compareSemForm k) = some (compareSemCoreForm k) := by
  cases k <;> rfl
theorem compare_sem_form_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (k : EqOp) :
    SpecSemEquiv compareSemTable Φ Ψ compareSemCtx (compareSemForm k) (compareSemCoreForm k) :=
  lowerS_eqForm_equiv (eq_parse k) (prop_noNat Φ) (var_bridge Φ Ψ) (pred_bridge Φ Ψ)
theorem compare_sem_form_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (k : EqOp) (ρ : SEnv) (hΓ : compareSemCtx = ρ.ctx) (P : Prop) :
    Sem compareSemTable Φ Ψ ρ (compareSemForm k) P ↔
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemCoreForm k) P :=
  lowerS_eqForm_sem_iff (compare_sem_form_wt k) (eq_parse k)
    (by simp [wtR, compareSemCtx, SCtx.ext]) (by rfl) (by rfl) (compare_sem_form_lower k)
    (prop_noNat Φ) (var_bridge Φ Ψ) (pred_bridge Φ Ψ) hΓ P
theorem compare_sem_form_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (k : EqOp) (Q : Prop) (F : List Val → Prop) (hF : Ψ "M.p" = some F) :
    Sem compareSemTable Φ Ψ (compareSemEnv Q) (compareSemForm k) (k.propIff Q (F [])) ∧
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ (compareSemEnv Q) (compareSemCoreForm k)
        (k.propIff Q (F [])) := by
  have hs : Sem compareSemTable Φ Ψ (compareSemEnv Q) (compareSemForm k) (k.propIff Q (F [])) :=
    .eqForm (eq_parse k) (.varProp rfl) (.callSpec rfl rfl rfl hF rfl rfl)
  exact ⟨hs, (compare_sem_form_arbitrary Φ Ψ k _ (compare_sem_ctx Q) _).mp hs⟩

private theorem pred_missing (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hm : Ψ "M.p" = none) (ρ : SEnv) (P : Prop) :
    ¬ Sem compareSemTable Φ Ψ ρ compareSemPred P := by
  intro h
  cases h with
  | callVal _ hr hd _ _ _ _ =>
    simp [compareSemTable] at hr
    subst hr
    simp [compareSemTable, DeclSig.value?] at hd
  | callSpec _ hr _ hF _ _ =>
    simp [compareSemTable] at hr
    subst hr
    rw [hm] at hF
    cases hF

theorem compare_sem_form_missing (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hm : Ψ "M.p" = none) (k : EqOp) (ρ : SEnv) (hΓ : compareSemCtx = ρ.ctx) (P : Prop) :
    (¬ Sem compareSemTable Φ Ψ ρ (compareSemForm k) P) ∧
      (¬ NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemCoreForm k) P) := by
  have hs : ¬ Sem compareSemTable Φ Ψ ρ (compareSemForm k) P := by
    intro h
    cases h with
    | logic hk => rw [eq_parse k] at hk; cases hk
    | eqNat _ hl _ => exact prop_noNat Φ ρ hΓ _ hl
    | eqForm _ _ hr => exact pred_missing Φ Ψ hm ρ _ hr
    | cmpNat hk => rw [eq_parse k] at hk; cases hk
    | cmpBool hk => rw [eq_parse k] at hk; cases hk
  exact ⟨hs, fun hc => hs ((compare_sem_form_arbitrary Φ Ψ k ρ hΓ P).mpr hc)⟩

/-! 入力呼出しを runtime の子式として使用し、任意解釈で局所入口を適用する。 -/
def compareSemInput : Expr := .call {} (.var {} ["n"]) []
def compareSemInputCmp (k : CmpOp) (n : Nat) : Expr :=
  .binop {} (compareSemOp k) compareSemInput (.lit {} (.nat n))
def compareSemCoreInputCmp (k : CmpOp) (n : Nat) : Core.Expr :=
  .binop (compareSemOp k) (.call "M.n" []) (.lit (.nat n) .nat) .nat
def compareSemInputEq (k : EqOp) (n : Nat) : Expr :=
  .binop {} (compareSemEqOp k) compareSemInput (.lit {} (.nat n))
def compareSemCoreInputEq (k : EqOp) (n : Nat) : Core.Expr :=
  .binop (compareSemEqOp k) (.call "M.n" []) (.lit (.nat n) .nat) .nat

/-- 任意の入力値を返す署名適合解釈。局所保存の runtime 前提は非空虚。 -/
def compareSemInterpretation (m : Nat) : NaruSem.Call.FEnv :=
  fun k => if k = "M.n" then some (fun _ => some (.nat m)) else none
theorem compare_sem_interpretation_respects (m : Nat) :
    (compareSemInterpretation m).Respects compareSemTable.Δ := by
  intro k ps t hs
  by_cases hn : k = "M.n"
  · subst k
    simp [NaruSem.Call.valueSig?, Table.Δ, compareSemTable, DeclSig.toSig,
      NaruSem.Call.Sig.value?] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨fun _ => some (.nat m), rfl, fun _ _ => ⟨.nat m, rfl, rfl⟩⟩
  · by_cases hp : k = "M.p"
    · simp [NaruSem.Call.valueSig?, Table.Δ, compareSemTable, hp,
        DeclSig.toSig, NaruSem.Call.Sig.value?] at hs
    · simp [NaruSem.Call.valueSig?, Table.Δ, compareSemTable, hn, hp] at hs

theorem compare_sem_input_cmp_wt (k : CmpOp) (n : Nat) :
    wtS compareSemTable compareSemCtx (compareSemInputCmp k n) = some (.val .bool) := by
  cases k <;> rfl
theorem compare_sem_input_cmp_lower (k : CmpOp) (n : Nat) :
    lowerS compareSemTable compareSemCtx (compareSemInputCmp k n) =
      some (compareSemCoreInputCmp k n) := by cases k <;> rfl
theorem compare_sem_input_eq_wt (k : EqOp) (n : Nat) :
    wtS compareSemTable compareSemCtx (compareSemInputEq k n) = some (.val .bool) := by
  cases k <;> rfl
theorem compare_sem_input_eq_lower (k : EqOp) (n : Nat) :
    lowerS compareSemTable compareSemCtx (compareSemInputEq k n) =
      some (compareSemCoreInputEq k n) := by cases k <;> rfl

theorem compare_sem_input_cmp_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects compareSemTable.Δ) (k : CmpOp) (n : Nat)
    (ρ : SEnv) (hΓ : compareSemCtx = ρ.ctx) (P : Prop) :
    Sem compareSemTable Φ Ψ ρ (compareSemInputCmp k n) P ↔
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemCoreInputCmp k n) P :=
  lowerS_cmp_sem_iff (compare_sem_input_cmp_wt k n) (cmp_parse k)
    (by rfl) (by rfl) (by rfl) (by rfl) (compare_sem_input_cmp_lower k n) hΦ hΓ P
theorem compare_sem_input_eq_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects compareSemTable.Δ) (k : EqOp) (n : Nat)
    (ρ : SEnv) (hΓ : compareSemCtx = ρ.ctx) (P : Prop) :
    Sem compareSemTable Φ Ψ ρ (compareSemInputEq k n) P ↔
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ ρ (compareSemCoreInputEq k n) P :=
  lowerS_eqNat_sem_iff (compare_sem_input_eq_wt k n) (eq_parse k)
    (by rfl) (by rfl) (by rfl) (by rfl) (compare_sem_input_eq_lower k n) hΦ hΓ P

private theorem input_eval (Φ : NaruSem.Call.FEnv) (f : List Val → Option Val)
    (hf : Φ "M.n" = some f) (m : Nat) (hm : f [] = some (.nat m)) (Q : Prop) :
    eval compareSemTable Φ (compareSemEnv Q) compareSemInput = some (.nat m) := by
  simpa [compareSemInput, eval, headBound, compareSemEnv, SEnv.ext, SEnv.empty,
    callVal, compareSemTable, evalArgs, arrange, assign, allSome, DeclSig.value?, hf] using hm
private theorem core_input_eval (Φ : NaruSem.Call.FEnv) (f : List Val → Option Val)
    (hf : Φ "M.n" = some f) (m : Nat) (hm : f [] = some (.nat m)) (Q : Prop) :
    NaruSem.Call.eval Φ (compareSemEnv Q).vals (.call "M.n" []) = some (.nat m) := by
  simpa [NaruSem.Call.eval, NaruSem.Call.evalArgs, hf] using hm

theorem compare_sem_input_cmp_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (f : List Val → Option Val) (hf : Φ "M.n" = some f) (k : CmpOp) (m n : Nat)
    (hm : f [] = some (.nat m)) (Q : Prop) :
    Sem compareSemTable Φ Ψ (compareSemEnv Q) (compareSemInputCmp k n) (k.propNat m n) ∧
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ (compareSemEnv Q) (compareSemCoreInputCmp k n)
        (k.propNat m n) :=
  ⟨.cmpNat (cmp_parse k) (input_eval Φ f hf m hm Q) rfl,
    .cmpNat (cmp_parse k) (core_input_eval Φ f hf m hm Q) rfl⟩
theorem compare_sem_input_eq_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (f : List Val → Option Val) (hf : Φ "M.n" = some f) (k : EqOp) (m n : Nat)
    (hm : f [] = some (.nat m)) (Q : Prop) :
    Sem compareSemTable Φ Ψ (compareSemEnv Q) (compareSemInputEq k n) (k.propNat m n) ∧
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ (compareSemEnv Q) (compareSemCoreInputEq k n)
        (k.propNat m n) :=
  ⟨.eqNat (eq_parse k) (input_eval Φ f hf m hm Q) rfl,
    .eqNat (eq_parse k) (core_input_eval Φ f hf m hm Q) rfl⟩

/-! 等号の境界、Nat=0、Bool の全4組を kernel 内で実際に読む。 -/
theorem compare_sem_nat_boundary :
    CmpOp.lt.propNat 0 0 ↔ False := by simp [CmpOp.propNat]
theorem compare_sem_nat_inclusive_boundary :
    (CmpOp.le.propNat 0 0 ↔ True) ∧ (CmpOp.ge.propNat 0 0 ↔ True) := by
  simp [CmpOp.propNat]
theorem compare_sem_bool_boundary (a b : Bool) :
    (CmpOp.lt.evalBool a b = true ↔ a = false ∧ b = true) ∧
    (CmpOp.le.evalBool a b = true ↔ a = false ∨ b = true) ∧
    (CmpOp.gt.evalBool a b = true ↔ a = true ∧ b = false) ∧
    (CmpOp.ge.evalBool a b = true ↔ a = true ∨ b = false) := by
  cases a <;> cases b <;> decide
theorem compare_sem_bool_eq_boundary (k : EqOp) (a b : Bool) :
    k.propIff (a = true) (b = true) ↔
      if k = .eq then a = b else a ≠ b := by
  cases k <;> cases a <;> cases b <;> simp [EqOp.propIff]

theorem compare_sem_mixed_cmp_rejected (k : CmpOp) (n : Nat) (b : Bool) :
    wtS compareSemTable SCtx.empty (compareSemSurface k (.nat n) (.bool b)) = none ∧
      wtS compareSemTable SCtx.empty (compareSemSurface k (.bool b) (.nat n)) = none := by
  cases k <;> exact ⟨rfl, rfl⟩
theorem compare_sem_mixed_eq_rejected (k : EqOp) (n : Nat) (b : Bool) :
    wtS compareSemTable SCtx.empty (compareSemEqSurface k (.nat n) (.bool b)) = none ∧
      wtS compareSemTable SCtx.empty (compareSemEqSurface k (.bool b) (.nat n)) = none := by
  cases k <;> exact ⟨rfl, rfl⟩

def compareSemWrongEqCore : Core.Expr :=
  .binop "!=" (.lit (.nat 0) .nat) (.lit (.nat 0) .nat) .nat
def compareSemWrongCmpCore : Core.Expr :=
  .binop ">" (.lit (.nat 0) .nat) (.lit (.nat 1) .nat) .nat
theorem compare_sem_wrong_eq_wt :
    NaruSem.Call.wtS compareSemTable.Δ SCtx.empty compareSemWrongEqCore = some (.val .bool) := rfl
theorem compare_sem_wrong_cmp_wt :
    NaruSem.Call.wtS compareSemTable.Δ SCtx.empty compareSemWrongCmpCore = some (.val .bool) := rfl
theorem compare_sem_wrong_eq_not_lower :
    lowerS compareSemTable SCtx.empty (compareSemEqSurface .eq (.nat 0) (.nat 0)) ≠
      some compareSemWrongEqCore := by
  intro h
  have he := Option.some.inj ((compare_sem_eq_nat_lower .eq 0 0).symm.trans h)
  have hop := congrArg (fun e : Core.Expr => match e with | .binop op _ _ _ => op | _ => "") he
  exact (by decide : "==" ≠ "!=") hop
theorem compare_sem_wrong_cmp_not_lower :
    lowerS compareSemTable SCtx.empty (compareSemSurface .lt (.nat 0) (.nat 1)) ≠
      some compareSemWrongCmpCore := by
  intro h
  have he := Option.some.inj ((compare_sem_nat_lower .lt 0 1).symm.trans h)
  have hop := congrArg (fun e : Core.Expr => match e with | .binop op _ _ _ => op | _ => "") he
  exact (by decide : "<" ≠ ">") hop

/-- 型の等しい != Core を == の lowering 出力の代わりに置くと保存は失われる。 -/
theorem compare_sem_wrong_eq_not_preserved (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    ¬ (Sem compareSemTable Φ Ψ SEnv.empty (compareSemEqSurface .eq (.nat 0) (.nat 0)) (0 = 0) ↔
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ SEnv.empty compareSemWrongEqCore (0 = 0)) := by
  have hs := (compare_sem_eq_nat_meaning Φ Ψ .eq 0 0 SEnv.empty).1
  have hw : NaruSem.Call.Sem compareSemTable.Δ Φ Ψ SEnv.empty compareSemWrongEqCore (0 ≠ 0) :=
    .eqNat (k := .ne) rfl rfl rfl
  intro h
  have hu := NaruSem.Call.Sem_unique hw (h.mp hs)
  exact (hu.mpr rfl) rfl

/-- 比較の向きを交換した適格な Core にも、閉じた kernel 反例がある。 -/
theorem compare_sem_wrong_cmp_not_preserved (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    ¬ (Sem compareSemTable Φ Ψ SEnv.empty (compareSemSurface .lt (.nat 0) (.nat 1)) (0 < 1) ↔
      NaruSem.Call.Sem compareSemTable.Δ Φ Ψ SEnv.empty compareSemWrongCmpCore (0 < 1)) := by
  have hs := (compare_sem_nat_meaning Φ Ψ .lt 0 1 SEnv.empty).1
  have hw : NaruSem.Call.Sem compareSemTable.Δ Φ Ψ SEnv.empty compareSemWrongCmpCore (0 > 1) :=
    .cmpNat (k := .gt) rfl rfl rfl
  intro h
  have hu := NaruSem.Call.Sem_unique hw (h.mp hs)
  exact (by decide : ¬ (0 > 1)) (hu.mpr (by decide))

end NaruSem.Surf.Call
