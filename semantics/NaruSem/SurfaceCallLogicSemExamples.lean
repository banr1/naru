import NaruSem.SurfaceCallLowerSpecSem

/-! 論理演算・否定・Bool/Prop 条件 if の非空虚な局所合成検体。
子対応は個別に証明し、全 spec 式や宣言群の保存は主張しない。 -/
namespace NaruSem.Surf.Call
open Naru

def logicSemTable : Table :=
  { resolve := fun p => if p = ["p"] then some "M.p" else none
    sig := fun k => if k = "M.p" then some (.spec []) else none }
def logicSemCtx : SCtx := (SCtx.empty.ext "x" (.val .bool)).ext "q" .prop
def logicSemEnv (b : Bool) (Q : Prop) : SEnv :=
  (SEnv.empty.ext "x" (.val (.bool b))).ext "q" (.prop Q)
def logicSemPred : Expr := .call {} (.var {} ["p"]) []
def logicSemDisj : Expr := .binop {} "||" (.var {} ["q"]) logicSemPred
def logicSemCoreDisj : Core.Expr := .binop "||" (.var "q") (.call "M.p" []) .bool
def logicSemOp : LogicOp → String
  | .and => "&&"
  | .or => "||"
  | .implies => "implies"
def logicSemSurface (k : LogicOp) : Expr :=
  .binop {} (logicSemOp k) (.var {} ["x"]) logicSemDisj
def logicSemCore (k : LogicOp) : Core.Expr :=
  .binop (logicSemOp k) (.var "x") logicSemCoreDisj .bool
def logicSemNot : Expr := .unop {} "!" (logicSemSurface .and)
def logicSemCoreNot : Core.Expr := .unop "!" (logicSemCore .and)
def logicSemIte : Bool → Expr
  | true => .ite {} (.var {} ["x"]) logicSemDisj (.unop {} "!" (.var {} ["q"]))
  | false => .ite {} (.var {} ["q"]) (.var {} ["x"]) logicSemPred
def logicSemCoreIte : Bool → Core.Expr
  | true => .ite (.var "x") logicSemCoreDisj (.unop "!" (.var "q"))
  | false => .ite (.var "q") (.var "x") (.call "M.p" [])

private theorem var_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (x : String) : SpecSemEquiv logicSemTable Φ Ψ logicSemCtx (.var {} [x]) (.var x) := by
  apply SpecSemEquiv.of_iff
  intro ρ _ P
  constructor <;> intro h <;> cases h with
  | varVal h => exact .varVal h
  | varProp h => exact .varProp h

private theorem absent (ρ : SEnv) (hΓ : logicSemCtx = ρ.ctx) : ρ "p" = none := by
  have hp : ρ.ctx "p" = none := by rw [← hΓ]; rfl
  cases h : ρ "p" <;> simp_all [SEnv.ctx]

private theorem pred_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SpecSemEquiv logicSemTable Φ Ψ logicSemCtx logicSemPred (.call "M.p" []) := by
  apply SpecSemEquiv.of_iff
  intro ρ hΓ P
  constructor
  · intro hs
    cases hs with
    | callVal _ hr hd _ _ _ _ =>
      simp [logicSemTable] at hr
      subst hr
      simp [logicSemTable, DeclSig.value?] at hd
    | callSpec _ hr hd hF ha harr =>
      simp [logicSemTable] at hr
      subst hr
      simp [logicSemTable] at hd
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
        logicSemTable, DeclSig.toSig, NaruSem.Call.Sig.value?] at hk
    | callSpec _ hF ha =>
      simp [NaruSem.Call.evalArgs] at ha
      subst ha
      exact .callSpec (by simp [headBound, absent ρ hΓ]) rfl rfl hF rfl rfl

private theorem disj_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SpecSemEquiv logicSemTable Φ Ψ logicSemCtx logicSemDisj logicSemCoreDisj :=
  lowerS_logic_equiv rfl (var_bridge Φ Ψ "q") (pred_bridge Φ Ψ)

private theorem op_parse (k : LogicOp) :
    BinOp.ofString? (logicSemOp k) = some (.logic k) := by cases k <;> rfl

private theorem pred_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (ρ : SEnv) (hΓ : logicSemCtx = ρ.ctx) (F : List Val → Prop)
    (hF : Ψ "M.p" = some F) : Sem logicSemTable Φ Ψ ρ logicSemPred (F []) :=
  .callSpec (by simp [headBound, absent ρ hΓ]) rfl rfl hF rfl rfl

private theorem pred_missing (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hm : Ψ "M.p" = none) (ρ : SEnv) (P : Prop) :
    ¬ Sem logicSemTable Φ Ψ ρ logicSemPred P := by
  intro h
  cases h with
  | callVal _ hr hd _ _ _ _ =>
    simp [logicSemTable] at hr
    subst hr
    simp [logicSemTable, DeclSig.value?] at hd
  | callSpec _ hr _ hF _ _ =>
    simp [logicSemTable] at hr
    subst hr
    rw [hm] at hF
    cases hF

theorem logic_sem_ctx (b : Bool) (Q : Prop) : logicSemCtx = (logicSemEnv b Q).ctx := by
  rw [logicSemEnv, SEnv.ctx_ext, SEnv.ctx_ext]
  rfl

theorem logic_sem_wt (k : LogicOp) :
    wtS logicSemTable logicSemCtx (logicSemSurface k) = some .prop := by cases k <;> rfl

theorem logic_sem_lower (k : LogicOp) :
    lowerS logicSemTable logicSemCtx (logicSemSurface k) = some (logicSemCore k) := by
  cases k <;> rfl

theorem logic_sem_not_wt : wtS logicSemTable logicSemCtx logicSemNot = some .prop := rfl
theorem logic_sem_not_lower : lowerS logicSemTable logicSemCtx logicSemNot = some logicSemCoreNot := rfl

theorem logic_sem_ite_wt (isBool : Bool) :
    wtS logicSemTable logicSemCtx (logicSemIte isBool) = some .prop := by cases isBool <;> rfl

theorem logic_sem_ite_lower (isBool : Bool) :
    lowerS logicSemTable logicSemCtx (logicSemIte isBool) = some (logicSemCoreIte isBool) := by
  cases isBool <;> rfl

theorem logic_sem_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (k : LogicOp) :
    SpecSemEquiv logicSemTable Φ Ψ logicSemCtx (logicSemSurface k) (logicSemCore k) :=
  lowerS_logic_equiv (op_parse k) (var_bridge Φ Ψ "x") (disj_bridge Φ Ψ)

theorem logic_sem_not_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SpecSemEquiv logicSemTable Φ Ψ logicSemCtx logicSemNot logicSemCoreNot :=
  lowerS_not_equiv (logic_sem_bridge Φ Ψ .and)

theorem logic_sem_ite_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (isBool : Bool) :
    SpecSemEquiv logicSemTable Φ Ψ logicSemCtx (logicSemIte isBool) (logicSemCoreIte isBool) := by
  cases isBool with
  | false => exact lowerS_ite_equiv (var_bridge Φ Ψ "q") (var_bridge Φ Ψ "x") (pred_bridge Φ Ψ)
  | true =>
    exact lowerS_ite_equiv (var_bridge Φ Ψ "x") (disj_bridge Φ Ψ)
      (lowerS_not_equiv (var_bridge Φ Ψ "q"))

/-- Bool と Prop の local 変数、spec 呼出しを混ぜ、任意環境・任意解釈で三演算を合成。 -/
theorem logic_sem_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (k : LogicOp) (ρ : SEnv) (hΓ : logicSemCtx = ρ.ctx) (P : Prop) :
    Sem logicSemTable Φ Ψ ρ (logicSemSurface k) P ↔
      NaruSem.Call.Sem logicSemTable.Δ Φ Ψ ρ (logicSemCore k) P := by
  exact lowerS_logic_sem_iff (logic_sem_wt k) (op_parse k) (by rfl) (by rfl)
    (logic_sem_lower k) (var_bridge Φ Ψ "x") (disj_bridge Φ Ψ) hΓ P

theorem logic_sem_not_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (ρ : SEnv) (hΓ : logicSemCtx = ρ.ctx) (P : Prop) :
    Sem logicSemTable Φ Ψ ρ logicSemNot P ↔
      NaruSem.Call.Sem logicSemTable.Δ Φ Ψ ρ logicSemCoreNot P :=
  lowerS_not_sem_iff logic_sem_not_wt (logic_sem_lower .and) logic_sem_not_lower
    (logic_sem_bridge Φ Ψ .and) hΓ P

theorem logic_sem_ite_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (isBool : Bool) (ρ : SEnv) (hΓ : logicSemCtx = ρ.ctx) (P : Prop) :
    Sem logicSemTable Φ Ψ ρ (logicSemIte isBool) P ↔
      NaruSem.Call.Sem logicSemTable.Δ Φ Ψ ρ (logicSemCoreIte isBool) P := by
  cases isBool with
  | false =>
    exact lowerS_ite_sem_iff (logic_sem_ite_wt false) (by rfl) (by rfl) (by rfl)
      (logic_sem_ite_lower false) (var_bridge Φ Ψ "q") (var_bridge Φ Ψ "x") (pred_bridge Φ Ψ) hΓ P
  | true =>
    exact lowerS_ite_sem_iff (logic_sem_ite_wt true) (by rfl) (by rfl) (by rfl)
      (logic_sem_ite_lower true) (var_bridge Φ Ψ "x") (disj_bridge Φ Ψ)
      (lowerS_not_equiv (var_bridge Φ Ψ "q")) hΓ P

theorem logic_sem_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (k : LogicOp) (ρ : SEnv) (hΓ : logicSemCtx = ρ.ctx) (b : Bool) (Q : Prop)
    (hx : ρ "x" = some (.val (.bool b))) (hq : ρ "q" = some (.prop Q))
    (F : List Val → Prop) (hF : Ψ "M.p" = some F) :
    Sem logicSemTable Φ Ψ ρ (logicSemSurface k) (k.prop (b = true) (Q ∨ F [])) ∧
      NaruSem.Call.Sem logicSemTable.Δ Φ Ψ ρ (logicSemCore k) (k.prop (b = true) (Q ∨ F [])) := by
  have hd : Sem logicSemTable Φ Ψ ρ logicSemDisj (Q ∨ F []) := by
    change Sem logicSemTable Φ Ψ ρ (.binop {} "||" (.var {} ["q"]) logicSemPred) _
    exact .logic (k := .or) rfl (.varProp hq) (pred_meaning Φ Ψ ρ hΓ F hF)
  have hs : Sem logicSemTable Φ Ψ ρ (logicSemSurface k) (k.prop (b = true) (Q ∨ F [])) :=
    .logic (op_parse k) (.varVal hx) hd
  exact ⟨hs, (logic_sem_arbitrary Φ Ψ k ρ hΓ _).mp hs⟩

theorem logic_sem_not_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (b : Bool) (Q : Prop) (F : List Val → Prop) (hF : Ψ "M.p" = some F) :
    Sem logicSemTable Φ Ψ (logicSemEnv b Q) logicSemNot (¬ (b = true ∧ (Q ∨ F []))) ∧
      NaruSem.Call.Sem logicSemTable.Δ Φ Ψ (logicSemEnv b Q) logicSemCoreNot
        (¬ (b = true ∧ (Q ∨ F []))) := by
  have hs : Sem logicSemTable Φ Ψ (logicSemEnv b Q) logicSemNot
      (¬ (b = true ∧ (Q ∨ F []))) :=
    .not (logic_sem_meaning Φ Ψ .and (logicSemEnv b Q) (logic_sem_ctx b Q)
      b Q rfl rfl F hF).1
  exact ⟨hs, (logic_sem_not_arbitrary Φ Ψ _ (logic_sem_ctx b Q) _).mp hs⟩

def logicSemIteMeaning (isBool b : Bool) (Q R : Prop) : Prop :=
  if isBool then ((b = true → Q ∨ R) ∧ (¬ (b = true) → ¬ Q))
  else ((Q → b = true) ∧ (¬ Q → R))

theorem logic_sem_ite_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (isBool b : Bool) (Q : Prop) (F : List Val → Prop) (hF : Ψ "M.p" = some F) :
    Sem logicSemTable Φ Ψ (logicSemEnv b Q) (logicSemIte isBool) (logicSemIteMeaning isBool b Q (F [])) ∧
      NaruSem.Call.Sem logicSemTable.Δ Φ Ψ (logicSemEnv b Q) (logicSemCoreIte isBool)
        (logicSemIteMeaning isBool b Q (F [])) := by
  have hp := pred_meaning Φ Ψ (logicSemEnv b Q) (logic_sem_ctx b Q) F hF
  have hd : Sem logicSemTable Φ Ψ (logicSemEnv b Q) logicSemDisj (Q ∨ F []) := by
    change Sem logicSemTable Φ Ψ (logicSemEnv b Q) (.binop {} "||" (.var {} ["q"]) logicSemPred) _
    exact .logic (k := .or) rfl (.varProp rfl) hp
  have hs : Sem logicSemTable Φ Ψ (logicSemEnv b Q) (logicSemIte isBool)
      (logicSemIteMeaning isBool b Q (F [])) := by
    cases isBool with
    | false => exact .ite (.varProp rfl) (.varVal rfl) hp
    | true => exact .ite (.varVal rfl) hd (.not (.varProp rfl))
  exact ⟨hs, (logic_sem_ite_arbitrary Φ Ψ isBool _ (logic_sem_ctx b Q) _).mp hs⟩

private theorem disj_missing (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hm : Ψ "M.p" = none) (ρ : SEnv) (P : Prop) :
    ¬ Sem logicSemTable Φ Ψ ρ logicSemDisj P := by
  intro h
  cases h with
  | logic _ _ hr => exact pred_missing Φ Ψ hm ρ _ hr
  | eqNat hk => cases hk
  | eqForm hk => cases hk
  | cmpNat hk => cases hk
  | cmpBool hk => cases hk

theorem logic_sem_missing (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hm : Ψ "M.p" = none) (k : LogicOp) (ρ : SEnv) (hΓ : logicSemCtx = ρ.ctx) (P : Prop) :
    (¬ Sem logicSemTable Φ Ψ ρ (logicSemSurface k) P) ∧
      (¬ NaruSem.Call.Sem logicSemTable.Δ Φ Ψ ρ (logicSemCore k) P) := by
  have hs : ¬ Sem logicSemTable Φ Ψ ρ (logicSemSurface k) P := by
    intro h
    cases h with
    | logic _ _ hr => exact disj_missing Φ Ψ hm ρ _ hr
    | eqNat hk => rw [op_parse k] at hk; cases hk
    | eqForm hk => rw [op_parse k] at hk; cases hk
    | cmpNat hk => rw [op_parse k] at hk; cases hk
    | cmpBool hk => rw [op_parse k] at hk; cases hk
  exact ⟨hs, fun hc => hs ((logic_sem_arbitrary Φ Ψ k ρ hΓ P).mpr hc)⟩

theorem logic_sem_not_missing (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hm : Ψ "M.p" = none) (ρ : SEnv) (hΓ : logicSemCtx = ρ.ctx) (P : Prop) :
    (¬ Sem logicSemTable Φ Ψ ρ logicSemNot P) ∧
      (¬ NaruSem.Call.Sem logicSemTable.Δ Φ Ψ ρ logicSemCoreNot P) := by
  have hs : ¬ Sem logicSemTable Φ Ψ ρ logicSemNot P := by
    intro h
    cases h with
    | not ha => exact (logic_sem_missing Φ Ψ hm .and ρ hΓ _).1 ha
  exact ⟨hs, fun hc => hs ((logic_sem_not_arbitrary Φ Ψ ρ hΓ P).mpr hc)⟩

theorem logic_sem_ite_missing (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hm : Ψ "M.p" = none) (isBool : Bool) (ρ : SEnv) (hΓ : logicSemCtx = ρ.ctx) (P : Prop) :
    (¬ Sem logicSemTable Φ Ψ ρ (logicSemIte isBool) P) ∧
      (¬ NaruSem.Call.Sem logicSemTable.Δ Φ Ψ ρ (logicSemCoreIte isBool) P) := by
  have hs : ¬ Sem logicSemTable Φ Ψ ρ (logicSemIte isBool) P := by
    intro h
    cases isBool with
    | false => cases h with
      | ite _ _ he => exact pred_missing Φ Ψ hm ρ _ he
    | true => cases h with
      | ite _ ht _ => exact disj_missing Φ Ψ hm ρ _ ht
  exact ⟨hs, fun hc => hs ((logic_sem_ite_arbitrary Φ Ψ isBool ρ hΓ P).mpr hc)⟩

/-- Bool=false の then、Prop=True の else は未選択でも意味が必須。 -/
theorem logic_sem_ite_unselected_missing (Φ : NaruSem.Call.FEnv) (P : Prop) :
    (¬ Sem logicSemTable Φ (fun _ => none) (logicSemEnv false False) (logicSemIte true) P) ∧
    (¬ NaruSem.Call.Sem logicSemTable.Δ Φ (fun _ => none) (logicSemEnv false False) (logicSemCoreIte true) P) ∧
    (¬ Sem logicSemTable Φ (fun _ => none) (logicSemEnv false True) (logicSemIte false) P) ∧
    (¬ NaruSem.Call.Sem logicSemTable.Δ Φ (fun _ => none) (logicSemEnv false True) (logicSemCoreIte false) P) := by
  have hb := logic_sem_ite_missing Φ (fun _ => none) rfl true _ (logic_sem_ctx false False) P
  have hp := logic_sem_ite_missing Φ (fun _ => none) rfl false _ (logic_sem_ctx false True) P
  exact ⟨hb.1, hb.2, hp.1, hp.2⟩

def logicSemWrongCore : Core.Expr := .binop "implies" logicSemCoreDisj (.var "x") .bool

theorem logic_sem_wrong_wt :
    NaruSem.Call.wtS logicSemTable.Δ logicSemCtx logicSemWrongCore = some .prop := rfl

theorem logic_sem_wrong_not_lower :
    lowerS logicSemTable logicSemCtx (logicSemSurface .implies) ≠ some logicSemWrongCore := by
  intro h
  cases h

/-- 含意を逆転した同型 Core は、閉じた True/False の kernel 反例を持つ。 -/
theorem logic_sem_wrong_not_preserved (Φ : NaruSem.Call.FEnv) :
    ¬ (Sem logicSemTable Φ (fun _ => some (fun _ => True)) (logicSemEnv false False)
        (logicSemSurface .implies) True ↔
      NaruSem.Call.Sem logicSemTable.Δ Φ (fun _ => some (fun _ => True)) (logicSemEnv false False)
        logicSemWrongCore True) := by
  have hs := (logic_sem_meaning Φ (fun _ => some (fun _ => True)) .implies
    (logicSemEnv false False) (logic_sem_ctx false False) false False rfl rfl (fun _ => True) rfl).1
  have he : LogicOp.implies.prop (false = true) (False ∨ True) = True := by
    apply propext
    simp [LogicOp.prop]
  have hs' := he ▸ hs
  have hd : NaruSem.Call.Sem logicSemTable.Δ Φ (fun _ => some (fun _ => True))
      (logicSemEnv false False) logicSemCoreDisj (False ∨ True) := by
    change NaruSem.Call.Sem logicSemTable.Δ Φ (fun _ => some (fun _ => True))
      (logicSemEnv false False) (.binop "||" (.var "q") (.call "M.p" []) .bool) _
    exact .logic (k := .or) rfl (.varProp rfl)
      (.callSpec (vs := []) (F := fun _ => True) rfl rfl rfl)
  have hw : NaruSem.Call.Sem logicSemTable.Δ Φ (fun _ => some (fun _ => True))
      (logicSemEnv false False) logicSemWrongCore ((False ∨ True) → false = true) := by
    change NaruSem.Call.Sem logicSemTable.Δ Φ (fun _ => some (fun _ => True))
      (logicSemEnv false False) (.binop "implies" logicSemCoreDisj (.var "x") .bool) _
    exact .logic (k := .implies) rfl hd (.varVal rfl)
  intro h
  have hc := h.mp hs'
  have hu := NaruSem.Call.Sem_unique hw hc
  have hf := (hu.mpr True.intro) (Or.inr True.intro)
  cases hf

end NaruSem.Surf.Call
