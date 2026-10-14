import Statements.Consensus.Spec.Constants
import Statements.Consensus.Spec.Conditions
import Mathlib.Tactic

/-!
# 定数の制約(claim `constants` の補題)

生成 Model の `Model/Consensus/Spec/Constants.lean` の定数(`period` / `participationWindow` / 各 delay / `prefixEnd` / `recoveryEnd` /
`outageStart` / `expiry`)が、`SetupWellFormed` の数値の前提(Δ > 0、R ≥ 3、K ≥ 4、R · η_SG ≥ 4 …)の下で
`Statements.Consensus.Spec.Constants.ConstantsValid` を満たすことを示す。手書き `constants_valid` / `concretePeriod_pos`
(`DecoupledConsensusProofs/Bridge/GenericRecurrence.lean`)と同じ筋で、時刻の式を Δ・R・η_SG の多項式に開いて不等式を閉じる。

時刻の式はすべて `slotStart δ k = (δ * 4) * k` の上に乗っている:
- `setupActionTime s r = 4δ · (r · R) + 6δ`(`actionTime`)
- `healingBoundaryTime s q = 4δ · (q · R + 2) + δ`(`voteTime` の `openingSlot q + 2`)
- `period s = setupActionTime s 1 - setupActionTime s 0 = 4δ · R`
- `expiry s tRead = earlyTime … G2 = 4δ · (Q · R) - 5δ`(Q は `roundOf (slotOf (nextAction s tRead)) + η_SG + 1`)
`outageStart < expiry` だけが `Int.fdiv`(`slotOf`)と Nat の除算(`roundOf`)を通る: `slotOf (setupActionTime s A) = A · R + 1`、
`roundOf (A · R + 1) = A`(R ≥ 2)で、残りは `R · η_SG ≥ 4 > 3` の多項式不等式になる。
-/

namespace Proofs.Consensus.Constants

open Model.Consensus.Execution.Setup (Setup)

/-- `period s = 4 · Δ · R`。 -/
theorem period_eq (s : Setup) :
    Model.Consensus.Spec.Constants.period s = 4 * s.e.delta * (s.hc.r : Int) := by
  unfold Model.Consensus.Spec.Constants.period Model.Consensus.Execution.Setup.setupActionTime
    Model.Consensus.Protocol.Grades.actionTime Model.Consensus.Objects.Time.slotStart
    Model.Consensus.Protocol.Grades.openingSlot
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

/-- Δ > 0 と R ≥ 3 から period は正。 -/
theorem period_pos (s : Setup) (hδ : 0 < s.e.delta) (hr : 3 ≤ s.hc.r) :
    0 < Model.Consensus.Spec.Constants.period s := by
  rw [period_eq]
  have hr' : (0 : Int) < (s.hc.r : Int) := by exact_mod_cast (show 0 < s.hc.r by omega)
  exact mul_pos (mul_pos (by norm_num) hδ) hr'

/-- `healingBoundaryTime s q - setupActionTime s 0 = 4Δ · (q · R) + 3Δ`。 -/
theorem healingBoundary_sub_a0 (s : Setup) (q : Nat) :
    Model.Consensus.Spec.Constants.healingBoundaryTime s q
        - Model.Consensus.Execution.Setup.setupActionTime s 0
      = 4 * s.e.delta * ((q : Int) * (s.hc.r : Int)) + 3 * s.e.delta := by
  unfold Model.Consensus.Spec.Constants.healingBoundaryTime Model.Consensus.Execution.Setup.setupActionTime
    Model.Consensus.Protocol.Grades.actionTime Model.Consensus.Protocol.Schedule.voteTime
    Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    Model.Consensus.Protocol.Grades.openingSlot
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

/-- 回復の境界時刻は時刻 0 の action 以後(Δ > 0)。`finalityStartup` / `finalityDeadline` の非負に使う。 -/
theorem healingBoundary_nonneg (s : Setup) (hδ : 0 < s.e.delta) (q : Nat) :
    0 ≤ Model.Consensus.Spec.Constants.healingBoundaryTime s q
        - Model.Consensus.Execution.Setup.setupActionTime s 0 := by
  rw [healingBoundary_sub_a0]
  have hq : (0 : Int) ≤ (q : Int) * (s.hc.r : Int) := by positivity
  have h4 : (0 : Int) ≤ 4 * s.e.delta * ((q : Int) * (s.hc.r : Int)) :=
    mul_nonneg (mul_nonneg (by norm_num) hδ.le) hq
  linarith

/-- 同じ round の action 時刻は回復の境界時刻以前(差は 3Δ)。`prefixEnd ≤ recoveryEnd` に使う。 -/
theorem a_le_healingBoundary (s : Setup) (hδ : 0 < s.e.delta) (q : Nat) :
    Model.Consensus.Execution.Setup.setupActionTime s q
      ≤ Model.Consensus.Spec.Constants.healingBoundaryTime s q := by
  have h : Model.Consensus.Spec.Constants.healingBoundaryTime s q
      - Model.Consensus.Execution.Setup.setupActionTime s q = 3 * s.e.delta := by
    unfold Model.Consensus.Spec.Constants.healingBoundaryTime Model.Consensus.Execution.Setup.setupActionTime
      Model.Consensus.Protocol.Grades.actionTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
      Model.Consensus.Protocol.Grades.openingSlot
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  linarith

/-- round `A` の action 時刻 `4Δ · (A · R) + 6Δ` が属する slot は `A · R + 1`(6Δ / 4Δ の床は 1)。 -/
theorem slotOf_setupActionTime (s : Setup) (hδ : 0 < s.e.delta) (A : Nat) :
    Model.Consensus.Objects.Parameters.slotOf s.e (Model.Consensus.Execution.Setup.setupActionTime s A)
      = A * s.hc.r + 1 := by
  unfold Model.Consensus.Objects.Parameters.slotOf Model.Consensus.Objects.Time.slotOfTime
    Model.Consensus.Execution.Setup.setupActionTime Model.Consensus.Protocol.Grades.actionTime
    Model.Consensus.Objects.Time.slotStart Model.Consensus.Protocol.Grades.openingSlot
  simp only [Int.ofNat_eq_natCast]
  have hb : (0 : Int) ≤ s.e.delta * 4 := by linarith
  have hne : s.e.delta * 4 ≠ 0 := by
    have : (0 : Int) < s.e.delta * 4 := by linarith
    exact this.ne'
  rw [Int.fdiv_eq_ediv_of_nonneg _ hb]
  have h6 : (6 * s.e.delta) / (s.e.delta * 4) = 1 := by
    have e : 6 * s.e.delta = 1 * (s.e.delta * 4) + 2 * s.e.delta := by ring
    rw [e, Int.mul_add_ediv_right _ _ hne,
      Int.ediv_eq_zero_of_lt (by linarith) (by linarith)]
    norm_num
  have e1 : s.e.delta * 4 * ((A * s.hc.r : Nat) : Int) + 6 * s.e.delta
      = ((A * s.hc.r : Nat) : Int) * (s.e.delta * 4) + 6 * s.e.delta := by ring
  rw [e1, Int.mul_add_ediv_right _ _ hne, h6]
  exact Int.toNat_natCast_add_one

/-- slot `A · R + 1` の round は `A`(R ≥ 2)。 -/
theorem roundOf_slot (s : Setup) (hr : 3 ≤ s.hc.r) (A : Nat) :
    Model.Consensus.Protocol.Grades.roundOf s.hc (A * s.hc.r + 1) = A := by
  unfold Model.Consensus.Protocol.Grades.roundOf
  have hr0 : 0 < s.hc.r := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right 1 A hr0, Nat.div_eq_of_lt (by omega : 1 < s.hc.r)]
  omega

/-- outage の窓は空でない: `outageStart s tRead < expiry s tRead`(Δ > 0、R ≥ 3、R · η_SG ≥ 4)。 -/
theorem outage_window (s : Setup) (hδ : 0 < s.e.delta) (hr : 3 ≤ s.hc.r)
    (hreta : 4 ≤ s.hc.r * s.hc.etaSG) (tRead : Int) :
    Model.Consensus.Spec.Constants.outageStart s tRead < Model.Consensus.Spec.Constants.expiry s tRead := by
  unfold Model.Consensus.Spec.Constants.outageStart Model.Consensus.Spec.Constants.expiry
    Model.Consensus.Spec.Constants.nextAction
  generalize Model.Consensus.Spec.Constants.roundAfter s tRead = A
  rw [slotOf_setupActionTime s hδ A, roundOf_slot s hr A, period_eq]
  unfold Model.Consensus.Execution.Setup.setupActionTime Model.Consensus.Protocol.Grades.actionTime
    Model.Consensus.Protocol.Grades.earlyTime Model.Consensus.Protocol.Grades.openingTime
    Model.Consensus.Protocol.Schedule.proposalTime Model.Consensus.Objects.Parameters.slotTime
    Model.Consensus.Objects.Time.slotStart Model.Consensus.Protocol.Grades.openingSlot
  simp only [Model.Consensus.Protocol.Grades.earlyOffset, Int.ofNat_eq_natCast]
  push_cast
  have hreta' : (4 : Int) ≤ (s.hc.r : Int) * (s.hc.etaSG : Int) := by exact_mod_cast hreta
  have key : 0 ≤ s.e.delta * ((s.hc.r : Int) * (s.hc.etaSG : Int) - 4) :=
    mul_nonneg hδ.le (by linarith)
  nlinarith [key, hδ]

/-- claim `constants` の本体: `SetupWellFormed` の数値の前提から `ConstantsValid`。 -/
theorem constantsValid_of_setupWellFormed
    (committee' : Nat → NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId)
    (proposer' : Nat → Model.Consensus.Objects.Identifiers.ValidatorId) (s : Setup)
    (hwf : Statements.Consensus.Spec.Conditions.SetupWellFormed committee' proposer' s) :
    Statements.Consensus.Spec.Constants.ConstantsValid s := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hδ, -⟩, hr⟩, -⟩, hk⟩, -⟩, -⟩, -⟩, hreta⟩, -⟩, -⟩, -⟩ := hwf
  have hperiod := period_pos s hδ hr
  unfold Statements.Consensus.Spec.Constants.ConstantsValid
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact hperiod
  · unfold Model.Consensus.Spec.Constants.participationWindow
    simp only [Int.ofNat_eq_natCast]
    exact mul_nonneg (by positivity) hperiod.le
  · unfold Model.Consensus.Spec.Constants.participationLag
    exact hperiod.le
  · unfold Model.Consensus.Spec.Constants.proposerSlots
    norm_num
  · unfold Model.Consensus.Spec.Constants.maxGap
    omega
  · intro gap
    have hg : (0 : Int) ≤ (gap : Int) := by positivity
    have heta : (0 : Int) ≤ (s.hc.etaSG : Int) := by positivity
    have hgp := mul_nonneg hg hperiod.le
    have hep := mul_nonneg heta hperiod.le
    have hb1 := healingBoundary_nonneg s hδ
      (Model.Consensus.Spec.Constants.finalityStartupRound s gap (Model.Consensus.Spec.Constants.extraRounds s) + 1)
    have hb2 := healingBoundary_nonneg s hδ
      (Model.Consensus.Spec.Constants.finalityDeadlineRound s gap (Model.Consensus.Spec.Constants.extraRounds s) + 1)
    unfold Model.Consensus.Spec.Constants.confirmationDelay Model.Consensus.Spec.Constants.growthDelay
      Model.Consensus.Spec.Constants.stableGrowthDelay Model.Consensus.Spec.Constants.stableInclusionDelay
      Model.Consensus.Spec.Constants.fastStableInclusionDelay Model.Consensus.Spec.Constants.finalityStartup
      Model.Consensus.Spec.Constants.finalityDeadline
    simp only [Int.ofNat_eq_natCast]
    push_cast
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    all_goals nlinarith [hgp, hep, hb1, hb2, hperiod, hδ]
  · intro t0 gap
    unfold Model.Consensus.Spec.Constants.prefixEnd Model.Consensus.Spec.Constants.recoveryEnd
    exact a_le_healingBoundary s hδ _
  · intro tRead
    exact outage_window s hδ hr hreta tRead

end Proofs.Consensus.Constants
