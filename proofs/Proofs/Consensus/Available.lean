import Statements.Consensus.Spec.Claims
import Proofs.Consensus.FinalizedAccountable
import Proofs.Consensus.Liveness
import Proofs.Consensus.RecordOrder
import Mathlib.Tactic

/-!
# claim `available` の結論の組み立てと、残る義務の明示(C71 の liveness 系 claim の足場)

claim `available` は `SetupWellFormed ∧ RunDomain ∧ SleepyRegime t0 → AvailableAt t0` で、結論 `AvailableAt t0` は
`SafeFrom Confirmed t0 ∧ IncludedFrom Confirmed t0 confirmationDelay ∧ SafeFrom Stable t0 ∧ IncludedFrom Stable t0 stableInclusionDelay`
(`generated/Statements/Consensus/Spec/Claims.lean`)。`Outputs.lean` / `RecordOrder.lean` が 2 つの `SafeFrom` を確認の記録
`latestConfirmed` についての欄の事実に還元したので、`available` の本体に残るのは次の 5 つの事実を示すことだけになる
(`availableAt_of_records`。run への前提は `EventsSorted` と `EventsNodup` だけ):
- 確認の記録の honest な 2 ノード・`t0` 以後の読みの一致(`RecordAgreeFrom`)と、finalized との交差の互換(`CrossAgreeFrom`)。
  stable の記録についての同じ 2 つは、記録の順序 `latestStable ⪯ latestConfirmed` からこれらに従う(`RecordOrder.lean`)。
- finalized の一致 `AgreeFrom … Finalized t0`。`t0 ≠ 0` なら `SleepyRegime` の `RecoveredBy` は回復の枝(`t0 = recoveryEnd …`)に
  限られ、その枝は `SlashableBound` を持つので `finalizedSafe` の本体から従う(`agreeFrom_finalized_of_recovered`)。
  GST-zero の枝(`t0 = 0`)は確認の出力の一致から従う(`agreeFrom_finalized_of_confirmed`。確認の出力の一致自体は未証明)。
- 期限内の包含 `IncludedFrom` ×2(未証明。手書き `available_confirmedIncluded` / `available_stableIncluded_any`)。
手書き `DecoupledConsensusProofs/ReviewTheorem.lean`(`concreteConsensus` の `available` の枝: `available_confirmedSafe` /
`available_confirmedIncluded` / `available_stableSafe` / `available_stableIncluded_any`)の筋。
-/

namespace Proofs.Consensus.Available

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Execution.Run Model.Consensus.Spec.Interface Model.Consensus.Spec.Constants
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions Statements.Consensus.Spec.Regimes
open Statements.Consensus.Spec.Claims
open Proofs.Consensus.Outputs Proofs.Consensus.RecordOrder Proofs.Consensus.Liveness

section Claims

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- `ScheduleWellFormed` から event 列の整列と重複なし。 -/
theorem schedule_sorted_nodup (hsch : ScheduleWellFormed s rho) : EventsSorted rho ∧ EventsNodup rho := by
  unfold ScheduleWellFormed at hsch
  obtain ⟨⟨⟨⟨⟨⟨-, hsorted⟩, hnodup⟩, -⟩, -⟩, -⟩, -⟩ := hsch
  exact ⟨hsorted, hnodup⟩

/-- `SleepyRegime` から event 列の整列と重複なし(`ExecutionValid` → `ScheduleWellFormed`)。 -/
theorem sorted_nodup_of_sleepy {t0 : Int} (hsleep : SleepyRegime c p a nr s rho t0) :
    EventsSorted rho ∧ EventsNodup rho := by
  have hexec := executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, -⟩, -⟩ := hexec
  exact schedule_sorted_nodup s rho hsch

/-- `ExecutionValid` は `RunWellFormed`(`0 ≤ horizon`・`EventsSorted`・`Idealization`)を含む。 -/
theorem runWellFormed_of_executionValid (hexec : ExecutionValid c p a nr s rho) : RunWellFormed c p a nr s rho := by
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, -⟩, hideal⟩ := hexec
  unfold ScheduleWellFormed at hsch
  obtain ⟨⟨⟨⟨⟨⟨hhor, hsorted⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hsch
  unfold RunWellFormed
  exact ⟨⟨hhor, hsorted⟩, hideal⟩

/-- `SlashableBound` の下では finalized の読みは `t0 ≥ 0` 以後で一致(claim `finalizedSafe` の本体を `t0` の窓に絞る)。 -/
theorem agreeFrom_finalized_of_slashableBound (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hexec : ExecutionValid c p a nr s rho) (hsb : SlashableBound c p a nr s rho) {t0 : Int} (ht0 : 0 ≤ t0) :
    AgreeFrom c p a nr s rho Output.Finalized t0 := by
  have h := Proofs.Consensus.FinalizedAccountable.finalizedSafe c p a nr s rho
  unfold Statements.Consensus.Spec.Claims.finalizedSafe at h
  have hreg : AccountableRegime c p a nr s rho := by
    unfold AccountableRegime
    exact ⟨runWellFormed_of_executionValid c p a nr s rho hexec, hsb⟩
  exact AgreeFrom.mono c p a nr s rho ht0 (h ⟨⟨hwf, hdom⟩, hreg⟩)

/-- `t0 ≠ 0` なら `SleepyRegime` の `RecoveredBy` は回復の枝(`t0 = recoveryEnd …`)に限られ、その枝は `SlashableBound` を持つので、
finalized の読みは `t0` 以後で一致する。GST-zero の枝(`t0 = 0`)はここでは扱わない。 -/
theorem agreeFrom_finalized_of_recovered (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho) {t0 : Int}
    (hsleep : SleepyRegime c p a nr s rho t0) (hne : t0 ≠ 0) : AgreeFrom c p a nr s rho Output.Finalized t0 := by
  obtain ⟨-, hgst0, -⟩ := wf_facts hwf
  have hexec := executionValid_of_sleepy c p a nr s rho hsleep
  unfold SleepyRegime at hsleep
  obtain ⟨⟨⟨⟨-, hgst⟩, -⟩, -⟩, hrec⟩ := hsleep
  unfold RecoveredBy at hrec
  rcases hrec with h0 | ⟨_, _, _, ⟨⟨-, hsb⟩, -⟩⟩
  · exact absurd h0 hne
  · exact agreeFrom_finalized_of_slashableBound c p a nr s rho hwf hdom hexec hsb (hgst0.trans hgst)

/-- `X ⪯ Y` で `Y` が `Z` と互換なら `X` も `Z` と互換。手書き `Protocol.compatible_of_preceq_of_compatible`。 -/
theorem compatible_of_preceq_of_compatible {X Y Z : Block} (hXY : preceq X Y = true) (hYZ : compatible Y Z = true) :
    compatible X Z = true := by
  unfold compatible at hYZ
  rw [Bool.or_eq_true] at hYZ
  rcases hYZ with hYZ | hZY
  · unfold compatible
    rw [Bool.or_eq_true]
    exact Or.inl (Proofs.Consensus.Blocks.preceq_trans hXY hYZ)
  · exact Proofs.Consensus.Blocks.compatible_of_preceq_common hXY hZY

/-- 確認の出力が `t0` 以後で一致すれば finalized も一致する(finalized は確認の出力の接頭辞 `f_preceq_getConfirmed`。regime の前提なし)。
手書き `finalized_compatible_of_confirmed_compatible`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)。 -/
theorem agreeFrom_finalized_of_confirmed {t0 : Int} (hC : AgreeFrom c p a nr s rho Output.Confirmed t0) :
    AgreeFrom c p a nr s rho Output.Finalized t0 := by
  unfold AgreeFrom ConsistentFrom at hC ⊢
  intro u v t t2 h
  have hcc := hC u v t t2 h
  rw [outputAt_confirmed, outputAt_confirmed] at hcc
  rw [outputAt_finalized, outputAt_finalized]
  have hU := compatible_of_preceq_of_compatible (f_preceq_getConfirmed _) hcc
  rw [Proofs.Consensus.Blocks.compatible_comm] at hU ⊢
  exact compatible_of_preceq_of_compatible (f_preceq_getConfirmed _) hU

/-- honest な 2 ノードの `t0` 以後の 2 つの読みの finalized と確認の記録 `latestConfirmed` の 4 つが、共通の上界 `X` を持つ。
手書きの GST-zero の枝が `latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero` / `finalizedAt_preceq_laterVoteDutyHead_of_gstZero`
(後の投票の務めの head `voterHeadAt` を上界にする)と、最初の確認の前に run が終わる場合(4 つとも genesis)から作る形。 -/
def CommonUpperFrom (t0 : Int) : Prop :=
  ∀ u v t t2, rho.honest.contains u = true → rho.honest.contains v = true →
    t0 ≤ t → t ≤ rho.horizon → t0 ≤ t2 → t2 ≤ rho.horizon →
    ∃ X : Block, preceq (storeAt c p a nr s rho u t).core.f X = true ∧
      preceq (storeAt c p a nr s rho u t).core.latestConfirmed X = true ∧
      preceq (storeAt c p a nr s rho v t2).core.f X = true ∧
      preceq (storeAt c p a nr s rho v t2).core.latestConfirmed X = true

/-- 共通の上界から確認の記録の一致。 -/
theorem recordAgreeFrom_of_commonUpper {t0 : Int} (h : CommonUpperFrom c p a nr s rho t0) :
    RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  intro u v t t2 hu hv h1 h2 h3 h4
  obtain ⟨X, -, hLu, -, hLv⟩ := h u v t t2 hu hv h1 h2 h3 h4
  exact Proofs.Consensus.Blocks.compatible_of_preceq_common hLu hLv

/-- 共通の上界から確認の記録と finalized の交差の互換。手書き `latestConfirmed_compatible_finalized_of_weakGenesis` の筋。 -/
theorem crossAgreeFrom_of_commonUpper {t0 : Int} (h : CommonUpperFrom c p a nr s rho t0) :
    CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  intro u v t t2 hu hv h1 h2 h3 h4
  obtain ⟨X, -, hLu, hFv, -⟩ := h u v t t2 hu hv h1 h2 h3 h4
  exact Proofs.Consensus.Blocks.compatible_of_preceq_common hLu hFv

/-- 共通の上界から確認の出力の一致: 確認の出力は finalized と確認の記録の上界の下にある(`getConfirmed_preceq`)。
手書き `confirmedOutputCompatibleFrom_of_weakGenesis_named`(`confirmedOutputAt_preceq_laterVoteDutyHead_of_gstZero` の 2 つの上界を
大きい方の slot で揃える)の筋。 -/
theorem agreeFrom_confirmed_of_commonUpper {t0 : Int} (h : CommonUpperFrom c p a nr s rho t0) :
    AgreeFrom c p a nr s rho Output.Confirmed t0 := by
  unfold AgreeFrom ConsistentFrom
  intro u v t t2 hh
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hh
  obtain ⟨X, hFu, hLu, hFv, hLv⟩ := h u v t t2 hu hv h1 h2 h3 h4
  rw [outputAt_confirmed, outputAt_confirmed]
  exact Proofs.Consensus.Blocks.compatible_of_preceq_common
    (getConfirmed_preceq (storeAt_sbc c p a nr s rho u t) hFu hLu)
    (getConfirmed_preceq (storeAt_sbc c p a nr s rho v t2) hFv hLv)

/-- claim `available` の結論 `AvailableAt t0` を、残る 5 つの事実(確認の記録の一致と finalized との交差の互換、finalized の一致、
2 つの包含)から組み立てる。run への前提は event 列の整列と重複なしだけ(regime に依らない形)。 -/
theorem availableAt_of_records (hs : EventsSorted rho) (hnd : EventsNodup rho) {t0 : Int}
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hF : AgreeFrom c p a nr s rho Output.Finalized t0)
    (hIc : IncludedFrom c p a nr s rho Output.Confirmed t0 (confirmationDelay s))
    (hIs : IncludedFrom c p a nr s rho Output.Stable t0 (stableInclusionDelay s)) :
    AvailableAt c p a nr s rho t0 := by
  unfold AvailableAt
  exact ⟨⟨⟨safeFrom_confirmed_of_records c p a nr s rho hs hnd t0 hL hF hX, hIc⟩,
    safeFrom_stable_of_records c p a nr s rho hs hnd t0 hL hF hX⟩, hIs⟩

/-- `availableAt_of_records` の `SleepyRegime` 版(regime からは event 列の整列と重複なしだけを使う)。 -/
theorem availableAt_of_fields {t0 : Int} (hsleep : SleepyRegime c p a nr s rho t0)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hF : AgreeFrom c p a nr s rho Output.Finalized t0)
    (hIc : IncludedFrom c p a nr s rho Output.Confirmed t0 (confirmationDelay s))
    (hIs : IncludedFrom c p a nr s rho Output.Stable t0 (stableInclusionDelay s)) :
    AvailableAt c p a nr s rho t0 := by
  obtain ⟨hs, hnd⟩ := sorted_nodup_of_sleepy c p a nr s rho hsleep
  exact availableAt_of_records c p a nr s rho hs hnd hL hX hF hIc hIs

/-- `t0 ≠ 0` の `SleepyRegime` では finalized の一致が `agreeFrom_finalized_of_recovered` で埋まるので、残る事実は 4 つ
(確認の記録の一致と交差の互換、2 つの包含)。 -/
theorem availableAt_of_fields_recovered (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho) {t0 : Int}
    (hsleep : SleepyRegime c p a nr s rho t0) (hne : t0 ≠ 0)
    (hL : RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hX : CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0)
    (hIc : IncludedFrom c p a nr s rho Output.Confirmed t0 (confirmationDelay s))
    (hIs : IncludedFrom c p a nr s rho Output.Stable t0 (stableInclusionDelay s)) :
    AvailableAt c p a nr s rho t0 :=
  availableAt_of_fields c p a nr s rho hsleep hL hX (agreeFrom_finalized_of_recovered c p a nr s rho hwf hdom hsleep hne) hIc hIs

end Claims

end Proofs.Consensus.Available
