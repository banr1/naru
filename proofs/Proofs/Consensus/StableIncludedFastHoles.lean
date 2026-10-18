import Statements.Consensus.Spec.Claims
import Proofs.Consensus.AvailableHoles
import Mathlib.Tactic

/-!
# claim `stableIncludedFast` の骨格(IDEAL.md C76)

claim `stableIncludedFast` は `SetupWellFormed ∧ RunDomain ∧ FreshSleepyRegime t0 → IncludedFrom … Stable t0 fastStableInclusionDelay`。
`FreshSleepyRegime` は `SleepyRegime t0` と、`t0` 以後の窓の各時刻の新鮮な過半 `FreshMajority` の連言。骨格の上位 2 段は次のとおり
(入口は `Proofs/Consensus/Spec/Claims.lean` の theorem `stableIncludedFast`):

1. 入口 `stableIncludedFastAt`: `FreshSleepyRegime` を `SleepyRegime` と新鮮な過半の仮定に分け、提案の確認の出力への包含を claim `available` の穴
   `AvailableHoles.confirmedIncluded` から取り、`t0 = 0`(`RecoveredBy` の genesis)か否かで stable の記録への書き込みの穴に渡す。
   手書き `stableIncludedFast_concrete`(`DecoupledConsensusProofs/Bridge/StableIncludedFresh.lean`)が `available_stableIncluded_fresh` に渡し、
   その本体が `available_confirmedIncluded` で提案 `B` を取って `RecoveredBy` の 2 枝(`stableWrite_anySlot_fresh_gstZero` /
   `stableWrite_anySlot_fresh_afterGST`)で stable の書き込みを出す段に当たる。
2. 穴(2 件): `stableWriteFresh_genesis` / `stableWriteFresh_recovered`。
-/

namespace Proofs.Consensus.StableIncludedFastHoles

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Execution.Run Model.Consensus.Spec.Interface Model.Consensus.Spec.Constants
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions Statements.Consensus.Spec.Regimes

section Holes

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 穴: GST-zero の枝(`t0 = 0`)で、確認の出力に入った honest な提案が新鮮な過半の下で 1 round の期限 `fastStableInclusionDelay` 以内に
stable の出力に入る。手書き `stableWrite_anySlot_fresh_gstZero`(`DecoupledConsensusProofs/Bridge/StableIncludedFresh.lean`)と、
それに続く `stable_retained_of_duty_from` の保持に当たる。
閉じるのに要るもの: 新鮮な過半から提案の次の round の grade の形成(手書き `gradeFormingMajority_of_freshAt`)、grade の候補(生成 Model の
`frameSgCandidate`)が提案を延ばして stable の記録に書かれること(手書き `stableWrite_of_freshCover` / `relativeCarrier_fastDuty_gstZero`)、
書かれた記録が期限まで保たれること。 -/
theorem stableWriteFresh_genesis (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hfresh : ∀ t : Int, ((0 ≤ t ∧ participationLag s ≤ t) ∧ t - participationLag s ≤ rho.horizon) →
      FreshMajority a s rho.honest t)
    (hconf : IncludedFrom c p a nr s rho Output.Confirmed 0 (confirmationDelay s)) :
    IncludedFrom c p a nr s rho Output.Stable 0 (fastStableInclusionDelay s) := by
  sorry

/-- 穴: 回復の枝(`t0 ≠ 0`)で、確認の出力に入った honest な提案が新鮮な過半の下で `fastStableInclusionDelay` 以内に stable の出力に入る。
手書き `stableWrite_anySlot_fresh_afterGST`(`DecoupledConsensusProofs/Bridge/StableIncludedFresh.lean`)と、それに続く
`stable_retained_of_duty_from` の保持に当たる。
閉じるのに要るもの: genesis の枝と同じ grade の形成と stable の書き込み(手書き `relativeCarrier_fastDuty_afterGST`)に加えて、回復の位相
(手書き `continuationV4Package` の phase shift と finality)から stable の記録が正準であること(手書き
`stableRecordCanonicalFrom_of_phaseShift_latestFinality`)。 -/
theorem stableWriteFresh_recovered {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) (h0 : t0 ≠ 0)
    (hfresh : ∀ t : Int, ((t0 ≤ t ∧ participationLag s ≤ t) ∧ t - participationLag s ≤ rho.horizon) →
      FreshMajority a s rho.honest t)
    (hconf : IncludedFrom c p a nr s rho Output.Confirmed t0 (confirmationDelay s)) :
    IncludedFrom c p a nr s rho Output.Stable t0 (fastStableInclusionDelay s) := by
  sorry

end Holes

/-- claim `stableIncludedFast` の骨格の入口: 確認の出力への包含を `available` の穴から取り、`t0` の 2 枝で stable の書き込みの穴に渡す。
手書き `stableIncludedFast_concrete` / `available_stableIncluded_fresh`(`DecoupledConsensusProofs/Bridge/StableIncludedFresh.lean`)に当たる。 -/
theorem stableIncludedFastAt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (t0 : Int)
    (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho) (hreg : FreshSleepyRegime c p a nr s rho t0) :
    IncludedFrom c p a nr s rho Output.Stable t0 (fastStableInclusionDelay s) := by
  unfold FreshSleepyRegime at hreg
  obtain ⟨hsleep, hfresh⟩ := hreg
  have hconf := Proofs.Consensus.AvailableHoles.confirmedIncluded c p a nr s rho hwf hdom hsleep
  by_cases h0 : t0 = 0
  · subst h0
    exact stableWriteFresh_genesis c p a nr s rho hwf hdom hsleep hfresh hconf
  · exact stableWriteFresh_recovered c p a nr s rho hwf hdom hsleep h0 hfresh hconf

end Proofs.Consensus.StableIncludedFastHoles
