import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Available
import Mathlib.Tactic

/-!
# claim `available` の骨格(IDEAL.md C76)

claim `available` は `SetupWellFormed ∧ RunDomain ∧ SleepyRegime t0 → AvailableAt t0`。`Available.lean` の `availableAt_of_fields` が結論を
5 つの事実に還元しているので、骨格の上位 2 段は次のとおり(入口は `Proofs/Consensus/Spec/Claims.lean` の theorem `available`):

1. 入口 `availableAt`: `t0 = 0`(GST-zero の枝。`RecoveredBy` の `genesis`)なら finalized の一致を穴 `finalizedAgree_genesis` から、
   `t0 ≠ 0`(回復の枝)なら証明済みの `agreeFrom_finalized_of_recovered` から取り、残る 4 つの事実を穴から取って `availableAt_of_fields` で組み立てる。
2. 穴(5 件。手書き `DecoupledConsensusProofs/Bridge/StandardVocabulary.lean` の `available_confirmedSafe` / `available_confirmedIncluded` /
   `available_stableSafe` と `DecoupledConsensusProofs/Bridge/StableIncludedAnySlot.lean` の `available_stableIncluded_any` に当たる):
   `recordAgree` / `crossAgree` / `finalizedAgree_genesis` / `confirmedIncluded` / `stableIncluded`。

手書きはどの穴も `RecoveredBy` の 2 枝で分ける: `genesis` は `WeakGenesis` に写して `gstZeroGuarantees_of_weakGenesis`
(`DecoupledConsensusProofs/Execution/GSTZeroSafetyClosedNamed.lean`)、`recovered` は `recoveryProducesHealedState` /
`boundedSafety`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の位相の保証から。穴を細分するときはこの 2 枝から切る。
穴の命題は義務の前提(`SetupWellFormed ∧ RunDomain ∧ SleepyRegime t0`)をそのまま受け取り、結論は `availableAt_of_fields` の引数の型。
-/

namespace Proofs.Consensus.AvailableHoles

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Execution.Run Model.Consensus.Spec.Interface Model.Consensus.Spec.Constants
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions Statements.Consensus.Spec.Regimes
open Statements.Consensus.Spec.Claims
open Proofs.Consensus.Outputs Proofs.Consensus.Available

section Holes

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 穴: 確認の記録 `latestConfirmed` の honest な 2 ノード・`t0` 以後の読みの一致。
手書き `available_confirmedSafe`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)の一致の半分に当たる。
閉じるのに要るもの: `genesis` の枝は `GSTZeroGuarantees` の欄 `availableConfirmations`(手書き `availableConfirmationsFrom_of_weakGenesis_named`。
Goldfish の門 `Majority.lean` と正準性 `eligible_compatible`)、`recovered` の枝は `boundedSafety` の位相の `UserConfirmationAfterHealing.latestCompatible`。 -/
theorem recordAgree {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  sorry

/-- 穴: 確認の記録 `latestConfirmed` と finalized の、honest な 2 ノード・`t0` 以後の読みの交差の互換。
手書き `latestConfirmed_compatible_finalized_of_weakGenesis`(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`。
`genesis` の枝)に当たる。`recovered` の枝は `SettledBootstrapPreparedV4.latest_compatible_finalized_core`
(`DecoupledConsensusProofs/Protocol/Schedule/PreparedV4PhaseShiftSafety.lean`)。
閉じるのに要るもの: 確認の記録が finalized を延ばすこと(記録についての事実。`Nested.lean` は出力 `getConfirmed` についてだけ)と、`recordAgree` と同じ枝の一致。 -/
theorem crossAgree {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  sorry

/-- 穴: GST-zero の枝(`t0 = 0`)の finalized の一致。回復の枝は `agreeFrom_finalized_of_recovered`(証明済み)。
手書き `gstZeroGuarantees_of_weakGenesis`(`DecoupledConsensusProofs/Execution/GSTZeroSafetyClosedNamed.lean`)の `outputCompatible` から
`available_stableSafe` の `finalized_compatible_of_confirmed_compatible` で finalized に下ろす筋に当たる。
閉じるのに要るもの: `t0 = 0` の `RecoveredBy` の genesis の枝は `SlashableBound` を与えないので `finalizedSafe` の本体は使えず、確認の出力の一致
(`recordAgree` / `crossAgree` の `genesis` の枝)と finalized ⪯ 確認の出力(`Nested.lean`)から出す。 -/
theorem finalizedAgree_genesis (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) :
    AgreeFrom c p a nr s rho Output.Finalized 0 := by
  sorry

/-- 穴: honest な提案の確認の出力への期限 `confirmationDelay` 以内の包含。
手書き `available_confirmedIncluded`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)に当たる。
閉じるのに要るもの: `genesis` の枝は `gstZeroGuarantees_of_weakGenesis` の `userProposals`、`recovered` の枝は位相の `userConfirmation.proposals`。
どちらも honest な提案が適格な子の一意な最大になって `ghost_reaches`(`Goldfish.lean`)で選ばれることと、提案が締切までに各ノードの tree に入ること
(`ProposerRoot.lean` の `partialSynchrony_emitted_block_mem_of_fgRoot`。FG root の上界 = 手書き `hreadBound`)。 -/
theorem confirmedIncluded {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    IncludedFrom c p a nr s rho Output.Confirmed t0 (confirmationDelay s) := by
  sorry

/-- 穴: honest な提案の stable の出力への期限 `stableInclusionDelay` 以内の包含。
手書き `available_stableIncluded_any`(`DecoupledConsensusProofs/Bridge/StableIncludedAnySlot.lean`)に当たる。
閉じるのに要るもの: `confirmedIncluded` と同じ包含を grade の候補 `frameSgCandidate` と stable の記録の床 `floorOnStable` に移すこと。 -/
theorem stableIncluded {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    IncludedFrom c p a nr s rho Output.Stable t0 (stableInclusionDelay s) := by
  sorry

end Holes

/-- claim `available` の骨格の入口: `t0` が 0 か否かで finalized の一致の出どころを分け、残りの 4 つの事実を穴から取って組み立てる。
手書き `concreteConsensus`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の `available` の枝に当たる。 -/
theorem availableAt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (t0 : Int)
    (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho) (hsleep : SleepyRegime c p a nr s rho t0) :
    AvailableAt c p a nr s rho t0 := by
  have hL := recordAgree c p a nr s rho hwf hdom hsleep
  have hX := crossAgree c p a nr s rho hwf hdom hsleep
  have hIc := confirmedIncluded c p a nr s rho hwf hdom hsleep
  have hIs := stableIncluded c p a nr s rho hwf hdom hsleep
  by_cases h0 : t0 = 0
  · subst h0
    exact availableAt_of_fields c p a nr s rho hsleep hL hX (finalizedAgree_genesis c p a nr s rho hwf hdom hsleep) hIc hIs
  · exact availableAt_of_fields_recovered c p a nr s rho hwf hdom hsleep h0 hL hX hIc hIs

end Proofs.Consensus.AvailableHoles
