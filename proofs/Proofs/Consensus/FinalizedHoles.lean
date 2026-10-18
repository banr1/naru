import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Liveness
import Mathlib.Tactic

/-!
# claim `finalized` の骨格(IDEAL.md C76)

claim `finalized` は `SetupWellFormed ∧ RunDomain ∧ FinalityRegime t0 gap → FinalizedAt (t0 + finalityStartup s gap) gap`。
`FinalizedAt t₁ gap` は finalized の包含 `IncludedFrom … Finalized t₁ (finalityDeadline s gap)` と活性 `LiveFrom … Finalized t₁ (gap · period + finalityDeadline s gap)`
の連言。骨格の上位 2 段は次のとおり(入口は `Proofs/Consensus/Spec/Claims.lean` の theorem `finalized`):

1. 入口 `finalizedAt`: 包含を穴 `finalizedIncluded` から取り、活性は証明済みの `Liveness.finalizedLive_of_included`(包含・単調性・未来の提案の不在・
   `StrongMultiProposerRecurrence` の再発)で包含から出す。手書き `concreteConsensus`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の
   `finalized` の枝(`finalizedIncluded := finalized_included …`、`finalizedLive := finalized_growth …`)に当たる。
2. 穴(1 件): `finalizedIncluded`。

手書きの穴の本体は `legacy_consensus_closed` の `liveness.honestProposalFinalization.afterGST`(回復の後の round `q` から honest な提案が finalize される)
に還元するので、細分はその段(healing の位相と finality gadget の進行)から切る。
-/

namespace Proofs.Consensus.FinalizedHoles

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Execution.Run Model.Consensus.Spec.Interface Model.Consensus.Spec.Constants
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions Statements.Consensus.Spec.Regimes
open Statements.Consensus.Spec.Claims

section Holes

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 穴: `finalityStartup` の後、honest な提案の finalized の出力への期限 `finalityDeadline` 以内の包含。
手書き `finalized_included`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)に当たる。
閉じるのに要るもの: GST 以後の round `rGST` に `finalityStartup` を足した round の境界の時刻が horizon 内に収まること(手書き `finality_startup_time_bound`)と、
その後の honest な提案が finality gadget で justify・finalize されること(手書き `honestProposalFinalization.afterGST`。`StrongFinalityRun` の
全員 awake・`BelowOneThird`・強い再発・`gap + 2 ≤ maxGap` を使う)。 -/
theorem finalizedIncluded {t0 : Int} {gap : Nat} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hreg : FinalityRegime c p a nr s rho t0 gap) :
    IncludedFrom c p a nr s rho Output.Finalized (t0 + finalityStartup s gap) (finalityDeadline s gap) := by
  sorry

end Holes

/-- claim `finalized` の骨格の入口: 包含を穴から取り、活性を包含から証明済みの `finalizedLive_of_included` で出す。
手書き `concreteConsensus`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の `finalized` の枝に当たる。 -/
theorem finalizedAt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (t0 : Int) (gap : Nat)
    (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho) (hreg : FinalityRegime c p a nr s rho t0 gap) :
    FinalizedAt c p a nr s rho (t0 + finalityStartup s gap) gap := by
  have hincl := finalizedIncluded c p a nr s rho hwf hdom hreg
  unfold FinalizedAt
  exact ⟨hincl, Proofs.Consensus.Liveness.finalizedLive_of_included c p a nr s rho t0 gap hwf hreg hincl⟩

end Proofs.Consensus.FinalizedHoles
