import Statements.Consensus.Spec.Claims
import Mathlib.Tactic

/-!
# claim `stableAsynchronyResilient` の骨格(IDEAL.md C76)

claim `stableAsynchronyResilient` は `SetupWellFormed ∧ RunDomain ∧ OutageRegime tRead b0 b1 → PersistsFrom … Stable tRead b0`。
`PersistsFrom` は「honest な `v` の時刻 `tRead` の stable の読みの接頭辞 `b` は、`b0` 以後 horizon までのどの時刻 `t` でも honest 全員の stable の読みにある
(`InBy … Stable b t`)」。骨格の上位 2 段は次のとおり(入口は `Proofs/Consensus/Spec/Claims.lean` の theorem `stableAsynchronyResilient`):

1. 入口 `persistsFrom`: `PersistsFrom` の量化(`v` / `b` / `t`)を開き、ブロックと時刻ごとの穴 `stableInBy` に渡す。手書き `concreteConsensus`
   (`DecoupledConsensusProofs/ReviewTheorem.lean`)の `stableAsynchronyResilient` の枝が量化を開いて `outage_stablePersists` に渡す段に当たる。
2. 穴(1 件): `stableInBy`。

手書きの穴の本体は `NamedOutageClosure.stable_chain_outage_resilience_public`(停止の区間 `[b0, b1]` の間の grade の形成と stable の記録の保持)に
還元するので、細分はその段から切る。
-/

namespace Proofs.Consensus.PersistsHoles

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Execution.Run Model.Consensus.Spec.Interface Model.Consensus.Spec.Constants
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions Statements.Consensus.Spec.Regimes

section Holes

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 穴: 停止の区間の後も、honest な `v` の時刻 `tRead` の stable の読みの接頭辞 `b` は `b0` 以後の各時刻 `t` で honest 全員の stable の読みにある。
手書き `outage_stablePersists`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)に当たる。
閉じるのに要るもの: `OutageRegime` の欄(`HealthyPrefixDelivery`・`PublicTime`・新鮮な過半・`SlashableBound`、形成の余裕と記録の期限の窓)から、
`tRead` の次の action から `formationMargin` の間に grade の候補が形成されて stable の記録が `b` を延ばし(手書き `gradeFormingThroughout_of_awake`)、
期限 `expiry` まで記録が保たれること(手書き `stable_chain_outage_resilience_public`)。 -/
theorem stableInBy {tRead b0 b1 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hreg : OutageRegime c p a nr s rho tRead b0 b1) (v : ValidatorId) (b : Block) (t : Int)
    (hv : rho.honest.contains v = true) (hpre : preceq b (outputAt c p a nr Output.Stable s rho v tRead) = true)
    (hb0 : b0 ≤ t) (hhor : t ≤ rho.horizon) :
    InBy c p a nr s rho Output.Stable b t := by
  sorry

end Holes

/-- claim `stableAsynchronyResilient` の骨格の入口: `PersistsFrom` の量化を開いて穴 `stableInBy` に渡す。
手書き `concreteConsensus`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の `stableAsynchronyResilient` の枝に当たる。 -/
theorem persistsFrom (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (tRead b0 b1 : Int)
    (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho) (hreg : OutageRegime c p a nr s rho tRead b0 b1) :
    PersistsFrom c p a nr s rho Output.Stable tRead b0 := by
  unfold PersistsFrom
  intro v b t h
  obtain ⟨⟨⟨hv, hpre⟩, hb0⟩, hhor⟩ := h
  exact stableInBy c p a nr s rho hwf hdom hreg v b t hv hpre hb0 hhor

end Proofs.Consensus.PersistsHoles
