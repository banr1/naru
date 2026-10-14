import Statements.Consensus.Spec.Claims
import Proofs.Consensus.EmissionSafety
import Proofs.Consensus.Attribution
import Mathlib.Tactic

/-!
# claim `honestNeverSlashed`(C71 の補題)

前提 `SetupWellFormed ∧ RunDomain ∧ UnforgeableRun` の下で、honest な validator `v` は slash されない
(`¬ Slashes s rho v`: どの 2 ノード `u` / `u2` のどの時刻 `t` / `t2` の store の attestation の間にも、`v` の署名の
slashable な組は無い)。使う前提は `UnforgeableRun` の `UnforgeableSignatures`(carried)と `EventsSorted` だけで、
`SetupWellFormed` / `RunDomain` / `HonestOnly` / `0 ≤ horizon` は使わない。

筋(手書き `Consensus.honestNeverSlashed` → `validatorVoteSafety.attributed` / `attributedVoteSafety`、
`DecoupledConsensusProofs/ReviewTheorem.lean` / `Protocol/ChainState/ValidatorVoteSafety.lean`):
1. store の `v` の署名の attestation は `v` の tick が実際に出した行の消去(`Attribution.attributed`: store の不変条件、
   bodies のブロックは処理されたブロック、`UnforgeableSignatures` の carried)。
2. `v` の 2 つの発行の消去は slashable でない(`EmissionSafety.emission_not_slashable`: 署名の記録の性質と run に沿った単調性)。
-/

namespace Proofs.Consensus.HonestNeverSlashed

open Model.Consensus.Objects.Identifiers Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Conditions Statements.Consensus.Spec.Interface Statements.Consensus.Spec.Accountability
open Proofs.Consensus.EmissionSafety Proofs.Consensus.Attribution

/-- 義務の型そのまま(`generated/obligations.json` の `type`)。 -/
theorem honestNeverSlashed : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) (awake' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Bool)) (newRoot' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Model.Consensus.Objects.Identifiers.BlockId)) («s» : Model.Consensus.Execution.Setup.Setup) («rho» : Model.Consensus.Execution.Run.NamedRun), Statements.Consensus.Spec.Claims.honestNeverSlashed committee' proposer' awake' newRoot' «s» «rho» := by
  intro c p a nr s rho
  unfold Statements.Consensus.Spec.Claims.honestNeverSlashed
  intro h v hv hsl
  obtain ⟨-, hunf⟩ := h
  unfold UnforgeableRun at hunf
  obtain ⟨⟨⟨hsig, hsorted⟩, -⟩, -⟩ := hunf
  unfold UnforgeableSignatures at hsig
  obtain ⟨-, hcar⟩ := hsig
  unfold Slashes at hsl
  obtain ⟨u, u2, t, t2, hsb⟩ := hsl
  unfold SlashableBetween at hsb
  obtain ⟨x, y, ⟨⟨⟨hx, hy⟩, hxv⟩, hyv⟩, hslash⟩ := hsb
  obtain ⟨ra, i, ta, hi, ha, rfl⟩ := attributed c p a nr s rho hcar hsorted u t hx hxv hv
  obtain ⟨rb, j, tb, hj, hb, rfl⟩ := attributed c p a nr s rho hcar hsorted u2 t2 hy hyv hv
  rw [emission_not_slashable c p a nr s rho v hi ha hj hb] at hslash
  exact Bool.false_ne_true hslash

end Proofs.Consensus.HonestNeverSlashed
