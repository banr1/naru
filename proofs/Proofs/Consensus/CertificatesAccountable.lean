import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Derivation
import Proofs.Consensus.Weights
import Proofs.Consensus.Slashing
import Mathlib.Tactic

/-!
# claim `certificatesAccountable`(C71 の補題)

2 つの名前付きブロック `c` / `c2` の導出状態がそれぞれ `target` / `target2` を finalize していて(`Finalizes`)、
2 本の chain の祖先の範囲で root がブロックを一意に決める(`CollisionFree`)なら、`target` と `target2` は互換(`compatible`)か、
2 本の chain の attestation の間に重み `2q − W` 以上の slashable な署名者集合がある(`Evidence`)。
手書き `namedAccountableSafety_oriented` / `namedChainAccountableSafety` / `pureAccountableFinalitySafety`
(`DecoupledConsensusProofs/Protocol/ChainState/WholeRunFinalitySafety.lean`)の筋をそのまま写す:
高さの低い方 `h₁ = hF₁` を取り、`h₁ = 0` なら `target = Genesis` で互換、さもなければ `Derivation.lean` の証明書
(`cert`: `finalityPair = some ⟨h₁, root target⟩` の定足数 `QF`)と、もう一方の chain の高さ `h₁` の横断(`crossing`: 祖先 `X` と
`matchesEntry … h₁ (root X)` の定足数 `QP`)を取り、`root X = root target` なら `CollisionFree` から `X = target` で互換、
さもなければ `QF ∩ QP`(`Weights.lean` の定足数の交わり)の各署名者の 2 つの行が E1 で slashable(`Slashing.lean`)。
-/

namespace Proofs.Consensus.CertificatesAccountable

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Weights Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Evidence
open Statements.Consensus.Spec.Accountability Statements.Consensus.Spec.Interface
open Proofs.Consensus.Blocks Proofs.Consensus.NamedBlocks Proofs.Consensus.Sets Proofs.Consensus.Weights
open Proofs.Consensus.Slashing Proofs.Consensus.Derivation

/-- `RootInjectiveOnAncestors` は対称。 -/
theorem rootInjective_symm {t1 t2 : Block} (h : RootInjectiveOnAncestors t1 t2) : RootInjectiveOnAncestors t2 t1 := by
  intro a c hac
  obtain ⟨⟨ha, hc⟩, hr⟩ := hac
  exact h a c ⟨⟨ha.symm, hc.symm⟩, hr⟩

/-- `HasSlashableWeightBetween` は対称(`slashable` の対称性)。 -/
theorem hasSlashableWeightBetween_symm {e : ProtocolEnv} {A1 A2 : NaruStd.Set CombinedAttestation}
    (h : HasSlashableWeightBetween e A1 A2) : HasSlashableWeightBetween e A2 A1 := by
  obtain ⟨members, hw, hs⟩ := h
  refine ⟨members, hw, fun i hi => ?_⟩
  obtain ⟨a, b, ⟨⟨⟨ha, hb⟩, hav⟩, hbv⟩, hsl⟩ := hs i hi
  exact ⟨b, a, ⟨⟨⟨hb, ha⟩, hbv⟩, hav⟩, by rw [slashable_comm]; exact hsl⟩

/-- 高さの順に向きを付けた本体: `hF₁ ≤ hF₂` のとき、`f₁` と `f₂` は互換か、2 本の chain の間に slashable な重みがある。 -/
theorem oriented (e : ProtocolEnv) (cfg : HeightConfig) (hv : Sorted (validators e.electorate))
    {B₁ B₂ : NamedBlock} (hroot : RootInjectiveOnAncestors (eraseBlock B₁) (eraseBlock B₂))
    (hle : (deriveNamed e cfg B₁).hF ≤ (deriveNamed e cfg B₂).hF) :
    compatible (deriveNamed e cfg B₁).f (deriveNamed e cfg B₂).f = true ∨
      HasSlashableWeightBetween e (chainAttestations (eraseBlock B₁)) (chainAttestations (eraseBlock B₂)) := by
  have I₁ := deriveNamed_inv e cfg B₁
  have I₂ := deriveNamed_inv e cfg B₂
  set st₁ := deriveNamed e cfg B₁ with hst₁
  set st₂ := deriveNamed e cfg B₂ with hst₂
  by_cases hz : st₁.hF = 0
  · left
    rw [I₁.hF_zero hz]
    unfold compatible
    rw [Bool.or_eq_true]
    exact Or.inl (preceq_genesis _)
  · obtain ⟨QF, hQFs, hQFq, hwF⟩ := I₁.cert hz
    have h1 : 1 ≤ st₁.hF := Nat.one_le_iff_ne_zero.mpr hz
    have h2 : st₁.hF < st₂.h := Nat.lt_of_le_of_lt hle (Nat.lt_of_le_of_lt I₂.hF_le_hJ I₂.hJ_lt_h)
    obtain ⟨X, hX, QP, hQPs, hQPq, hwP⟩ := I₂.crossing st₁.hF h1 h2
    by_cases hxr : root X = root st₁.f
    · left
      have hXT : X = st₁.f := hroot X st₁.f ⟨⟨Or.inr hX, Or.inl I₁.f_preceq⟩, hxr⟩
      rw [← hXT]
      exact compatible_of_preceq_common hX I₂.f_preceq
    · right
      refine ⟨(QF.inter QP).elems, ?_⟩
      dsimp only
      refine ⟨?_, ?_⟩
      · have hq := quorum_intersection hv hQFs hQPs hQFq hQPq
        unfold HasIntersectionWeight at hq ⊢
        rw [weightOf_eq (Sorted.toSet _), toFinset_toSet, ← weightOf_eq (hQFs.inter QP)]
        exact hq
      · intro i hi
        rw [contains_iff_mem vid_eq, mem_toSet_iff vid_eq, mem_inter_iff vid_eq] at hi
        obtain ⟨hiF, hiP⟩ := hi
        obtain ⟨a, ⟨ca, hca, haMem⟩, hav, hap⟩ := hwF i hiF
        obtain ⟨b, ⟨cb, hcb, hbMem⟩, hbv, hbm⟩ := hwP i hiP
        refine ⟨eraseAttestation a, eraseAttestation b,
          ⟨⟨⟨contains_chainAttestations_of_row haMem hca, contains_chainAttestations_of_row hbMem hcb⟩, hav⟩, hbv⟩, ?_⟩
        exact slashable_of_e1 (p := ⟨st₁.hF, root st₁.f⟩) (hav.trans hbv.symm) hap
          (conflictsWithFinality_erase_of_matchesEntry hbm hxr)

/-- claim `certificatesAccountable` の本体(義務の型そのまま)。 -/
theorem certificatesAccountable : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) («s» : Model.Consensus.Execution.Setup.Setup) («c» : Model.Consensus.Objects.NamedBlocks.NamedBlock) («c2» : Model.Consensus.Objects.NamedBlocks.NamedBlock) («target» : Model.Consensus.Objects.Blocks.Block) («target2» : Model.Consensus.Objects.Blocks.Block), Statements.Consensus.Spec.Claims.certificatesAccountable committee' proposer' «s» «c» «c2» «target» «target2» := by
  intro committee' proposer' s c c2 target target2
  unfold Statements.Consensus.Spec.Claims.certificatesAccountable
  intro h
  obtain ⟨⟨⟨hwf, hcf⟩, hfin1⟩, hfin2⟩ := h
  have hv : Sorted (validators s.e.electorate) := by
    unfold Statements.Consensus.Spec.Conditions.SetupWellFormed at hwf
    obtain ⟨⟨⟨_, hnorm⟩, _⟩, _⟩ := hwf
    exact sorted_of_normalized hnorm
  unfold CollisionFree at hcf
  unfold Finalizes NamedFinalizedAt at hfin1 hfin2
  obtain ⟨_, hT1, -⟩ := hfin1
  obtain ⟨_, hT2, -⟩ := hfin2
  unfold Evidence
  rw [← hT1, ← hT2]
  rcases Nat.le_total (deriveNamed s.e s.cfg c).hF (deriveNamed s.e s.cfg c2).hF with hle | hle
  · exact oriented s.e s.cfg hv hcf hle
  · rcases oriented s.e s.cfg hv (rootInjective_symm hcf) hle with hc | hs
    · exact Or.inl (by rw [compatible_comm]; exact hc)
    · exact Or.inr (hasSlashableWeightBetween_symm hs)

end Proofs.Consensus.CertificatesAccountable
