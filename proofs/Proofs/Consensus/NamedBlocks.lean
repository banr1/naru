import Model.Consensus.Objects.NamedBlocks
import Model.Consensus.Protocol.Evidence
import Proofs.Consensus.Blocks
import Proofs.Consensus.Sets

/-!
# 名前付きブロックと消去(C71 の補題)

生成 Model の `NamedBlock`(行が `NamedAttestation` のブロック)と `eraseBlock`(行を `eraseAttestation` で `CombinedAttestation` に
落とした `Block`)、名前付きの祖先関係 `namedPreceq` について:
`namedPreceq` の反射律と子への延長、`namedPreceq a b → preceq (eraseBlock a) (eraseBlock b)`、
名前付き祖先 `c` の行 `row` の消去が `chainAttestations (eraseBlock B)` に入ること(`contains … = true`)。
手書き `named_self` / `named_extend` / `NamedWire.erase_preceq` / `named_row_erase_mem`
(`DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean` / `Main.lean`)に当たる。
-/

namespace Proofs.Consensus.NamedBlocks

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.NamedBlocks Model.Consensus.Protocol.Evidence
open Proofs.Consensus.Blocks

/-- 反射律。 -/
theorem namedPreceq_self (b : NamedBlock) : namedPreceq b b = true := by
  cases b <;> simp [namedPreceq]

/-- 親の祖先は子の祖先。 -/
theorem namedPreceq_node {a p : NamedBlock} (h : namedPreceq a p = true) (s : Nat)
    (r : Model.Consensus.Objects.Identifiers.BlockId) (v sup : List GoldfishVote) (rows : List NamedAttestation)
    (i : Model.Consensus.Objects.Identifiers.ValidatorId) :
    namedPreceq a (NamedBlock.Node p s r v sup rows i) = true := by
  simp only [namedPreceq, Bool.or_eq_true]
  exact Or.inr h

/-- genesis の祖先は genesis だけ。 -/
theorem namedPreceq_genesis {a : NamedBlock} (h : namedPreceq a NamedBlock.Genesis = true) :
    a = NamedBlock.Genesis := by
  simpa [namedPreceq] using h

/-- 名前付きの祖先関係は消去で保たれる。 -/
theorem eraseBlock_preceq {a : NamedBlock} : ∀ {b : NamedBlock}, namedPreceq a b = true →
    preceq (eraseBlock a) (eraseBlock b) = true
  | NamedBlock.Genesis, h => by
    rw [namedPreceq_genesis h]
    exact preceq_self _
  | NamedBlock.Node p s r v sup rows i, h => by
    simp only [namedPreceq, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact preceq_self _
    · have ih := eraseBlock_preceq h
      simp only [eraseBlock, preceq, Bool.or_eq_true]
      exact Or.inr ih

/-- 親の消去は子の消去の接頭辞。 -/
theorem eraseBlock_node_preceq (p : NamedBlock) (s : Nat) (r : Model.Consensus.Objects.Identifiers.BlockId)
    (v sup : List GoldfishVote) (rows : List NamedAttestation) (i : Model.Consensus.Objects.Identifiers.ValidatorId) :
    preceq (eraseBlock p) (eraseBlock (NamedBlock.Node p s r v sup rows i)) = true := by
  simp only [eraseBlock]
  exact preceq_node _ _ _ _ _ _ _

/-- 名前付き祖先 `c` の行 `row` の消去は、消去した tip の `chainAttestations` に入る。手書き `named_row_erase_mem`。 -/
theorem contains_chainAttestations_of_row {c : NamedBlock} {row : NamedAttestation}
    (hrow : row ∈ namedAttestations c) :
    ∀ {B : NamedBlock}, namedPreceq c B = true →
      (chainAttestations (eraseBlock B)).contains (eraseAttestation row) = true
  | NamedBlock.Genesis, hc => by
    rw [namedPreceq_genesis hc] at hrow
    simp [namedAttestations] at hrow
  | NamedBlock.Node p s r v sup rows i, hc => by
    rw [Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.ca_compare_eq_iff]
    simp only [namedPreceq, Bool.or_eq_true, beq_iff_eq] at hc
    simp only [eraseBlock, chainAttestations]
    rw [Proofs.Consensus.Sets.mem_union_iff Proofs.Consensus.Orders.ca_compare_eq_iff]
    rcases hc with rfl | hc
    · left
      rw [Proofs.Consensus.Sets.mem_toSet_iff Proofs.Consensus.Orders.ca_compare_eq_iff]
      simp only [namedAttestations] at hrow
      exact List.mem_map_of_mem hrow
    · right
      have ih := contains_chainAttestations_of_row hrow hc
      rw [Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.ca_compare_eq_iff] at ih
      exact ih

end Proofs.Consensus.NamedBlocks
