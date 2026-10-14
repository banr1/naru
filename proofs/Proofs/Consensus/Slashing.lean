import Model.Consensus.Protocol.ChainState
import Model.Consensus.Objects.NamedBlocks

/-!
# slashable の対称性と E1 の証拠(C71 の補題)

生成 Model の `slashable a b = e1Slashable a b || e2Slashable a b`(`Protocol/ChainState.lean`)について、
対称性(`sameValidator` / `e1Fields` / `e2Fields` がそれぞれ対称)と、同じ署名者の 2 つの attestation `a` / `b` で
`a.finalityPair = some p` かつ `conflictsWithFinality b.heightPair p` なら `slashable a b`(E1)であること、
`matchesEntry row.heightPair h X` な名前付き行の消去は、同じ高さ `h` で別の root `T` の finality pair と衝突することを示す。
手書き `slashableBetween_of_e1EvidenceForPair` / `conflictsWithFinality_erase_of_matchesEntry`
(`DecoupledConsensusProofs/Protocol/ChainState/Evidence.lean` / `Main.lean`)に当たる。
-/

namespace Proofs.Consensus.Slashing

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.NamedBlocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Protocol.ChainState

theorem sameValidator_comm (a b : CombinedAttestation) : sameValidator a b = sameValidator b a := by
  unfold sameValidator
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact eq_comm

theorem e1Fields_comm (a b : CombinedAttestation) : e1Fields a b = e1Fields b a := by
  unfold e1Fields
  exact Bool.or_comm _ _

theorem e2Fields_comm (a b : CombinedAttestation) : e2Fields a b = e2Fields b a := by
  unfold e2Fields
  cases ha : a.heightPair <;> cases hb : b.heightPair <;> try rfl
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, fun h => h2 h.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, fun h => h2 h.symm⟩

/-- `slashable` は対称。 -/
theorem slashable_comm (a b : CombinedAttestation) : slashable a b = slashable b a := by
  unfold slashable e1Slashable e2Slashable
  rw [sameValidator_comm, e1Fields_comm, e2Fields_comm]

/-- 同じ署名者で、`a` の finality pair `p` と `b` の height pair が衝突すれば E1 で slashable。 -/
theorem slashable_of_e1 {a b : CombinedAttestation} {p : FinalityPair} (hv : a.valIndex = b.valIndex)
    (hfp : a.finalityPair = some p) (hc : conflictsWithFinality b.heightPair p = true) :
    slashable a b = true := by
  unfold slashable e1Slashable sameValidator e1Fields
  rw [hfp, hv]
  simp [hc]

/-- 高さ `h` で entry `X` に投票した名前付き行の消去は、同じ高さで別の root `T` の finality pair と衝突する
(target なら root が違うので衝突、timeout なら高さだけで衝突)。 -/
theorem conflictsWithFinality_erase_of_matchesEntry {row : NamedAttestation} {h : Nat} {X T : BlockId}
    (hm : matchesEntry row.heightPair h X = true) (hne : X ≠ T) :
    conflictsWithFinality (eraseAttestation row).heightPair ⟨h, T⟩ = true := by
  show conflictsWithFinality (eraseHeightPair row.heightPair) ⟨h, T⟩ = true
  cases hp : row.heightPair with
  | Empty =>
    rw [hp] at hm
    simp [matchesEntry] at hm
  | Vote h' entry timeout =>
    rw [hp] at hm
    simp only [matchesEntry, Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    cases timeout <;> simp [eraseHeightPair, conflictsWithFinality, hne]

end Proofs.Consensus.Slashing
