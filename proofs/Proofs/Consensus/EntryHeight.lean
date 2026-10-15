import Proofs.Consensus.FinalizedSource
import Mathlib.Tactic

/-!
# 高さの入口(C71 の補題)

導出の高さ `h` と、その高さの入口 `tH` について。手書き `NamedEntryHeight`(`Protocol/ChainState/EntryHeight.lean`)の
`entry_ancestor_same_height` / `node_entry_eq_of_height_eq` / `entry_eq_on_plateau` に当たる(`entry_geometry_ancestor` は移していない)。

- **導出の 1 段**: `foldRows` は `h` / `tH` を変えない(`processAttestation` は署名者の集合だけを書く。`foldRows_htH`)。
  `processHeightEvents` は `(h, tH)` を保つか、`advanceHeight` で `(h + 1, l)` にする(`processHeightEvents_htH`)。`foldRows` の後の
  `l` はブロックの消去なので、子の導出の `(h, tH)` は親の導出の `(h, tH)` か `(親の h + 1, 子の消去)`(`deriveNamed_htH_node`)。
- **入口の祖先**: どの `B` にも名前付きの祖先 `K` があり、`K` の消去は `B` の導出の `tH` で、`K` の導出の `h` は `B` の導出の `h`
  (`entry_ancestor_same_height`。genesis は自分)。
- **高さの単調性と平坦な区間**: 祖先の導出の `h` は子孫の導出の `h` 以下(`deriveNamed_h_mono`)。祖先と子孫の導出の `h` が等しければ
  `tH` も等しい(`entry_eq_on_plateau`)。
-/

namespace Proofs.Consensus.EntryHeight

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState
open Proofs.Consensus.NamedBlocks

/-! ## 導出の 1 段 -/

/-- 行の畳み込みは `h` / `tH` を変えない。 -/
theorem foldAttest_htH : ∀ (rows : List NamedAttestation) (st : ChainState),
    (rows.foldl processAttestationWith st).h = st.h ∧ (rows.foldl processAttestationWith st).tH = st.tH
  | [], _ => ⟨rfl, rfl⟩
  | row :: rows, st => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldAttest_htH rows (processAttestationWith st row)
    obtain ⟨hh, htH, -⟩ := Proofs.Consensus.Derivation.pa_fields st (targetedView st row)
    exact ⟨h1.trans hh, h2.trans htH⟩

/-- `foldRows` は `h` / `tH` を変えない。 -/
theorem foldRows_htH (st : ChainState) (geom : Block) (rows : List NamedAttestation) :
    (foldRows st geom rows).h = st.h ∧ (foldRows st geom rows).tH = st.tH :=
  foldAttest_htH rows { st with s := slot geom }

/-- `processHeightEvents` の後の `(h, tH)` は、前の `(h, tH)` か `(h + 1, l)`。 -/
theorem processHeightEvents_htH (e : ProtocolEnv) (cfg : HeightConfig) (st : ChainState) :
    ((processHeightEvents e cfg st).h = st.h ∧ (processHeightEvents e cfg st).tH = st.tH) ∨
    ((processHeightEvents e cfg st).h = st.h + 1 ∧ (processHeightEvents e cfg st).tH = st.l) := by
  unfold processHeightEvents advanceHeight
  dsimp only
  split_ifs <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

/-- 子の導出の `(h, tH)` は、親の導出の `(h, tH)` か `(親の h + 1, 子の消去)`。手書き `transition_height_entry_cases` の
名前付きの読み。 -/
theorem deriveNamed_htH_node (e : ProtocolEnv) (cfg : HeightConfig) (p : NamedBlock) (s : Nat) (r : BlockId)
    (v sup : List GoldfishVote) (rows : List NamedAttestation) (i : ValidatorId) :
    ((deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).h = (deriveNamed e cfg p).h ∧
      (deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).tH = (deriveNamed e cfg p).tH) ∨
    ((deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).h = (deriveNamed e cfg p).h + 1 ∧
      (deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).tH = eraseBlock (NamedBlock.Node p s r v sup rows i)) := by
  simp only [deriveNamed]
  unfold namedTransition transitionRows
  obtain ⟨hh, htH⟩ := foldRows_htH (deriveNamed e cfg p)
    (eraseBlock (NamedBlock.Node p s r v sup rows i)) (namedAttestations (NamedBlock.Node p s r v sup rows i))
  rcases processHeightEvents_htH e cfg (foldRows (deriveNamed e cfg p)
      (eraseBlock (NamedBlock.Node p s r v sup rows i)) (namedAttestations (NamedBlock.Node p s r v sup rows i))) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.trans hh, h2.trans htH⟩
  · exact Or.inr ⟨h1.trans (congrArg (· + 1) hh), h2.trans (Proofs.Consensus.Derivation.foldRows_l _ _ _)⟩

/-! ## 入口の祖先 -/

/-- **どの `B` にも、消去が `B` の導出の `tH` で、導出の `h` が `B` の導出の `h` に等しい名前付きの祖先 `K` がある**。
手書き `entry_ancestor_same_height`。 -/
theorem entry_ancestor_same_height (e : ProtocolEnv) (cfg : HeightConfig) : ∀ B : NamedBlock,
    ∃ K : NamedBlock, namedPreceq K B = true ∧ eraseBlock K = (deriveNamed e cfg B).tH ∧
      (deriveNamed e cfg K).h = (deriveNamed e cfg B).h
  | NamedBlock.Genesis => ⟨NamedBlock.Genesis, namedPreceq_self _, rfl, rfl⟩
  | NamedBlock.Node p s r v sup rows i => by
    rcases deriveNamed_htH_node e cfg p s r v sup rows i with ⟨hh, htH⟩ | ⟨-, htH⟩
    · obtain ⟨K, hK, hKe, hKh⟩ := entry_ancestor_same_height e cfg p
      exact ⟨K, namedPreceq_node hK s r v sup rows i, hKe.trans htH.symm, hKh.trans hh.symm⟩
    · exact ⟨NamedBlock.Node p s r v sup rows i, namedPreceq_self _, htH.symm, rfl⟩

/-! ## 高さの単調性と平坦な区間 -/

/-- 子の導出の `h` は親の導出の `h` 以上。 -/
theorem deriveNamed_h_node_ge (e : ProtocolEnv) (cfg : HeightConfig) (p : NamedBlock) (s : Nat) (r : BlockId)
    (v sup : List GoldfishVote) (rows : List NamedAttestation) (i : ValidatorId) :
    (deriveNamed e cfg p).h ≤ (deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).h := by
  rcases deriveNamed_htH_node e cfg p s r v sup rows i with ⟨hh, -⟩ | ⟨hh, -⟩ <;> omega

/-- 祖先の導出の `h` は子孫の導出の `h` 以下。手書き `derive_height_mono`。 -/
theorem deriveNamed_h_mono (e : ProtocolEnv) (cfg : HeightConfig) {A : NamedBlock} : ∀ {B : NamedBlock},
    namedPreceq A B = true → (deriveNamed e cfg A).h ≤ (deriveNamed e cfg B).h
  | NamedBlock.Genesis, h => by
    rw [namedPreceq_genesis h]
  | NamedBlock.Node p s r v sup rows i, h => by
    simp only [namedPreceq, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact le_refl _
    · exact le_trans (deriveNamed_h_mono e cfg h) (deriveNamed_h_node_ge e cfg p s r v sup rows i)

/-- 子と親の導出の `h` が等しければ、`tH` も等しい。手書き `node_entry_eq_of_height_eq`。 -/
theorem node_entry_eq_of_height_eq (e : ProtocolEnv) (cfg : HeightConfig) (p : NamedBlock) (s : Nat) (r : BlockId)
    (v sup : List GoldfishVote) (rows : List NamedAttestation) (i : ValidatorId)
    (hh : (deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).h = (deriveNamed e cfg p).h) :
    (deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).tH = (deriveNamed e cfg p).tH := by
  rcases deriveNamed_htH_node e cfg p s r v sup rows i with ⟨-, htH⟩ | ⟨hh', -⟩
  · exact htH
  · omega

/-- **祖先と子孫の導出の `h` が等しければ、`tH` も等しい**。手書き `entry_eq_on_plateau`。 -/
theorem entry_eq_on_plateau (e : ProtocolEnv) (cfg : HeightConfig) {A : NamedBlock} : ∀ {B : NamedBlock},
    namedPreceq A B = true → (deriveNamed e cfg A).h = (deriveNamed e cfg B).h →
      (deriveNamed e cfg A).tH = (deriveNamed e cfg B).tH
  | NamedBlock.Genesis, h, _ => by
    rw [namedPreceq_genesis h]
  | NamedBlock.Node p s r v sup rows i, h, hh => by
    simp only [namedPreceq, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · rfl
    · have hlow := deriveNamed_h_mono e cfg h
      have hge := deriveNamed_h_node_ge e cfg p s r v sup rows i
      have hpa : (deriveNamed e cfg A).h = (deriveNamed e cfg p).h := by omega
      have hpn : (deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).h = (deriveNamed e cfg p).h := by omega
      exact (entry_eq_on_plateau e cfg h hpa).trans (node_entry_eq_of_height_eq e cfg p s r v sup rows i hpn).symm

end Proofs.Consensus.EntryHeight
