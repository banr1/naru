import Model.Consensus.Objects.Blocks

/-!
# ブロックの祖先関係の補題(C71 の補題)

生成 Model の `Model.Consensus.Objects.Blocks.preceq b c`(`b` が `c` の祖先か `c` 自身。`c` の親を遡る構造的再帰)の基本性質。
手書き `Block.preceq_self` / `Block.preceq_trans` / `preceq_linear` / `compatible_of_preceq_common`
(`DecoupledConsensusProofs/Objects/Ancestry.lean`)に当たる補題を、生成 Model の定義に対して書き直す。
-/

namespace Proofs.Consensus.Blocks

open Model.Consensus.Objects.Blocks

/-- 反射律: どのブロックも自分自身の接頭辞である(`preceq b b = true`)。 -/
theorem preceq_self (b : Block) : preceq b b = true := by
  cases b <;> simp [preceq]

/-- 推移律: `a ⪯ b` かつ `b ⪯ c` なら `a ⪯ c`。`c` の親を遡る帰納法で、`b = c` なら `a ⪯ b = c`、
さもなければ `b ⪯ parent c` に帰納法の仮定を使う。 -/
theorem preceq_trans {a b c : Block} (hab : preceq a b = true) (hbc : preceq b c = true) :
    preceq a c = true := by
  induction c with
  | Genesis =>
    simp only [preceq, beq_iff_eq] at hbc
    subst hbc
    exact hab
  | Node p s r v sup ats i ih =>
    simp only [preceq, Bool.or_eq_true, beq_iff_eq] at hbc ⊢
    rcases hbc with rfl | hbp
    · simpa only [preceq, Bool.or_eq_true, beq_iff_eq] using hab
    · exact Or.inr (ih hbp)

/-- 真の接頭辞 `prec a b`(`a != b && preceq a b`)は接頭辞 `preceq a b` を含む。 -/
theorem preceq_of_prec {a b : Block} (h : prec a b = true) : preceq a b = true := by
  unfold prec at h
  exact (Bool.and_eq_true _ _ |>.mp h).2

/-- genesis はどのブロックの接頭辞でもある。 -/
theorem preceq_genesis (c : Block) : preceq Block.Genesis c = true := by
  induction c with
  | Genesis => simp [preceq]
  | Node p s r v sup ats i ih =>
    simp only [preceq, Bool.or_eq_true]
    exact Or.inr ih

/-- 親は子の接頭辞である。 -/
theorem preceq_node (p : Block) (s : Nat) (r : Model.Consensus.Objects.Identifiers.BlockId)
    (v sup : List GoldfishVote) (ats : List CombinedAttestation) (i : Model.Consensus.Objects.Identifiers.ValidatorId) :
    preceq p (Block.Node p s r v sup ats i) = true := by
  simp only [preceq, Bool.or_eq_true]
  exact Or.inr (preceq_self p)

/-- 同じブロックの 2 つの祖先は一方が他方の接頭辞である(`Z` の親を遡る帰納法)。 -/
theorem preceq_linear {X Y Z : Block} (hX : preceq X Z = true) (hY : preceq Y Z = true) :
    preceq X Y = true ∨ preceq Y X = true := by
  induction Z with
  | Genesis =>
    simp only [preceq, beq_iff_eq] at hX hY
    subst hX
    subst hY
    exact Or.inl (preceq_self _)
  | Node p s r v sup ats i ih =>
    simp only [preceq, Bool.or_eq_true, beq_iff_eq] at hX hY
    rcases hX with rfl | hX
    · rcases hY with rfl | hY
      · exact Or.inl (preceq_self _)
      · right
        simp only [preceq, Bool.or_eq_true]
        exact Or.inr hY
    · rcases hY with rfl | hY
      · left
        simp only [preceq, Bool.or_eq_true]
        exact Or.inr hX
      · exact ih hX hY

/-- 同じブロックの 2 つの祖先は互換(`compatible`)。手書き `compatible_of_preceq_common`。 -/
theorem compatible_of_preceq_common {X Y Z : Block} (hX : preceq X Z = true) (hY : preceq Y Z = true) :
    compatible X Y = true := by
  unfold compatible
  rw [Bool.or_eq_true]
  exact preceq_linear hX hY

/-- `compatible` は対称。 -/
theorem compatible_comm (b c : Block) : compatible b c = compatible c b := by
  unfold compatible
  exact Bool.or_comm _ _

end Proofs.Consensus.Blocks
