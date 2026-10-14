import Model.Consensus.Objects.Blocks

/-!
# ブロックの祖先関係の補題(C71 の補題)

生成 Model の `Model.Consensus.Objects.Blocks.preceq b c`(`b` が `c` の祖先か `c` 自身。`c` の親を遡る構造的再帰)の基本性質。
手書き `Block.preceq_self` / `Block.preceq_trans`(`DecoupledConsensusProofs/Objects/Ancestry.lean`)に当たる補題を、
生成 Model の定義に対して書き直す。
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

end Proofs.Consensus.Blocks
