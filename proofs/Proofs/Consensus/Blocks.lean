import Model.Consensus.Objects.Blocks

/-!
# ブロックの祖先関係の補題(C71 の補題)

生成 Model の `Model.Consensus.Objects.Blocks.preceq b c`(`b` が `c` の祖先か `c` 自身。`c` の親を遡る構造的再帰)の基本性質。
手書き `Block.preceq_self`(`DecoupledConsensusProofs/Objects/Ancestry.lean`)に当たる補題を、生成 Model の定義に対して書き直す。
-/

namespace Proofs.Consensus.Blocks

open Model.Consensus.Objects.Blocks

/-- 反射律: どのブロックも自分自身の接頭辞である(`preceq b b = true`)。 -/
theorem preceq_self (b : Block) : preceq b b = true := by
  cases b <;> simp [preceq]

end Proofs.Consensus.Blocks
