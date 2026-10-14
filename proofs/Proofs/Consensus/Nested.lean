import Model.Consensus.Protocol.Handlers
import Model.Consensus.Spec.Interface
import Statements.Consensus.Spec.Properties
import Proofs.Consensus.Blocks

/-!
# 3 つの出力の入れ子(claim `nested` の補題)

生成 Model の `getStable` / `getConfirmed`(`Model/Consensus/Protocol/Handlers.lean`)は、下の出力より上にある記録だけを返す
(`if preceq st.f st.latestStable then st.latestStable else st.f` の形)ので、どの store でも finalized ⪯ stable ⪯ confirmed が
構成から成り立つ。手書き `DecoupledConsensusProofs/Protocol/Handlers/NestedOutputs.lean`(`finalized_preceq_get_stable` /
`get_stable_preceq_get_confirmed` / `nestedOutputs_holds`)と同じ筋で、run への前提は要らない。
-/

namespace Proofs.Consensus.Nested

open Model.Consensus.Objects.Blocks Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Store

/-- finalized は stable の接頭辞(任意の store)。 -/
theorem f_preceq_getStable (st : Store) : preceq st.f (getStable st) = true := by
  unfold getStable
  split
  · assumption
  · exact Proofs.Consensus.Blocks.preceq_self _

/-- stable は confirmed の接頭辞(任意の store)。 -/
theorem getStable_preceq_getConfirmed (st : Store) :
    preceq (getStable st) (getConfirmed st) = true := by
  unfold getConfirmed
  split
  · assumption
  · exact Proofs.Consensus.Blocks.preceq_self _

/-- どの run・ノード・時刻の読みでも finalized ⪯ stable ⪯ confirmed(property `OutputOrder`)。前提は要らない。 -/
theorem outputOrder
    (committee' : Nat → NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId)
    (proposer' : Nat → Model.Consensus.Objects.Identifiers.ValidatorId)
    (awake' : Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Bool)
    (newRoot' : Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Model.Consensus.Objects.Identifiers.BlockId)
    (s : Model.Consensus.Execution.Setup.Setup) (rho : Model.Consensus.Execution.Run.NamedRun) :
    Statements.Consensus.Spec.Properties.OutputOrder committee' proposer' awake' newRoot' s rho := by
  unfold Statements.Consensus.Spec.Properties.OutputOrder Statements.Consensus.Spec.Properties.Prefix
  refine ⟨fun v t => ?_, fun v t => ?_⟩
  · exact f_preceq_getStable
      (Model.Consensus.Execution.Run.storeAt committee' proposer' awake' newRoot' s rho v t).core
  · exact getStable_preceq_getConfirmed
      (Model.Consensus.Execution.Run.storeAt committee' proposer' awake' newRoot' s rho v t).core

end Proofs.Consensus.Nested
