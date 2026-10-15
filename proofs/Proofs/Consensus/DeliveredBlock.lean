import Proofs.Consensus.ParentSlot
import Mathlib.Tactic

/-!
# 配送の前提が親の受理を与え、発行されたブロックの受理の条件は `extends_f` だけが残る(C71 の補題)

`BlockReceipt.deliver_block_mem` の条件のうち、名前付きの親が受信者の bodies にあること(`hpar`)と親が tree にあること
(`Admits.parent_mem`)を、run の前提 `DeliveryWellFormed`(`ExecutionValid` の一部)から外す。`DeliveryWellFormed` は添字 `i` の
配送 `Deliver v o t` について、配送の直前の `v` の store で依存が揃い(`depsPresent`: ブロックなら名前付きの親が bodies にある)
まだ受理していない(`!processed`: ブロックなら bodies に無い)ことを要求する(`deliver_deps`)。bodies の消去は tree にある
(`Carrier.StoreInv.tree`)ので、消去したブロックの親(= 名前付きの親の消去 `NamedBlocks.parent_eraseBlock`)は tree にある
(`deliver_parent_tree`)。

周回 150・151 の補題(`Proposal.emits_block_fields` / `emits_block_slot_le`、`ParentSlot.emits_block_parent_slot`)と合わせると、
honest な受信者 `w` に発行より後に配送された発行されたブロック `D` について、`Admits` の 5 つの守りのうち `extends_f`
(`preceq st.f (eraseBlock D)`)を除く 4 つが setup と run の前提(`ScheduleWellFormed` / `DeliveryWellFormed` / `0 < Δ`)から
出る(`emits_admits_of_extends`。名前付きの親の所属は `deliver_deps`、運ばれた attestation の round の守りは `emits_block_fields`)。したがって `extends_f` だけを仮定に、配送の後の tree にある(`deliver_emitted_block_mem`)、
以後ずっと tree にあり受信の印が配送の時刻より後の `γ` より前(`deliver_emitted_block_stamped`)、tree に無かったなら
bodies にもある(`deliver_emitted_block_mem_bodies`)。配送の前に bodies に無いこと(`deliver_not_processed`)は
`DeliveryWellFormed` の `!processed` から出る。

残る `extends_f` は finality の事実(受信者の確定のブロックが honest な提案の祖先であること)で、後続の層。
手書きでは `Protocol/Handlers/Blocks.lean` の `on_block` の受理の分岐の前提と、`ProposalBridge.proposedBlockAt_admit` の
`hparentPreceq` 以外の前提に当たる。
-/

namespace Proofs.Consensus.DeliveredBlock

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.Carrier
open Proofs.Consensus.BlockReceipt (Admits)

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-! ## 配送の前提 -/

/-- **配送の直前に名前付きの親が受信者の bodies にあり、ブロック自身は無い**(`DeliveryWellFormed` の `depsPresent` と
`!processed`)。 -/
theorem deliver_deps (hdw : DeliveryWellFormed c p a nr s rho) {j : Nat} {w : ValidatorId} {b : NamedBlock} {t : Int}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block b) t)) :
    namedParent b ∈ (worldAt (stateBefore c p a nr s rho j) w).st.bodies.elems ∧
      b ∉ (worldAt (stateBefore c p a nr s rho j) w).st.bodies.elems := by
  obtain ⟨⟨-, hdep⟩, hnp⟩ := hdw j w _ t hj
  refine ⟨(contains_iff_mem nb_compare_eq_iff _ _).mp hdep, fun hb => hnp ?_⟩
  exact (contains_iff_mem nb_compare_eq_iff _ _).mpr hb

/-- 配送の直前にブロックは受信者の bodies に無い(`DeliveryWellFormed` の `!processed`)。 -/
theorem deliver_not_processed (hdw : DeliveryWellFormed c p a nr s rho) {j : Nat} {w : ValidatorId} {b : NamedBlock}
    {t : Int} (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block b) t)) :
    b ∉ (worldAt (stateBefore c p a nr s rho j) w).st.bodies.elems :=
  (deliver_deps c p a nr s rho hdw hj).2

/-- **配送の直前に、消去したブロックの親が受信者の tree にある**(`Admits.parent_mem`): 名前付きの親は bodies にあり
(`deliver_deps`)、bodies の消去は tree にある(`StoreInv.tree`)。 -/
theorem deliver_parent_tree (hdw : DeliveryWellFormed c p a nr s rho) {j : Nat} {w : ValidatorId} {b : NamedBlock}
    {t : Int} (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block b) t)) :
    parent (eraseBlock b) ∈ (worldAt (stateBefore c p a nr s rho j) w).st.core.tree.elems := by
  rw [Proofs.Consensus.NamedBlocks.parent_eraseBlock]
  exact (stateBefore_inv c p a nr s rho j w).tree _ (deliver_deps c p a nr s rho hdw hj).1

/-! ## 発行されたブロック -/

/-- **発行されたブロックの受理の条件**: honest な `w` に発行の時刻 `t` より後の `t2` に配送されたなら、配送の直前の `w` の
store について `Admits` の守りのうち `extends_f` を除く 4 つが run の前提から出る。`extends_f` を足せば `Admits`。 -/
theorem emits_admits_of_extends (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {D : NamedBlock} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t < t2)
    (hf : preceq (worldAt (stateBefore c p a nr s rho j) w).st.core.f (eraseBlock D) = true) :
    Admits p (worldAt (stateBefore c p a nr s rho j) w).st.core (eraseBlock D) where
  slot_le := Proofs.Consensus.Proposal.emits_block_slot_le c p a nr s rho hsch hδ hem hw hj ht
  parent_mem := deliver_parent_tree c p a nr s rho hdw hj
  extends_f := hf
  proposer := (Proofs.Consensus.Proposal.emits_block_fields c p a nr s rho hem).2.2.1
  parent_slot := Proofs.Consensus.ParentSlot.emits_block_parent_slot c p a nr s rho hsch hδ hem

/-- **発行されたブロックは、`extends_f` の下で配送の後の受信者の tree にある**。 -/
theorem deliver_emitted_block_mem (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {D : NamedBlock} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t < t2)
    (hf : preceq (worldAt (stateBefore c p a nr s rho j) w).st.core.f (eraseBlock D) = true) :
    eraseBlock D ∈ (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems :=
  Proofs.Consensus.BlockReceipt.deliver_block_mem c p a nr s rho hj (deliver_deps c p a nr s rho hdw hj).1
    (Proofs.Consensus.Proposal.emits_block_fields c p a nr s rho hem).2.2.2
    (emits_admits_of_extends c p a nr s rho hsch hdw hδ hem hw hj ht hf)

/-- 配送の直前の tree に無かったなら、配送の後の受信者の bodies に名前付きのブロックがある。 -/
theorem deliver_emitted_block_mem_bodies (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {D : NamedBlock} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t < t2)
    (hf : preceq (worldAt (stateBefore c p a nr s rho j) w).st.core.f (eraseBlock D) = true)
    (hnew : eraseBlock D ∉ (worldAt (stateBefore c p a nr s rho j) w).st.core.tree.elems) :
    D ∈ (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.bodies.elems :=
  Proofs.Consensus.BlockReceipt.deliver_block_mem_bodies c p a nr s rho hj (deliver_deps c p a nr s rho hdw hj).1
    (Proofs.Consensus.Proposal.emits_block_fields c p a nr s rho hem).2.2.2
    (emits_admits_of_extends c p a nr s rho hsch hdw hδ hem hw hj ht hf) hnew

/-- **配送の時刻が `γ` より前なら、`extends_f` の下で以後ずっと受信者の tree にあり受信の印が `γ` より前**。 -/
theorem deliver_emitted_block_stamped (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {D : NamedBlock} {t t2 γ : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t < t2) (ht2 : t2 < γ)
    (hf : preceq (worldAt (stateBefore c p a nr s rho j) w).st.core.f (eraseBlock D) = true) {i : Nat} (hji : j < i) :
    eraseBlock D ∈ (worldAt (stateBefore c p a nr s rho i) w).st.core.tree.elems ∧
      Model.Consensus.Objects.Time.occurrenceBefore
        ((worldAt (stateBefore c p a nr s rho i) w).st.core.timestampBlock.get? (eraseBlock D)) γ = true :=
  Proofs.Consensus.BlockReceipt.deliver_block_stamped c p a nr s rho
    (Proofs.Consensus.Window.eventsSorted_of_schedule hsch)
    (fun _ hev => (Proofs.Consensus.Window.eventTime_bounds hsch hev).1) hj ht2
    (deliver_deps c p a nr s rho hdw hj).1 (Proofs.Consensus.Proposal.emits_block_fields c p a nr s rho hem).2.2.2
    (emits_admits_of_extends c p a nr s rho hsch hdw hδ hem hw hj ht hf) hji

end Run

end Proofs.Consensus.DeliveredBlock
