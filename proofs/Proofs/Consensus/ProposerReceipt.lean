import Proofs.Consensus.BlockSynchrony
import Mathlib.Tactic

/-!
# 提案者自身の受理と、締切の読みのすべての honest な受信者の tree(C71 の補題)

`BlockSynchrony.partialSynchrony_emitted_block_mem` は、ブロックの提案者(発行者)でない honest な受信者 `w ≠ v` に限っていた。
提案者自身は配送に頼らず、提案の tick の中で自分のブロックを処理する: `tick` の提案の務め `proposeBlockWith` は、時計を合わせた
store `st0` の `proposalWith` の出力 `D` を `onBlockWith … st0 D` で受理してから出す。

- **受理の守り**: `st0` について `Admits` の 5 つの守りが出る。slot は `st0` の slot そのもの(`proposalWith_slot`)、名前付きの親は
  bodies にあり(`proposalWith_parent_mem`)その消去は tree にある(`Carrier.StoreInv.tree`)、`f ⪯ j` の下で親の head は `f` を延ばす
  (`ProposerFinality.proposalWith_extends`)、提案者は `proposer' (slot)`(`Proposal.tick_block_shape`)、親の slot はブロックの slot
  より小さい(run では `ParentSlot.emits_block_parent_slot`。tick の補題では仮定)。運ばれた attestation の round の守りも通る
  (`proposalWith_admissible`)ので、`onBlockWith` の後の tree にある(`BlockReceipt.onBlockWith_mem_tree`)。
- **tick の残りの務め**: 投票・確定の更新・attestation は tree のブロックを保存する(`BlockStamps.Step` の `keep`)。提案の務めが
  走らない経路はブロックを出さないので起きない。したがって tick の後の tree にある(`tick_block_mem`、`Trees.tick_treeInv` と同じ
  16 経路のうち提案の務めが走る 8 経路)。
- **run**: 発行されたブロックは、発行の tick の直後の提案者の tree にあり(`emits_block_mem_self`)、以後ずっと残る
  (`BlockStamps.stateBefore_keep`)。発行の時刻 `t` より後の時刻の読みの tree にもある(`emits_block_mem_stateBeforeTime_self`)。
  受信者の FG root の事実も配送も要らない。
- **すべての honest な受信者**: 締切 `max t tGST + Δ` は `0 < Δ` で `t` より後なので、提案者自身は上の補題、提案者でない受信者は
  `BlockSynchrony.partialSynchrony_emitted_block_mem` で、`w ≠ v` の仮定なしに締切の読みの tree にある
  (`partialSynchrony_emitted_block_mem_honest`)。

手書きの対応: `Protocol/Handlers/HonestProposalAdmission.lean` の `acceptsAt_proposedBlock`(提案者自身の受理)と、
それを使う `ProposalAdoptionNamedClosed.lean` の `proposedBlock_admittedBefore_vote_after_gst_named` の提案者の分岐。手書きの結論は投票の時刻より前の受理の event で、ここは
締切の読みの tree への所属。FG root が honest な提案の祖先であること(liveness の本体)は残る。
-/

namespace Proofs.Consensus.ProposerReceipt

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Grades
open Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick Model.Consensus.Protocol.Schedule
open Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.BlockReceipt (Admits)
open Proofs.Consensus.BlockStamps (Step SStep)
open Proofs.Consensus.ProposerFinality (FJ)

/-! ## 提案の務めの受理 -/

section Tick

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
  (nd : Node) (st : NamedStore) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int)

/-- 1 段の後も tree のブロックは残る(`BlockStamps.Step.keep`)。 -/
theorem mem_of_sstep {X Y : NamedStore} {B : Block} (h : SStep X Y) (hB : B ∈ X.core.tree.elems) :
    B ∈ Y.core.tree.elems :=
  (h.keep B hB).1

/-- **提案の務めの受理**: `proposalWith` の出力 `b` は、提案者の bodies の消去が tree にあり `f ⪯ j` で、提案者が
`proposer' (slot)`、親の slot がブロックの slot より小さければ、`proposeBlockWith` の後の提案者の tree にある。 -/
theorem proposeBlockWith_mem {b : NamedBlock} (hb : proposalWith nr cache .PoolAndCarried e hc nd st = some b)
    (htree : ∀ D, D ∈ st.bodies.elems → eraseBlock D ∈ st.core.tree.elems) (hfj : FJ st.core)
    (hp : p st.core.s = nd.valIndex) (hps : slot (parent (eraseBlock b)) < slot (eraseBlock b)) :
    eraseBlock b ∈ (proposeBlockWith c p nr cache e hc cfg nd st).1.core.tree.elems := by
  have hs := Proofs.Consensus.Proposal.proposalWith_slot nr cache e hc nd st hb
  have hadm : Admits p st.core (eraseBlock b) :=
    { slot_le := le_of_eq hs
      parent_mem := by
        rw [Proofs.Consensus.NamedBlocks.parent_eraseBlock]
        exact htree _ (Proofs.Consensus.Proposal.proposalWith_parent_mem nr cache e hc nd st hb)
      extends_f := Proofs.Consensus.ProposerFinality.proposalWith_extends nr cache e hc nd hfj hb
      proposer := by
        rw [Proofs.Consensus.Proposal.proposalWith_proposer nr cache e hc nd st hb, hs, hp]
      parent_slot := hps }
  unfold proposeBlockWith
  rw [hb]
  exact Proofs.Consensus.BlockReceipt.onBlockWith_mem_tree c p e hc cfg CarriedAdmission.AlsoCarried
    (Proofs.Consensus.Proposal.proposalWith_parent_mem nr cache e hc nd st hb)
    (Proofs.Consensus.Proposal.proposalWith_admissible nr cache e hc nd st hb) hadm

/-- **tick が出すブロックは tick の後の自分の tree にある**: 提案の務めが受理し(`proposeBlockWith_mem`)、残りの務めは tree の
ブロックを保存する。前提は tick の前の store の bodies の消去が tree にあること、`f ⪯ j`、親の slot の守り。 -/
theorem tick_block_mem {D : NamedBlock} (h : NamedObject.Block D ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2)
    (htree : ∀ B, B ∈ st.bodies.elems → eraseBlock B ∈ st.core.tree.elems) (hfj : FJ st.core)
    (hps : slot (parent (eraseBlock D)) < slot (eraseBlock D)) :
    eraseBlock D ∈ (tick c p a nr cache e hc cfg nd st rec t).1.core.tree.elems := by
  obtain ⟨h0, ht, hp, hD⟩ := Proofs.Consensus.Proposal.tick_block_shape c p a nr cache e hc cfg nd st rec t h
  have hprop : ((decide (0 < slotOf e t) && t == proposalTime e (slotOf e t)) &&
      (p (slotOf e t) == nd.valIndex)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨h0, ht⟩, hp⟩
  have hmem := proposeBlockWith_mem c p nr cache e hc cfg nd
    { st with core := { st.core with t := t, s := slotOf e t } } hD htree hfj hp hps
  unfold tick
  dsimp only at hmem ⊢
  simp only [hprop, ↓reduceIte]
  generalize proposeBlockWith c p nr cache e hc cfg nd _ = R at hmem ⊢
  have hX : SStep R.1 R.1 := Step.refl _
  split_ifs
  all_goals dsimp only
  all_goals refine mem_of_sstep ?_ hmem
  all_goals first
    | with_reducible exact Proofs.Consensus.BlockStamps.attestWith_step' cache e hc nd (Proofs.Consensus.BlockStamps.namedUpdateConfirmationWith_step' cache e hc (Proofs.Consensus.BlockStamps.namedGoldfishVoteWith_step' c cache e hc nd hX) _) rec
    | with_reducible exact Proofs.Consensus.BlockStamps.attestWith_step' cache e hc nd (Proofs.Consensus.BlockStamps.namedUpdateConfirmationWith_step' cache e hc hX _) rec
    | with_reducible exact Proofs.Consensus.BlockStamps.attestWith_step' cache e hc nd (Proofs.Consensus.BlockStamps.namedGoldfishVoteWith_step' c cache e hc nd hX) rec
    | with_reducible exact Proofs.Consensus.BlockStamps.attestWith_step' cache e hc nd hX rec
    | with_reducible exact Proofs.Consensus.BlockStamps.namedUpdateConfirmationWith_step' cache e hc (Proofs.Consensus.BlockStamps.namedGoldfishVoteWith_step' c cache e hc nd hX) _
    | with_reducible exact Proofs.Consensus.BlockStamps.namedUpdateConfirmationWith_step' cache e hc hX _
    | with_reducible exact Proofs.Consensus.BlockStamps.namedGoldfishVoteWith_step' c cache e hc nd hX
    | with_reducible exact hX

end Tick

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- ノードの tick が出すブロックは、tick の後のそのノードの tree にある。 -/
theorem nodeTick_block_mem (v : ValidatorId) {n : NamedNodeState} (hinv : Proofs.Consensus.Carrier.StoreInv s.e s.cfg n.st)
    (hfj : FJ n.st.core) (t : Int) {D : NamedBlock} (hD : NamedObject.Block D ∈ (nodeTick c p a nr s v n t).2)
    (hps : slot (parent (eraseBlock D)) < slot (eraseBlock D)) :
    eraseBlock D ∈ (nodeTick c p a nr s v n t).1.st.core.tree.elems := by
  rw [Proofs.Consensus.Signing.nodeTick_out] at hD
  unfold nodeTick profileTick
  dsimp only
  exact tick_block_mem c p a nr _ s.e s.hc s.cfg _ n.st n.signing t hD hinv.tree hfj hps

/-- **発行されたブロックは、発行の tick の直後の提案者の tree にある**(setup と run の前提 `ScheduleWellFormed` / `0 < Δ` の下で。
親の slot の守りは `ParentSlot.emits_block_parent_slot`)。 -/
theorem emits_block_mem_self (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {v : ValidatorId}
    {D : NamedBlock} {t : Int} (hem : Emits c p a nr s rho v (NamedObject.Block D) t) :
    ∃ i, rho.events[i]? = some (NamedEvent.Tick v t) ∧
      eraseBlock D ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) v).st.core.tree.elems := by
  have hps := Proofs.Consensus.ParentSlot.emits_block_parent_slot c p a nr s rho hsch hδ hem
  obtain ⟨i, hi, ho⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t).mp hem
  refine ⟨i, hi, ?_⟩
  rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hi]
  unfold worldStep
  dsimp only
  rw [Proofs.Consensus.Signing.worldAt_insert_self]
  exact nodeTick_block_mem c p a nr s v (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i v)
    (Proofs.Consensus.ProposerFinality.stateBefore_fj c p a nr s rho i v) t ho hps

/-- **発行の時刻より後の時刻の読みの提案者の tree にある**: 発行の tick の添字は読みの添字 `idxLt d` より前で、tree のブロックは
残る。 -/
theorem emits_block_mem_stateBeforeTime_self (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta)
    (hnd : EventsNodup rho) {v : ValidatorId} {D : NamedBlock} {t d : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) (hd : t < d) :
    eraseBlock D ∈ (worldAt (stateBeforeTime c p a nr s rho d) v).st.core.tree.elems := by
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  obtain ⟨i, hi, hmem⟩ := emits_block_mem_self c p a nr s rho hsch hδ hem
  have hlt : i < Proofs.Consensus.ReceiverFinality.idxLt rho d :=
    Proofs.Consensus.ReceiverFinality.lt_idxLt_of_time_lt rho hs
      (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) hi hd
  have hkeep := Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho (Nat.succ_le_of_lt hlt) v _ hmem
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
  exact hkeep.1

/-- **発行されたブロックは締切の読みのすべての honest な受信者の tree にある**: honest な `v` が時刻 `t` に発行したブロック `D` は、
honest な `w` の締切 `max t tGST + Δ`(horizon 以内)の時刻の読みの FG root が `D` の消去の祖先なら、その読みの tree にある。
`w = v` は締切が発行の時刻より後なので `emits_block_mem_stateBeforeTime_self`(FG root の事実は使わない)、`w ≠ v` は
`BlockSynchrony.partialSynchrony_emitted_block_mem`。 -/
theorem partialSynchrony_emitted_block_mem_honest (hps : PartialSynchrony c p a nr s rho)
    (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho) (hδ : 0 < s.e.delta)
    (hnd : EventsNodup rho) {v w : ValidatorId} {D : NamedBlock} {t : Int}
    (hv : rho.honest.contains v = true) (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) (hd : max t s.e.tGST + s.e.delta ≤ rho.horizon)
    (hroot : preceq (getFgRoot (storeToHealing
      (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core)) (eraseBlock D) = true) :
    eraseBlock D ∈
      (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core.tree.elems := by
  by_cases hwv : w = v
  · subst hwv
    exact emits_block_mem_stateBeforeTime_self c p a nr s rho hsch hδ hnd hem
      (by have := le_max_left t s.e.tGST; omega)
  · exact Proofs.Consensus.BlockSynchrony.partialSynchrony_emitted_block_mem c p a nr s rho hps hsch hdw hδ hnd
      hv hem hw hwv hd hroot

end Run

end Proofs.Consensus.ProposerReceipt
