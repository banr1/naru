import Proofs.Consensus.ReceiverFinality
import Proofs.Consensus.DeliveredBlock
import Mathlib.Tactic

/-!
# 発行されたブロックの部分同期と、締切の読みの tree への到達(C71 の補題)

`ReceiverFinality.deliver_emitted_block_mem_stateBeforeTime_of_root` は配送の event(添字 `j`、時刻 `t2`)と、発行の時刻 `t` より
後の配送(`t < t2`)を仮定していた。ここでは配送の event を run の前提 `PartialSynchrony` の第 1 連言から取り出し、配送の時刻が
発行の時刻と等しい場合も扱う。

- **同じ時刻では tick が配送より前**: event の整列の鍵 `eventKey` は (時刻, phase) で、tick の phase は 0、配送の phase は 1
  (`Model/Consensus/Execution/Run.lean` の `eventPhase`)。したがって時刻 `t1 ≤ t2` の tick と配送は tick の添字が前
  (`tick_lt_deliver`)で、honest な受信者への時刻 `t2` の配送の直前の slot は `proposalTime k ≤ t2` なら `k` 以上
  (`slot_ge_of_deliver_le`。`Window.slot_ge_of_deliver` は `<` の版)。発行されたブロックの `Admits` のうち `extends_f` を除く 4 つは
  配送の時刻が発行の時刻以上なら出る(`emits_admits_of_extends_le`。`DeliveredBlock.emits_admits_of_extends` は `<` の版)。
- **ブロックの発行者は提案者**: tick が出すブロックの提案者は tick のノード自身(`Proposal.tick_block_shape` /
  `proposalWith_proposer`)なので、同じブロックを発行したノードは 1 つ(`emits_block_proposer` / `emits_block_unique`)。
- **ブロックの部分同期**: honest な `v` が時刻 `t` に発行したブロック `D` は、honest な `w` が締切 `max t tGST + Δ`(horizon 以内)
  より前に扱う。ただし締切の時刻の読み(`stateBeforeTime`)の `w` の `f` が `D` と互換でないとき(`excludes`)は除く
  (`partialSynchrony_block`)。ブロックの `HandlesAt` の経路は `w` 自身の tick の発行か `w` への配送の 2 つ(`handlesAt_block_cases`)で、
  `w ≠ v`(ブロックの提案者 = 発行者でない受信者)なら前者は起きない(発行者は 1 つ)ので配送(`partialSynchrony_block_deliver`)。
- **締切の読みの tree への到達**: 締切の時刻の読みの `w` の FG root が `D` の消去の祖先なら、`f` も祖先(`f ⪯ FG root`)なので
  `excludes` は偽で、配送の直前の `f` も祖先(`ReceiverFinality.stateBefore_f_preceq_of_stateBeforeTime_root`)。配送で `w` の tree に
  入り、tree のブロックは残るので、締切の読みの tree にある(`partialSynchrony_emitted_block_mem`)。前提は setup と run の前提
  (`ScheduleWellFormed` / `DeliveryWellFormed` / `PartialSynchrony` / `0 < Δ`)、honest な `v ≠ w`、締切 ≤ horizon と FG root の事実だけで、配送の event と時刻の仮定は要らない。

手書きの対応: `ProposalAdoptionNamedClosed.lean` の `proposedBlock_admittedBefore_vote_after_gst_named` の提案者でない受信者の分岐
(`Protocol.processes_proposedBlock_before_vote_after_gst` の配送の腕と `delivery_store_slot_before_freeze`)。手書きの結論は投票の時刻より前の
受理の event で、ここは締切の読みの tree への所属。手書きは
受信の守りの `extends_f` を `ProposalFinalizedBelowAtDeliveries`(配送の各添字の `f` ⪯ 提案)で与え、ここは締切の読みの FG root で与える。
提案者自身(`w = v`)の受理(手書きの `acceptsAt_proposedBlock`)と、FG root が honest な提案の祖先であること(liveness の本体)は残る。
-/

namespace Proofs.Consensus.BlockSynchrony

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Protocol.Schedule
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.BlockReceipt (Admits)

/-! ## 同じ時刻の tick と配送 -/

/-- **時刻 `t1 ≤ t2` の tick は時刻 `t2` の配送より添字が前**: 同じ時刻なら phase(tick 0 < 配送 1)で整列する。 -/
theorem tick_lt_deliver {rho : NamedRun} (hs : EventsSorted rho) {i j : Nat} {v w : ValidatorId} {o : NamedObject}
    {t1 t2 : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t1))
    (hj : rho.events[j]? = some (NamedEvent.Deliver w o t2)) (h : t1 ≤ t2) : i < j := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · exact hij
  · rw [hi] at hj
    cases hj
  · have hs' := hs j i hji
    simp only [hj, hi] at hs'
    apply absurd _ hs'
    show (compare t2 t1).then (compare (1 : Nat) 0) = .gt
    rcases lt_or_eq_of_le h with hlt | rfl
    · rw [Int.compare_eq_gt.mpr hlt]
      rfl
    · rw [Int.compare_eq_eq.mpr rfl]
      rfl

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **配送の直前の slot の下限(`≤` の版)**: honest な `w` への時刻 `t2` の配送の直前、`proposalTime k ≤ t2` なら `w` の slot は
`k` 以上(slot `k` の開始の tick は公開時刻で、時刻が配送以下なので添字が前: `tick_lt_deliver`)。 -/
theorem slot_ge_of_deliver_le (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {j : Nat} {w : ValidatorId}
    {o : NamedObject} {t2 : Int} (hw : rho.honest.contains w = true)
    (hj : rho.events[j]? = some (NamedEvent.Deliver w o t2)) {k : Nat} (hlo : proposalTime s.e k ≤ t2) :
    k ≤ (worldAt (stateBefore c p a nr s rho j) w).st.core.s := by
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev hev =>
    (Proofs.Consensus.Window.eventTime_bounds hsch hev).1
  have hb := Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? hj)
  obtain ⟨j', hj'⟩ := Proofs.Consensus.Window.honest_tick_index hsch hw
    (Proofs.Consensus.Window.publicTime_proposalTime s.e k)
    (Proofs.Consensus.Window.proposalTime_nonneg s.e hδ.le k) (le_trans hlo hb.2)
  have hlt : j' < j := tick_lt_deliver hs hj' hj hlo
  have hle := Proofs.Consensus.Window.tick_le_clock c p a nr s rho hs hnn hlt hj'
  rw [Proofs.Consensus.Clocks.clock_slot c p a nr s rho j w]
  exact Proofs.Consensus.Window.le_slotOf_of_le s.e hδ hle

/-! ## 発行されたブロックの発行者 -/

/-- **発行されたブロックの提案者は発行したノード**: tick が出すブロックは提案の務めの出力で、提案者は tick のノード自身。 -/
theorem emits_block_proposer {v : ValidatorId} {D : NamedBlock} {t : Int}
    (h : Emits c p a nr s rho v (NamedObject.Block D) t) : proposer? (eraseBlock D) = some v := by
  obtain ⟨i, -, ho⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t).mp h
  rw [Proofs.Consensus.Signing.nodeTick_out] at ho
  obtain ⟨-, -, -, hD⟩ := Proofs.Consensus.Proposal.tick_block_shape c p a nr _ s.e s.hc s.cfg _ _ _ t ho
  exact Proofs.Consensus.Proposal.proposalWith_proposer nr _ s.e s.hc _ _ hD

/-- 同じブロックを発行したノードは 1 つ。 -/
theorem emits_block_unique {v w : ValidatorId} {D : NamedBlock} {t t' : Int}
    (hv : Emits c p a nr s rho v (NamedObject.Block D) t) (hw : Emits c p a nr s rho w (NamedObject.Block D) t') :
    w = v := by
  have h1 := emits_block_proposer c p a nr s rho hv
  rw [emits_block_proposer c p a nr s rho hw] at h1
  exact Option.some.inj h1

/-! ## 発行の時刻以上の配送 -/

/-- **発行されたブロックの受理の条件(`≤` の版)**: honest な `w` に発行の時刻 `t` 以上の `t2` に配送されたなら、`Admits` の守りの
うち `extends_f` を除く 4 つが run の前提から出る。 -/
theorem emits_admits_of_extends_le (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {D : NamedBlock} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t ≤ t2)
    (hf : preceq (worldAt (stateBefore c p a nr s rho j) w).st.core.f (eraseBlock D) = true) :
    Admits p (worldAt (stateBefore c p a nr s rho j) w).st.core (eraseBlock D) where
  slot_le := by
    obtain ⟨-, htp, -, -⟩ := Proofs.Consensus.Proposal.emits_block_fields c p a nr s rho hem
    rw [htp] at ht
    exact slot_ge_of_deliver_le c p a nr s rho hsch hδ hw hj ht
  parent_mem := Proofs.Consensus.DeliveredBlock.deliver_parent_tree c p a nr s rho hdw hj
  extends_f := hf
  proposer := (Proofs.Consensus.Proposal.emits_block_fields c p a nr s rho hem).2.2.1
  parent_slot := Proofs.Consensus.ParentSlot.emits_block_parent_slot c p a nr s rho hsch hδ hem

/-- **発行されたブロックは、`extends_f` の下で配送の後の受信者の tree にある(`≤` の版)**。 -/
theorem deliver_emitted_block_mem_le (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {D : NamedBlock} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t ≤ t2)
    (hf : preceq (worldAt (stateBefore c p a nr s rho j) w).st.core.f (eraseBlock D) = true) :
    eraseBlock D ∈ (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems :=
  Proofs.Consensus.BlockReceipt.deliver_block_mem c p a nr s rho hj
    (Proofs.Consensus.DeliveredBlock.deliver_deps c p a nr s rho hdw hj).1
    (Proofs.Consensus.Proposal.emits_block_fields c p a nr s rho hem).2.2.2
    (emits_admits_of_extends_le c p a nr s rho hsch hdw hδ hem hw hj ht hf)

/-- **締切の読みの tree に入る(`≤` の版)**: 発行の時刻 `t` 以上、締切 `d` より前の配送で、締切の時刻の読みの `w` の FG root が
`D` の消去の祖先なら、その読みの tree にある(`ReceiverFinality.deliver_emitted_block_mem_stateBeforeTime_of_root` の `t ≤ t2` の版)。 -/
theorem deliver_emitted_block_mem_stateBeforeTime_of_root_le (hsch : ScheduleWellFormed s rho)
    (hdw : DeliveryWellFormed c p a nr s rho) (hδ : 0 < s.e.delta) (hnd : EventsNodup rho)
    {v w : ValidatorId} {D : NamedBlock} {t t2 d : Int} (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t ≤ t2) (hd : t2 < d)
    (hroot : preceq (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho d) w).st.core))
      (eraseBlock D) = true) :
    eraseBlock D ∈ (worldAt (stateBeforeTime c p a nr s rho d) w).st.core.tree.elems := by
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hlt : j < Proofs.Consensus.ReceiverFinality.idxLt rho d :=
    Proofs.Consensus.ReceiverFinality.lt_idxLt_of_time_lt rho hs
      (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) hj hd
  have hmem := deliver_emitted_block_mem_le c p a nr s rho hsch hdw hδ hem hw hj ht
    (Proofs.Consensus.ReceiverFinality.stateBefore_f_preceq_of_stateBeforeTime_root c p a nr s rho hs hlt.le hroot)
  have hkeep := Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho (Nat.succ_le_of_lt hlt) w _ hmem
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
  exact hkeep.1

/-! ## ブロックの部分同期 -/

/-- **ブロックの `HandlesAt` の 2 つの経路**: (1) 添字 `j` が `w` 自身の時刻 `t2` の tick で、その tick が `D` を出す、
(2) 添字 `j` が `w` への `D` の配送。 -/
theorem handlesAt_block_cases {j : Nat} {w : ValidatorId} {D : NamedBlock} {t2 : Int}
    (h : HandlesAt c p a nr s rho j w (NamedObject.Block D) t2) :
    (rho.events[j]? = some (NamedEvent.Tick w t2) ∧
        (emittedAt c p a nr s rho j w t2).contains (NamedObject.Block D) = true) ∨
      rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2) := by
  obtain ⟨ev, ⟨⟨hev, hn⟩, ht⟩, hh⟩ := h
  rcases hh with ⟨t', hevt, hco⟩ | ⟨t', hevd⟩
  · left
    cases ev with
    | Tick v' t'' =>
      simp only [eventNode, eventTime, NamedEvent.Tick.injEq, true_and] at hn ht hevt hco
      subst hn ht hevt
      exact ⟨hev, hco⟩
    | Deliver v' o t'' =>
      simp only [eventNode] at hevt
      exact absurd hevt (by simp)
  · right
    cases ev with
    | Tick v' t'' =>
      simp only [eventNode] at hevd
      exact absurd hevd (by simp)
    | Deliver v' o t'' =>
      simp only [eventNode, eventTime] at hn ht hevd
      obtain ⟨-, rfl, -⟩ := hevd
      subst hn ht
      exact hev

/-- **ブロックの部分同期**: honest な `v` が時刻 `t` に発行したブロックは、締切 `max t tGST + Δ`(horizon 以内)の時刻の読みの
honest な `w` の `f` が `D` の消去と互換なら、発行の時刻以上・締切より前の時刻 `t2` に、ある添字 `j` で `w` が扱う。 -/
theorem partialSynchrony_block (hps : PartialSynchrony c p a nr s rho) {v w : ValidatorId} {D : NamedBlock} {t : Int}
    (hv : rho.honest.contains v = true) (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) (hd : max t s.e.tGST + s.e.delta ≤ rho.horizon)
    (hc : compatible
      (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core.f (eraseBlock D) = true) :
    ∃ t2, (t ≤ t2 ∧ t2 < max t s.e.tGST + s.e.delta) ∧
      ∃ j, HandlesAt c p a nr s rho j w (NamedObject.Block D) t2 := by
  have h := hps.1 v (NamedObject.Block D) t ⟨hv, hem⟩ w
  dsimp only at h
  refine h ⟨⟨hw, hd⟩, ?_⟩
  simp only [excludes, hc, Bool.not_true, Bool.false_eq_true, not_false_eq_true]

/-- **ブロックの部分同期の配送の形**: `w ≠ v` なら、`w` 自身の tick は `D` を出さない(発行者は 1 つ)ので、締切より前に
`w` への `D` の配送がある。 -/
theorem partialSynchrony_block_deliver (hps : PartialSynchrony c p a nr s rho) {v w : ValidatorId} {D : NamedBlock}
    {t : Int} (hv : rho.honest.contains v = true) (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) (hwv : w ≠ v) (hd : max t s.e.tGST + s.e.delta ≤ rho.horizon)
    (hc : compatible
      (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core.f (eraseBlock D) = true) :
    ∃ (t2 : Int) (j : Nat), (t ≤ t2 ∧ t2 < max t s.e.tGST + s.e.delta) ∧
      rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2) := by
  obtain ⟨t2, ht2, j, hj⟩ := partialSynchrony_block c p a nr s rho hps hv hem hw hd hc
  rcases handlesAt_block_cases c p a nr s rho hj with ⟨hjt, hco⟩ | hjd
  · have hem' : Emits c p a nr s rho w (NamedObject.Block D) t2 := ⟨j, hjt, hco⟩
    exact absurd (emits_block_unique c p a nr s rho hem hem') hwv
  · exact ⟨t2, j, ht2, hjd⟩

/-! ## 締切の読みの tree -/

/-- 締切の時刻の読みの FG root が `B` の祖先なら、その読みの `f` は `B` と互換(`f ⪯ FG root ⪯ B`)。 -/
theorem compatible_of_stateBeforeTime_root (hs : EventsSorted rho) {d : Int} {w : ValidatorId} {B : Block}
    (hroot : preceq (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho d) w).st.core)) B = true) :
    compatible (worldAt (stateBeforeTime c p a nr s rho d) w).st.core.f B = true := by
  have hf := Proofs.Consensus.ReceiverFinality.stateBefore_f_preceq_of_stateBeforeTime_root c p a nr s rho hs
    (le_refl (Proofs.Consensus.ReceiverFinality.idxLt rho d)) hroot
  rw [← Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs] at hf
  unfold compatible
  rw [hf, Bool.true_or]

/-- **発行されたブロックは締切の読みの honest な受信者の tree にある**: honest な `v` が時刻 `t` に発行したブロック `D` について、
`v` でない honest な `w` の締切 `max t tGST + Δ`(horizon 以内)の時刻の読みの FG root が `D` の消去の祖先なら、その読みの tree に
`D` の消去がある。配送の event と時刻は `PartialSynchrony` から出し、受理の守りは setup と run の前提と FG root の事実から出す。 -/
theorem partialSynchrony_emitted_block_mem (hps : PartialSynchrony c p a nr s rho) (hsch : ScheduleWellFormed s rho)
    (hdw : DeliveryWellFormed c p a nr s rho) (hδ : 0 < s.e.delta) (hnd : EventsNodup rho)
    {v w : ValidatorId} {D : NamedBlock} {t : Int}
    (hv : rho.honest.contains v = true) (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) (hwv : w ≠ v) (hd : max t s.e.tGST + s.e.delta ≤ rho.horizon)
    (hroot : preceq (getFgRoot (storeToHealing
      (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core)) (eraseBlock D) = true) :
    eraseBlock D ∈
      (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core.tree.elems := by
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  obtain ⟨t2, j, ⟨ht, hd2⟩, hj⟩ := partialSynchrony_block_deliver c p a nr s rho hps hv hem hw hwv hd
    (compatible_of_stateBeforeTime_root c p a nr s rho hs hroot)
  exact deliver_emitted_block_mem_stateBeforeTime_of_root_le c p a nr s rho hsch hdw hδ hnd hem hw hj ht hd2 hroot

end Run

end Proofs.Consensus.BlockSynchrony
