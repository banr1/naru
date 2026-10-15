import Proofs.Consensus.ProposerFinality
import Proofs.Consensus.FinalizedMonotone
import Proofs.Consensus.RecordGrowth
import Proofs.Consensus.BlockStamps
import Mathlib.Tactic

/-!
# 受信者の finalized を後の読みで抑える(C71 の補題)

`DeliveredBlock.deliver_emitted_block_mem` に残る受理の守り `extends_f`(`preceq st.f b`)の、受信者の側の半分。
仮定は配送の直前の受信者の `f` についての事実だが、liveness の主張側が手にするのは締切の時刻の読み(`storeAt w d`)についての
事実なので、これを配送の直前へ引き戻す。

`f` は run の添字について `preceq` で単調(`stateBefore_f_mono`: 各 `worldStep` が `f` を縮めない
`FinalizedMonotone.worldStep_f` の積み上げ)、store の `f ⪯ j`(`ProposerFinality.stateBefore_fj`)から FG root(`j` か `f`)は
`f` を延ばす(`store_fgRoot_extends`)。したがって後の添字 `k` の `f` か FG root がブロック `B` の祖先なら、`k` 以前のどの添字の
`f` も `B` の祖先(`stateBefore_f_preceq_of_later` / `stateBefore_f_preceq_of_root`)。時刻の読みは添字 `idx d` の直前の状態
(`RecordGrowth.readAt_eq_stateBefore_idx`)で、時刻 `d` 以下の event の添字は `idx d` より前(`lt_idx_of_time_le`)。

発行されたブロック `D` が honest な `w` に発行より後、時刻 `d` 以下に配送されたとき、時刻 `d` の読みの `w` の `f`(または FG root)が
`D` の消去の祖先なら、配送の後の `w` の tree にあり、tree のブロックは残る(`BlockStamps.stateBefore_keep`)ので時刻 `d` の読みの
tree にもある(`deliver_emitted_block_mem_storeAt` / `_of_root`)。`storeAt` / `readAt` は時刻 `≤ d` の event の読みで、
前提(`PartialSynchrony` など)が使う `stateBeforeTime` は時刻 `< d` の event の読みなので、そちらの版も置く(添字 `idxLt d`、
配送の時刻は `d` より前: `stateBefore_f_preceq_of_stateBeforeTime_root` / `deliver_emitted_block_mem_stateBeforeTime_of_root`)。

手書き `finalized_preceq_at_prefix_of_storeBeforeRoot_preceq`(`Execution/ExcludesRefute.lean`。`stateBefore_F_mono` と
`finalized_preceq_justified_stateBeforeTime` / `preceq_get_fg_root_of_F`)と、それを使う `ProposalFinalizedBelowAtDeliveries`
(`HonestProposalAdmission.lean`)の組み立て(`ProposalAdoptionNamedClosed.lean` の `hFhist`)に当たる。手書きの読みは
`stateBeforeTime`(時刻 `< d`)で、`stateBeforeTime` の版がそれと同じ形。
残るのは、honest な提案のブロックが締切の時刻の受信者の FG root を延ばすこと(liveness の本体の事実)。
-/

namespace Proofs.Consensus.ReceiverFinality

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Blocks Proofs.Consensus.ProposerFinality

/-- `f ⪯ j` の store の FG root は `f` を延ばす。 -/
theorem store_fgRoot_extends {st : Store} (h : FJ st) : preceq st.f (getFgRoot (storeToHealing st)) = true :=
  fgRoot_extends (hs := storeToHealing st) h

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **`f` は run の添字について単調**(前提なし): `i ≤ k` なら添字 `i` の直前の `f` は添字 `k` の直前の `f` の祖先。 -/
theorem stateBefore_f_mono {i k : Nat} (h : i ≤ k) (v : ValidatorId) :
    preceq (worldAt (stateBefore c p a nr s rho i) v).st.core.f
      (worldAt (stateBefore c p a nr s rho k) v).st.core.f = true := by
  induction h with
  | refl => exact preceq_self _
  | step _ ih =>
    rw [Proofs.Consensus.Signing.stateBefore_succ]
    exact preceq_trans ih (Proofs.Consensus.FinalizedMonotone.foldl_worldStep_f c p a nr s _ _ v)

/-- 後の添字 `k` の `f` が `B` の祖先なら、`k` 以前の添字 `i` の `f` も `B` の祖先。 -/
theorem stateBefore_f_preceq_of_later {i k : Nat} (h : i ≤ k) {w : ValidatorId} {B : Block}
    (hF : preceq (worldAt (stateBefore c p a nr s rho k) w).st.core.f B = true) :
    preceq (worldAt (stateBefore c p a nr s rho i) w).st.core.f B = true :=
  preceq_trans (stateBefore_f_mono c p a nr s rho h w) hF

/-- 後の添字 `k` の FG root が `B` の祖先なら、`k` 以前の添字 `i` の `f` も `B` の祖先(前提なし)。 -/
theorem stateBefore_f_preceq_of_root {i k : Nat} (h : i ≤ k) {w : ValidatorId} {B : Block}
    (hroot : preceq (getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho k) w).st.core)) B = true) :
    preceq (worldAt (stateBefore c p a nr s rho i) w).st.core.f B = true :=
  stateBefore_f_preceq_of_later c p a nr s rho h
    (preceq_trans (store_fgRoot_extends (stateBefore_fj c p a nr s rho k w)) hroot)

/-- 時刻 `d` 以下の event の添字は `idx d` より前(event の整列と重複なしの下で)。 -/
theorem lt_idx_of_time_le (hs : EventsSorted rho) (hnd : rho.events.Nodup) {d : Int} {j : Nat} {ev : NamedEvent}
    (hev : rho.events[j]? = some ev) (hd : eventTime ev ≤ d) : j < Proofs.Consensus.RecordGrowth.idx rho d := by
  by_contra hle
  exact absurd (Proofs.Consensus.RecordGrowth.lt_of_idx_le rho hs hnd (not_lt.mp hle) hev) (not_lt.mpr hd)

/-- 時刻 `d` の読みの `f` が `B` の祖先なら、`idx d` 以前の添字 `i` の `f` も `B` の祖先。 -/
theorem stateBefore_f_preceq_of_storeAt (hs : EventsSorted rho) {i : Nat} {d : Int}
    (hi : i ≤ Proofs.Consensus.RecordGrowth.idx rho d) {w : ValidatorId} {B : Block}
    (hF : preceq (storeAt c p a nr s rho w d).core.f B = true) :
    preceq (worldAt (stateBefore c p a nr s rho i) w).st.core.f B = true := by
  unfold storeAt at hF
  rw [Proofs.Consensus.RecordGrowth.readAt_eq_stateBefore_idx c p a nr s rho hs] at hF
  exact stateBefore_f_preceq_of_later c p a nr s rho hi hF

/-- 時刻 `d` の読みの FG root が `B` の祖先なら、`idx d` 以前の添字 `i` の `f` も `B` の祖先。手書き
`finalized_preceq_at_prefix_of_storeBeforeRoot_preceq`。 -/
theorem stateBefore_f_preceq_of_storeAt_root (hs : EventsSorted rho) {i : Nat} {d : Int}
    (hi : i ≤ Proofs.Consensus.RecordGrowth.idx rho d) {w : ValidatorId} {B : Block}
    (hroot : preceq (getFgRoot (storeToHealing (storeAt c p a nr s rho w d).core)) B = true) :
    preceq (worldAt (stateBefore c p a nr s rho i) w).st.core.f B = true := by
  unfold storeAt at hroot
  rw [Proofs.Consensus.RecordGrowth.readAt_eq_stateBefore_idx c p a nr s rho hs] at hroot
  exact stateBefore_f_preceq_of_root c p a nr s rho hi hroot

/-- **時刻 `d` の読みの `f` で受理を示す**: setup と run の前提(`ScheduleWellFormed` / `DeliveryWellFormed` / `0 < Δ`、event の整列と
重複なし)の下で、honest な `w` に発行より後、時刻 `d` 以下に配送された発行されたブロック `D` は、時刻 `d` の読みの `w` の `f` が
`D` の消去の祖先なら、時刻 `d` の読みの `w` の tree にある。 -/
theorem deliver_emitted_block_mem_storeAt (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho)
    (hδ : 0 < s.e.delta) (hs : EventsSorted rho) (hnd : EventsNodup rho) {v w : ValidatorId} {D : NamedBlock}
    {t t2 d : Int} (hem : Emits c p a nr s rho v (NamedObject.Block D) t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t < t2) (hd : t2 ≤ d)
    (hF : preceq (storeAt c p a nr s rho w d).core.f (eraseBlock D) = true) :
    eraseBlock D ∈ (storeAt c p a nr s rho w d).core.tree.elems := by
  have hlt : j < Proofs.Consensus.RecordGrowth.idx rho d :=
    lt_idx_of_time_le rho hs (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) hj hd
  have hmem := Proofs.Consensus.DeliveredBlock.deliver_emitted_block_mem c p a nr s rho hsch hdw hδ hem hw hj ht
    (stateBefore_f_preceq_of_storeAt c p a nr s rho hs hlt.le hF)
  have hkeep := Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho (Nat.succ_le_of_lt hlt) w _ hmem
  unfold storeAt
  rw [Proofs.Consensus.RecordGrowth.readAt_eq_stateBefore_idx c p a nr s rho hs]
  exact hkeep.1

/-- **時刻 `d` の読みの FG root で受理を示す**: `deliver_emitted_block_mem_storeAt` の仮定を、時刻 `d` の読みの `w` の FG root が
`D` の消去の祖先であることに替えたもの(FG root は `f` を延ばす)。手書き `ProposalFinalizedBelowAtDeliveries` を
`finalized_preceq_at_prefix_of_storeBeforeRoot_preceq` で組み立てる筋。 -/
theorem deliver_emitted_block_mem_storeAt_of_root (hsch : ScheduleWellFormed s rho)
    (hdw : DeliveryWellFormed c p a nr s rho) (hδ : 0 < s.e.delta) (hs : EventsSorted rho) (hnd : EventsNodup rho)
    {v w : ValidatorId} {D : NamedBlock} {t t2 d : Int} (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t < t2) (hd : t2 ≤ d)
    (hroot : preceq (getFgRoot (storeToHealing (storeAt c p a nr s rho w d).core)) (eraseBlock D) = true) :
    eraseBlock D ∈ (storeAt c p a nr s rho w d).core.tree.elems :=
  deliver_emitted_block_mem_storeAt c p a nr s rho hsch hdw hδ hs hnd hem hw hj ht hd
    (preceq_trans (store_fgRoot_extends (readAt_fj c p a nr s rho d w)) hroot)

/-! ## 時刻 `< d` の読み(`stateBeforeTime`) -/

/-- 時刻が非減少な event の列では、`filter (< t)` はある接頭辞 `take i`。 -/
theorem filter_lt_eq_take (t : Int) :
    ∀ (l : List NamedEvent), l.Pairwise (fun a b => eventTime a ≤ eventTime b) →
      ∃ i, l.filter (fun ev => decide (eventTime ev < t)) = l.take i
  | [], _ => ⟨0, rfl⟩
  | x :: xs, hp => by
    rw [List.pairwise_cons] at hp
    obtain ⟨hx, hxs⟩ := hp
    by_cases hxt : eventTime x < t
    · obtain ⟨i, hi⟩ := filter_lt_eq_take t xs hxs
      exact ⟨i + 1, by simp [hxt, hi]⟩
    · refine ⟨0, ?_⟩
      rw [List.take_zero, List.filter_eq_nil_iff]
      intro y hy
      simp only [decide_eq_true_eq]
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hxt
      · exact fun hyt => hxt (lt_of_le_of_lt (hx y hy') hyt)

/-- 時刻 `< t` の読みの添字: `filter (eventTime < t)` の長さ。 -/
def idxLt (t : Int) : Nat := (rho.events.filter (fun ev => decide (eventTime ev < t))).length

/-- `EventsSorted` の下で `filter (< t)` は長さ `idxLt t` の接頭辞。 -/
theorem filter_eq_take_idxLt (hs : EventsSorted rho) (t : Int) :
    rho.events.filter (fun ev => decide (eventTime ev < t)) = rho.events.take (idxLt rho t) := by
  unfold idxLt
  obtain ⟨i, hi⟩ := filter_lt_eq_take t rho.events (Proofs.Consensus.Runs.pairwise_of_eventsSorted rho hs)
  rw [hi, List.length_take]
  rcases le_total i rho.events.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.take_length, List.take_of_length_le h]

/-- 時刻 `< t` の読みは添字 `idxLt t` の直前の状態。 -/
theorem stateBeforeTime_eq_stateBefore_idxLt (hs : EventsSorted rho) (t : Int) :
    stateBeforeTime c p a nr s rho t = stateBefore c p a nr s rho (idxLt rho t) := by
  unfold stateBeforeTime stateBefore
  rw [filter_eq_take_idxLt rho hs]

/-- 時刻 `< d` の event の添字は `idxLt d` より前(event の整列と重複なしの下で)。 -/
theorem lt_idxLt_of_time_lt (hs : EventsSorted rho) (hnd : rho.events.Nodup) {d : Int} {j : Nat} {ev : NamedEvent}
    (hev : rho.events[j]? = some ev) (hd : eventTime ev < d) : j < idxLt rho d := by
  have hmem : ev ∈ rho.events.filter (fun ev => decide (eventTime ev < d)) :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? hev, decide_eq_true hd⟩
  rw [filter_eq_take_idxLt rho hs, List.mem_iff_getElem?] at hmem
  obtain ⟨k, hk⟩ := hmem
  rw [List.getElem?_take] at hk
  split at hk
  · rename_i hki
    have hkl : k < rho.events.length := (List.getElem?_eq_some_iff.mp hk).1
    have hkj : k = j := (List.Nodup.getElem?_inj hkl hnd).mp (hk.trans hev.symm)
    omega
  · exact absurd hk (by simp)

/-- 時刻 `< d` の読みの FG root が `B` の祖先なら、`idxLt d` 以前の添字 `i` の `f` も `B` の祖先。手書き
`finalized_preceq_at_prefix_of_storeBeforeRoot_preceq` と同じ読み。 -/
theorem stateBefore_f_preceq_of_stateBeforeTime_root (hs : EventsSorted rho) {i : Nat} {d : Int}
    (hi : i ≤ idxLt rho d) {w : ValidatorId} {B : Block}
    (hroot : preceq (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho d) w).st.core)) B = true) :
    preceq (worldAt (stateBefore c p a nr s rho i) w).st.core.f B = true := by
  rw [stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs] at hroot
  exact stateBefore_f_preceq_of_root c p a nr s rho hi hroot

/-- **時刻 `< d` の読みの FG root で受理を示す**: `deliver_emitted_block_mem_storeAt_of_root` の読みを `stateBeforeTime`
(時刻 `< d` の event)に替えたもの。配送の時刻は `d` より前。 -/
theorem deliver_emitted_block_mem_stateBeforeTime_of_root (hsch : ScheduleWellFormed s rho)
    (hdw : DeliveryWellFormed c p a nr s rho) (hδ : 0 < s.e.delta) (hs : EventsSorted rho) (hnd : EventsNodup rho)
    {v w : ValidatorId} {D : NamedBlock} {t t2 d : Int} (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t < t2) (hd : t2 < d)
    (hroot : preceq (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho d) w).st.core))
      (eraseBlock D) = true) :
    eraseBlock D ∈ (worldAt (stateBeforeTime c p a nr s rho d) w).st.core.tree.elems := by
  have hlt : j < idxLt rho d :=
    lt_idxLt_of_time_lt rho hs (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) hj hd
  have hmem := Proofs.Consensus.DeliveredBlock.deliver_emitted_block_mem c p a nr s rho hsch hdw hδ hem hw hj ht
    (stateBefore_f_preceq_of_stateBeforeTime_root c p a nr s rho hs hlt.le hroot)
  have hkeep := Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho (Nat.succ_le_of_lt hlt) w _ hmem
  rw [stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
  exact hkeep.1

end Run

end Proofs.Consensus.ReceiverFinality
