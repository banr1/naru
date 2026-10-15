import Proofs.Consensus.Majority
import Proofs.Consensus.Delivery
import Proofs.Consensus.Window
import Proofs.Consensus.PoolFrom
import Mathlib.Tactic

/-!
# honest な投票者は pool で equivocate しない・GST 以後の honest な投票の配送は受信者の pool に入る(C71 の補題)

受信の処理 `onGoldfishVote` の equivocation の守りは「pool の slot `u.slot` に同じ投票者の投票が 2 つ以上ある」
(`equivocates (storePool st u.slot) u.valIndex`: `2 ≤ Set.size (votesBy …)`、`Model/Consensus/Protocol/Schedule.lean`)。
honest な投票者 `v` についてこれが偽であることを、run のどの添字・どのノード・どの鍵の pool でも示す(`pool_no_equivocation`)。
- pool の集合 `storePool` は整列(`Majority.storePool_sortedLt`)なので、その `votesBy` の絞り込みのリストに重複は無い。
- 鍵 `k` の pool の投票の slot はどれも `k`(`Votes.PoolInv`、`Votes.stateBefore_pool`)。
- 同じ honest な投票者・同じ slot の pool の投票は 1 つ(`PoolFrom.pool_honest_unique`。`ScheduleWellFormed` + `UnforgeableSignatures`)。
したがって `votesBy` の要素はすべて等しく、大きさは 1 以下(`Majority.length_le_one_of_nodup`。支持の投票についての
`Majority.supportVotes_no_equivocation` と同じ運び)。

これで `Delivery.deliver_gfVote_mem` の 3 つの仮定がすべて run の条件から出る: 投票者が committee の要素(`voteWellFormed`)は
発行の形 `Voting.emits_gfVote_shape` から(`voteWellFormed_of_emits`)、受信者の slot の窓は `Window.inWindow_of_deliver_gfVote`、
equivocation の守りは `pool_no_equivocation`。GST 以後に honest な `v` が発行した投票が honest な `w` に発行の時刻 `t` 以後・締切
`max t tGST + Δ` より前に配送されると、配送の後のどの添字でも `w` の鍵 `u.slot` の pool にある(`deliver_honest_gfVote_mem` /
`deliver_honest_gfVote_mem_of_lt`)。これは `Majority.lean` の `HonestSupport.vote` に向けた配送の経路 (2) の完成で、
経路 (1)(自分の tick の投票)は `OwnVote.tick_honest_gfVote_mem`、残りは経路 (3)(ブロックが運ぶ投票)の pool への到達。

手書きでは `on_goldfish_vote_insert`(`DecoupledConsensusProofs/Protocol/Handlers/Pool.lean`)の equivocation の仮定を、
`GfFrom` と署名の偽造不能から honest な投票者について外す運びに当たる。
-/

namespace Proofs.Consensus.Equivocation

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Schedule
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Votes

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **honest な投票者は pool で equivocate しない**: `ScheduleWellFormed` と `UnforgeableSignatures` の下で、run のどの添字・
どのノード・どの鍵の pool でも、honest な投票者の投票は 1 つ以下。 -/
theorem pool_no_equivocation (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (i : Nat) (w : ValidatorId) (k : Nat) {v : ValidatorId} (hh : rho.honest.contains v = true) :
    equivocates (storePool (worldAt (stateBefore c p a nr s rho i) w).st.core k) v = false := by
  unfold equivocates
  rw [decide_eq_false_iff_not]
  intro h2
  have hnd : (votesBy (storePool (worldAt (stateBefore c p a nr s rho i) w).st.core k) v).elems.Nodup := by
    unfold votesBy
    exact Proofs.Consensus.Majority.SortedLt.nodup Proofs.Consensus.Majority.gv_irrefl
      (Proofs.Consensus.Majority.SortedLt.filter (Proofs.Consensus.Majority.storePool_sortedLt _ k) _)
  have hinv := stateBefore_pool c p a nr s rho i w
  have hle : (votesBy (storePool (worldAt (stateBefore c p a nr s rho i) w).st.core k) v).elems.length ≤ 1 := by
    apply Proofs.Consensus.Majority.length_le_one_of_nodup hnd
    intro x hx y hy
    rw [Proofs.Consensus.Goldfish.mem_votesBy_iff] at hx hy
    have hxs := (hinv.mem hx.1).1
    have hys := (hinv.mem hy.1).1
    exact Proofs.Consensus.PoolFrom.pool_honest_unique c p a nr s rho hsch hunf
      ((mem_storePool_iff _ _ _).mp hx.1) ((mem_storePool_iff _ _ _).mp hy.1)
      (by rw [hx.2]; exact hh) (hx.2.trans hy.2.symm) (hxs.trans hys.symm)
  unfold NaruStd.Set.size at h2
  omega

/-- 発行された投票の投票者は committee の要素(`voteWellFormed`。`Voting.emits_gfVote_shape`)。 -/
theorem voteWellFormed_of_emits {v : ValidatorId} {u : GoldfishVote} {t : Int}
    (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t) : voteWellFormed c u = true := by
  obtain ⟨-, -, hv, -, hc⟩ := Proofs.Consensus.Voting.emits_gfVote_shape c p a nr s rho hem
  unfold voteWellFormed
  rw [hv]
  exact hc

/-- **GST 以後の honest な投票の配送は受信者の pool に入る**: `ScheduleWellFormed` / `UnforgeableSignatures` / Δ > 0 の下で、honest な `v` が GST 以後の時刻 `t` に発行した投票 `u` の、
honest な `w` への添字 `j` の配送(時刻 `t2`、`t ≤ t2 < max t tGST + Δ`)の後、`w` の鍵 `u.slot` の pool に `u` がある
(`Delivery.deliver_gfVote_mem` の 3 つの仮定を `voteWellFormed_of_emits` / `Window.inWindow_of_deliver_gfVote` /
`pool_no_equivocation` で外したもの)。 -/
theorem deliver_honest_gfVote_mem (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {u : GoldfishVote} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t) (hv : rho.honest.contains v = true)
    (hgst : s.e.tGST ≤ t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.GfVote u) t2))
    (ht : t ≤ t2) (ht2 : t2 < max t s.e.tGST + s.e.delta) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot := by
  obtain ⟨-, -, hvi, -, -⟩ := Proofs.Consensus.Voting.emits_gfVote_shape c p a nr s rho hem
  exact Proofs.Consensus.Delivery.deliver_gfVote_mem c p a nr s rho hj (voteWellFormed_of_emits c p a nr s rho hem)
    (Proofs.Consensus.Window.inWindow_of_deliver_gfVote c p a nr s rho hsch hδ hem hgst hw hj ht ht2)
    (pool_no_equivocation c p a nr s rho hsch hunf j w u.slot (by rw [hvi]; exact hv))

/-- 同じ配送の後のどの添字でも、`u` は `w` の鍵 `u.slot` の pool に残る(`Delivery.gfVote_mem_of_le`)。 -/
theorem deliver_honest_gfVote_mem_of_lt (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {u : GoldfishVote} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t) (hv : rho.honest.contains v = true)
    (hgst : s.e.tGST ≤ t) (hw : rho.honest.contains w = true) {j i : Nat} (hji : j < i)
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.GfVote u) t2))
    (ht : t ≤ t2) (ht2 : t2 < max t s.e.tGST + s.e.delta) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot :=
  Proofs.Consensus.Delivery.gfVote_mem_of_le c p a nr s rho hji
    (deliver_honest_gfVote_mem c p a nr s rho hsch hunf hδ hem hv hgst hw hj ht ht2)

end Run

end Proofs.Consensus.Equivocation
