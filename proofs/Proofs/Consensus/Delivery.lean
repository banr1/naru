import Model.Consensus.Execution.Run
import Statements.Consensus.Spec.Execution
import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.Votes
import Proofs.Consensus.Voting
import Mathlib.Tactic

/-!
# 投票の配送と受信者の pool(C71 の補題)

`PartialSynchrony`(`Statements/Consensus/Spec/Conditions.lean`)の第 1 連言は、honest な `v` が時刻 `t` に発行した object を、
honest な `w` が締切 `max t tGST + Δ`(horizon 以内)より前のある添字 `j` で扱う(`HandlesAt j w o t2`、`t ≤ t2 < 締切`)ことを
保証する。ただし締切の時点の `w` の store が object を退ける(`excludes`)ときは除く。投票(`GfVote u`)は `excludes` が常に偽なので、
この除外は無い(`partialSynchrony_gfVote`)。

`HandlesAt j w (GfVote u) t2`(`Statements/Consensus/Spec/Execution.lean` の `Handles` の投票の腕)の経路は 3 つ
(`handlesAt_gfVote_cases`): (1) 添字 `j` が `w` 自身の時刻 `t2` の tick で、その tick が `u` を出す(= `Emits` の添字 `j`)、
(2) 添字 `j` が `w` への `u` の配送、(3) 添字 `j` でブロックの処理(配送か自分の提案)が `u` を運ぶブロックを新しく tree に入れる。

配送の経路 (2) で `u` が `w` の pool に入るかは受信の処理 `receiptProcess` → `onGoldfishVoteChecked` → `onGoldfishVote`
(`Model/Consensus/Protocol/Handlers.lean`)で決まり、無条件ではない: 投票者が `committee' u.slot` の要素(`voteWellFormed`)、
受信者の slot `st.s` が `u.slot` か `u.slot + 1`(`InWindow`。`u.slot < st.s - 1` か `st.s < u.slot` なら退ける)、
pool の slot `u.slot` に同じ投票者の投票がまだ 2 つ無い(`equivocates` が偽)。この 3 つの下で `u` は鍵 `u.slot` の pool に入る
(既にあればそのまま。`mem_onGoldfishVote` / `mem_receiptProcess_gfVote`)。run では、添字 `j` の配送の後の `stateBefore (j + 1)` の
`w` の pool に `u` があり(`deliver_gfVote_mem`)、pool は増えるだけ(`Votes.stateBefore_poolExt`)なので以後の添字でも残る
(`gfVote_mem_of_le`)。pool の所属は受信済みの判定 `processed st (GfVote u)` と同じ(`processed_gfVote_iff`)。

これは `Majority.lean` の `HonestSupport.vote`(honest な committee の要素の投票が `supportCutoff` までに honest な全ノードの pool に
あること)に向けた配送の層の入口で、残りは経路 (1)(自分の投票: `goldfishVoteWith_some` の `onGoldfishVoteChecked`。`OwnVote.tick_honest_gfVote_mem`)と経路 (3)
(運ばれた投票)の pool への到達、受信の直前に `InWindow` が成り立つこと(配送は時計 `st.s` を進めないので、受信者の slot は
受信の前の受信者自身の最後の tick で決まる。`ScheduleWellFormed` の honest な tick の網羅と時刻の順から示す — GST 以後に発行された投票の
締切より前の配送は `Window.inWindow_of_deliver_gfVote`)、`UnforgeableSignatures` から
honest な投票者の偽の投票が pool に無い(`equivocates` が偽)こと(同じ honest な投票者・同じ slot の pool の投票は 1 つ: `PoolFrom.pool_honest_unique`。`equivocates` の個数
`Set.size (votesBy …) < 2` までの橋渡しは `Equivocation.pool_no_equivocation`)。経路 (2) の 3 つの仮定をすべて外した形は
`Equivocation.deliver_honest_gfVote_mem`。
受信の処理の条件は手書き `on_goldfish_vote_insert`(`DecoupledConsensusProofs/Protocol/Handlers/Pool.lean`)の窓と equivocation の
守りに当たる(手書きは「まだ pool に無い」も仮定して末尾に足す式を結論にし、ここは既にあってもよい所属を結論にする)。
`PartialSynchrony` の読みは、手書き `genericPartialSynchrony_of_named`(`DecoupledConsensusProofs/Bridge/GenericExecution.lean`)が
名前付きの run の部分同期を一般形に写すうちの broadcast の腕に当たる。
-/

namespace Proofs.Consensus.Delivery

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Schedule
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Votes

/-! ## 受信の処理 -/

/-- 受信者の slot の窓: `onGoldfishVote` は `u.slot < st.s - 1` か `st.s < u.slot` の投票を退ける。 -/
def InWindow (st : Store) (u : GoldfishVote) : Prop := u.slot ≤ st.s ∧ st.s ≤ u.slot + 1

/-- **窓の中で equivocation の無い投票は `onGoldfishVote` の後の pool にある**(既にあればそのまま、無ければ末尾に足す)。 -/
theorem mem_onGoldfishVote (st : Store) (u : GoldfishVote) (hw : InWindow st u)
    (heq : equivocates (storePool st u.slot) u.valIndex = false) :
    u ∈ poolList (onGoldfishVote st u) u.slot := by
  obtain ⟨hlo, hhi⟩ := hw
  unfold onGoldfishVote
  split_ifs with h1 h2
  · have hc : (NaruStd.Table.getOr st.gfVotes u.slot []).contains u = true := by
      have hw1 : decide (u.slot < st.s - 1) = false := decide_eq_false (by omega)
      have hw2 : decide (st.s < u.slot) = false := decide_eq_false (by omega)
      rw [hw1, hw2] at h1
      simpa using h1
    exact List.contains_iff_mem.mp hc
  · rw [heq] at h2
    exact absurd h2 Bool.false_ne_true
  · unfold poolList
    show u ∈ NaruStd.Table.getOr (st.gfVotes.insert u.slot (NaruStd.Table.getOr st.gfVotes u.slot [] ++ [u])) u.slot []
    rw [Proofs.Consensus.Tables.getOr_insert_self Proofs.Consensus.Records.nat_compare_eq_iff]
    exact List.mem_append_right _ (List.mem_singleton_self u)

/-- 投票者が committee の要素(`voteWellFormed`)なら、守り `onGoldfishVoteChecked` も同じ。 -/
theorem mem_onGoldfishVoteChecked (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote)
    (hc : voteWellFormed c u = true) (hw : InWindow st u)
    (heq : equivocates (storePool st u.slot) u.valIndex = false) :
    u ∈ poolList (onGoldfishVoteChecked c st u) u.slot := by
  unfold onGoldfishVoteChecked
  have hc' : (c u.slot).contains u.valIndex = true := hc
  rw [hc']
  exact mem_onGoldfishVote st u hw heq

/-- **配送された投票の受信の処理**(`receiptProcess` の投票の腕): 上の 3 つの条件の下で投票は pool に入る。 -/
theorem mem_receiptProcess_gfVote (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (st : NamedStore) (u : GoldfishVote)
    (hc : voteWellFormed c u = true) (hw : InWindow st.core u)
    (heq : equivocates (storePool st.core u.slot) u.valIndex = false) :
    u ∈ poolList (receiptProcess c p s st (NamedObject.GfVote u)).core u.slot :=
  mem_onGoldfishVoteChecked c st.core u hc hw heq

/-- 受信済みの判定 `processed st (GfVote u)` は鍵 `u.slot` の pool の所属。 -/
theorem processed_gfVote_iff (st : NamedStore) (u : GoldfishVote) :
    processed st (NamedObject.GfVote u) = true ↔ u ∈ poolList st.core u.slot := by
  show (storePool st.core u.slot).contains u = true ↔ _
  rw [Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.gv_compare_eq_iff]
  exact mem_storePool_iff st.core u.slot u

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **添字 `j` の配送の後、受信者の pool に投票がある**: `stateBefore (j + 1)` の `w` は `stateBefore j` の `w` に
`nodeProcess` を施したもの。条件は受信の直前の `w` の store について。 -/
theorem deliver_gfVote_mem {j : Nat} {w : ValidatorId} {u : GoldfishVote} {t : Int}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.GfVote u) t))
    (hc : voteWellFormed c u = true) (hw : InWindow (worldAt (stateBefore c p a nr s rho j) w).st.core u)
    (heq : equivocates (storePool (worldAt (stateBefore c p a nr s rho j) w).st.core u.slot) u.valIndex = false) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot := by
  rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hj]
  unfold worldStep
  dsimp only
  rw [Proofs.Consensus.Signing.worldAt_insert_self]
  exact mem_receiptProcess_gfVote c p s _ u hc hw heq

/-- pool の投票は以後の添字でも pool に残る(`Votes.stateBefore_poolExt`)。 -/
theorem gfVote_mem_of_le {i j : Nat} (hij : i ≤ j) {w : ValidatorId} {k : Nat} {u : GoldfishVote}
    (h : u ∈ poolList (worldAt (stateBefore c p a nr s rho i) w).st.core k) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho j) w).st.core k :=
  (stateBefore_poolExt c p a nr s rho hij w).mono k u h

/-- 配送された投票は、配送の後のどの添字でも受信者の pool にある(`deliver_gfVote_mem` + `gfVote_mem_of_le`)。 -/
theorem deliver_gfVote_mem_of_lt {j i : Nat} (hji : j < i) {w : ValidatorId} {u : GoldfishVote} {t : Int}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.GfVote u) t))
    (hc : voteWellFormed c u = true) (hw : InWindow (worldAt (stateBefore c p a nr s rho j) w).st.core u)
    (heq : equivocates (storePool (worldAt (stateBefore c p a nr s rho j) w).st.core u.slot) u.valIndex = false) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot :=
  gfVote_mem_of_le c p a nr s rho hji (deliver_gfVote_mem c p a nr s rho hj hc hw heq)

/-- **`HandlesAt` の投票の 3 つの経路**: (1) `w` 自身の時刻 `t2` の tick が添字 `j` で `u` を出す(`Emits` の添字)、
(2) 添字 `j` が `w` への `u` の配送、(3) 添字 `j` の event のブロックの処理が `u` を運ぶブロックを新しく tree に入れる。 -/
theorem handlesAt_gfVote_cases {j : Nat} {w : ValidatorId} {u : GoldfishVote} {t2 : Int}
    (h : HandlesAt c p a nr s rho j w (NamedObject.GfVote u) t2) :
    (rho.events[j]? = some (NamedEvent.Tick w t2) ∧
        (emittedAt c p a nr s rho j w t2).contains (NamedObject.GfVote u) = true) ∨
      rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.GfVote u) t2) ∨
      ∃ ev, rho.events[j]? = some ev ∧ eventNode ev = w ∧ eventTime ev = t2 ∧
        ∃ (b : NamedBlock) (k : Nat) (before : NamedStore),
          ((BlockCall c p a nr s (worldAt (stateBefore c p a nr s rho j) w) ev b before ∧
              ¬ (before.core.tree.contains (eraseBlock b) = true)) ∧
            (postCore c p s before b).core.tree.contains (eraseBlock b) = true) ∧
          (namedGfVotes b)[k]? = some u := by
  obtain ⟨ev, ⟨⟨hev, hn⟩, ht⟩, hh⟩ := h
  rcases hh with ⟨⟨t', hevt, hco⟩ | ⟨t', hevd⟩⟩ | ⟨b, k, before, hb⟩
  · left
    cases ev with
    | Tick v' t'' =>
      simp only [eventNode, eventTime, NamedEvent.Tick.injEq, true_and] at hn ht hevt hco
      subst hn ht hevt
      exact ⟨hev, hco⟩
    | Deliver v' o t'' =>
      simp only [eventNode] at hevt
      exact absurd hevt (by simp)
  · right; left
    cases ev with
    | Tick v' t'' =>
      simp only [eventNode] at hevd
      exact absurd hevd (by simp)
    | Deliver v' o t'' =>
      simp only [eventNode, eventTime] at hn ht hevd
      obtain ⟨-, rfl, -⟩ := hevd
      subst hn ht
      exact hev
  · right; right
    exact ⟨ev, hev, hn, ht, b, k, before, hb⟩

/-- **投票の部分同期**: honest な `v` が時刻 `t` に発行した投票は、honest な `w` が締切 `max t tGST + Δ`(horizon 以内)より前の
ある添字 `j` で扱う。投票は `excludes` が偽なので、`PartialSynchrony` の除外の条件は要らない。 -/
theorem partialSynchrony_gfVote (hps : PartialSynchrony c p a nr s rho) {v w : ValidatorId} {u : GoldfishVote} {t : Int}
    (hv : rho.honest.contains v = true) (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t)
    (hw : rho.honest.contains w = true) (hd : max t s.e.tGST + s.e.delta ≤ rho.horizon) :
    ∃ t2, (t ≤ t2 ∧ t2 < max t s.e.tGST + s.e.delta) ∧
      ∃ j, HandlesAt c p a nr s rho j w (NamedObject.GfVote u) t2 := by
  have h := hps.1 v (NamedObject.GfVote u) t ⟨hv, hem⟩ w
  dsimp only at h
  exact h ⟨⟨hw, hd⟩, by simp [excludes]⟩

/-- 投票の部分同期と経路の分解をまとめた形: 締切より前に、(1) `w` 自身がその投票を出すか、(2) `u` が `w` に配送されるか、
(3) `u` を運ぶブロックが `w` の tree に新しく入る。 -/
theorem partialSynchrony_gfVote_cases (hps : PartialSynchrony c p a nr s rho) {v w : ValidatorId} {u : GoldfishVote}
    {t : Int} (hv : rho.honest.contains v = true) (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t)
    (hw : rho.honest.contains w = true) (hd : max t s.e.tGST + s.e.delta ≤ rho.horizon) :
    ∃ t2 j, (t ≤ t2 ∧ t2 < max t s.e.tGST + s.e.delta) ∧
      ((rho.events[j]? = some (NamedEvent.Tick w t2) ∧
          (emittedAt c p a nr s rho j w t2).contains (NamedObject.GfVote u) = true) ∨
        rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.GfVote u) t2) ∨
        ∃ ev, rho.events[j]? = some ev ∧ eventNode ev = w ∧ eventTime ev = t2 ∧
          ∃ (b : NamedBlock) (k : Nat) (before : NamedStore),
            ((BlockCall c p a nr s (worldAt (stateBefore c p a nr s rho j) w) ev b before ∧
                ¬ (before.core.tree.contains (eraseBlock b) = true)) ∧
              (postCore c p s before b).core.tree.contains (eraseBlock b) = true) ∧
            (namedGfVotes b)[k]? = some u) := by
  obtain ⟨t2, ht2, j, hj⟩ := partialSynchrony_gfVote c p a nr s rho hps hv hem hw hd
  exact ⟨t2, j, ht2, handlesAt_gfVote_cases c p a nr s rho hj⟩

/-- 経路 (1) の投票は `w` 自身の投票: `Emits w (GfVote u) t2` なので投票者は `w`(`Voting.emits_gfVote_shape`)。 -/
theorem handlesAt_gfVote_tick_self {j : Nat} {w : ValidatorId} {u : GoldfishVote} {t2 : Int}
    (hj : rho.events[j]? = some (NamedEvent.Tick w t2))
    (hco : (emittedAt c p a nr s rho j w t2).contains (NamedObject.GfVote u) = true) :
    Emits c p a nr s rho w (NamedObject.GfVote u) t2 ∧ u.valIndex = w :=
  have he : Emits c p a nr s rho w (NamedObject.GfVote u) t2 := ⟨j, hj, hco⟩
  ⟨he, (Proofs.Consensus.Voting.emits_gfVote_shape c p a nr s rho he).2.2.1⟩

end Run

end Proofs.Consensus.Delivery
