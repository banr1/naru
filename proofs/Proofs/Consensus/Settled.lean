import Proofs.Consensus.Proposal
import Proofs.Consensus.Stamps
import Mathlib.Tactic

/-!
# honest なノードが扱った投票は、pool に入るか投票者の equivocation が pool に残る(C71 / C77 の補題)

`AvailableHoles.genuineConf_adoptionTransport`(手書き `adoptionTransport_B_after_gst`)の `forward` / `backward` は、どちらも
「あるノードが受理した投票(投票者は byzantine でもよい)を、中継(`PartialSynchrony` の第 2 連言)で受けた honest なノードの pool に
運ぶ」運びを使う。投票者が honest なら pool に入る(`Carried.handlesAt_honest_gfVote_mem`)が、byzantine なら受け手の pool に同じ
投票者の別の投票が既にあって退けられることがある。そのとき受け手の pool には同じ投票者の 2 つの投票がある。この 2 通りをまとめて
`PoolSettled`(pool にあるか、pool で投票者の投票が 1 つ以下ではない)と呼ぶ。手書き `weakct_actual_gfVote_settled_before_deadline`
(`DecoupledConsensusProofs/Protocol/Schedule/WeakConfirmationTransport.lean`)の「pool にあるか equivocation」に当たる。

- 時刻が同じなら tick は配送より前(`eventKey` の phase が tick 0・配送 1)なので、配送の直前の受け手の slot の下限は
  `proposalTime k ≤ t2` で足りる(`tick_index_lt_deliver` / `slot_ge_of_deliver_le`。`Window.slot_ge_of_deliver` は狭義)。
- `handlesAt_gfVote_settled`: honest な `w` が添字 `j` で投票 `u`(committee の要素)を扱い、時刻が `u.slot` の窓
  (`proposalTime u.slot ≤ t2 < proposalTime (u.slot + 2)`)の中なら、`stateBefore (j + 1)` の `w` で `PoolSettled`。経路は
  `Delivery.handlesAt_gfVote_cases` の 3 つ: (1) 自分の tick の投票は pool に入る(`OwnVote.tick_honest_gfVote_mem`)、
  (2) 配送は `onGoldfishVoteChecked` の守り(受理の後の pool で一意なら受理の前でも一意で、equivocation の守りを通る)、
  (3) ブロックの処理は、配送なら `Carried.processBlockCore_mem` と同じ運び、自分の提案なら運ぶ投票は提案者の pool のバケツ
  `proposerView`(`Proposal.tick_block_shape` / `proposalWith_some`)なので既に pool にある。
- `acceptsAt_gfVote_settled`: honest な `x` が添字 `i`・時刻 `t0` に投票 `u` を受理し(`AcceptsAt`)、`u.slot` の窓の中で
  中継の締切 `max t0 tGST + Δ` が horizon 以内なら、honest な `w` は締切より前の時刻のある添字 `j` の後で `PoolSettled`
  (受理の直後に既に `w` の pool にあれば `j = i`)。
- `settled_stamped`: `PoolSettled` は後の添字の、印が event の時刻より後の `γ` より前の pool(`stampedPool`。`lateVotes` の形)に
  移る(その pool にあるか、そこで投票者が equivocate する)。
- `pool_accepted`: ある添字の前の pool の投票は、それより前のある添字で受理された(`AcceptsAt`)。新しく pool に入る経路は
  自分の tick の投票・配送された投票・配送されて新しく tree に入ったブロックが運ぶ投票(`processBlockCore_new`)だけ
  (`pool_step_accepts`)。
-/

namespace Proofs.Consensus.Settled

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Schedule
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Votes Proofs.Consensus.Carried

/-- 投票 `u` は store の pool に入ったか、鍵 `u.slot` の pool で投票者 `u.valIndex` の投票が 1 つ以下ではない。 -/
def PoolSettled (st : Store) (u : GoldfishVote) : Prop :=
  u ∈ poolList st u.slot ∨ ¬ UniqueIn st u.slot u.valIndex

/-- `PoolSettled` は pool の拡張で保たれる。 -/
theorem PoolSettled.mono {a b : Store} {u : GoldfishVote} (h : PoolSettled a u)
    (hsub : ∀ k x, x ∈ poolList a k → x ∈ poolList b k) : PoolSettled b u := by
  rcases h with h | h
  · exact Or.inl (hsub _ _ h)
  · exact Or.inr (fun hb => h (hb.mono (hsub _)))

/-- **同じ時刻なら tick は配送より前**: `eventKey` は(時刻, phase)で、tick の phase は 0、配送は 1。 -/
theorem tick_index_lt_deliver {rho : NamedRun} (hs : EventsSorted rho) {i j : Nat} {v w : ValidatorId}
    {o : NamedObject} {τ t2 : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v τ))
    (hj : rho.events[j]? = some (NamedEvent.Deliver w o t2)) (h : τ ≤ t2) : i < j := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · exact hij
  · rw [hi] at hj
    cases hj
  · exfalso
    have hs' := hs j i hji
    simp only [hj, hi] at hs'
    apply hs'
    show (compare t2 τ).then (compare (1 : Nat) (0 : Nat)) = .gt
    rcases lt_or_eq_of_le h with hlt | heq
    · rw [Int.compare_eq_gt.mpr hlt]
      rfl
    · rw [heq, Int.compare_eq_eq.mpr rfl]
      rfl

/-! ## 新しく pool に入った投票の由来 -/

/-- **ブロックの処理で新しく pool に入った投票は、新しく tree に入ったブロックが運ぶ投票**: 処理の後の鍵 `k` の pool にあって前に
無い投票 `x` は `B` が運ぶ投票で、`B` は処理の前の tree に無く後の tree にある(受理の分岐 `acceptBody` を通った)。 -/
theorem processBlockCore_new (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    {st : NamedStore} {B : NamedBlock} {x : GoldfishVote} {k : Nat}
    (hx : x ∈ poolList (processBlockCore c p e hc cfg st B).core k) (hnot : x ∉ poolList st.core k) :
    x ∈ namedGfVotes B ∧ ¬ (st.core.tree.contains (eraseBlock B) = true) ∧
      (processBlockCore c p e hc cfg st B).core.tree.contains (eraseBlock B) = true := by
  revert hx
  unfold processBlockCore
  split_ifs
  · intro hx
    exact absurd hx hnot
  · dsimp only
    rw [Proofs.Consensus.Stores.commitBlock_core]
    rcases Proofs.Consensus.Carrier.onBlockCheckedUsing_eq _ hc st.core (eraseBlock B) with h | h
    · rw [h]
      rcases Proofs.Consensus.Carrier.onBlockUsing_eq c p st.core (eraseBlock B)
          (fun parentState => Model.Consensus.Protocol.ChainState.namedTransition e cfg parentState B) with
        h' | ⟨hnotin, -, h'⟩
      · rw [h']
        intro hx
        exact absurd hx hnot
      · intro hx
        refine ⟨?_, ?_, ?_⟩
        · rcases Proofs.Consensus.PoolFrom.onBlockUsing_from c p hx with h1 | h1
          · exact absurd h1 hnot
          · rw [Proofs.Consensus.PoolFrom.gfVotes_eraseBlock] at h1
            exact h1
        · rw [Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.block_compare_eq_iff]
          exact hnotin
        · rw [h', Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.block_compare_eq_iff,
            Proofs.Consensus.Carrier.acceptBody_tree,
            Proofs.Consensus.Sets.mem_insert_iff Proofs.Consensus.Orders.block_compare_eq_iff]
          exact Or.inl rfl
    · rw [h]
      intro hx
      exact absurd hx hnot

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **配送の直前の slot の下限(非狭義)**: honest な `w` への時刻 `t2` の配送の直前、`proposalTime k ≤ t2` なら `w` の slot は
`k` 以上(slot `k` の開始の tick は同じ時刻でも配送より前の添字)。 -/
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
  have hlt : j' < j := tick_index_lt_deliver hs hj' hj hlo
  have hle := Proofs.Consensus.Window.tick_le_clock c p a nr s rho hs hnn hlt hj'
  rw [Proofs.Consensus.Clocks.clock_slot c p a nr s rho j w]
  exact Proofs.Consensus.Window.le_slotOf_of_le s.e hδ hle

/-- 配送の直前の窓(非狭義の下限): `proposalTime u.slot ≤ t2 < proposalTime (u.slot + 2)` なら `InWindow`。 -/
theorem inWindow_of_deliver_le (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {j : Nat} {w : ValidatorId}
    {o : NamedObject} {u : GoldfishVote} {t2 : Int} (hw : rho.honest.contains w = true)
    (hj : rho.events[j]? = some (NamedEvent.Deliver w o t2))
    (hlo : proposalTime s.e u.slot ≤ t2) (hhi : t2 < proposalTime s.e (u.slot + 1 + 1)) :
    Proofs.Consensus.Delivery.InWindow (worldAt (stateBefore c p a nr s rho j) w).st.core u :=
  ⟨slot_ge_of_deliver_le c p a nr s rho hsch hδ hw hj hlo,
    Proofs.Consensus.Window.slot_le_of_deliver c p a nr s rho hsch hδ hj hhi⟩

/-- 添字 `j` の pool は `j + 1` の pool に含まれる。 -/
theorem pool_succ_sub (j : Nat) (w : ValidatorId) :
    ∀ k x, x ∈ poolList (worldAt (stateBefore c p a nr s rho j) w).st.core k →
      x ∈ poolList (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core k :=
  fun _ _ hx => Proofs.Consensus.Delivery.gfVote_mem_of_le c p a nr s rho (Nat.le_succ j) hx

/-- **自分の提案の運ぶ投票は提案者の pool にある**: 添字 `j` の `w` の tick が出したブロック `b` の運ぶ投票は、tick の前の `w` の
鍵 `u.slot` の pool にある(運ぶ投票は時計を合わせた store のバケツ `slotOf t - 1` の `proposerView`、pool の不変条件で鍵は slot)。 -/
theorem tick_block_gfVote_mem {j : Nat} {w : ValidatorId} {t : Int} {b : NamedBlock} {u : GoldfishVote}
    (hcont : NamedObject.Block b ∈ (nodeTick c p a nr s w (worldAt (stateBefore c p a nr s rho j) w) t).2)
    (hu : u ∈ namedGfVotes b) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho j) w).st.core u.slot := by
  rw [Proofs.Consensus.Signing.nodeTick_out] at hcont
  obtain ⟨-, -, -, hD⟩ := Proofs.Consensus.Proposal.tick_block_shape c p a nr _ s.e s.hc s.cfg _ _ _ t hcont
  obtain ⟨par, -, rfl⟩ := Proofs.Consensus.Proposal.proposalWith_some nr _ s.e s.hc _ _ hD
  have hpool : u ∈ poolList (worldAt (stateBefore c p a nr s rho j) w).st.core (slotOf s.e t - 1) := hu
  have hsl := (stateBefore_pool c p a nr s rho j w _ u hpool).1
  rw [← hsl] at hpool
  exact hpool

/-- **honest なノードが扱った投票は落ち着く**: `ScheduleWellFormed` / `UnforgeableSignatures` / Δ > 0 の下で、honest な `w` が
添字 `j`・時刻 `t2` で投票 `u`(committee の要素。投票者は byzantine でもよい)を扱い、`proposalTime u.slot ≤ t2 <
proposalTime (u.slot + 2)` なら、`stateBefore (j + 1)` の `w` で `PoolSettled`。 -/
theorem handlesAt_gfVote_settled (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (hδ : 0 < s.e.delta) {w : ValidatorId} (hw : rho.honest.contains w = true) {u : GoldfishVote}
    (hwf : voteWellFormed c u = true) {j : Nat} {t2 : Int}
    (hh : HandlesAt c p a nr s rho j w (NamedObject.GfVote u) t2)
    (hlo : proposalTime s.e u.slot ≤ t2) (hhi : t2 < proposalTime s.e (u.slot + 1 + 1)) :
    PoolSettled (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u := by
  rcases Proofs.Consensus.Delivery.handlesAt_gfVote_cases c p a nr s rho hh with ⟨hj, hco⟩ | hj |
    ⟨ev, hev, hn, hte, b, k, before, ⟨⟨hbc, hnew⟩, hin⟩, hk⟩
  · exact Or.inl (Proofs.Consensus.OwnVote.tick_honest_gfVote_mem c p a nr s rho hsch hunf hδ hw hj hco)
  · by_cases hU : UniqueIn (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot u.valIndex
    · left
      exact Proofs.Consensus.Delivery.deliver_gfVote_mem c p a nr s rho hj hwf
        (inWindow_of_deliver_le c p a nr s rho hsch hδ hw hj hlo hhi)
        (equivocates_false_of_unique (hU.mono (pool_succ_sub c p a nr s rho j w u.slot)))
    · exact Or.inr hU
  · have hu : u ∈ namedGfVotes b := List.mem_of_getElem? hk
    rcases hbc with ⟨t', hevd, hbef⟩ | ⟨t', ⟨hevt, hcont⟩, -⟩
    · rw [hn] at hevd
      subst hevd hbef
      simp only [eventTime] at hte
      subst hte
      have hwin := inWindow_of_deliver_le c p a nr s rho hsch hδ hw hev hlo hhi
      by_cases hU : UniqueIn (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot u.valIndex
      · left
        rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev] at hU ⊢
        unfold worldStep at hU ⊢
        dsimp only at hU ⊢
        rw [Proofs.Consensus.Signing.worldAt_insert_self] at hU ⊢
        rw [nodeProcess_block_poolList]
        have hU' := hU.mono (a := (postCore c p s (worldAt (stateBefore c p a nr s rho j) w).st b).core)
          (fun x hx => by rw [nodeProcess_block_poolList]; exact hx)
        exact processBlockCore_mem c p s.e s.hc s.cfg hnew hin hu hwf hwin hU'
      · exact Or.inr hU
    · rw [hn] at hevt hcont
      subst hevt
      unfold Model.Consensus.Spec.Execution.tickEmits at hcont
      rw [List.contains_iff_mem] at hcont
      exact Or.inl (pool_succ_sub c p a nr s rho j w _ _ (tick_block_gfVote_mem c p a nr s rho hcont hu))

/-- 受理(`AcceptsAt`)した投票は受理の直後の pool にあり、committee の要素(pool の不変条件)。 -/
theorem acceptsAt_gfVote_mem {i : Nat} {x : ValidatorId} {u : GoldfishVote} {t0 : Int}
    (hacc : AcceptsAt c p a nr s rho i x (NamedObject.GfVote u) t0) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho (i + 1)) x).st.core u.slot ∧ voteWellFormed c u = true := by
  have hm := (Proofs.Consensus.Delivery.processed_gfVote_iff _ u).mp hacc.2
  exact ⟨hm, (stateBefore_pool c p a nr s rho (i + 1) x _ u hm).2⟩

/-- **受理された投票は中継で honest な各ノードに落ち着く**: `PartialSynchrony` / `ScheduleWellFormed` /
`UnforgeableSignatures` / Δ > 0 の下で、honest な `x` が添字 `i`・時刻 `t0` に投票 `u` を受理し、`proposalTime u.slot ≤ t0`、
中継の締切 `max t0 tGST + Δ` が `proposalTime (u.slot + 2)` 以下かつ horizon 以内なら、honest な `w` について、時刻
`t2`(`t0 ≤ t2 < max t0 tGST + Δ`)の添字 `j` があり、`stateBefore (j + 1)` の `w` で `PoolSettled`(受理の直後に既に `w` の pool に
あれば `j = i`)。 -/
theorem acceptsAt_gfVote_settled (hps : PartialSynchrony c p a nr s rho) (hsch : ScheduleWellFormed s rho)
    (hunf : UnforgeableSignatures c p a nr s rho) (hδ : 0 < s.e.delta) {x w : ValidatorId}
    (hx : rho.honest.contains x = true) (hw : rho.honest.contains w = true) {i : Nat} {u : GoldfishVote} {t0 : Int}
    (hacc : AcceptsAt c p a nr s rho i x (NamedObject.GfVote u) t0)
    (hlo : proposalTime s.e u.slot ≤ t0)
    (hhi : max t0 s.e.tGST + s.e.delta ≤ proposalTime s.e (u.slot + 1 + 1))
    (hd : max t0 s.e.tGST + s.e.delta ≤ rho.horizon) :
    ∃ t2 j, (t0 ≤ t2 ∧ t2 < max t0 s.e.tGST + s.e.delta) ∧
      (∃ ev, rho.events[j]? = some ev ∧ eventTime ev = t2) ∧
      PoolSettled (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u := by
  have hwf := (acceptsAt_gfVote_mem c p a nr s rho hacc).2
  obtain ⟨ev0, ⟨⟨hev0, -⟩, hte0⟩, -⟩ := hacc.1.1
  by_cases hpw : processed (worldAt (stateBefore c p a nr s rho (i + 1)) w).st (NamedObject.GfVote u) = true
  · refine ⟨t0, i, ⟨le_rfl, by have := le_max_left t0 s.e.tGST; linarith⟩, ⟨ev0, hev0, hte0⟩, ?_⟩
    exact Or.inl ((Proofs.Consensus.Delivery.processed_gfVote_iff _ u).mp hpw)
  · have h := hps.2 x i (NamedObject.GfVote u) t0 ⟨hx, hacc⟩ w
    dsimp only at h
    obtain ⟨t2, ⟨ht, ht2⟩, j, hh⟩ := h ⟨⟨⟨hw, hpw⟩, hd⟩, by simp [excludes]⟩
    have hevj : ∃ ev, rho.events[j]? = some ev ∧ eventTime ev = t2 := by
      obtain ⟨ev, ⟨⟨hev, -⟩, hte⟩, -⟩ := hh
      exact ⟨ev, hev, hte⟩
    exact ⟨t2, j, ⟨ht, ht2⟩, hevj,
      handlesAt_gfVote_settled c p a nr s rho hsch hunf hδ hw hwf hh (le_trans hlo ht) (lt_of_lt_of_le ht2 hhi)⟩

/-- **新しく pool に入った投票は、その添字で受理された**: 添字 `i` の前の `x` の鍵 `u.slot` の pool に無く後にある投票 `u` は、
添字 `i` の event で `x` が受理した(`AcceptsAt`)。経路は `PoolFrom.nodeTick_from` / `receiptProcess` の場合分け: 自分の tick の
投票(経路 (1))、配送された投票(経路 (2))、配送されて新しく tree に入ったブロックが運ぶ投票(経路 (3)、`processBlockCore_new`)。
自分の提案が運ぶ投票は既に pool にある(`tick_block_gfVote_mem`)ので新しくない。 -/
theorem pool_step_accepts {i : Nat} {x : ValidatorId} {u : GoldfishVote}
    (hnot : u ∉ poolList (worldAt (stateBefore c p a nr s rho i) x).st.core u.slot)
    (hin : u ∈ poolList (worldAt (stateBefore c p a nr s rho (i + 1)) x).st.core u.slot) :
    ∃ t0, AcceptsAt c p a nr s rho i x (NamedObject.GfVote u) t0 := by
  have hproc : ∀ (ev : NamedEvent), rho.events[i]? = some ev → eventNode ev = x →
      Handles c p a nr s (worldAt (stateBefore c p a nr s rho i) x) ev (NamedObject.GfVote u) →
      ∃ t0, AcceptsAt c p a nr s rho i x (NamedObject.GfVote u) t0 := by
    intro ev hev hn hH
    refine ⟨eventTime ev, ⟨⟨ev, ⟨⟨hev, hn⟩, rfl⟩, hH⟩, ?_⟩, ?_⟩
    · rw [Proofs.Consensus.Delivery.processed_gfVote_iff]
      exact hnot
    · rw [Proofs.Consensus.Delivery.processed_gfVote_iff]
      exact hin
  cases hev : rho.events[i]? with
  | none =>
    rw [Proofs.Consensus.Signing.stateBefore_succ_of_none c p a nr s rho hev] at hin
    exact absurd hin hnot
  | some ev =>
    have hin' := hin
    rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev] at hin'
    cases ev with
    | Tick w t =>
      unfold worldStep at hin'
      dsimp only at hin'
      by_cases hwx : w = x
      · subst hwx
        rw [Proofs.Consensus.Signing.worldAt_insert_self] at hin'
        rcases Proofs.Consensus.PoolFrom.nodeTick_from c p a nr s w _ t hin' with h | h | ⟨B, hB, huB⟩
        · exact absurd h hnot
        · refine hproc _ hev rfl (Or.inl (Or.inl ⟨t, rfl, ?_⟩))
          unfold Model.Consensus.Spec.Execution.tickEmits
          exact List.contains_iff_mem.mpr h
        · exact absurd (tick_block_gfVote_mem c p a nr s rho hB huB) hnot
      · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwx] at hin'
        exact absurd hin' hnot
    | Deliver w o t =>
      unfold worldStep at hin'
      dsimp only at hin'
      by_cases hwx : w = x
      · subst hwx
        rw [Proofs.Consensus.Signing.worldAt_insert_self] at hin'
        cases o with
        | Block B =>
          have h2 : u ∈ poolList (onBlockWith c p CarriedAdmission.AlsoCarried s.e s.hc s.cfg
              (worldAt (stateBefore c p a nr s rho i) w).st B).core u.slot := hin'
          unfold onBlockWith at h2
          rw [Proofs.Consensus.PoolFrom.admitCarried_poolList] at h2
          obtain ⟨huB, hnew, hpost⟩ := processBlockCore_new c p s.e s.hc s.cfg h2 hnot
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp huB
          exact hproc _ hev rfl (Or.inr ⟨B, k, _, ⟨⟨Or.inl ⟨t, rfl, rfl⟩, hnew⟩, hpost⟩, hk⟩)
        | GfVote v =>
          have h2 : u ∈ poolList (onGoldfishVoteChecked c (worldAt (stateBefore c p a nr s rho i) w).st.core v)
              u.slot := hin'
          rcases Proofs.Consensus.PoolFrom.onGoldfishVoteChecked_from c h2 with h | rfl
          · exact absurd h hnot
          · exact hproc _ hev rfl (Or.inl (Or.inr ⟨t, rfl⟩))
        | Attest row =>
          have h2 : u ∈ poolList (admitRow s.hc (worldAt (stateBefore c p a nr s rho i) w).st row).core u.slot := hin'
          rw [Proofs.Consensus.PoolFrom.admitRow_poolList] at h2
          exact absurd h2 hnot
      · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwx] at hin'
        exact absurd hin' hnot

/-- **pool の投票の最初の受理**: 添字 `n` の前の `x` の鍵 `u.slot` の pool にある投票 `u` は、`n` より前のある添字 `i` で `x` が
受理した(`AcceptsAt`)。添字 0 の pool は空なので、`u` が初めて pool に現れる添字を取って `pool_step_accepts`。 -/
theorem pool_accepted (x : ValidatorId) (u : GoldfishVote) :
    ∀ n, u ∈ poolList (worldAt (stateBefore c p a nr s rho n) x).st.core u.slot →
      ∃ i t0, i < n ∧ AcceptsAt c p a nr s rho i x (NamedObject.GfVote u) t0
  | 0, h => by
    have h0 : poolList (worldAt worldInit x).st.core u.slot = [] := initial_poolList u.slot
    unfold stateBefore at h
    simp only [List.take_zero, List.foldl_nil] at h
    rw [h0] at h
    exact absurd h List.not_mem_nil
  | n + 1, h => by
    by_cases hn : u ∈ poolList (worldAt (stateBefore c p a nr s rho n) x).st.core u.slot
    · obtain ⟨i, t0, hi, hacc⟩ := pool_accepted x u n hn
      exact ⟨i, t0, Nat.lt_succ_of_lt hi, hacc⟩
    · obtain ⟨t0, hacc⟩ := pool_step_accepts c p a nr s rho hn h
      exact ⟨n, t0, Nat.lt_succ_self n, hacc⟩

/-- 印が `γ` より前の鍵 `k` の pool の投票(`Goldfish.lateVotes` の形。`lateVotes e st s` は `γ = confirmationTime e s`)。 -/
def stampedPool (st : Store) (k : Nat) (γ : Int) : NaruStd.Set GoldfishVote :=
  NaruStd.Set.filter (storePool st k)
    (fun v => Model.Consensus.Objects.Time.occurrenceBefore (NaruStd.Table.get? st.timestampVote v) γ)

/-- 異なる 2 つの要素を含むリストの長さは 2 以上。 -/
theorem two_le_length_of_ne {α : Type} {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) :
    2 ≤ l.length := by
  classical
  have hsub : ({x, y} : Finset α) ⊆ l.toFinset := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact List.mem_toFinset.mpr hx
    · exact List.mem_toFinset.mpr hy
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at h2
  exact le_trans h2 (List.toFinset_card_le l)

/-- **落ち着いた投票は後の読みの印の付いた pool に残る**: `stateBefore (j + 1)` の `w` で `PoolSettled` なら、`j` より後の添字 `i` の
`w` の、印が添字 `j` の event の時刻より後の `γ` より前の pool(`stampedPool`)に `u` があるか、そこで投票者 `u.valIndex` が
equivocate する(pool の投票は動かず、印は event の時刻以下に固定される。`Stamps.stamp_le_of_mem`)。 -/
theorem settled_stamped (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    {j : Nat} {ev : NamedEvent} (hev : rho.events[j]? = some ev) {w : ValidatorId} {u : GoldfishVote}
    (hset : PoolSettled (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u) {i : Nat} (hji : j < i)
    {γ : Int} (hγ : eventTime ev < γ) :
    u ∈ (stampedPool (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot γ).elems ∨
      equivocates (stampedPool (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot γ) u.valIndex = true := by
  have hmem : ∀ x, x ∈ poolList (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot →
      x ∈ (stampedPool (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot γ).elems := by
    intro x hx
    have hxs := (stateBefore_pool c p a nr s rho (j + 1) w _ x hx).1
    rw [← hxs] at hx
    obtain ⟨hm, τ, hτ, hle⟩ := Proofs.Consensus.Stamps.stamp_le_of_mem c p a nr s rho hs hnn hev hx hji
    rw [hxs] at hm
    unfold stampedPool
    rw [Proofs.Consensus.Trees.mem_filter_iff]
    refine ⟨(mem_storePool_iff _ _ _).mpr hm, ?_⟩
    show Model.Consensus.Objects.Time.occurrenceBefore
      ((worldAt (stateBefore c p a nr s rho i) w).st.core.timestampVote.get? x) γ = true
    rw [hτ]
    exact Proofs.Consensus.Stamps.occurrenceBefore_at (lt_of_le_of_lt hle hγ)
  rcases hset with h | h
  · exact Or.inl (hmem u h)
  · right
    unfold UniqueIn at h
    push Not at h
    obtain ⟨x, y, hx, hy, hxv, hyv, hne⟩ := h
    unfold equivocates
    rw [decide_eq_true_eq]
    unfold NaruStd.Set.size
    exact two_le_length_of_ne ((Proofs.Consensus.Goldfish.mem_votesBy_iff _ _ _).mpr ⟨hmem x hx, hxv⟩)
      ((Proofs.Consensus.Goldfish.mem_votesBy_iff _ _ _).mpr ⟨hmem y hy, hyv⟩) hne

end Run

end Proofs.Consensus.Settled
