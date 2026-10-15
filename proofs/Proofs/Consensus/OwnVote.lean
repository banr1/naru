import Proofs.Consensus.Equivocation
import Mathlib.Tactic

/-!
# 自分の tick の投票は自分の pool に入る(C71 の補題)

`Delivery.handlesAt_gfVote_cases` の経路 (1): 添字 `j` が `w` 自身の tick で、その tick が投票 `u` を出す。

tick(`Model/Consensus/Protocol/Tick.lean`)の投票の務め `namedGoldfishVoteWith` は、投票 `u` を出すとき store 側に
`onGoldfishVoteChecked` で `u` を入れる(`Votes.goldfishVoteWith_some`)。務めの store の slot は `u.slot` そのものなので
受信者の窓 `InWindow` は自明に成り立ち、投票者は committee の要素なので守り `voteWellFormed` も通る。残る equivocation の守りは
務めの直前の pool について要り、時計を合わせただけの store の pool は tick の前の pool と定義上同じ。
Δ > 0 なら投票の時刻は提案の時刻と違う(`Voting.voteStore_of_voteTime`)ので提案の務めは走らず、務めの後の確定の更新
(`namedUpdateConfirmationWith`)と attestation の務め(`attestWith`)は pool を変えない。したがって tick の前の pool で
equivocation が無ければ、tick の後の鍵 `u.slot` の pool に `u` がある(`tick_gfVote_mem`)。

run では、honest な `w` の添字 `j` の tick が `u` を出すと、`u` の投票者は `w`(`Voting.emits_gfVote_shape`)で、
`stateBefore j` の pool に equivocation は無い(`Equivocation.pool_no_equivocation`)ので、`stateBefore (j + 1)` の `w` の
鍵 `u.slot` の pool に `u` がある(`tick_honest_gfVote_mem`)。`Delivery.handlesAt_gfVote_cases` の経路 (1)(2) をこれと
`Equivocation.deliver_honest_gfVote_mem` でまとめると、GST 以後の honest な投票を honest な `w` が発行の時刻以後・締切より前の添字 `j` で扱えば、
`stateBefore (j + 1)` の `w` の pool に投票があるか、経路 (3)(`u` を運ぶブロックが添字 `j` で `w` の tree に新しく入る)のどちらか
(`handlesAt_honest_gfVote_mem_or_carried`)。残りは経路 (3) の pool への到達。

手書きでは `on_goldfish_vote_insert`(`DecoupledConsensusProofs/Protocol/Handlers/Pool.lean`)を自分の投票の務めに当てる運びに当たる。
-/

namespace Proofs.Consensus.OwnVote

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Votes

/-! ## 投票の務めと tick -/

/-- **投票の務めが出した投票は務めの後の pool にある**: 務めの直前の pool で投票者が equivocate していなければ。 -/
theorem namedGoldfishVoteWith_mem (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) (st : NamedStore) {u : GoldfishVote}
    (h : (namedGoldfishVoteWith c cache e hc nd st).2 = some u)
    (heq : equivocates (storePool st.core u.slot) u.valIndex = false) :
    u ∈ poolList (namedGoldfishVoteWith c cache e hc nd st).1.core u.slot := by
  rw [Proofs.Consensus.Voting.namedGoldfishVoteWith_out] at h
  obtain ⟨hval, hslot, -, hmem, hstore⟩ := goldfishVoteWith_some c cache e hc nd st.core h
  have h1 : (namedGoldfishVoteWith c cache e hc nd st).1.core = (goldfishVoteWith c cache e hc nd st.core).1 := by
    unfold namedGoldfishVoteWith; rfl
  rw [h1, hstore]
  refine Proofs.Consensus.Delivery.mem_onGoldfishVoteChecked c st.core u ?_ ?_ heq
  · show (c u.slot).contains u.valIndex = true
    rw [hval, hslot]
    exact hmem
  · exact ⟨hslot.le, by omega⟩

section Tick

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
  (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Node) (st : NamedStore)
  (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int)

/-- **tick が出した投票は tick の後の自分の pool にある**(Δ > 0): tick の前の pool で投票者が equivocate していなければ。 -/
theorem tick_gfVote_mem (hδ : 0 < e.delta) {u : GoldfishVote}
    (h : NamedObject.GfVote u ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2)
    (heq : equivocates (storePool st.core u.slot) u.valIndex = false) :
    u ∈ poolList (tick c p a nr cache e hc cfg nd st rec t).1.core u.slot := by
  obtain ⟨hs, ht, hv⟩ := Proofs.Consensus.Voting.tick_gfVote_shape c p a nr cache e hc cfg nd st rec t h
  rw [Proofs.Consensus.Voting.voteStore_of_voteTime c p nr cache e hc cfg nd st t hδ ht,
    ← Proofs.Consensus.Voting.namedGoldfishVoteWith_out] at hv
  have hmem := namedGoldfishVoteWith_mem c cache e hc nd _ hv heq
  have hne : t ≠ proposalTime e (slotOf e t) :=
    fun h' => Proofs.Consensus.Voting.voteTime_ne_proposalTime e hδ (slotOf e t) (ht.symm.trans h')
  have hnp : ((decide (0 < slotOf e t) && t == proposalTime e (slotOf e t)) && (p (slotOf e t) == nd.valIndex)) = false := by
    simp [hne]
  have hvt : (decide (0 < slotOf e t) && t == voteTime e (slotOf e t)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨hs, ht⟩
  unfold Proofs.Consensus.Voting.clocked at hmem
  unfold tick
  dsimp only
  rw [hnp, hvt]
  simp only [Bool.false_eq_true, ↓reduceIte]
  generalize namedGoldfishVoteWith c cache e hc nd _ = g at hmem ⊢
  obtain ⟨st2, vo⟩ := g
  dsimp only at hmem ⊢
  split_ifs
  all_goals dsimp only
  all_goals (try simp only [Proofs.Consensus.PoolFrom.attestWith_poolList,
    Proofs.Consensus.PoolFrom.namedUpdateConfirmationWith_poolList])
  all_goals exact hmem

end Tick

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- ノードの tick(`nodeTick`)でも同じ(Δ > 0)。 -/
theorem nodeTick_gfVote_mem (hδ : 0 < s.e.delta) (v : ValidatorId) (n : NamedNodeState) (t : Int) {u : GoldfishVote}
    (h : NamedObject.GfVote u ∈ (nodeTick c p a nr s v n t).2)
    (heq : equivocates (storePool n.st.core u.slot) u.valIndex = false) :
    u ∈ poolList (nodeTick c p a nr s v n t).1.st.core u.slot := by
  rw [Proofs.Consensus.Signing.nodeTick_out] at h
  unfold nodeTick profileTick
  dsimp only
  exact tick_gfVote_mem c p a nr _ s.e s.hc s.cfg _ n.st n.signing t hδ h heq

/-- **honest なノードの tick の投票は tick の後の自分の pool にある**: `ScheduleWellFormed` / `UnforgeableSignatures` / Δ > 0 の
下で、honest な `w` の添字 `j` の tick(時刻 `t`)が投票 `u` を出すなら、`stateBefore (j + 1)` の `w` の鍵 `u.slot` の pool に
`u` がある(投票者は `w` 自身なので、tick の前の pool の equivocation の守りは `Equivocation.pool_no_equivocation`)。 -/
theorem tick_honest_gfVote_mem (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (hδ : 0 < s.e.delta) {w : ValidatorId} {u : GoldfishVote} {t : Int} (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Tick w t))
    (hco : (emittedAt c p a nr s rho j w t).contains (NamedObject.GfVote u) = true) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot := by
  obtain ⟨-, hval⟩ := Proofs.Consensus.Delivery.handlesAt_gfVote_tick_self c p a nr s rho hj hco
  rw [Proofs.Consensus.Signing.emittedAt_eq, List.contains_iff_mem] at hco
  rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hj]
  unfold worldStep
  dsimp only
  rw [Proofs.Consensus.Signing.worldAt_insert_self]
  exact nodeTick_gfVote_mem c p a nr s hδ w _ t hco
    (Proofs.Consensus.Equivocation.pool_no_equivocation c p a nr s rho hsch hunf j w u.slot (by rw [hval]; exact hw))

/-- **honest な発行者の投票は発行の後の自分の pool に残る**: `ScheduleWellFormed` / `UnforgeableSignatures` / Δ > 0 の下で、
honest な `w` が時刻 `t` に投票 `u` を発行すると、その tick の
添字 `j` の後のどの添字でも `w` の鍵 `u.slot` の pool に `u` がある(`Delivery.gfVote_mem_of_le`)。 -/
theorem emits_honest_gfVote_mem_of_lt (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (hδ : 0 < s.e.delta) {w : ValidatorId} {u : GoldfishVote} {t : Int} (hw : rho.honest.contains w = true)
    (hem : Emits c p a nr s rho w (NamedObject.GfVote u) t) :
    ∃ j, rho.events[j]? = some (NamedEvent.Tick w t) ∧
      ∀ i, j < i → u ∈ poolList (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot := by
  obtain ⟨j, hj, hco⟩ := hem
  exact ⟨j, hj, fun i hji => Proofs.Consensus.Delivery.gfVote_mem_of_le c p a nr s rho hji
    (tick_honest_gfVote_mem c p a nr s rho hsch hunf hδ hw hj hco)⟩

/-- **GST 以後の honest な投票の扱い: pool に入るか、運ぶブロックが tree に入るか**: `ScheduleWellFormed` /
`UnforgeableSignatures` / Δ > 0 の下で、honest な `v` が GST 以後の時刻 `t` に発行した投票 `u` を honest な `w` が添字 `j`
(時刻 `t2`、`t ≤ t2 < max t tGST + Δ`)で扱う(`HandlesAt`)なら、経路 (1)(自分の tick、`tick_honest_gfVote_mem`)と
経路 (2)(配送、`Equivocation.deliver_honest_gfVote_mem`)では `stateBefore (j + 1)` の `w` の鍵 `u.slot` の pool に `u` があり、
残りは経路 (3)(添字 `j` のブロックの処理が `u` を運ぶブロックを新しく `w` の tree に入れる)。 -/
theorem handlesAt_honest_gfVote_mem_or_carried (hsch : ScheduleWellFormed s rho)
    (hunf : UnforgeableSignatures c p a nr s rho) (hδ : 0 < s.e.delta) {v w : ValidatorId} {u : GoldfishVote}
    {t t2 : Int} (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t) (hv : rho.honest.contains v = true)
    (hgst : s.e.tGST ≤ t) (hw : rho.honest.contains w = true) {j : Nat}
    (hh : HandlesAt c p a nr s rho j w (NamedObject.GfVote u) t2)
    (ht : t ≤ t2) (ht2 : t2 < max t s.e.tGST + s.e.delta) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot ∨
      ∃ ev, rho.events[j]? = some ev ∧ eventNode ev = w ∧ eventTime ev = t2 ∧
        ∃ (b : NamedBlock) (k : Nat) (before : NamedStore),
          ((BlockCall c p a nr s (worldAt (stateBefore c p a nr s rho j) w) ev b before ∧
              ¬ (before.core.tree.contains (eraseBlock b) = true)) ∧
            (postCore c p s before b).core.tree.contains (eraseBlock b) = true) ∧
          (namedGfVotes b)[k]? = some u := by
  rcases Proofs.Consensus.Delivery.handlesAt_gfVote_cases c p a nr s rho hh with ⟨hj, hco⟩ | hj | h3
  · exact Or.inl (tick_honest_gfVote_mem c p a nr s rho hsch hunf hδ hw hj hco)
  · exact Or.inl (Proofs.Consensus.Equivocation.deliver_honest_gfVote_mem c p a nr s rho hsch hunf hδ hem hv hgst hw
      hj ht ht2)
  · exact Or.inr h3

end Run

end Proofs.Consensus.OwnVote
