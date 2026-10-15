import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.Votes
import Proofs.Consensus.Voting
import Proofs.Consensus.Attribution
import Mathlib.Tactic

/-!
# pool の投票の由来と honest な投票者の投票の真正性(C71 の補題)

store の投票の pool に投票を入れるのは `onGoldfishVote` だけで(`Votes.lean`)、そこへ来る投票は 3 通りしかない:
配送された投票(`receiptProcess` の投票の腕)、受理したブロックが運ぶ投票(`onBlockUsing` の `foldl onGoldfishVoteChecked`。
運ばれる投票は名前付きブロックの `namedGfVotes`: `gfVotes (eraseBlock B) = namedGfVotes B`)、自分の tick の出力(提案したブロックが
運ぶ投票と自分の投票)。したがって run のどの添字の pool の投票も、そのノードが処理した(`Processes`)投票か、処理したブロックが運ぶ
投票である(`pool_from`)。`UnforgeableSignatures` の 2 つの連言(処理した object / 運ばれた object の honest な署名は署名者が実際に
出した)と合わせると、pool の honest な投票者の投票はその投票者の tick が出した投票(`pool_genuine`)で、`Voting.emits_gfVote_unique`
(投票者と slot ごとに 1 つ)から、どのノードの pool でも同じ honest な投票者・同じ slot の投票は 1 つに定まる(`pool_honest_unique`)。
これは `Delivery.deliver_gfVote_mem` の equivocation の仮定(`equivocates` が偽)に向けた層。

手書きでは `DecoupledConsensusProofs/Protocol/Handlers/Pool.lean` の `GfFrom`(pool の投票は元からあったか、処理した object の列の投票か、
その列のブロックが運ぶ投票。投票 1 つの場合が `gfFrom_on_goldfish_vote_checked`)がこの由来に当たり、`Attribution.lean`(store の attestation の真正性: `bodies_processed`)と
同じ運びで tick → node → run の順に積み上げる。
-/

namespace Proofs.Consensus.PoolFrom

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Votes Proofs.Consensus.Signing Proofs.Consensus.Carrier

/-! ## `Store` のハンドラ -/

/-- `onGoldfishVote st u` の後の pool の投票は、元からあるか `u`。 -/
theorem onGoldfishVote_from {st : Store} {u x : GoldfishVote} {k : Nat} (hx : x ∈ poolList (onGoldfishVote st u) k) :
    x ∈ poolList st k ∨ x = u := by
  rcases poolList_onGoldfishVote st u k with h | ⟨-, h⟩
  · rw [h] at hx; exact Or.inl hx
  · rw [h, List.mem_append, List.mem_singleton] at hx
    exact hx

theorem onGoldfishVoteChecked_from (c : Nat → NaruStd.Set ValidatorId) {st : Store} {u x : GoldfishVote} {k : Nat}
    (hx : x ∈ poolList (onGoldfishVoteChecked c st u) k) : x ∈ poolList st k ∨ x = u := by
  unfold onGoldfishVoteChecked at hx
  split_ifs at hx
  · exact Or.inl hx
  · exact onGoldfishVote_from hx

/-- 投票の列を `onGoldfishVoteChecked` で畳み込んだ後の pool の投票は、元からあるか列の要素。 -/
theorem foldl_onGoldfishVoteChecked_from (c : Nat → NaruStd.Set ValidatorId) {x : GoldfishVote} {k : Nat} :
    ∀ (l : List GoldfishVote) (st : Store),
      x ∈ poolList (List.foldl (fun acc u => onGoldfishVoteChecked c acc u) st l) k → x ∈ poolList st k ∨ x ∈ l
  | [], _, hx => Or.inl hx
  | u :: l, st, hx => by
    rw [List.foldl_cons] at hx
    rcases foldl_onGoldfishVoteChecked_from c l _ hx with hx | hx
    · rcases onGoldfishVoteChecked_from c hx with hx | rfl
      · exact Or.inl hx
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ hx)

/-- ブロックの受理 `onBlockUsing` の後の pool の投票は、元からあるかブロックが運ぶ投票(`gfVotes b`)。 -/
theorem onBlockUsing_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) {st : Store} {b : Block}
    {build : ChainState → ChainState} {x : GoldfishVote} {k : Nat} (hx : x ∈ poolList (onBlockUsing c p st b build) k) :
    x ∈ poolList st k ∨ x ∈ gfVotes b := by
  rcases Proofs.Consensus.Carrier.onBlockUsing_eq c p st b build with h | ⟨-, -, h⟩
  · rw [h] at hx; exact Or.inl hx
  · rw [h] at hx
    -- `acceptBody` = `updateFinality`(pool は不変)∘ `unpackedOf`(`storedOf` の後の投票の畳み込み)
    have hsame : ∀ post, poolList (acceptBody c st b post) k = poolList (unpackedOf c st b post) k := fun post => by
      unfold acceptBody updateFinality
      dsimp only
      split_ifs <;> rfl
    rw [hsame] at hx
    unfold unpackedOf at hx
    rcases foldl_onGoldfishVoteChecked_from c _ _ hx with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- 消去したブロックが運ぶ投票は名前付きブロックが運ぶ投票。 -/
theorem gfVotes_eraseBlock (B : NamedBlock) : gfVotes (eraseBlock B) = namedGfVotes B := by
  cases B <;> rfl

/-! ## `NamedStore` のハンドラ -/

theorem admitRow_poolList (hc : HealConfig) (st : NamedStore) (row : NamedAttestation) (k : Nat) :
    poolList (admitRow hc st row).core k = poolList st.core k := by
  unfold admitRow
  dsimp only
  split_ifs
  all_goals
    unfold onSgVote
    dsimp only
    split_ifs <;> rfl

theorem admitRows_poolList (hc : HealConfig) (k : Nat) :
    ∀ (rows : List NamedAttestation) (st : NamedStore), poolList (admitRows hc st rows).core k = poolList st.core k
  | [], _ => rfl
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_poolList hc k rows (admitRow hc st row)
    unfold admitRows at ih
    rw [ih, admitRow_poolList]

theorem admitCarried_poolList (adm : CarriedAdmission) (hc : HealConfig) (before after : NamedStore) (b : NamedBlock)
    (k : Nat) : poolList (admitCarried adm hc before after b).core k = poolList after.core k := by
  unfold admitCarried
  split_ifs
  · exact admitRows_poolList hc k _ after
  · rfl

/-- 名前付きブロック `B` の処理の後の pool の投票は、元からあるか `B` が運ぶ投票。 -/
theorem onBlockWith_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig) {st : NamedStore} {B : NamedBlock} {x : GoldfishVote} {k : Nat}
    (hx : x ∈ poolList (onBlockWith c p adm e hc cfg st B).core k) : x ∈ poolList st.core k ∨ x ∈ namedGfVotes B := by
  unfold onBlockWith at hx
  rw [admitCarried_poolList] at hx
  unfold processBlockCore at hx
  split_ifs at hx
  · exact Or.inl hx
  · dsimp only at hx
    rw [Proofs.Consensus.Stores.commitBlock_core] at hx
    rw [← gfVotes_eraseBlock]
    rcases Proofs.Consensus.Carrier.onBlockCheckedUsing_eq _ hc st.core (eraseBlock B) with h | h
    · rw [h] at hx
      exact onBlockUsing_from c p hx
    · rw [h] at hx
      exact Or.inl hx

/-- 受信した object の処理の後の pool の投票は、元からあるか、その投票か、そのブロックが運ぶ投票。 -/
theorem receiptProcess_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {st : NamedStore} {o : NamedObject} {x : GoldfishVote} {k : Nat}
    (hx : x ∈ poolList (receiptProcess c p s st o).core k) :
    x ∈ poolList st.core k ∨ o = NamedObject.GfVote x ∨ ∃ B, o = NamedObject.Block B ∧ x ∈ namedGfVotes B := by
  cases o with
  | Block b =>
    rcases onBlockWith_from c p CarriedAdmission.AlsoCarried s.e s.hc s.cfg hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨b, rfl, h⟩)
  | GfVote u =>
    rcases onGoldfishVoteChecked_from c (st := st.core) hx with h | rfl
    · exact Or.inl h
    · exact Or.inr (Or.inl rfl)
  | Attest row =>
    left
    have h : poolList (receiptProcess c p s st (NamedObject.Attest row)).core k = poolList st.core k :=
      admitRow_poolList s.hc st row k
    rw [h] at hx
    exact hx

/-! ## tick の務め -/

theorem proposeBlockWith_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} {x : GoldfishVote} {k : Nat}
    (hx : x ∈ poolList (proposeBlockWith c p nr cache e hc cfg nd st).1.core k) :
    x ∈ poolList st.core k ∨ ∃ B, (proposeBlockWith c p nr cache e hc cfg nd st).2 = some B ∧ x ∈ namedGfVotes B := by
  unfold proposeBlockWith at hx ⊢
  cases hm : proposalWith nr cache ProposalRowSource.PoolAndCarried e hc nd st with
  | none =>
    rw [hm] at hx
    exact Or.inl hx
  | some b =>
    rw [hm] at hx
    rcases onBlockWith_from c p CarriedAdmission.AlsoCarried e hc cfg hx with h | h
    · exact Or.inl h
    · exact Or.inr ⟨b, rfl, h⟩

theorem namedGoldfishVoteWith_from (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv)
    (hc : HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} {x : GoldfishVote} {k : Nat}
    (hx : x ∈ poolList (namedGoldfishVoteWith c cache e hc nd st).1.core k) :
    x ∈ poolList st.core k ∨ (namedGoldfishVoteWith c cache e hc nd st).2 = some x := by
  have h1 : (namedGoldfishVoteWith c cache e hc nd st).1.core = (goldfishVoteWith c cache e hc nd st.core).1 := by
    unfold namedGoldfishVoteWith; rfl
  have h2 : (namedGoldfishVoteWith c cache e hc nd st).2 = (goldfishVoteWith c cache e hc nd st.core).2 := by
    unfold namedGoldfishVoteWith; rfl
  rw [h1] at hx
  rw [h2]
  cases hv : (goldfishVoteWith c cache e hc nd st.core).2 with
  | none =>
    rw [(goldfishVoteWith_none c cache e hc nd st.core hv).1] at hx
    exact Or.inl hx
  | some u =>
    rw [(goldfishVoteWith_some c cache e hc nd st.core hv).2.2.2.2] at hx
    rcases onGoldfishVoteChecked_from c hx with h | rfl
    · exact Or.inl h
    · exact Or.inr rfl

theorem namedUpdateConfirmationWith_poolList (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : NamedStore)
    (s k : Nat) : poolList (namedUpdateConfirmationWith cache e hc st s).core k = poolList st.core k := rfl

theorem attestWith_poolList (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (k : Nat) :
    poolList (attestWith cache e hc nd st rec).1.core k = poolList st.core k := by
  unfold attestWith
  dsimp only
  exact admitRow_poolList hc st _ k

/-- 時計を合わせただけの store の pool は元の pool。 -/
theorem poolList_clocked (st : Store) (t : Int) (s' k : Nat) :
    poolList { st with t := t, s := s' } k = poolList st k := rfl

/-- 1 tick の後の pool の投票は、元からあるか、その tick が出力した投票か、その tick が出力したブロックが運ぶ投票。 -/
theorem tick_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) {x : GoldfishVote} {k : Nat}
    (hx : x ∈ poolList (tick c p a nr cache e hc cfg nd st rec t).1.core k) :
    x ∈ poolList st.core k ∨ NamedObject.GfVote x ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2 ∨
      ∃ B, NamedObject.Block B ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2 ∧ x ∈ namedGfVotes B := by
  unfold tick at hx ⊢
  dsimp only at hx ⊢
  split_ifs at hx ⊢
  all_goals
    (try simp only [attestWith_poolList, namedUpdateConfirmationWith_poolList] at hx)
  all_goals (try simp only [poolList_clocked] at hx)
  all_goals (with_reducible try exact Or.inl hx)
  all_goals first
    | (guard_hyp hx :~ x ∈ poolList (namedGoldfishVoteWith c cache e hc nd _).1.core k
       rcases namedGoldfishVoteWith_from c cache e hc nd hx with hx | hv
       · first
          | (guard_hyp hx :~ x ∈ poolList (proposeBlockWith c p nr cache e hc cfg nd _).1.core k
             rcases proposeBlockWith_from c p nr cache e hc cfg nd hx with hx | ⟨B, hB, hxB⟩
             · simp only [poolList_clocked] at hx
               exact Or.inl hx
             · refine Or.inr (Or.inr ⟨B, ?_, hxB⟩)
               rw [hB]
               simp only [List.mem_append, List.mem_cons, true_or])
          | (simp only [poolList_clocked] at hx
             exact Or.inl hx)
       · refine Or.inr (Or.inl ?_)
         rw [hv]
         simp only [List.mem_append, List.mem_cons, true_or, or_true])
    | (guard_hyp hx :~ x ∈ poolList (proposeBlockWith c p nr cache e hc cfg nd _).1.core k
       rcases proposeBlockWith_from c p nr cache e hc cfg nd hx with hx | ⟨B, hB, hxB⟩
       · simp only [poolList_clocked] at hx
         exact Or.inl hx
       · refine Or.inr (Or.inr ⟨B, ?_, hxB⟩)
         rw [hB]
         simp only [List.mem_append, List.mem_cons, true_or])

theorem nodeTick_from (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId) (n : NamedNodeState)
    (t : Int) {x : GoldfishVote} {k : Nat} (hx : x ∈ poolList (nodeTick c p a nr s v n t).1.st.core k) :
    x ∈ poolList n.st.core k ∨ NamedObject.GfVote x ∈ (nodeTick c p a nr s v n t).2 ∨
      ∃ B, NamedObject.Block B ∈ (nodeTick c p a nr s v n t).2 ∧ x ∈ namedGfVotes B := by
  unfold nodeTick profileTick at hx ⊢
  dsimp only at hx ⊢
  exact tick_from c p a nr _ s.e s.hc s.cfg _ n.st n.signing t hx

/-! ## run -/

/-- ブロックはそれが運ぶ投票を運ぶ(`Carries`)。 -/
theorem carries_gfVote {B : NamedBlock} {x : GoldfishVote} (hx : x ∈ namedGfVotes B) :
    Carries (NamedObject.Block B) (NamedObject.GfVote x) := by
  dsimp only [Carries]
  left
  rw [List.any_eq_true]
  exact ⟨x, hx, by simp⟩

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **pool の投票の由来**: `stateBefore i` のノード `u` の pool の投票は、`u` がある時刻に処理した(`Processes`)投票か、
`u` がある時刻に処理したブロックが運ぶ投票。 -/
theorem pool_from (u : ValidatorId) :
    ∀ (i k : Nat) (x : GoldfishVote), x ∈ poolList (worldAt (stateBefore c p a nr s rho i) u).st.core k →
      (∃ t, Processes c p a nr s rho u (NamedObject.GfVote x) t) ∨
        ∃ B t, Processes c p a nr s rho u (NamedObject.Block B) t ∧ x ∈ namedGfVotes B
  | 0, k, x, hx => by
    have h : poolList (worldAt worldInit u).st.core k = [] := initial_poolList k
    unfold stateBefore at hx
    simp only [List.take_zero, List.foldl_nil] at hx
    rw [h] at hx
    exact absurd hx List.not_mem_nil
  | i + 1, k, x, hx => by
    cases hev : rho.events[i]? with
    | none =>
      rw [stateBefore_succ_of_none c p a nr s rho hev] at hx
      exact pool_from u i k x hx
    | some ev =>
      rw [stateBefore_succ_of_get c p a nr s rho hev] at hx
      cases ev with
      | Tick w t =>
        unfold worldStep at hx
        dsimp only at hx
        by_cases hwu : w = u
        · subst hwu
          rw [worldAt_insert_self] at hx
          rcases nodeTick_from c p a nr s w _ t hx with h | h | ⟨B, hB, hxB⟩
          · exact pool_from w i k x h
          · exact Or.inl ⟨t, Or.inl ((emits_iff c p a nr s rho w _ t).mpr ⟨i, hev, h⟩)⟩
          · exact Or.inr ⟨B, t, Or.inl ((emits_iff c p a nr s rho w _ t).mpr ⟨i, hev, hB⟩), hxB⟩
        · rw [worldAt_insert_ne _ _ _ _ hwu] at hx
          exact pool_from u i k x hx
      | Deliver w o t =>
        unfold worldStep at hx
        dsimp only at hx
        by_cases hwu : w = u
        · subst hwu
          rw [worldAt_insert_self] at hx
          rcases receiptProcess_from c p s (st := (worldAt (stateBefore c p a nr s rho i) w).st) hx with
            h | rfl | ⟨B, rfl, hxB⟩
          · exact pool_from w i k x h
          · exact Or.inl ⟨t, Or.inr ⟨i, hev⟩⟩
          · exact Or.inr ⟨B, t, Or.inr ⟨i, hev⟩, hxB⟩
        · rw [worldAt_insert_ne _ _ _ _ hwu] at hx
          exact pool_from u i k x hx

/-- **pool の honest な投票者の投票は真正**: `UnforgeableSignatures` の下で、どのノードの pool の投票も、投票者が honest なら
その投票者の tick が実際に出した投票。 -/
theorem pool_genuine (hunf : UnforgeableSignatures c p a nr s rho) {u : ValidatorId} {i k : Nat} {x : GoldfishVote}
    (hx : x ∈ poolList (worldAt (stateBefore c p a nr s rho i) u).st.core k) (hh : rho.honest.contains x.valIndex = true) :
    ∃ t, Emits c p a nr s rho x.valIndex (NamedObject.GfVote x) t := by
  have hauth : author (NamedObject.GfVote x) = some x.valIndex := rfl
  rcases pool_from c p a nr s rho u i k x hx with ⟨t, hproc⟩ | ⟨B, t, hproc, hxB⟩
  · obtain ⟨t2, -, hem⟩ := hunf.1 u _ t hproc x.valIndex ⟨hh, hauth⟩
    exact ⟨t2, hem⟩
  · obtain ⟨t2, -, hem⟩ := hunf.2 u _ t hproc _ (carries_gfVote hxB) x.valIndex ⟨hh, hauth⟩
    exact ⟨t2, hem⟩

/-- **honest な投票者の投票は slot ごとに 1 つ**: `ScheduleWellFormed` と `UnforgeableSignatures` の下で、どのノード・どの添字の
pool の投票でも、同じ honest な投票者・同じ slot の 2 つの投票は等しい(`Voting.emits_gfVote_unique`)。 -/
theorem pool_honest_unique (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    {u₁ u₂ : ValidatorId} {i₁ i₂ k₁ k₂ : Nat} {x₁ x₂ : GoldfishVote}
    (hx₁ : x₁ ∈ poolList (worldAt (stateBefore c p a nr s rho i₁) u₁).st.core k₁)
    (hx₂ : x₂ ∈ poolList (worldAt (stateBefore c p a nr s rho i₂) u₂).st.core k₂)
    (hh : rho.honest.contains x₁.valIndex = true) (hv : x₁.valIndex = x₂.valIndex) (hslot : x₁.slot = x₂.slot) :
    x₁ = x₂ := by
  obtain ⟨t₁, he₁⟩ := pool_genuine c p a nr s rho hunf hx₁ hh
  obtain ⟨t₂, he₂⟩ := pool_genuine c p a nr s rho hunf hx₂ (hv ▸ hh)
  rw [← hv] at he₂
  exact Proofs.Consensus.Voting.emits_gfVote_unique c p a nr s rho hsch he₁ he₂ hslot

end Run

end Proofs.Consensus.PoolFrom
