import Proofs.Consensus.OwnVote
import Mathlib.Tactic

/-!
# ブロックが運ぶ投票は受理したノードの pool に入る(C71 の補題)

`Delivery.handlesAt_gfVote_cases` の経路 (3): 添字 `j` のブロックの処理(`BlockCall`: `w` への配送か `w` 自身の提案)が、
投票 `u` を運ぶブロック `b` を新しく `w` の tree に入れる。

ブロックの受理 `onBlockUsing` は、新しいブロックを tree に入れるときだけ受理の分岐(`Carrier.acceptBody`)を通り、そこで
`b` の運ぶ投票を `foldl onGoldfishVoteChecked` で順に pool に入れる(`Carrier.unpackedOf`)。畳み込みの途中の store は
時計が元のまま(`Clocks.onGoldfishVoteChecked_clock`)なので受信者の窓 `InWindow` は受理の直前の store と同じで、途中の pool は
最終の pool の部分集合(`Votes.foldl_poolExt`)なので、最終の pool で投票者の投票が 1 つ以下(`UniqueIn`)なら途中の
equivocation の守りも通る(`equivocates_false_of_unique`)。したがって窓と committee と最終の pool の一意性の下で、運ばれた `u` は
受理の後の pool にある(`foldl_mem` / `onBlockUsing_mem`)。名前付きの処理 `processBlockCore` では、tree に新しく入ったなら
core は `onBlockUsing` の結果そのもの(`processBlockCore_core_of_new`)。

run では、GST 以後に honest な `v` が時刻 `t` に発行した投票 `u` を、honest な `w` が `t ≤ t2 < max t tGST + Δ` の時刻 `t2` に
経路 (3) で扱うとき:
- 配送の場合: 受信の直前の `w` の slot はちょうど `u.slot`(`Window.slot_ge_of_deliver` / `slot_le_of_deliver`。配送する object に
  依らない)、配送の後の pool は `postCore` の pool と同じ(`admitCarried` は pool を変えない)、配送の後の pool で honest な `v` の
  投票は 1 つ以下(`stateBefore_uniqueIn`。`PoolFrom.pool_honest_unique` から)。したがって `stateBefore (j + 1)` の `w` の pool に `u` がある。
- 自分の提案の場合: tick がブロックを出すのは提案の時刻だけ(`tick_block_time`)だが、`t2` は `u.slot` の投票の時刻以後・次の slot の
  提案の時刻より前なので提案の時刻ではない(`ne_proposalTime_of_vote_window`)。この場合は起こらない。
これで経路 (1)(2)(3) がすべて閉じ、GST 以後の honest な投票を honest な `w` が発行の時刻以後・締切より前に扱えば、
`stateBefore (j + 1)` の `w` の鍵 `u.slot` の pool に投票がある(`handlesAt_honest_gfVote_mem`)。`Delivery.partialSynchrony_gfVote` と
合わせると、締切が horizon 以内なら、honest な各ノード `w` について締切より前の `w` ごとのある添字の後で `w` の pool にある
(`partialSynchrony_honest_gfVote_mem`。全ノードに共通の添字はまだ示していない)。

手書きでは `onBlock` の運んだ投票の畳み込みに `on_goldfish_vote_insert`(`DecoupledConsensusProofs/Protocol/Handlers/Pool.lean`)を
当てる運びに当たる。
-/

namespace Proofs.Consensus.Carried

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Votes Proofs.Consensus.Carrier

/-! ## 投票者の投票の一意性 -/

/-- 鍵 `k` の pool で投票者 `v` の投票は 1 つ以下。 -/
def UniqueIn (st : Store) (k : Nat) (v : ValidatorId) : Prop :=
  ∀ x y, x ∈ poolList st k → y ∈ poolList st k → x.valIndex = v → y.valIndex = v → x = y

/-- 一意性は pool の部分集合へ移る。 -/
theorem UniqueIn.mono {a b : Store} {k : Nat} {v : ValidatorId} (h : UniqueIn b k v)
    (hsub : ∀ x, x ∈ poolList a k → x ∈ poolList b k) : UniqueIn a k v :=
  fun x y hx hy => h x y (hsub x hx) (hsub y hy)

/-- **一意なら equivocate しない**: pool の集合は整列していて重複が無いので、`votesBy` の大きさは 1 以下。 -/
theorem equivocates_false_of_unique {st : Store} {k : Nat} {v : ValidatorId} (h : UniqueIn st k v) :
    equivocates (storePool st k) v = false := by
  unfold equivocates
  rw [decide_eq_false_iff_not]
  intro h2
  have hnd : (votesBy (storePool st k) v).elems.Nodup := by
    unfold votesBy
    exact Proofs.Consensus.Majority.SortedLt.nodup Proofs.Consensus.Majority.gv_irrefl
      (Proofs.Consensus.Majority.SortedLt.filter (Proofs.Consensus.Majority.storePool_sortedLt _ k) _)
  have hle : (votesBy (storePool st k) v).elems.length ≤ 1 := by
    apply Proofs.Consensus.Majority.length_le_one_of_nodup hnd
    intro x hx y hy
    rw [Proofs.Consensus.Goldfish.mem_votesBy_iff] at hx hy
    exact h x y ((mem_storePool_iff _ _ _).mp hx.1) ((mem_storePool_iff _ _ _).mp hy.1) hx.2 hy.2
  unfold NaruStd.Set.size at h2
  omega

/-! ## ブロックの受理 -/

/-- **運ばれた投票の畳み込み**: 列 `l` の投票 `u` は、committee の要素で、畳み込みの前の store の窓の中にあり、
畳み込みの後の pool で投票者の投票が 1 つ以下なら、畳み込みの後の pool にある。 -/
theorem foldl_mem (c : Nat → NaruStd.Set ValidatorId) {u : GoldfishVote} (hwf : voteWellFormed c u = true) :
    ∀ (l : List GoldfishVote) (st : Store), u ∈ l → Proofs.Consensus.Delivery.InWindow st u →
      UniqueIn (List.foldl (fun acc x => onGoldfishVoteChecked c acc x) st l) u.slot u.valIndex →
      u ∈ poolList (List.foldl (fun acc x => onGoldfishVoteChecked c acc x) st l) u.slot
  | [], _, hu, _, _ => by simp at hu
  | x :: l, st, hu, hw, huniq => by
    rw [List.foldl_cons] at huniq ⊢
    rcases List.mem_cons.mp hu with hux | hu
    · subst hux
      have hext := foldl_poolExt (c := c) (fun acc x => onGoldfishVoteChecked c acc x)
        (fun s x => onGoldfishVoteChecked_poolExt c s x) l (onGoldfishVoteChecked c st u)
      have hsub : ∀ y, y ∈ poolList st u.slot →
          y ∈ poolList (List.foldl (fun acc x => onGoldfishVoteChecked c acc x) (onGoldfishVoteChecked c st u) l) u.slot :=
        fun y hy => hext.mono _ _ ((onGoldfishVoteChecked_poolExt c st u).mono _ _ hy)
      exact hext.mono _ _ (Proofs.Consensus.Delivery.mem_onGoldfishVoteChecked c st u hwf hw
        (equivocates_false_of_unique (huniq.mono hsub)))
    · have hcl := Proofs.Consensus.Clocks.onGoldfishVoteChecked_clock c st x
      have hw' : Proofs.Consensus.Delivery.InWindow (onGoldfishVoteChecked c st x) u := by
        unfold Proofs.Consensus.Delivery.InWindow
        rw [hcl.s]
        exact hw
      exact foldl_mem c hwf l _ hu hw' huniq

/-- **新しく受理したブロックの運ぶ投票は受理の後の pool にある**: `b` が受理の前の tree に無く後の tree にあるなら
受理の分岐を通ったので、運ばれた `u` は(committee・窓・受理の後の pool の一意性の下で)受理の後の pool にある。 -/
theorem onBlockUsing_mem (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) {st : Store} {b : Block}
    {build : Model.Consensus.Protocol.ChainState.ChainState → Model.Consensus.Protocol.ChainState.ChainState}
    {u : GoldfishVote} (hnew : ¬ (st.tree.contains b = true))
    (hin : (onBlockUsing c p st b build).tree.contains b = true) (hu : u ∈ gfVotes b)
    (hwf : voteWellFormed c u = true) (hw : Proofs.Consensus.Delivery.InWindow st u)
    (huniq : UniqueIn (onBlockUsing c p st b build) u.slot u.valIndex) :
    u ∈ poolList (onBlockUsing c p st b build) u.slot := by
  rcases onBlockUsing_eq c p st b build with h | ⟨-, -, h⟩
  · rw [h] at hin
    exact absurd hin hnew
  · rw [h] at huniq ⊢
    have hsame : ∀ post, poolList (acceptBody c st b post) u.slot = poolList (unpackedOf c st b post) u.slot :=
      fun post => by
        unfold acceptBody updateFinality
        dsimp only
        split_ifs <;> rfl
    rw [hsame]
    have huniq' := huniq.mono (a := unpackedOf c st b _) (fun x hx => by rw [hsame]; exact hx)
    unfold unpackedOf at huniq' ⊢
    exact foldl_mem c hwf _ _ hu hw huniq'

/-- 名前付きのブロックの処理で `b` が tree に新しく入ったなら、core は `onBlockUsing` の結果。 -/
theorem processBlockCore_core_of_new (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) {st : NamedStore} {b : NamedBlock}
    (hnew : ¬ (st.core.tree.contains (eraseBlock b) = true))
    (hin : (processBlockCore c p e hc cfg st b).core.tree.contains (eraseBlock b) = true) :
    ∃ build, (processBlockCore c p e hc cfg st b).core = onBlockUsing c p st.core (eraseBlock b) build := by
  revert hin
  unfold processBlockCore
  split_ifs
  · intro hin
    exact absurd hin hnew
  · dsimp only
    rw [Proofs.Consensus.Stores.commitBlock_core]
    rcases onBlockCheckedUsing_eq _ hc st.core (eraseBlock b) with h | h
    · rw [h]
      intro _
      exact ⟨_, rfl⟩
    · rw [h]
      intro hin
      exact absurd hin hnew

/-- 名前付きのブロックの処理でも同じ: 新しく入った `b` の運ぶ投票は処理の後の pool にある。 -/
theorem processBlockCore_mem (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) {st : NamedStore} {b : NamedBlock}
    {u : GoldfishVote} (hnew : ¬ (st.core.tree.contains (eraseBlock b) = true))
    (hin : (processBlockCore c p e hc cfg st b).core.tree.contains (eraseBlock b) = true) (hu : u ∈ namedGfVotes b)
    (hwf : voteWellFormed c u = true) (hw : Proofs.Consensus.Delivery.InWindow st.core u)
    (huniq : UniqueIn (processBlockCore c p e hc cfg st b).core u.slot u.valIndex) :
    u ∈ poolList (processBlockCore c p e hc cfg st b).core u.slot := by
  obtain ⟨build, h⟩ := processBlockCore_core_of_new c p e hc cfg hnew hin
  rw [h] at hin huniq ⊢
  rw [← Proofs.Consensus.PoolFrom.gfVotes_eraseBlock] at hu
  exact onBlockUsing_mem c p hnew hin hu hwf hw huniq

/-! ## tick がブロックを出す時刻 -/

section Tick

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
  (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Node) (st : NamedStore)
  (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int)

/-- **tick がブロックを出すのは提案の時刻だけ**: 提案の務めが走るのは `t = proposalTime e (slotOf e t)` のとき。 -/
theorem tick_block_time {D : NamedBlock} (h : NamedObject.Block D ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2) :
    t = proposalTime e (slotOf e t) := by
  unfold tick at h
  dsimp only at h
  split_ifs at h
  all_goals simp only [List.mem_append] at h
  all_goals repeat' (obtain h | h := (h : _ ∨ _))
  all_goals first
    | (have hp : ((decide (0 < slotOf e t) && t == proposalTime e (slotOf e t)) && (p (slotOf e t) == nd.valIndex)) = true := by
          assumption
       simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
       exact hp.1.2)
    | (simp at h)
    | (revert h; split <;> intro h <;> simp at h)

end Tick

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- ノードの tick(`nodeTick`)でも同じ。 -/
theorem nodeTick_block_time (v : ValidatorId) (n : NamedNodeState) (t : Int) {D : NamedBlock}
    (h : NamedObject.Block D ∈ (nodeTick c p a nr s v n t).2) : t = proposalTime s.e (slotOf s.e t) := by
  rw [Proofs.Consensus.Signing.nodeTick_out] at h
  exact tick_block_time c p a nr _ s.e s.hc s.cfg _ n.st n.signing t h

/-- **投票の時刻以後・次の slot の提案の時刻より前は提案の時刻ではない**(Δ > 0)。 -/
theorem ne_proposalTime_of_vote_window (hδ : 0 < s.e.delta) {k : Nat} {t2 : Int} (hlo : voteTime s.e k ≤ t2)
    (hhi : t2 < proposalTime s.e (k + 1)) : t2 ≠ proposalTime s.e (slotOf s.e t2) := by
  rw [Proofs.Consensus.Window.voteTime_eq] at hlo
  have h0 := Proofs.Consensus.Window.proposalTime_nonneg s.e hδ.le k
  have hk : slotOf s.e t2 = k := le_antisymm
    (Proofs.Consensus.Window.slotOf_le_of_lt s.e hδ (by linarith) hhi)
    (Proofs.Consensus.Window.le_slotOf_of_le s.e hδ (by linarith))
  rw [hk]
  intro h
  linarith

/-- 配送の後の pool は `postCore` の pool(`admitCarried` は pool を変えない)。 -/
theorem nodeProcess_block_poolList (n : NamedNodeState) (b : NamedBlock) (k : Nat) :
    poolList (nodeProcess c p s n (NamedObject.Block b)).st.core k = poolList (postCore c p s n.st b).core k :=
  Proofs.Consensus.PoolFrom.admitCarried_poolList CarriedAdmission.AlsoCarried s.hc n.st _ b k

/-- run の pool で honest な投票者の投票は 1 つ以下(`PoolFrom.pool_honest_unique`)。 -/
theorem stateBefore_uniqueIn (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (i : Nat) (w : ValidatorId) (k : Nat) {v : ValidatorId} (hv : rho.honest.contains v = true) :
    UniqueIn (worldAt (stateBefore c p a nr s rho i) w).st.core k v := by
  intro x y hx hy hxv hyv
  have hinv := stateBefore_pool c p a nr s rho i w
  exact Proofs.Consensus.PoolFrom.pool_honest_unique c p a nr s rho hsch hunf hx hy (by rw [hxv]; exact hv)
    (hxv.trans hyv.symm) ((hinv k x hx).1.trans (hinv k y hy).1.symm)

/-- **経路 (3): ブロックが運ぶ GST 以後の honest な投票は pool に入る**: `ScheduleWellFormed` / `UnforgeableSignatures` /
Δ > 0 の下で、honest な `v` が GST 以後の時刻 `t` に発行した投票 `u` を運ぶブロック `b` を、honest な `w` の添字 `j` の
event(時刻 `t2`、`t ≤ t2 < max t tGST + Δ`)のブロックの処理が新しく tree に入れるなら、`stateBefore (j + 1)` の `w` の
鍵 `u.slot` の pool に `u` がある。 -/
theorem carried_honest_gfVote_mem (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {u : GoldfishVote} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t) (hv : rho.honest.contains v = true)
    (hgst : s.e.tGST ≤ t) (hw : rho.honest.contains w = true) {j : Nat} {ev : NamedEvent}
    (hev : rho.events[j]? = some ev) (hn : eventNode ev = w) (hte : eventTime ev = t2)
    {b : NamedBlock} {k : Nat} {before : NamedStore}
    (hbc : BlockCall c p a nr s (worldAt (stateBefore c p a nr s rho j) w) ev b before)
    (hnew : ¬ (before.core.tree.contains (eraseBlock b) = true))
    (hin : (postCore c p s before b).core.tree.contains (eraseBlock b) = true)
    (hk : (namedGfVotes b)[k]? = some u) (ht : t ≤ t2) (ht2 : t2 < max t s.e.tGST + s.e.delta) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot := by
  have hu : u ∈ namedGfVotes b := List.mem_of_getElem? hk
  have hwf := Proofs.Consensus.Equivocation.voteWellFormed_of_emits c p a nr s rho hem
  obtain ⟨-, htv, hvi, hsl, -⟩ := Proofs.Consensus.Voting.emits_gfVote_shape c p a nr s rho hem
  rw [← hsl] at htv
  rw [max_eq_left hgst] at ht2
  have htv' := htv
  rw [Proofs.Consensus.Window.voteTime_eq] at htv'
  have hsucc := Proofs.Consensus.Window.proposalTime_succ s.e u.slot
  have huniq := stateBefore_uniqueIn c p a nr s rho hsch hunf (j + 1) w u.slot (v := u.valIndex) (by rw [hvi]; exact hv)
  rcases hbc with ⟨t', hevd, hbef⟩ | ⟨t', ⟨hevt, hcont⟩, -⟩
  · rw [hn] at hevd
    subst hevd hbef
    simp only [eventTime] at hte
    subst hte
    have hwin : Proofs.Consensus.Delivery.InWindow (worldAt (stateBefore c p a nr s rho j) w).st.core u :=
      ⟨Proofs.Consensus.Window.slot_ge_of_deliver c p a nr s rho hsch hδ hw hev (k := u.slot) (by linarith),
        le_trans (Proofs.Consensus.Window.slot_le_of_deliver c p a nr s rho hsch hδ hev (k := u.slot) (by linarith))
          (Nat.le_succ _)⟩
    rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev] at huniq ⊢
    unfold worldStep at huniq ⊢
    dsimp only at huniq ⊢
    rw [Proofs.Consensus.Signing.worldAt_insert_self] at huniq ⊢
    rw [nodeProcess_block_poolList]
    have huniq' := huniq.mono (a := (postCore c p s (worldAt (stateBefore c p a nr s rho j) w).st b).core)
      (fun x hx => by rw [nodeProcess_block_poolList]; exact hx)
    exact processBlockCore_mem c p s.e s.hc s.cfg hnew hin hu hwf hwin huniq'
  · exfalso
    rw [hn] at hevt hcont
    subst hevt
    simp only [eventTime] at hte
    subst hte
    unfold Model.Consensus.Spec.Execution.tickEmits at hcont
    rw [List.contains_iff_mem] at hcont
    have hpt := nodeTick_block_time c p a nr s w _ t' hcont
    exact ne_proposalTime_of_vote_window s hδ (k := u.slot) (by linarith) (by linarith) hpt

/-- **GST 以後の honest な投票の扱いは pool に届く**: `handlesAt_honest_gfVote_mem_or_carried` の経路 (3) を
`carried_honest_gfVote_mem` で閉じた形。honest な `v` が GST 以後の時刻 `t` に発行した投票 `u` を honest な `w` が添字 `j`
(時刻 `t2`、`t ≤ t2 < max t tGST + Δ`)で扱えば、`stateBefore (j + 1)` の `w` の鍵 `u.slot` の pool に `u` がある。 -/
theorem handlesAt_honest_gfVote_mem (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (hδ : 0 < s.e.delta) {v w : ValidatorId} {u : GoldfishVote} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t) (hv : rho.honest.contains v = true)
    (hgst : s.e.tGST ≤ t) (hw : rho.honest.contains w = true) {j : Nat}
    (hh : HandlesAt c p a nr s rho j w (NamedObject.GfVote u) t2)
    (ht : t ≤ t2) (ht2 : t2 < max t s.e.tGST + s.e.delta) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot := by
  rcases Proofs.Consensus.OwnVote.handlesAt_honest_gfVote_mem_or_carried c p a nr s rho hsch hunf hδ hem hv hgst hw hh
    ht ht2 with h | ⟨ev, hev, hn, hte, b, k, before, ⟨⟨hbc, hnew⟩, hin⟩, hk⟩
  · exact h
  · exact carried_honest_gfVote_mem c p a nr s rho hsch hunf hδ hem hv hgst hw hev hn hte hbc hnew hin hk ht ht2

/-- **GST 以後の honest な投票は締切より前に honest な各ノードの pool に届く**(添字はノードごと): `PartialSynchrony` / `ScheduleWellFormed` /
`UnforgeableSignatures` / Δ > 0 の下で、honest な `v` が GST 以後の時刻 `t` に発行した投票 `u` は、締切 `max t tGST + Δ` が
horizon 以内なら、honest な `w` について時刻 `t2`(`t ≤ t2 < 締切`)のある添字 `j` があり、`j` より後のどの添字でも `w` の
鍵 `u.slot` の pool にある。 -/
theorem partialSynchrony_honest_gfVote_mem (hps : PartialSynchrony c p a nr s rho) (hsch : ScheduleWellFormed s rho)
    (hunf : UnforgeableSignatures c p a nr s rho) (hδ : 0 < s.e.delta) {v w : ValidatorId} {u : GoldfishVote} {t : Int}
    (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t) (hv : rho.honest.contains v = true)
    (hgst : s.e.tGST ≤ t) (hw : rho.honest.contains w = true) (hd : max t s.e.tGST + s.e.delta ≤ rho.horizon) :
    ∃ t2 j, (t ≤ t2 ∧ t2 < max t s.e.tGST + s.e.delta) ∧ HandlesAt c p a nr s rho j w (NamedObject.GfVote u) t2 ∧
      ∀ i, j < i → u ∈ poolList (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot := by
  obtain ⟨t2, ⟨ht, ht2⟩, j, hh⟩ := Proofs.Consensus.Delivery.partialSynchrony_gfVote c p a nr s rho hps hv hem hw hd
  exact ⟨t2, j, ⟨ht, ht2⟩, hh, fun i hji => Proofs.Consensus.Delivery.gfVote_mem_of_le c p a nr s rho hji
    (handlesAt_honest_gfVote_mem c p a nr s rho hsch hunf hδ hem hv hgst hw hh ht ht2)⟩

end Run

end Proofs.Consensus.Carried
