import Model.Consensus.Execution.Run
import Proofs.Consensus.Carrier
import Proofs.Consensus.Stores
import Proofs.Consensus.Signing
import Proofs.Consensus.RecordGrowth
import Mathlib.Tactic

/-!
# Goldfish の投票の pool は committee の投票だけを持ち、増えるだけ(C71 の liveness 系 claim の足場)

store の投票の pool `storePool st k`(`Model/Consensus/Protocol/Store.lean`: `gfVotes` の鍵 `k` のリストの集合)に投票を入れるのは
`onGoldfishVote`(`Model/Consensus/Protocol/Handlers.lean`)だけで、そこへは必ず `onGoldfishVoteChecked`(`vote.valIndex ∈ committee' vote.slot`
の守り)を通って来る(ブロックの受理 `onBlockUsing` が運ぶ投票の `foldl`、配送された投票 `receiptProcess`、自分の投票 `goldfishVoteWith`)。
`onGoldfishVote` は投票を鍵 `vote.slot` のリストの末尾に足し、他の鍵は変えない。したがって
- **pool の不変条件** `PoolInv committee' st`: 鍵 `k` の pool の投票は slot が `k` で、投票者は `committee' k` の要素(`Admissible`)。
- **pool の拡張** `PoolExt committee' a b`: `a` の pool の投票は `b` にも残り、`b` に増えた投票は適格。
どのハンドラも `PoolExt` を満たし(投票を触らないハンドラは `PoolExt.of_same`)、`PoolExt` は不変条件を運ぶ(`PoolInv.of_poolExt`)。初期 store の
pool は空なので、run のどの読み(`storeAt` / `stateBefore`)の store でも前提なしに成り立つ(`storeAt_pool` / `stateBefore_pool`)。
さらに `EventsSorted` の下で、同じノードの pool は時刻について増えるだけ(`storeAt_poolExt`)。
自分の投票 `goldfishVoteWith` の形(`goldfishVoteWith_some`): 投票者は自分、slot は store の `s`、head は `getHeadInTreeWith` の結果の root で、
投票は `onGoldfishVoteChecked` で自分の store に入る。

これは `Majority.lean`(過半の支持に honest な投票者が含まれること)の「支持者・参加者は committee の要素」の根拠。手書きでは Model の
`on_goldfish_vote_checked`(`DecoupledConsensusModel/Protocol/Handlers.lean`)が `vote.val_index ∉ E.committee vote.slot` の投票を退け、
`DecoupledConsensusProofs/Protocol/Handlers/Pool.lean` の `PoolStep`(pool は増えるだけ: `poolStep_on_goldfish_vote_checked` /
`poolStep_foldl_on_goldfish_vote_checked`)と `GfFrom`(新しい投票は配送された投票か運ばれた投票: `gfFrom_on_goldfish_vote_checked`)が
この `PoolExt` に当たる(手書きの数え上げ側は committee の所属を前提 `VoteSetValid`(`ModelVocabulary/Goldfish/ForkChoice.lean`:
`u.slot = s ∧ u.val_index ∈ E.committee s`。`PoolInv` の 1 つの鍵の分と同じ形)として受け取り、pool の不変条件としては置かない)。
`Carrier.lean`(`StoreInv`)/ `RecordOrder.lean`(`StableBelowConfirmed`)と同じ運びで `Store` → `NamedStore` →
`nodeTick` / `nodeProcess` → world → `readAt` / `stateBefore` の順に積み上げる。
-/

namespace Proofs.Consensus.Votes

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Grades Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.Tables Proofs.Consensus.Carrier Proofs.Consensus.Runs

/-! ## pool のリストと適格な投票 -/

/-- slot `k` の pool のリスト(`storePool st k` の元のリスト)。 -/
def poolList (st : Store) (k : Nat) : List GoldfishVote := NaruStd.Table.getOr st.gfVotes k []

theorem mem_storePool_iff (st : Store) (k : Nat) (u : GoldfishVote) :
    u ∈ (storePool st k).elems ↔ u ∈ poolList st k := by
  unfold storePool poolList
  exact mem_toSet_iff gv_compare_eq_iff _ _

/-- 鍵 `k` の pool に入ってよい投票: slot が `k` で、投票者が `committee' k` の要素。 -/
def Admissible (c : Nat → NaruStd.Set ValidatorId) (k : Nat) (u : GoldfishVote) : Prop :=
  u.slot = k ∧ (c u.slot).contains u.valIndex = true

/-- pool の不変条件: どの鍵の pool のどの投票も適格。 -/
def PoolInv (c : Nat → NaruStd.Set ValidatorId) (st : Store) : Prop :=
  ∀ k u, u ∈ poolList st k → Admissible c k u

/-- pool の拡張: `a` の pool の投票は `b` にも残り(`mono`)、`b` の pool の投票は `a` にもあったか適格(`new`)。 -/
structure PoolExt (c : Nat → NaruStd.Set ValidatorId) (a b : Store) : Prop where
  mono : ∀ k u, u ∈ poolList a k → u ∈ poolList b k
  new : ∀ k u, u ∈ poolList b k → u ∈ poolList a k ∨ Admissible c k u

theorem PoolExt.refl (c : Nat → NaruStd.Set ValidatorId) (a : Store) : PoolExt c a a :=
  ⟨fun _ _ h => h, fun _ _ h => Or.inl h⟩

theorem PoolExt.trans {c : Nat → NaruStd.Set ValidatorId} {a b d : Store} (h1 : PoolExt c a b) (h2 : PoolExt c b d) :
    PoolExt c a d :=
  ⟨fun k u h => h2.mono k u (h1.mono k u h), fun k u h => by
    rcases h2.new k u h with h | h
    · exact h1.new k u h
    · exact Or.inr h⟩

/-- `gfVotes` が等しい store の間は拡張(何も増えない)。 -/
theorem PoolExt.of_same (c : Nat → NaruStd.Set ValidatorId) {a b : Store} (h : b.gfVotes = a.gfVotes) : PoolExt c a b := by
  have hp : ∀ k, poolList b k = poolList a k := fun k => by unfold poolList; rw [h]
  exact ⟨fun k u hu => by rw [hp]; exact hu, fun k u hu => Or.inl (by rw [← hp]; exact hu)⟩

theorem PoolExt.of_eq (c : Nat → NaruStd.Set ValidatorId) {a b : Store} (h : b = a) : PoolExt c a b := by
  subst h
  exact PoolExt.refl c _

/-- 拡張は不変条件を運ぶ。 -/
theorem PoolInv.of_poolExt {c : Nat → NaruStd.Set ValidatorId} {a b : Store} (h : PoolInv c a) (he : PoolExt c a b) :
    PoolInv c b := fun k u hu => by
  rcases he.new k u hu with h' | h'
  · exact h k u h'
  · exact h'

/-- 不変条件の下では、pool の投票の slot は鍵で、投票者は committee の要素。 -/
theorem PoolInv.mem {c : Nat → NaruStd.Set ValidatorId} {st : Store} (h : PoolInv c st) {k : Nat} {u : GoldfishVote}
    (hu : u ∈ (storePool st k).elems) : u.slot = k ∧ u.valIndex ∈ (c k).elems := by
  obtain ⟨hs, hc⟩ := h k u ((mem_storePool_iff st k u).mp hu)
  refine ⟨hs, ?_⟩
  rw [hs] at hc
  exact (contains_iff_mem vid_eq _ _).mp hc

/-- 初期 store の pool は空。 -/
theorem initial_poolList (k : Nat) : poolList initStore k = [] := rfl

theorem initial_pool (c : Nat → NaruStd.Set ValidatorId) : PoolInv c initStore := fun k u hu => by
  rw [initial_poolList] at hu
  exact absurd hu (List.not_mem_nil)

/-! ## `onGoldfishVote` / `onGoldfishVoteChecked` -/

/-- `onGoldfishVote st u` は pool を変えないか、鍵 `u.slot` のリストの末尾に `u` を足すだけ。 -/
theorem poolList_onGoldfishVote (st : Store) (u : GoldfishVote) (k : Nat) :
    poolList (onGoldfishVote st u) k = poolList st k ∨
      (k = u.slot ∧ poolList (onGoldfishVote st u) k = poolList st k ++ [u]) := by
  unfold onGoldfishVote
  split_ifs
  · exact Or.inl rfl
  · exact Or.inl rfl
  · by_cases hk : k = u.slot
    · right
      refine ⟨hk, ?_⟩
      unfold poolList
      rw [hk]
      show NaruStd.Table.getOr (st.gfVotes.insert u.slot (NaruStd.Table.getOr st.gfVotes u.slot [] ++ [u])) u.slot [] = _
      rw [getOr_insert_self Proofs.Consensus.Records.nat_compare_eq_iff]
    · left
      unfold poolList
      show NaruStd.Table.getOr (st.gfVotes.insert u.slot (NaruStd.Table.getOr st.gfVotes u.slot [] ++ [u])) k [] = _
      exact getOr_insert_ne Proofs.Consensus.Records.nat_compare_eq_iff _ _ _ _ _ (Ne.symm hk)

/-- 受理した投票が `onGoldfishVote` の後の pool にある。 -/
theorem onGoldfishVote_poolExt (c : Nat → NaruStd.Set ValidatorId) (st : Store) {u : GoldfishVote}
    (hu : (c u.slot).contains u.valIndex = true) : PoolExt c st (onGoldfishVote st u) := by
  refine ⟨fun k w hw => ?_, fun k w hw => ?_⟩
  · rcases poolList_onGoldfishVote st u k with h | ⟨-, h⟩
    · rw [h]; exact hw
    · rw [h]; exact List.mem_append_left _ hw
  · rcases poolList_onGoldfishVote st u k with h | ⟨hk, h⟩
    · rw [h] at hw; exact Or.inl hw
    · rw [h, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl hw
      · exact Or.inr ⟨hk.symm, hu⟩

/-- `onGoldfishVoteChecked` は守り `vote.valIndex ∈ committee' vote.slot` を通った投票だけを入れる。 -/
theorem onGoldfishVoteChecked_poolExt (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    PoolExt c st (onGoldfishVoteChecked c st u) := by
  unfold onGoldfishVoteChecked
  split_ifs with h
  · exact PoolExt.refl c _
  · apply onGoldfishVote_poolExt c st
    cases hc : (c u.slot).contains u.valIndex with
    | true => rfl
    | false => exact absurd (by simp [hc]) h

theorem foldl_poolExt {c : Nat → NaruStd.Set ValidatorId} {β : Type} (g : Store → β → Store)
    (hg : ∀ s x, PoolExt c s (g s x)) : ∀ (l : List β) (s : Store), PoolExt c s (List.foldl g s l)
  | [], _ => PoolExt.refl c _
  | x :: l, s => by
    rw [List.foldl_cons]
    exact (hg s x).trans (foldl_poolExt g hg l (g s x))

/-! ## 投票を触らない `Store` のハンドラ -/

theorem onSgVote_poolExt (c : Nat → NaruStd.Set ValidatorId) (hc : HealConfig) (st : Store) (a : CombinedAttestation) :
    PoolExt c st (onSgVote hc st a) := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact PoolExt.of_same c rfl

theorem updateFinality_poolExt (c : Nat → NaruStd.Set ValidatorId) (st : Store) (σ : ChainState) :
    PoolExt c st (updateFinality st σ) := by
  unfold updateFinality
  dsimp only
  split_ifs <;> exact PoolExt.of_same c rfl

theorem updateConfirmationWith_poolExt (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (st : Store) (k : Nat) : PoolExt c st (updateConfirmationWith cache e hc st k) :=
  PoolExt.of_same c rfl

theorem goldfishVoteWith_poolExt (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : Store) : PoolExt c st (goldfishVoteWith c cache e hc nd st).1 := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_poolExt c st _
  · exact PoolExt.refl c _

/-! ## ブロックの受理 -/

theorem storedOf_poolExt (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    PoolExt c st (storedOf st b post) :=
  PoolExt.of_same c rfl

theorem unpackedOf_poolExt (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    PoolExt c st (unpackedOf c st b post) :=
  (storedOf_poolExt c st b post).trans (foldl_poolExt _ (fun s u => onGoldfishVoteChecked_poolExt c s u) _ _)

theorem acceptBody_poolExt (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    PoolExt c st (acceptBody c st b post) :=
  (unpackedOf_poolExt c st b post).trans (updateFinality_poolExt c _ _)

/-- ブロックの受理 `onBlockUsing` は、運ばれた投票を `onGoldfishVoteChecked` で入れるだけ(`onBlockUsing_eq`)。 -/
theorem onBlockUsing_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) : PoolExt c st (onBlockUsing c p st b build) := by
  rcases onBlockUsing_eq c p st b build with h | ⟨-, -, h⟩
  · rw [h]; exact PoolExt.refl c _
  · rw [h]; exact acceptBody_poolExt c st b _

theorem onBlockCheckedUsing_poolExt {c : Nat → NaruStd.Set ValidatorId} (handle : Store → Store)
    (hh : ∀ s, PoolExt c s (handle s)) (hc : HealConfig) (st : Store) (b : Block) :
    PoolExt c st (onBlockCheckedUsing handle hc st b) := by
  rcases onBlockCheckedUsing_eq handle hc st b with h | h
  · rw [h]; exact hh st
  · rw [h]; exact PoolExt.refl c _

/-! ## `NamedStore` のハンドラ -/

theorem processBlockCore_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    PoolExt c st.core (processBlockCore c p e hc cfg st b).core := by
  unfold processBlockCore
  dsimp only
  split_ifs
  · exact PoolExt.refl c _
  · rw [Proofs.Consensus.Stores.commitBlock_core]
    exact onBlockCheckedUsing_poolExt _ (fun cur => onBlockUsing_poolExt c p cur _ _) hc st.core _

theorem admitRow_poolExt (c : Nat → NaruStd.Set ValidatorId) (hc : HealConfig) (st : NamedStore) (row : NamedAttestation) :
    PoolExt c st.core (admitRow hc st row).core := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact onSgVote_poolExt c hc st.core _

theorem admitRows_poolExt (c : Nat → NaruStd.Set ValidatorId) (hc : HealConfig) :
    ∀ (rows : List NamedAttestation) (st : NamedStore), PoolExt c st.core (admitRows hc st rows).core
  | [], _ => PoolExt.refl c _
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_poolExt c hc rows (admitRow hc st row)
    unfold admitRows at ih
    exact (admitRow_poolExt c hc st row).trans ih

theorem admitCarried_poolExt (c : Nat → NaruStd.Set ValidatorId) (adm : CarriedAdmission) (hc : HealConfig)
    (before after : NamedStore) (b : NamedBlock) : PoolExt c after.core (admitCarried adm hc before after b).core := by
  unfold admitCarried
  split_ifs
  · exact admitRows_poolExt c hc _ after
  · exact PoolExt.refl c _

theorem onBlockWith_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    PoolExt c st.core (onBlockWith c p adm e hc cfg st b).core := by
  unfold onBlockWith
  exact (processBlockCore_poolExt c p e hc cfg st b).trans (admitCarried_poolExt c adm hc st _ b)

/-- 受信した object の処理は pool を拡張するだけ(投票は `onGoldfishVoteChecked`、ブロックは `onBlockWith`、attestation は不変)。 -/
theorem receiptProcess_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (st : NamedStore) (o : Model.Consensus.Execution.Objects.NamedObject) :
    PoolExt c st.core (receiptProcess c p s st o).core := by
  cases o with
  | Block b => exact onBlockWith_poolExt c p _ _ _ _ st b
  | GfVote u =>
    show PoolExt c st.core (onGoldfishVoteChecked c st.core u)
    exact onGoldfishVoteChecked_poolExt c st.core u
  | Attest a =>
    show PoolExt c st.core (admitRow s.hc st a).core
    exact admitRow_poolExt c s.hc st a

theorem nodeProcess_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState) (o : Model.Consensus.Execution.Objects.NamedObject) :
    PoolExt c n.st.core (nodeProcess c p s n o).st.core :=
  receiptProcess_poolExt c p s n.st o

/-! ## Tick の務め -/

theorem proposeBlockWith_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) :
    PoolExt c st.core (proposeBlockWith c p nr cache e hc cfg nd st).1.core := by
  unfold proposeBlockWith
  split
  · exact PoolExt.refl c _
  · rename_i b _
    exact onBlockWith_poolExt c p CarriedAdmission.AlsoCarried e hc cfg st b

theorem namedGoldfishVoteWith_poolExt (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) :
    PoolExt c st.core (namedGoldfishVoteWith c cache e hc nd st).1.core := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out h
  show PoolExt c st.core core
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [h]
  rw [h1]
  exact goldfishVoteWith_poolExt c cache e hc nd st.core

theorem namedUpdateConfirmationWith_poolExt (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv)
    (hc : HealConfig) (st : NamedStore) (k : Nat) :
    PoolExt c st.core (namedUpdateConfirmationWith cache e hc st k).core :=
  updateConfirmationWith_poolExt c cache e hc st.core k

theorem attestWith_poolExt (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    PoolExt c st.core (attestWith cache e hc nd st rec).1.core := by
  unfold attestWith
  split
  exact admitRow_poolExt c hc st _

/-- `NamedStore` の間の pool の拡張(`core` の `PoolExt`)。tick の 16 経路を `Carrier.tick_inv` と同じ入れ子の形で閉じるため、
出発点 `s0` を固定して各務めの補題を「`s0` からの拡張を 1 段延ばす」形(`*_poolExt'`)にする(`abbrev` なので `PoolExt` の目標に
reducible な展開で一致する)。 -/
abbrev NExt (c : Nat → NaruStd.Set ValidatorId) (a b : NamedStore) : Prop := PoolExt c a.core b.core

theorem proposeBlockWith_poolExt' (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {s0 st : NamedStore} (h : NExt c s0 st) :
    NExt c s0 (proposeBlockWith c p nr cache e hc cfg nd st).1 :=
  PoolExt.trans h (proposeBlockWith_poolExt c p nr cache e hc cfg nd st)

theorem namedGoldfishVoteWith_poolExt' (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {s0 st : NamedStore} (h : NExt c s0 st) :
    NExt c s0 (namedGoldfishVoteWith c cache e hc nd st).1 :=
  PoolExt.trans h (namedGoldfishVoteWith_poolExt c cache e hc nd st)

theorem namedUpdateConfirmationWith_poolExt' (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv)
    (hc : HealConfig) {s0 st : NamedStore} (h : NExt c s0 st) (k : Nat) :
    NExt c s0 (namedUpdateConfirmationWith cache e hc st k) :=
  PoolExt.trans h (namedUpdateConfirmationWith_poolExt c cache e hc st k)

theorem attestWith_poolExt' (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {s0 st : NamedStore} (h : NExt c s0 st)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    NExt c s0 (attestWith cache e hc nd st rec).1 :=
  PoolExt.trans h (attestWith_poolExt c cache e hc nd st rec)

/-- 1 tick の務め `tick` は pool を拡張するだけ(時計合わせは不変、提案・投票は `onGoldfishVoteChecked` を通る、確認・attestation は不変)。
`Carrier.tick_inv` と同じ 16 経路。 -/
theorem tick_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    PoolExt c st.core (tick c p a nr cache e hc cfg nd st rec t).1.core := by
  have h0 : NExt c st { st with core := { st.core with t := t, s := slotOf e t } } := PoolExt.of_same c rfl
  unfold tick
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact attestWith_poolExt' c cache e hc nd (namedUpdateConfirmationWith_poolExt' c cache e hc (namedGoldfishVoteWith_poolExt' c cache e hc nd (proposeBlockWith_poolExt' c p nr cache e hc cfg nd h0)) _) rec
    | with_reducible exact attestWith_poolExt' c cache e hc nd (namedUpdateConfirmationWith_poolExt' c cache e hc (namedGoldfishVoteWith_poolExt' c cache e hc nd h0) _) rec
    | with_reducible exact attestWith_poolExt' c cache e hc nd (namedUpdateConfirmationWith_poolExt' c cache e hc (proposeBlockWith_poolExt' c p nr cache e hc cfg nd h0) _) rec
    | with_reducible exact attestWith_poolExt' c cache e hc nd (namedUpdateConfirmationWith_poolExt' c cache e hc h0 _) rec
    | with_reducible exact attestWith_poolExt' c cache e hc nd (namedGoldfishVoteWith_poolExt' c cache e hc nd (proposeBlockWith_poolExt' c p nr cache e hc cfg nd h0)) rec
    | with_reducible exact attestWith_poolExt' c cache e hc nd (namedGoldfishVoteWith_poolExt' c cache e hc nd h0) rec
    | with_reducible exact attestWith_poolExt' c cache e hc nd (proposeBlockWith_poolExt' c p nr cache e hc cfg nd h0) rec
    | with_reducible exact attestWith_poolExt' c cache e hc nd h0 rec
    | with_reducible exact namedUpdateConfirmationWith_poolExt' c cache e hc (namedGoldfishVoteWith_poolExt' c cache e hc nd (proposeBlockWith_poolExt' c p nr cache e hc cfg nd h0)) _
    | with_reducible exact namedUpdateConfirmationWith_poolExt' c cache e hc (namedGoldfishVoteWith_poolExt' c cache e hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_poolExt' c cache e hc (proposeBlockWith_poolExt' c p nr cache e hc cfg nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_poolExt' c cache e hc h0 _
    | with_reducible exact namedGoldfishVoteWith_poolExt' c cache e hc nd (proposeBlockWith_poolExt' c p nr cache e hc cfg nd h0)
    | with_reducible exact namedGoldfishVoteWith_poolExt' c cache e hc nd h0
    | with_reducible exact proposeBlockWith_poolExt' c p nr cache e hc cfg nd h0
    | with_reducible exact h0

theorem nodeTick_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) : PoolExt c n.st.core (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_poolExt c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-! ## world と run の読み -/

/-- 1 event の後、どのノードの pool も拡張されただけ(他のノードは不変)。 -/
theorem worldStep_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (w : NamedWorld) (ev : NamedEvent)
    (v : ValidatorId) : PoolExt c (worldAt w v).st.core (worldAt (worldStep c p a nr s w ev) v).st.core := by
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, h⟩ | h
    · rw [h]
      exact nodeTick_poolExt c p a nr s u (worldAt w u) t
    · rw [h]
      exact PoolExt.refl c _
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, h⟩ | h
    · rw [h]
      exact nodeProcess_poolExt c p s (worldAt w u) o
    · rw [h]
      exact PoolExt.refl c _

theorem foldl_worldStep_poolExt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) (w : NamedWorld) (v : ValidatorId),
      PoolExt c (worldAt w v).st.core (worldAt (List.foldl (fun w ev => worldStep c p a nr s w ev) w l) v).st.core
  | [], _, _ => PoolExt.refl c _
  | ev :: l, w, v => by
    rw [List.foldl_cons]
    exact (worldStep_poolExt c p a nr s w ev v).trans (foldl_worldStep_poolExt c p a nr s l _ v)

/-- 初期 world のどのノードの pool も空。 -/
theorem worldInit_pool (c : Nat → NaruStd.Set ValidatorId) (v : ValidatorId) : PoolInv c (worldAt worldInit v).st.core :=
  initial_pool c

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 時刻 `t` の読みの store の pool は不変条件を満たす(run への前提なし)。 -/
theorem readAt_pool (t : Int) (v : ValidatorId) : PoolInv c (worldAt (readAt c p a nr s rho t) v).st.core := by
  unfold readAt
  exact (worldInit_pool c v).of_poolExt (foldl_worldStep_poolExt c p a nr s _ _ v)

theorem storeAt_pool (v : ValidatorId) (t : Int) : PoolInv c (storeAt c p a nr s rho v t).core :=
  readAt_pool c p a nr s rho t v

/-- 添字 `i` の前の world の store の pool も不変条件を満たす。 -/
theorem stateBefore_pool (i : Nat) (v : ValidatorId) : PoolInv c (worldAt (stateBefore c p a nr s rho i) v).st.core := by
  unfold stateBefore
  exact (worldInit_pool c v).of_poolExt (foldl_worldStep_poolExt c p a nr s _ _ v)

/-- 添字について、同じノードの pool は増えるだけ。 -/
theorem stateBefore_poolExt {i j : Nat} (hij : i ≤ j) (v : ValidatorId) :
    PoolExt c (worldAt (stateBefore c p a nr s rho i) v).st.core (worldAt (stateBefore c p a nr s rho j) v).st.core := by
  induction j with
  | zero =>
    rw [Nat.le_zero.mp hij]
    exact PoolExt.refl c _
  | succ j ih =>
    rcases Nat.lt_or_ge j i with hlt | hle
    · have : i = j + 1 := by omega
      rw [this]
      exact PoolExt.refl c _
    · refine (ih hle).trans ?_
      rw [Proofs.Consensus.Signing.stateBefore_succ]
      cases rho.events[j]? with
      | none => exact PoolExt.refl c _
      | some ev =>
        show PoolExt c _ (worldAt (worldStep c p a nr s (stateBefore c p a nr s rho j) ev) v).st.core
        exact worldStep_poolExt c p a nr s _ ev v

/-- `EventsSorted` の下で、同じノードの pool は時刻について増えるだけ(`storeAt_f_mono` と同じ運び)。 -/
theorem storeAt_poolExt (hs : Statements.Consensus.Spec.Conditions.EventsSorted rho) (v : ValidatorId) {t t2 : Int}
    (h : t ≤ t2) : PoolExt c (storeAt c p a nr s rho v t).core (storeAt c p a nr s rho v t2).core := by
  unfold storeAt readAt
  obtain ⟨l2, hl2⟩ := filter_le_append t t2 h rho.events (pairwise_of_eventsSorted rho hs)
  rw [hl2, List.foldl_append]
  exact foldl_worldStep_poolExt c p a nr s l2 _ v

end Run

/-! ## 自分の投票の形 -/

/-- `goldfishVoteWith` が投票 `u` を返したなら、`u` は自分の slot `st.s` の投票で、head は fork choice の結果の root、
自分は slot の committee の要素で、store 側は `u` を `onGoldfishVoteChecked` で入れたもの。 -/
theorem goldfishVoteWith_some (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : Store) {u : GoldfishVote}
    (h : (goldfishVoteWith c cache e hc nd st).2 = some u) :
    u.valIndex = nd.valIndex ∧ u.slot = st.s ∧
      u.head = root (getHeadInTreeWith cache e hc st (voterFilteredBlockTree e st st.s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterView e (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (storeToHealing st)) st.s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView e (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (storeToHealing st)) st.s)
        (st.s - 1)) ∧
      (c st.s).contains nd.valIndex = true ∧
      (goldfishVoteWith c cache e hc nd st).1 = onGoldfishVoteChecked c st u := by
  unfold goldfishVoteWith at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hmem
  dsimp only at h
  rw [Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl, hmem, rfl⟩

/-- `goldfishVoteWith` が投票を返さなければ store は変わらない(committee の外)。 -/
theorem goldfishVoteWith_none (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : Store) (h : (goldfishVoteWith c cache e hc nd st).2 = none) :
    (goldfishVoteWith c cache e hc nd st).1 = st ∧ (c st.s).contains nd.valIndex = false := by
  unfold goldfishVoteWith at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hmem
  refine ⟨rfl, ?_⟩
  cases hc' : (c st.s).contains nd.valIndex with
  | true => exact absurd hc' hmem
  | false => rfl

end Proofs.Consensus.Votes
