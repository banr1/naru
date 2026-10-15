import Proofs.Consensus.Carried
import Proofs.Consensus.Majority
import Mathlib.Tactic

/-!
# pool の投票の受信の印は固定され、GST 以後の honest な投票の印は支持の締切より前(C71 の補題)

`Majority.HonestSupport.vote` の支持の投票(`supportVotes`)は、解決の印 `storeTau`(投票の受信の印 `timestampVote` と head の
ブロックの受信の印の大きい方)が `supportCutoff` より前の投票。この節はその投票の側の半分を示す。

store の受信の印の表 `timestampVote` を書くのは `onGoldfishVote`(`Model/Consensus/Protocol/Handlers.lean`)だけで、投票を pool に
入れるときに、その投票の印を現在の時計 `Stamp.At st.t` にする。既に鍵 `u.slot` の pool にある投票 `u` は受理されないので
(`onGoldfishVote_cases`)、
- **印の保存** `Keep a b`: `a` の鍵 `u.slot` の pool の投票は `b` にも残り、印は変わらない。
- **新しい投票の印** `Fresh a b`: `b` の鍵 `u.slot` の pool に増えた投票の印は `b` の時計以下の時刻。
どのハンドラも時計を変えずにこの 2 つを満たし(`Step`)、tick は時計を合わせた後の store からの `Step` なので `Keep` と `Fresh`
を満たす(`Grow`)。run では時計は 1 つの event で戻らない(`Window.clock_succ_ge`)ので、どの添字の store でも pool の投票の印は時計以下の
時刻(`StampInv`、`stateBefore_stampInv`)。添字 `j` の event の後の store は時計がその event の時刻以下(`clock_succ_le_event`)
なので、`stateBefore (j + 1)` の pool にある投票の印は以後ずっと、添字 `j` の event の時刻以下のまま(`stamp_le_of_mem`)。

`Carried.partialSynchrony_honest_gfVote_mem` と合わせると、GST 以後に honest な `v` が出した投票 `u` は、`supportCutoff` が horizon
以内なら、honest な各ノード `w` について `w` ごとのある添字(時刻は `supportCutoff` より前)より後のどの添字でも `w` の鍵 `u.slot`
の pool にあり、受信の印が `supportCutoff e u.slot` より前(`partialSynchrony_honest_gfVote_stamped`。投票の締切
`voteTime + Δ` はちょうど `supportCutoff`)。head のブロックの受信の印の側は別に示す。

手書きでは `DecoupledConsensusProofs/Protocol/Handlers/Pool.lean` の `PoolStamps`(`stamped` / `bounded`: pool の投票は印を持ち、
印は時計以下)と `PoolCarry`(`mem` / `stamp`: 投票は残り印は書き換わらない。手書きは印のある投票すべてについて言うが、印のある投票は
pool にあるので naru の `Keep` と実質同じ)に当たり、受信の時刻を締切に結ぶのは
`DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean` の運びに当たる。
-/

namespace Proofs.Consensus.Stamps

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Time Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Tables Proofs.Consensus.Carrier Proofs.Consensus.Votes
open Proofs.Consensus.Clocks (SameClock)

/-! ## 投票を鍵にした表 -/

theorem gv_get?_insert_self {ν : Type} (t : NaruStd.Table GoldfishVote ν) (k : GoldfishVote) (v : ν) :
    (t.insert k v).get? k = some v := by
  simp [NaruStd.Table.get?, NaruStd.Table.insert, find?_insertSorted_self gv_compare_eq_iff k v t.entries]

theorem gv_get?_insert_ne {ν : Type} (t : NaruStd.Table GoldfishVote ν) (k : GoldfishVote) (v : ν) (k' : GoldfishVote)
    (hne : k ≠ k') : (t.insert k v).get? k' = t.get? k' := by
  have htr : ∀ a b c : GoldfishVote, compare a b = .eq → compare b c = .eq → compare a c = .eq := fun a b c hab hbc => by
    rw [gv_compare_eq_iff] at hab hbc ⊢
    exact hab.trans hbc
  rcases find?_insertSorted htr k v k' t.entries with ⟨hk, _⟩ | hf
  · exact absurd ((gv_compare_eq_iff k k').mp hk) hne
  · simp [NaruStd.Table.get?, NaruStd.Table.insert, hf]

/-! ## 印の保存と新しい投票の印 -/

/-- 印の保存: `a` の鍵 `u.slot` の pool の投票は `b` にも残り、受信の印は変わらない。 -/
def Keep (a b : Store) : Prop :=
  ∀ u, u ∈ poolList a u.slot → u ∈ poolList b u.slot ∧ b.timestampVote.get? u = a.timestampVote.get? u

/-- 新しい投票の印: `b` の鍵 `u.slot` の pool の投票は `a` にもあったか、受信の印が `b` の時計以下の時刻。 -/
def Fresh (a b : Store) : Prop :=
  ∀ u, u ∈ poolList b u.slot → u ∈ poolList a u.slot ∨ ∃ τ, b.timestampVote.get? u = some (Stamp.At τ) ∧ τ ≤ b.t

/-- 時計を変えないハンドラの 1 段: 印の保存・新しい投票の印・時計の一致。 -/
structure Step (a b : Store) : Prop where
  keep : Keep a b
  fresh : Fresh a b
  clock : SameClock b a

theorem Keep.refl (a : Store) : Keep a a := fun _ h => ⟨h, rfl⟩

theorem Keep.trans {a b d : Store} (h1 : Keep a b) (h2 : Keep b d) : Keep a d := fun u h => by
  obtain ⟨hb, hb'⟩ := h1 u h
  obtain ⟨hd, hd'⟩ := h2 u hb
  exact ⟨hd, hd'.trans hb'⟩

theorem Step.refl (a : Store) : Step a a := ⟨Keep.refl a, fun _ h => Or.inl h, SameClock.refl a⟩

theorem Step.trans {a b d : Store} (h1 : Step a b) (h2 : Step b d) : Step a d := by
  refine ⟨h1.keep.trans h2.keep, fun u hu => ?_, h2.clock.trans h1.clock⟩
  rcases h2.fresh u hu with hb | hd
  · rcases h1.fresh u hb with ha | ⟨τ, hτ, hle⟩
    · exact Or.inl ha
    · obtain ⟨-, heq⟩ := h2.keep u hb
      exact Or.inr ⟨τ, heq.trans hτ, by rw [h2.clock.t]; exact hle⟩
  · exact Or.inr hd

/-- pool・印の表・時計が等しい store の間は 1 段(何も増えない)。 -/
theorem Step.of_same {a b : Store} (hg : b.gfVotes = a.gfVotes) (htv : b.timestampVote = a.timestampVote)
    (hc : SameClock b a) : Step a b := by
  have hp : ∀ k, poolList b k = poolList a k := fun k => by unfold poolList; rw [hg]
  exact ⟨fun u hu => ⟨by rw [hp]; exact hu, by rw [htv]⟩, fun u hu => Or.inl (by rw [← hp]; exact hu), hc⟩

/-! ## `onGoldfishVote` -/

/-- `onGoldfishVote st x` は store のままか、`x` がまだ鍵 `x.slot` の pool に無く、`x` の印を時計の時刻にする。 -/
theorem onGoldfishVote_cases (st : Store) (x : GoldfishVote) :
    onGoldfishVote st x = st ∨
      (x ∉ poolList st x.slot ∧
        (onGoldfishVote st x).timestampVote = st.timestampVote.insert x (Stamp.At st.t)) := by
  unfold onGoldfishVote
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inl rfl
  · refine Or.inr ⟨fun hx => h1 ?_, rfl⟩
    have hc : (NaruStd.Table.getOr st.gfVotes x.slot []).contains x = true := List.contains_iff_mem.mpr hx
    rw [hc, Bool.or_true]

theorem onGoldfishVote_step (st : Store) (x : GoldfishVote) : Step st (onGoldfishVote st x) := by
  rcases onGoldfishVote_cases st x with h | ⟨hx, htv⟩
  · rw [h]; exact Step.refl st
  · refine ⟨fun u hu => ⟨?_, ?_⟩, fun u hu => ?_, Proofs.Consensus.Clocks.onGoldfishVote_clock st x⟩
    · rcases poolList_onGoldfishVote st x u.slot with h | ⟨-, h⟩
      · rw [h]; exact hu
      · rw [h]; exact List.mem_append_left _ hu
    · rw [htv]
      refine gv_get?_insert_ne _ _ _ _ ?_
      rintro rfl
      exact hx hu
    · rcases poolList_onGoldfishVote st x u.slot with h | ⟨-, h⟩
      · rw [h] at hu; exact Or.inl hu
      · rw [h, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | hu
        · exact Or.inl hu
        · subst hu
          refine Or.inr ⟨st.t, ?_, le_of_eq (Proofs.Consensus.Clocks.onGoldfishVote_clock st u).t.symm⟩
          rw [htv]
          exact gv_get?_insert_self _ _ _

theorem onGoldfishVoteChecked_step (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    Step st (onGoldfishVoteChecked c st u) := by
  unfold onGoldfishVoteChecked
  split_ifs
  · exact Step.refl st
  · exact onGoldfishVote_step st u

theorem foldl_step {β : Type} (g : Store → β → Store) (hg : ∀ s x, Step s (g s x)) :
    ∀ (l : List β) (s : Store), Step s (List.foldl g s l)
  | [], _ => Step.refl _
  | x :: l, s => by
    rw [List.foldl_cons]
    exact (hg s x).trans (foldl_step g hg l (g s x))

/-! ## 投票の印を触らない `Store` のハンドラ -/

theorem onSgVote_step (hc : HealConfig) (st : Store) (a : CombinedAttestation) : Step st (onSgVote hc st a) := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact Step.of_same rfl rfl ⟨rfl, rfl⟩

theorem updateFinality_step (st : Store) (σ : ChainState) : Step st (updateFinality st σ) := by
  unfold updateFinality
  dsimp only
  split_ifs <;> exact Step.of_same rfl rfl ⟨rfl, rfl⟩

theorem updateConfirmationWith_step (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (k : Nat) :
    Step st (updateConfirmationWith cache e hc st k) :=
  Step.of_same rfl rfl ⟨rfl, rfl⟩

theorem goldfishVoteWith_step (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) (st : Store) : Step st (goldfishVoteWith c cache e hc nd st).1 := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_step c st _
  · exact Step.refl st

/-! ## ブロックの受理 -/

theorem storedOf_step (st : Store) (b : Block) (post : ChainState) : Step st (storedOf st b post) :=
  Step.of_same rfl rfl ⟨rfl, rfl⟩

theorem unpackedOf_step (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    Step st (unpackedOf c st b post) :=
  (storedOf_step st b post).trans (foldl_step _ (fun s u => onGoldfishVoteChecked_step c s u) _ _)

theorem acceptBody_step (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    Step st (acceptBody c st b post) :=
  (unpackedOf_step c st b post).trans (updateFinality_step _ _)

theorem onBlockUsing_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) : Step st (onBlockUsing c p st b build) := by
  rcases onBlockUsing_eq c p st b build with h | ⟨-, -, h⟩
  · rw [h]; exact Step.refl st
  · rw [h]; exact acceptBody_step c st b _

theorem onBlockCheckedUsing_step (handle : Store → Store) (hh : ∀ s, Step s (handle s)) (hc : HealConfig) (st : Store)
    (b : Block) : Step st (onBlockCheckedUsing handle hc st b) := by
  rcases onBlockCheckedUsing_eq handle hc st b with h | h
  · rw [h]; exact hh st
  · rw [h]; exact Step.refl st

/-! ## `NamedStore` のハンドラ -/

theorem processBlockCore_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    Step st.core (processBlockCore c p e hc cfg st b).core := by
  unfold processBlockCore
  dsimp only
  split_ifs
  · exact Step.refl _
  · rw [Proofs.Consensus.Stores.commitBlock_core]
    exact onBlockCheckedUsing_step _ (fun cur => onBlockUsing_step c p cur _ _) hc st.core _

theorem admitRow_step (hc : HealConfig) (st : NamedStore) (row : NamedAttestation) :
    Step st.core (admitRow hc st row).core := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact onSgVote_step hc st.core _

theorem admitRows_step (hc : HealConfig) :
    ∀ (rows : List NamedAttestation) (st : NamedStore), Step st.core (admitRows hc st rows).core
  | [], _ => Step.refl _
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_step hc rows (admitRow hc st row)
    unfold admitRows at ih
    exact (admitRow_step hc st row).trans ih

theorem admitCarried_step (adm : CarriedAdmission) (hc : HealConfig) (before after : NamedStore) (b : NamedBlock) :
    Step after.core (admitCarried adm hc before after b).core := by
  unfold admitCarried
  split_ifs
  · exact admitRows_step hc _ after
  · exact Step.refl _

theorem onBlockWith_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    Step st.core (onBlockWith c p adm e hc cfg st b).core := by
  unfold onBlockWith
  exact (processBlockCore_step c p e hc cfg st b).trans (admitCarried_step adm hc st _ b)

theorem receiptProcess_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (st : NamedStore) (o : NamedObject) :
    Step st.core (receiptProcess c p s st o).core := by
  cases o with
  | Block b => exact onBlockWith_step c p _ _ _ _ st b
  | GfVote u =>
    show Step st.core (onGoldfishVoteChecked c st.core u)
    exact onGoldfishVoteChecked_step c st.core u
  | Attest a =>
    show Step st.core (admitRow s.hc st a).core
    exact admitRow_step s.hc st a

theorem nodeProcess_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState) (o : NamedObject) :
    Step n.st.core (nodeProcess c p s n o).st.core :=
  receiptProcess_step c p s n.st o

/-! ## Tick の務め -/

/-- `NamedStore` の間の 1 段(`core` の `Step`)。`Votes.NExt` と同じく、tick の 16 経路を入れ子の形で閉じるため。 -/
abbrev SStep (a b : NamedStore) : Prop := Step a.core b.core

theorem proposeBlockWith_step' (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Node) {s0 st : NamedStore} (h : SStep s0 st) : SStep s0 (proposeBlockWith c p nr cache e hc cfg nd st).1 := by
  refine Step.trans h ?_
  unfold proposeBlockWith
  split
  · exact Step.refl _
  · rename_i b _
    exact onBlockWith_step c p CarriedAdmission.AlsoCarried e hc cfg st b

theorem namedGoldfishVoteWith_step' (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) {s0 st : NamedStore} (h : SStep s0 st) : SStep s0 (namedGoldfishVoteWith c cache e hc nd st).1 := by
  refine Step.trans h ?_
  unfold namedGoldfishVoteWith
  split
  rename_i core out hm
  show Step st.core core
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [hm]
  rw [h1]
  exact goldfishVoteWith_step c cache e hc nd st.core

theorem namedUpdateConfirmationWith_step' (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) {s0 st : NamedStore}
    (h : SStep s0 st) (k : Nat) : SStep s0 (namedUpdateConfirmationWith cache e hc st k) :=
  Step.trans h (updateConfirmationWith_step cache e hc st.core k)

theorem attestWith_step' (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (nd : Node) {s0 st : NamedStore}
    (h : SStep s0 st) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    SStep s0 (attestWith cache e hc nd st rec).1 := by
  refine Step.trans h ?_
  unfold attestWith
  split
  exact admitRow_step hc st _

/-- 印の保存と新しい投票の印(時計の一致は問わない)。 -/
def Grow (a b : Store) : Prop := Keep a b ∧ Fresh a b

theorem Step.grow {a b : Store} (h : Step a b) : Grow a b := ⟨h.keep, h.fresh⟩

theorem Grow.refl (a : Store) : Grow a a := (Step.refl a).grow

/-- 1 tick の務め `tick` は印を保存し、新しい投票の印は tick の後の時計以下(時計合わせの後の store からの `Step`。
`Votes.tick_poolExt` と同じ 16 経路)。 -/
theorem tick_grow (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Node) (st : NamedStore) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    Grow st.core (tick c p a nr cache e hc cfg nd st rec t).1.core := by
  have h0 : SStep { st with core := { st.core with t := t, s := slotOf e t } }
      { st with core := { st.core with t := t, s := slotOf e t } } := Step.refl _
  have hfin : SStep { st with core := { st.core with t := t, s := slotOf e t } } (tick c p a nr cache e hc cfg nd st rec t).1 := by
    unfold tick
    dsimp only
    split_ifs
    all_goals first
      | with_reducible exact attestWith_step' cache e hc nd (namedUpdateConfirmationWith_step' cache e hc (namedGoldfishVoteWith_step' c cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0)) _) rec
      | with_reducible exact attestWith_step' cache e hc nd (namedUpdateConfirmationWith_step' cache e hc (namedGoldfishVoteWith_step' c cache e hc nd h0) _) rec
      | with_reducible exact attestWith_step' cache e hc nd (namedUpdateConfirmationWith_step' cache e hc (proposeBlockWith_step' c p nr cache e hc cfg nd h0) _) rec
      | with_reducible exact attestWith_step' cache e hc nd (namedUpdateConfirmationWith_step' cache e hc h0 _) rec
      | with_reducible exact attestWith_step' cache e hc nd (namedGoldfishVoteWith_step' c cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0)) rec
      | with_reducible exact attestWith_step' cache e hc nd (namedGoldfishVoteWith_step' c cache e hc nd h0) rec
      | with_reducible exact attestWith_step' cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0) rec
      | with_reducible exact attestWith_step' cache e hc nd h0 rec
      | with_reducible exact namedUpdateConfirmationWith_step' cache e hc (namedGoldfishVoteWith_step' c cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0)) _
      | with_reducible exact namedUpdateConfirmationWith_step' cache e hc (namedGoldfishVoteWith_step' c cache e hc nd h0) _
      | with_reducible exact namedUpdateConfirmationWith_step' cache e hc (proposeBlockWith_step' c p nr cache e hc cfg nd h0) _
      | with_reducible exact namedUpdateConfirmationWith_step' cache e hc h0 _
      | with_reducible exact namedGoldfishVoteWith_step' c cache e hc nd (proposeBlockWith_step' c p nr cache e hc cfg nd h0)
      | with_reducible exact namedGoldfishVoteWith_step' c cache e hc nd h0
      | with_reducible exact proposeBlockWith_step' c p nr cache e hc cfg nd h0
      | with_reducible exact h0
  exact ⟨fun u hu => hfin.keep u hu, fun u hu => hfin.fresh u hu⟩

theorem nodeTick_grow (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) : Grow n.st.core (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_grow c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-! ## world と run -/

/-- 1 event の後、どのノードの store も印を保存し、新しい投票の印はその store の時計以下。 -/
theorem worldStep_grow (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (w : NamedWorld) (ev : NamedEvent)
    (v : ValidatorId) : Grow (worldAt w v).st.core (worldAt (worldStep c p a nr s w ev) v).st.core := by
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, h⟩ | h
    · rw [h]
      exact nodeTick_grow c p a nr s u (worldAt w u) t
    · rw [h]
      exact Grow.refl _
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, h⟩ | h
    · rw [h]
      exact (nodeProcess_step c p s (worldAt w u) o).grow
    · rw [h]
      exact Grow.refl _

/-- 印の不変条件: 鍵 `u.slot` の pool の投票の受信の印は、store の時計以下の時刻。 -/
def StampInv (st : Store) : Prop :=
  ∀ u, u ∈ poolList st u.slot → ∃ τ, st.timestampVote.get? u = some (Stamp.At τ) ∧ τ ≤ st.t

theorem StampInv.of_grow {a b : Store} (h : StampInv a) (hg : Grow a b) (ht : a.t ≤ b.t) : StampInv b := fun u hu => by
  rcases hg.2 u hu with ha | hb
  · obtain ⟨τ, hτ, hle⟩ := h u ha
    obtain ⟨-, heq⟩ := hg.1 u ha
    exact ⟨τ, heq.trans hτ, le_trans hle ht⟩
  · exact hb

theorem initial_stampInv : StampInv initStore := fun u hu => by
  rw [initial_poolList] at hu
  exact absurd hu List.not_mem_nil

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字について、同じノードの store は印を保存する。 -/
theorem stateBefore_keep {i j : Nat} (hij : i ≤ j) (v : ValidatorId) :
    Keep (worldAt (stateBefore c p a nr s rho i) v).st.core (worldAt (stateBefore c p a nr s rho j) v).st.core := by
  induction j with
  | zero =>
    rw [Nat.le_zero.mp hij]
    exact Keep.refl _
  | succ j ih =>
    rcases Nat.lt_or_ge j i with hlt | hle
    · have : i = j + 1 := by omega
      rw [this]
      exact Keep.refl _
    · refine (ih hle).trans ?_
      rw [Proofs.Consensus.Signing.stateBefore_succ]
      cases rho.events[j]? with
      | none => exact Keep.refl _
      | some ev =>
        show Keep _ (worldAt (worldStep c p a nr s (stateBefore c p a nr s rho j) ev) v).st.core
        exact (worldStep_grow c p a nr s _ ev v).1

/-- **run のどの添字・どのノードでも印の不変条件**(event の整列と時刻の非負の下で。時計の単調性 `Window.clock_succ_ge`)。 -/
theorem stateBefore_stampInv (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev) :
    ∀ (i : Nat) (v : ValidatorId), StampInv (worldAt (stateBefore c p a nr s rho i) v).st.core
  | 0, _ => initial_stampInv
  | i + 1, v => by
    have ih := stateBefore_stampInv hs hnn i v
    have ht := Proofs.Consensus.Window.clock_succ_ge c p a nr s rho hs hnn i v
    refine ih.of_grow ?_ ht
    rw [Proofs.Consensus.Signing.stateBefore_succ]
    cases rho.events[i]? with
    | none => exact Grow.refl _
    | some ev =>
      show Grow _ (worldAt (worldStep c p a nr s (stateBefore c p a nr s rho i) ev) v).st.core
      exact worldStep_grow c p a nr s _ ev v

/-- 添字 `j` の event の後の時計は、その event の時刻以下(自分の tick ならその時刻、他は直前の時計のまま)。 -/
theorem clock_succ_le_event (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    {j : Nat} {ev : NamedEvent} (hev : rho.events[j]? = some ev) (v : ValidatorId) :
    (worldAt (stateBefore c p a nr s rho (j + 1)) v).st.core.t ≤ eventTime ev := by
  have hle := (Proofs.Consensus.Clocks.clock_le_event c p a nr s rho hs hnn j v).2 j ev le_rfl hev
  rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev]
  cases ev with
  | Tick w t =>
    unfold worldStep
    dsimp only
    by_cases hwv : w = v
    · subst hwv
      rw [Proofs.Consensus.Signing.worldAt_insert_self,
        (Proofs.Consensus.Clocks.nodeTick_clockIs c p a nr s w (worldAt (stateBefore c p a nr s rho j) w) t).1]
      rfl
    · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwv]
      exact hle
  | Deliver w o t =>
    unfold worldStep
    dsimp only
    by_cases hwv : w = v
    · subst hwv
      rw [Proofs.Consensus.Signing.worldAt_insert_self,
        (Proofs.Consensus.Clocks.nodeProcess_clock c p s (worldAt (stateBefore c p a nr s rho j) w) o).t]
      exact hle
    · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwv]
      exact hle

/-- **印は event の時刻以下に固定される**: `stateBefore (j + 1)` の `w` の鍵 `u.slot` の pool に `u` があれば、`j` より後の
どの添字でも `u` は `w` の pool にあり、受信の印は添字 `j` の event の時刻以下の時刻のまま。 -/
theorem stamp_le_of_mem (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    {j : Nat} {ev : NamedEvent} (hev : rho.events[j]? = some ev) {w : ValidatorId} {u : GoldfishVote}
    (hu : u ∈ poolList (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core u.slot) {i : Nat} (hji : j < i) :
    u ∈ poolList (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot ∧
      ∃ τ, (worldAt (stateBefore c p a nr s rho i) w).st.core.timestampVote.get? u = some (Stamp.At τ) ∧
        τ ≤ eventTime ev := by
  obtain ⟨τ, hτ, hle⟩ := stateBefore_stampInv c p a nr s rho hs hnn (j + 1) w u hu
  obtain ⟨hmem, heq⟩ := stateBefore_keep c p a nr s rho (i := j + 1) (j := i) hji w u hu
  exact ⟨hmem, τ, heq.trans hτ, le_trans hle (clock_succ_le_event c p a nr s rho hs hnn hev w)⟩

/-- 印 `At τ` は `τ < γ` なら `γ` より前。 -/
theorem occurrenceBefore_at {τ γ : Int} (h : τ < γ) : occurrenceBefore (some (Stamp.At τ)) γ = true := by
  unfold occurrenceBefore
  exact (Proofs.Consensus.Majority.stampBefore_iff _ _).mpr (Or.inr ⟨τ, rfl, h⟩)

/-- `HandlesAt` の添字の event の時刻は扱いの時刻。 -/
theorem handlesAt_event {j : Nat} {w : ValidatorId} {u : GoldfishVote} {t2 : Int}
    (h : HandlesAt c p a nr s rho j w (NamedObject.GfVote u) t2) :
    ∃ ev, rho.events[j]? = some ev ∧ eventTime ev = t2 := by
  rcases Proofs.Consensus.Delivery.handlesAt_gfVote_cases c p a nr s rho h with ⟨hev, -⟩ | hev |
    ⟨ev, hev, -, hte, -⟩
  · exact ⟨_, hev, rfl⟩
  · exact ⟨_, hev, rfl⟩
  · exact ⟨ev, hev, hte⟩

/-- **GST 以後の honest な投票は、honest な各ノードの pool に、支持の締切より前の受信の印で入る**(添字はノードごと):
`PartialSynchrony` / `ScheduleWellFormed` / `UnforgeableSignatures` / Δ > 0 の下で、honest な `v` が GST 以後の時刻 `t` に
発行した投票 `u` は、`supportCutoff e u.slot` が horizon 以内なら、honest な `w` について時刻 `t2`
(`t ≤ t2 < supportCutoff e u.slot`)の添字 `j` があり、`j` より後のどの添字でも `u` は `w` の鍵 `u.slot` の pool にあり、
受信の印は `supportCutoff e u.slot` より前。 -/
theorem partialSynchrony_honest_gfVote_stamped (hps : PartialSynchrony c p a nr s rho) (hsch : ScheduleWellFormed s rho)
    (hunf : UnforgeableSignatures c p a nr s rho) (hδ : 0 < s.e.delta) {v w : ValidatorId} {u : GoldfishVote} {t : Int}
    (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t) (hv : rho.honest.contains v = true)
    (hgst : s.e.tGST ≤ t) (hw : rho.honest.contains w = true) (hd : supportCutoff s.e u.slot ≤ rho.horizon) :
    ∃ t2 j, (t ≤ t2 ∧ t2 < supportCutoff s.e u.slot) ∧ HandlesAt c p a nr s rho j w (NamedObject.GfVote u) t2 ∧
      ∀ i, j < i → u ∈ poolList (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot ∧
        occurrenceBefore ((worldAt (stateBefore c p a nr s rho i) w).st.core.timestampVote.get? u)
          (supportCutoff s.e u.slot) = true := by
  obtain ⟨-, htv, -, hsl, -⟩ := Proofs.Consensus.Voting.emits_gfVote_shape c p a nr s rho hem
  rw [← hsl] at htv
  have hcut : max t s.e.tGST + s.e.delta = supportCutoff s.e u.slot := by
    rw [max_eq_left hgst, htv]
    unfold voteTime supportCutoff
    ring
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev h =>
    (Proofs.Consensus.Window.eventTime_bounds hsch h).1
  obtain ⟨t2, j, ⟨ht, ht2⟩, hh, -⟩ :=
    Proofs.Consensus.Carried.partialSynchrony_honest_gfVote_mem c p a nr s rho hps hsch hunf hδ hem hv hgst hw
      (by rw [hcut]; exact hd)
  rw [hcut] at ht2
  have hmem := Proofs.Consensus.Carried.handlesAt_honest_gfVote_mem c p a nr s rho hsch hunf hδ hem hv hgst hw hh ht
    (by rw [hcut]; exact ht2)
  obtain ⟨ev, hev, hte⟩ := handlesAt_event c p a nr s rho hh
  refine ⟨t2, j, ⟨ht, ht2⟩, hh, fun i hji => ?_⟩
  obtain ⟨hm, τ, hτ, hle⟩ := stamp_le_of_mem c p a nr s rho hs hnn hev hmem hji
  refine ⟨hm, ?_⟩
  rw [hτ]
  exact occurrenceBefore_at (by rw [hte] at hle; exact lt_of_le_of_lt hle ht2)

end Run

end Proofs.Consensus.Stamps
