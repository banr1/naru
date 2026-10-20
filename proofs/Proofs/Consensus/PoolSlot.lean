import Proofs.Consensus.Stamps
import Mathlib.Tactic

/-!
# pool に新しく入った投票の slot は時計の slot 以下で、受理の時刻は投票の slot の提案の時刻以後(C77 の補題)

`AvailableHoles.genuineConf_adoptionTransport` の `backward` は、読みの pool の投票の受理(`Settled.pool_accepted`)を中継
(`Settled.acceptsAt_gfVote_settled`)に掛ける。中継の補題は受理の時刻 `t0` が投票の slot の窓の下限 `proposalTime u.slot` 以上で
あることを前提に取る。pool を育てるのは `onGoldfishVote` だけで、その守り `st.s < vote.slot` を通った投票は slot が store の slot 以下
(`onGoldfishVote_step`)。他のハンドラは pool と時計を変えないか `onGoldfishVote` を重ねるだけで、tick は時計を `slotOf e t` に
進めてから務めを走らせる(`tick_fresh`)。`ParentSlot` の tree の slot と同じ形。

- `Fresh a b`: `b` の鍵 `u.slot` の pool の投票は `a` にもあったか、slot が `b` の slot 以下。
- `worldStep_fresh`: 1 event の後のどのノードの store も `Fresh`。
- `accepts_slot_le`: 添字 `i` で新しく `x` の pool に入った投票の slot の提案の時刻は、添字 `i` の event の時刻以下
  (`stateBefore (i + 1)` の時計の slot は `slotOf` の時計で、時計は event の時刻以下。`Stamps.clock_succ_le_event`)。
- `acceptsAt_gfVote_slot_le`: `AcceptsAt` の形。
-/

namespace Proofs.Consensus.PoolSlot

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Time Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Tables Proofs.Consensus.Carrier Proofs.Consensus.Votes
open Proofs.Consensus.Clocks (SameClock)

/-! ## 新しい投票の slot -/

/-- 新しい投票の slot: `b` の鍵 `u.slot` の pool の投票は `a` にもあったか、slot が `b` の slot 以下。 -/
def Fresh (a b : Store) : Prop :=
  ∀ u, u ∈ poolList b u.slot → u ∈ poolList a u.slot ∨ u.slot ≤ b.s

/-- 時計を変えないハンドラの 1 段: 新しい投票の slot・pool の拡張・時計の一致。 -/
structure Step (a b : Store) : Prop where
  fresh : Fresh a b
  ext : ∀ u, u ∈ poolList a u.slot → u ∈ poolList b u.slot
  clock : SameClock b a

theorem Step.refl (a : Store) : Step a a := ⟨fun _ h => Or.inl h, fun _ h => h, SameClock.refl a⟩

theorem Step.trans {a b d : Store} (h1 : Step a b) (h2 : Step b d) : Step a d := by
  refine ⟨fun u hu => ?_, fun u hu => h2.ext u (h1.ext u hu), h2.clock.trans h1.clock⟩
  rcases h2.fresh u hu with hb | hd
  · rcases h1.fresh u hb with ha | hle
    · exact Or.inl ha
    · exact Or.inr (by rw [h2.clock.s]; exact hle)
  · exact Or.inr hd

/-- pool と時計が等しい store の間は 1 段。 -/
theorem Step.of_same {a b : Store} (hg : b.gfVotes = a.gfVotes) (hc : SameClock b a) : Step a b := by
  have hp : ∀ k, poolList b k = poolList a k := fun k => by unfold poolList; rw [hg]
  exact ⟨fun u hu => Or.inl (by rw [← hp]; exact hu), fun u hu => by rw [hp]; exact hu, hc⟩

/-! ## `onGoldfishVote` -/

/-- **守り `st.s < vote.slot` を通った投票だけが pool に入る**。 -/
theorem onGoldfishVote_step (st : Store) (x : GoldfishVote) : Step st (onGoldfishVote st x) := by
  by_cases hlt : st.s < x.slot
  · have h : onGoldfishVote st x = st := by
      unfold onGoldfishVote
      simp [hlt]
    rw [h]
    exact Step.refl st
  · refine ⟨fun u hu => ?_, fun u hu => ?_, Proofs.Consensus.Clocks.onGoldfishVote_clock st x⟩
    · rcases poolList_onGoldfishVote st x u.slot with h | ⟨-, h⟩
      · rw [h] at hu; exact Or.inl hu
      · rw [h, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | hu
        · exact Or.inl hu
        · subst hu
          refine Or.inr ?_
          rw [(Proofs.Consensus.Clocks.onGoldfishVote_clock st u).s]
          exact Nat.le_of_not_lt hlt
    · rcases poolList_onGoldfishVote st x u.slot with h | ⟨-, h⟩
      · rw [h]; exact hu
      · rw [h]; exact List.mem_append_left _ hu

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

/-! ## pool を触らない `Store` のハンドラ -/

theorem onSgVote_step (hc : HealConfig) (st : Store) (a : CombinedAttestation) : Step st (onSgVote hc st a) := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact Step.of_same rfl ⟨rfl, rfl⟩

theorem updateFinality_step (st : Store) (σ : ChainState) : Step st (updateFinality st σ) := by
  unfold updateFinality
  dsimp only
  split_ifs <;> exact Step.of_same rfl ⟨rfl, rfl⟩

theorem updateConfirmationWith_step (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (st : Store) (k : Nat) :
    Step st (updateConfirmationWith cache e hc st k) :=
  Step.of_same rfl ⟨rfl, rfl⟩

theorem goldfishVoteWith_step (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Node) (st : Store) : Step st (goldfishVoteWith c cache e hc nd st).1 := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_step c st _
  · exact Step.refl st

/-! ## ブロックの受理 -/

theorem storedOf_step (st : Store) (b : Block) (post : ChainState) : Step st (storedOf st b post) :=
  Step.of_same rfl ⟨rfl, rfl⟩

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

/-- `NamedStore` の間の 1 段(`core` の `Step`)。tick の 16 経路を入れ子の形で閉じるため。 -/
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

/-- 1 tick の務め `tick` の後の pool の投票は、tick の前の pool にあったか、slot が tick の後の slot 以下
(時計合わせの後の store からの `Step`。`ParentSlot.tick_fresh` と同じ 16 経路)。 -/
theorem tick_fresh (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Node) (st : NamedStore) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    Fresh st.core (tick c p a nr cache e hc cfg nd st rec t).1.core := by
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
  exact fun u hu => hfin.fresh u hu

theorem nodeTick_fresh (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) : Fresh n.st.core (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_fresh c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-! ## world と run -/

/-- 1 event の後、どのノードの store も、新しい pool の投票の slot はその store の slot 以下。 -/
theorem worldStep_fresh (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (w : NamedWorld) (ev : NamedEvent)
    (v : ValidatorId) : Fresh (worldAt w v).st.core (worldAt (worldStep c p a nr s w ev) v).st.core := by
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, h⟩ | h
    · rw [h]
      exact nodeTick_fresh c p a nr s u (worldAt w u) t
    · rw [h]
      exact (Step.refl _).fresh
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases Proofs.Consensus.Runs.worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, h⟩ | h
    · rw [h]
      exact (nodeProcess_step c p s (worldAt w u) o).fresh
    · rw [h]
      exact (Step.refl _).fresh

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **新しく pool に入った投票の slot の提案の時刻は event の時刻以下**: 添字 `i` の event で `x` の鍵 `u.slot` の pool に新しく
`u` が入ったなら、`proposalTime u.slot` はその event の時刻以下。 -/
theorem accepts_slot_le (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (hδ : 0 < s.e.delta) {i : Nat} {ev : NamedEvent} (hev : rho.events[i]? = some ev) {x : ValidatorId}
    {u : GoldfishVote} (hnot : u ∉ poolList (worldAt (stateBefore c p a nr s rho i) x).st.core u.slot)
    (hin : u ∈ poolList (worldAt (stateBefore c p a nr s rho (i + 1)) x).st.core u.slot) :
    proposalTime s.e u.slot ≤ eventTime ev := by
  have hf : Fresh (worldAt (stateBefore c p a nr s rho i) x).st.core
      (worldAt (stateBefore c p a nr s rho (i + 1)) x).st.core := by
    rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev]
    exact worldStep_fresh c p a nr s _ ev x
  have hle : u.slot ≤ (worldAt (stateBefore c p a nr s rho (i + 1)) x).st.core.s := by
    rcases hf u hin with h | h
    · exact absurd h hnot
    · exact h
  rw [Proofs.Consensus.Clocks.clock_slot c p a nr s rho (i + 1) x] at hle
  have h0 := (Proofs.Consensus.Clocks.clock_le_event c p a nr s rho hs hnn (i + 1) x).1
  calc proposalTime s.e u.slot
      ≤ proposalTime s.e (slotOf s.e (worldAt (stateBefore c p a nr s rho (i + 1)) x).st.core.t) :=
        Proofs.Consensus.Clocks.proposalTime_mono s.e hδ hle
    _ ≤ (worldAt (stateBefore c p a nr s rho (i + 1)) x).st.core.t := Proofs.Consensus.Clocks.proposalTime_slotOf_le s.e hδ h0
    _ ≤ eventTime ev := Proofs.Consensus.Stamps.clock_succ_le_event c p a nr s rho hs hnn hev x

/-- **受理の時刻は投票の slot の提案の時刻以後**: honest でもなくてもよいノード `x` が添字 `i`・時刻 `t0` に投票 `u` を受理した
(`AcceptsAt`)なら `proposalTime u.slot ≤ t0`。`Settled.acceptsAt_gfVote_settled` の前提 `hlo`。 -/
theorem acceptsAt_gfVote_slot_le (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (hδ : 0 < s.e.delta) {i : Nat} {x : ValidatorId} {u : GoldfishVote} {t0 : Int}
    (hacc : AcceptsAt c p a nr s rho i x (NamedObject.GfVote u) t0) :
    proposalTime s.e u.slot ≤ t0 := by
  obtain ⟨⟨⟨ev, ⟨⟨hev, -⟩, hte⟩, -⟩, hnp⟩, hp⟩ := hacc
  rw [← hte]
  refine accepts_slot_le c p a nr s rho hs hnn hδ hev ?_ ((Proofs.Consensus.Delivery.processed_gfVote_iff _ u).mp hp)
  intro h
  exact hnp ((Proofs.Consensus.Delivery.processed_gfVote_iff _ u).mpr h)

end Run

end Proofs.Consensus.PoolSlot
