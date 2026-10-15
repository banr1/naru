import Proofs.Consensus.Proposal
import Mathlib.Tactic

/-!
# tree のブロックの slot は時計の slot 以下で、発行されたブロックの親の slot はブロックの slot より小さい(C71 の補題)

`BlockReceipt.Admits` の 5 つの守りのうち `parent_slot`(`slot (parent b) < slot b`)を、発行されたブロックについて run の事実から
示す。`Proposal` が示したとおり、提案の務めのブロック `D` の名前付きの親は提案者の tick の前の bodies にあり、slot は
`slotOf e t`(`t` は提案の時刻)。ここでは次の 2 つを足して親の slot を抑える:
- **tree の slot の不変条件** `SlotInv`: tree のブロックの slot は store の slot 以下。tree を育てるのは `onBlockUsing` の受理だけで、
  その守り `st.s < slot b` を通ったブロックは slot が `st.s` 以下(`onBlockUsing_step`)。他のハンドラは tree と時計を変えず、
  tick は時計を `slotOf e t` に進めてから務めを走らせる(`tick_fresh`)。初期の tree `{Genesis}` の slot は 0。時計の slot は
  添字について単調(`Clocks.clock_slot` と `Window.clock_succ_ge`)なので、run のどの添字でも成り立つ(`stateBefore_slotInv`)。
- **tick の直前の時計は tick の時刻より狭義に前**: 時計は初期の 0 か、それより前の自分の tick の時刻(`clock_origin`)で、
  同じ tick の event は 2 度現れない(`EventsNodup`)から、正の時刻の tick の直前の時計はその時刻より前(`clock_lt_of_tick`)。
  提案の時刻 `proposalTime k`(`0 < k`)より前の時計の slot は `k` より小さい(`slot_lt_of_tick`)。
したがって発行されたブロック `D` の名前付きの親の消去(`Carrier.StoreInv.tree`)は提案者の tick の直前の tree にあり、
その slot は直前の時計の slot 以下、すなわちブロックの slot より小さい(`emits_block_parent_slot`)。
あわせて名前付きの親が発行の添字の直前の提案者の bodies にあること(`emits_block_parent_mem`)も run に持ち上げる。

手書きでは `DecoupledConsensusProofs/Generic/SlotFreshness.lean` の `block_slot_lt_of_mem_beforeTime_of_le_proposal`
(提案の時刻より前の読みの tree のブロックの slot は提案の slot より小さい)に当たり、`Protocol/ChainState/ProposalBridge.lean` の
`proposedBlockAt_admit` がそれを提案のブロックの親に当てる(受理の守りの親の slot の条件)。
-/

namespace Proofs.Consensus.ParentSlot

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.StoreBase
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.Carrier
open Proofs.Consensus.Clocks (SameClock)

/-! ## 新しいブロックの slot -/

/-- 新しいブロックの slot: `b` の tree のブロックは `a` の tree にもあったか、slot が `b` の slot 以下。 -/
def Fresh (a b : Store) : Prop :=
  ∀ B, B ∈ b.tree.elems → B ∈ a.tree.elems ∨ slot B ≤ b.s

/-- 時計を変えないハンドラの 1 段: 新しいブロックの slot・時計の一致。 -/
structure Step (a b : Store) : Prop where
  fresh : Fresh a b
  clock : SameClock b a

theorem Step.refl (a : Store) : Step a a := ⟨fun _ h => Or.inl h, SameClock.refl a⟩

theorem Step.trans {a b d : Store} (h1 : Step a b) (h2 : Step b d) : Step a d := by
  refine ⟨fun B hB => ?_, h2.clock.trans h1.clock⟩
  rcases h2.fresh B hB with hb | hd
  · rcases h1.fresh B hb with ha | hle
    · exact Or.inl ha
    · exact Or.inr (by rw [h2.clock.s]; exact hle)
  · exact Or.inr hd

/-- tree と時計が等しい store の間は 1 段。 -/
theorem Step.of_same {a b : Store} (htr : b.tree = a.tree) (hc : SameClock b a) : Step a b :=
  ⟨fun B hB => Or.inl (by rw [← htr]; exact hB), hc⟩

/-! ## tree を触らない `Store` のハンドラ -/

theorem onGoldfishVote_step (st : Store) (x : GoldfishVote) : Step st (onGoldfishVote st x) := by
  unfold onGoldfishVote
  split_ifs <;> exact Step.of_same rfl ⟨rfl, rfl⟩

theorem onGoldfishVoteChecked_step (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    Step st (onGoldfishVoteChecked c st u) := by
  unfold onGoldfishVoteChecked
  split_ifs
  · exact Step.refl st
  · exact onGoldfishVote_step st u

theorem onSgVote_step (hc : HealConfig) (st : Store) (a : CombinedAttestation) : Step st (onSgVote hc st a) := by
  unfold onSgVote
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

/-- **受理の守り `st.s < slot b` を通ったブロックだけが tree に入る**: `onBlockUsing` の後の tree のブロックは元の tree に
あったか、slot が store の slot 以下。 -/
theorem onBlockUsing_step (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) : Step st (onBlockUsing c p st b build) := by
  have hcl := Proofs.Consensus.Clocks.onBlockUsing_clock c p st b build
  refine ⟨fun B hB => ?_, hcl⟩
  rw [hcl.s]
  revert hB
  unfold onBlockUsing
  split_ifs with h1
  · exact Or.inl
  · exact Or.inl
  · exact Or.inl
  · exact Or.inl
  · intro hB
    have hle : slot b ≤ st.s := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1
      exact Nat.le_of_not_lt h1.1.1
    change B ∈ (acceptBody c st b _).tree.elems at hB
    rw [acceptBody_tree, mem_insert_iff block_compare_eq_iff] at hB
    rcases hB with rfl | hB
    · exact Or.inr hle
    · exact Or.inl hB

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

/-- 1 tick の務め `tick` の後の tree のブロックは、tick の前の tree にあったか、slot が tick の後の slot 以下
(時計合わせの後の store からの `Step`。`BlockStamps.tick_grow` と同じ 16 経路)。 -/
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
  exact fun B hB => hfin.fresh B hB

theorem nodeTick_fresh (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) : Fresh n.st.core (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_fresh c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-! ## world と run -/

/-- 1 event の後、どのノードの store も、新しいブロックの slot はその store の slot 以下。 -/
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

/-- tree の slot の不変条件: tree のブロックの slot は store の slot 以下。 -/
def SlotInv (st : Store) : Prop :=
  ∀ B, B ∈ st.tree.elems → slot B ≤ st.s

theorem SlotInv.of_fresh {a b : Store} (h : SlotInv a) (hf : Fresh a b) (hs : a.s ≤ b.s) : SlotInv b := fun B hB => by
  rcases hf B hB with ha | hle
  · exact le_trans (h B ha) hs
  · exact hle

/-- 初期の store: tree は `{Genesis}` で、genesis の slot は 0。 -/
theorem initial_slotInv : SlotInv initStore := fun B hB => by
  have hB' : B ∈ (NaruStd.Set.singleton Block.Genesis).elems := hB
  rw [mem_singleton_iff] at hB'
  subst hB'
  exact le_refl _

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 1 つの event で時計の slot は戻らない(`s = slotOf e t` と時計の単調性)。 -/
theorem slot_succ_ge (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (hδ : 0 < s.e.delta) (i : Nat) (v : ValidatorId) :
    (worldAt (stateBefore c p a nr s rho i) v).st.core.s ≤
      (worldAt (stateBefore c p a nr s rho (i + 1)) v).st.core.s := by
  rw [Proofs.Consensus.Clocks.clock_slot c p a nr s rho i v, Proofs.Consensus.Clocks.clock_slot c p a nr s rho (i + 1) v]
  exact Proofs.Consensus.Clocks.slotOf_mono s.e hδ (Proofs.Consensus.Window.clock_succ_ge c p a nr s rho hs hnn i v)

/-- **run のどの添字・どのノードでも tree のブロックの slot は store の slot 以下**(event の整列と時刻の非負、Δ > 0 の下で)。 -/
theorem stateBefore_slotInv (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (hδ : 0 < s.e.delta) : ∀ (i : Nat) (v : ValidatorId), SlotInv (worldAt (stateBefore c p a nr s rho i) v).st.core
  | 0, _ => initial_slotInv
  | i + 1, v => by
    have ih := stateBefore_slotInv hs hnn hδ i v
    refine ih.of_fresh ?_ (slot_succ_ge c p a nr s rho hs hnn hδ i v)
    rw [Proofs.Consensus.Signing.stateBefore_succ]
    cases rho.events[i]? with
    | none => exact (Step.refl _).fresh
    | some ev =>
      show Fresh _ (worldAt (worldStep c p a nr s (stateBefore c p a nr s rho i) ev) v).st.core
      exact worldStep_fresh c p a nr s _ ev v

/-! ## tick の直前の時計 -/

/-- **時計の由来**: `stateBefore i` の `v` の時計は初期の 0 か、`i` より前の `v` 自身の tick の時刻。 -/
theorem clock_origin : ∀ (i : Nat) (v : ValidatorId),
    (worldAt (stateBefore c p a nr s rho i) v).st.core.t = 0 ∨
      ∃ j : Nat, j < i ∧ rho.events[j]? = some (NamedEvent.Tick v (worldAt (stateBefore c p a nr s rho i) v).st.core.t)
  | 0, _ => Or.inl rfl
  | i + 1, v => by
    cases hev : rho.events[i]? with
    | none =>
      rw [Proofs.Consensus.Signing.stateBefore_succ_of_none c p a nr s rho hev]
      rcases clock_origin i v with h | ⟨j, hj, hjev⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hjev⟩
    | some ev =>
      rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev]
      cases ev with
      | Tick w t =>
        unfold worldStep
        dsimp only
        by_cases hwv : w = v
        · subst hwv
          rw [Proofs.Consensus.Signing.worldAt_insert_self,
            (Proofs.Consensus.Clocks.nodeTick_clockIs c p a nr s w (worldAt (stateBefore c p a nr s rho i) w) t).1]
          exact Or.inr ⟨i, Nat.lt_succ_self i, hev⟩
        · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwv]
          rcases clock_origin i v with h | ⟨j, hj, hjev⟩
          · exact Or.inl h
          · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hjev⟩
      | Deliver w o t =>
        unfold worldStep
        dsimp only
        by_cases hwv : w = v
        · subst hwv
          rw [Proofs.Consensus.Signing.worldAt_insert_self,
            (Proofs.Consensus.Clocks.nodeProcess_clock c p s (worldAt (stateBefore c p a nr s rho i) w) o).t]
          rcases clock_origin i w with h | ⟨j, hj, hjev⟩
          · exact Or.inl h
          · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hjev⟩
        · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwv]
          rcases clock_origin i v with h | ⟨j, hj, hjev⟩
          · exact Or.inl h
          · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hjev⟩

/-- **正の時刻の tick の直前の時計は、その時刻より前**(同じ tick の event は 2 度現れない)。 -/
theorem clock_lt_of_tick (hs : EventsSorted rho) (hnd : EventsNodup rho)
    (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev) {i : Nat} {v : ValidatorId} {t : Int}
    (hi : rho.events[i]? = some (NamedEvent.Tick v t)) (ht : 0 < t) :
    (worldAt (stateBefore c p a nr s rho i) v).st.core.t < t := by
  have hle : (worldAt (stateBefore c p a nr s rho i) v).st.core.t ≤ t :=
    (Proofs.Consensus.Clocks.clock_le_event c p a nr s rho hs hnn i v).2 i _ le_rfl hi
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    rcases clock_origin c p a nr s rho i v with h0 | ⟨j, hj, hjev⟩
    · rw [h0] at heq
      exact absurd heq.symm (ne_of_gt ht)
    · rw [heq] at hjev
      have h := hnd j i hj
      simp only [hjev, hi] at h
      exact h rfl

/-- **提案の時刻の tick の直前の slot は、提案の slot より小さい**(`0 < k`、Δ > 0)。 -/
theorem slot_lt_of_tick (hs : EventsSorted rho) (hnd : EventsNodup rho)
    (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev) (hδ : 0 < s.e.delta) {i : Nat} {v : ValidatorId} {k : Nat}
    (hk : 0 < k) (hi : rho.events[i]? = some (NamedEvent.Tick v (proposalTime s.e k))) :
    (worldAt (stateBefore c p a nr s rho i) v).st.core.s < k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hpos : 0 < proposalTime s.e (k' + 1) := by
    rw [Proofs.Consensus.Window.proposalTime_succ]
    have := Proofs.Consensus.Window.proposalTime_nonneg s.e hδ.le k'
    linarith
  have hlt := clock_lt_of_tick c p a nr s rho hs hnd hnn hi hpos
  have h0 := (Proofs.Consensus.Clocks.clock_le_event c p a nr s rho hs hnn i v).1
  rw [Proofs.Consensus.Clocks.clock_slot c p a nr s rho i v]
  have := Proofs.Consensus.Window.slotOf_le_of_lt s.e hδ h0 hlt
  omega

/-! ## 発行されたブロックの親 -/

/-- **発行されたブロックの名前付きの親は、発行の添字の直前の提案者の bodies にある**(`Proposal.nodeTick_block_fields`)。 -/
theorem emits_block_parent_mem {v : ValidatorId} {D : NamedBlock} {t : Int}
    (h : Emits c p a nr s rho v (NamedObject.Block D) t) :
    ∃ i, rho.events[i]? = some (NamedEvent.Tick v t) ∧
      namedParent D ∈ (worldAt (stateBefore c p a nr s rho i) v).st.bodies.elems := by
  obtain ⟨i, hi, ho⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t).mp h
  obtain ⟨-, -, -, -, -, hpar⟩ := Proofs.Consensus.Proposal.nodeTick_block_fields c p a nr s v _ t ho
  exact ⟨i, hi, hpar⟩

/-- **発行されたブロックの親の slot はブロックの slot より小さい**(`Admits.parent_slot`): 親は提案者の tick の直前の tree に
あり(`Carrier.StoreInv.tree`)、その slot は直前の slot 以下(`stateBefore_slotInv`)で、直前の slot は提案の slot より小さい
(`slot_lt_of_tick`)。 -/
theorem emits_block_parent_slot (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {v : ValidatorId}
    {D : NamedBlock} {t : Int} (h : Emits c p a nr s rho v (NamedObject.Block D) t) :
    slot (parent (eraseBlock D)) < slot (eraseBlock D) := by
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev hev =>
    (Proofs.Consensus.Window.eventTime_bounds hsch hev).1
  have hnd : EventsNodup rho := by
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := hsch
    exact hnd
  obtain ⟨i, hi, ho⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t).mp h
  obtain ⟨h0, ht, hsl, -, -, hpar⟩ := Proofs.Consensus.Proposal.nodeTick_block_fields c p a nr s v _ t ho
  have hmem := (stateBefore_inv c p a nr s rho i v).tree _ hpar
  have hle := stateBefore_slotInv c p a nr s rho hs hnn hδ i v _ hmem
  rw [ht] at hi
  have hlt := slot_lt_of_tick c p a nr s rho hs hnd hnn hδ h0 hi
  rw [Proofs.Consensus.NamedBlocks.parent_eraseBlock, hsl]
  omega

end Run

end Proofs.Consensus.ParentSlot
