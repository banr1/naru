import Statements.Consensus.Spec.Properties
import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.Clocks
import Proofs.Consensus.TreeInv
import Proofs.Consensus.Attribution
import Mathlib.Tactic

/-!
# 時刻 `t` の読みに未来の提案は入らない(C71 の補題)

property `NoFutureRead`(`Statements/Consensus/Spec/Properties.lean`): honest な `v` の時刻 `t` の出力 `g` の読みは、提案時刻が
`t` より後の slot `k` の honest な提案 `b` を接頭辞に含まない。筋(手書き `noFutureRead_of_store_mem` /
`block_slot_lt_of_mem_storeAt`、`DecoupledConsensusProofs/Bridge/FinalizedLive.lean`):
1. 出力の読みは store の tree の要素(`TreeInv.lean`)で tree は祖先について閉じているので、`b ⪯ 読み` なら `b ∈ tree`。
2. tree の genesis でないブロックは bodies の名前付きブロックの消去で(`Carrier.lean`)、bodies にブロックが入るのはブロックの受理
   (`onBlockUsing`)のときだけ。受理の守り `¬ (st.s < slot b)` から、入ったブロックの slot はそのときの store の slot 以下
   (`onBlockUsing_slot_le` → `bodies_entry_slot`)。store の slot は時計 `t` の slot で、時計はその event の時刻以下(`Clocks.lean`)なので、
   `proposalTime (slot b) ≤ slotTime (slotOf 時計) ≤ 時計 ≤ event の時刻 ≤ t`(`tree_block_slot`)。
3. honest な提案 `proposedBlockAt k` は slot `k` の genesis でないブロック(`proposedBlockAt_slot`: 提案の時計は `proposalTime k`
   なので `slotOf (proposalTime k) = k`)。したがって `proposalTime k ≤ t` となり `t < proposalTime k` に反する。
前提は `EventsSorted`、event の時刻が非負であること、Δ > 0 だけ(`ScheduleWellFormed` と `SetupWellFormed` から取る)。
-/

namespace Proofs.Consensus.NoFutureRead

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers
open Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick Model.Consensus.Protocol.Schedule
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Model.Consensus.Spec.Interface
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.NamedBlocks Proofs.Consensus.Blocks
open Proofs.Consensus.Carrier Proofs.Consensus.Signing Proofs.Consensus.Runs Proofs.Consensus.Attribution
open Proofs.Consensus.FinalizedAccountable Proofs.Consensus.Clocks Proofs.Consensus.Trees

/-! ## 受理の守り: 入ったブロックの slot は store の slot 以下 -/

/-- `onBlockUsing` が tree に入れたブロックの slot は store の slot 以下(最初の守り `¬ (st.s < slot b)`)。 -/
theorem onBlockUsing_slot_le (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : Model.Consensus.Protocol.ChainState.ChainState → Model.Consensus.Protocol.ChainState.ChainState)
    (hnb : b ∉ st.tree.elems) (hb : b ∈ (onBlockUsing c p st b build).tree.elems) : slot b ≤ st.s := by
  unfold onBlockUsing at hb
  split_ifs at hb with h1 h2 h3 h4
  · exact absurd hb hnb
  · exact absurd hb hnb
  · exact absurd hb hnb
  · exact absurd hb hnb
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1
    exact Nat.le_of_not_lt h1.1.1

/-- `processBlockCore` で bodies に入ったブロックは処理したブロックで、その slot は store の slot 以下。 -/
theorem processBlockCore_entry (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    {st : NamedStore} {B D : NamedBlock} (hD : D ∉ st.bodies.elems)
    (hD' : D ∈ (processBlockCore c p e hc cfg st B).bodies.elems) : D = B ∧ slot (eraseBlock B) ≤ st.core.s := by
  unfold processBlockCore at hD'
  split_ifs at hD' with hpar
  · exact absurd hD' hD
  · dsimp only at hD'
    unfold commitBlock at hD'
    dsimp only at hD'
    split_ifs at hD' with hcom
    · have hDB : D = B := by
        have h' : D ∈ (st.bodies.insert B).elems := hD'
        rw [mem_insert_iff nb_compare_eq_iff] at h'
        rcases h' with rfl | h'
        · rfl
        · exact absurd h' hD
      subst hDB
      refine ⟨rfl, ?_⟩
      obtain ⟨hnot, hin⟩ := (Bool.and_eq_true _ _).mp hcom
      have hnb : eraseBlock D ∉ st.core.tree.elems := by
        intro hm
        rw [← contains_iff_mem block_compare_eq_iff] at hm
        rw [hm] at hnot
        simp at hnot
      rw [contains_iff_mem block_compare_eq_iff] at hin
      rcases onBlockCheckedUsing_eq (fun cur => onBlockUsing c p cur (eraseBlock D)
          (fun ps => Model.Consensus.Protocol.ChainState.namedTransition e cfg ps D)) hc st.core (eraseBlock D)
          with hafter | hafter
      · rw [hafter] at hin
        exact onBlockUsing_slot_le c p st.core (eraseBlock D) _ hnb hin
      · rw [hafter] at hin
        exact absurd hin hnb
    · exact absurd hD' hD

theorem onBlockWith_entry (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) {st : NamedStore} {B D : NamedBlock}
    (hD : D ∉ st.bodies.elems) (hD' : D ∈ (onBlockWith c p adm e hc cfg st B).bodies.elems) :
    D = B ∧ slot (eraseBlock B) ≤ st.core.s := by
  unfold onBlockWith at hD'
  rw [admitCarried_bodies] at hD'
  exact processBlockCore_entry c p e hc cfg hD hD'

theorem receiptProcess_entry (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {st : NamedStore} {o : NamedObject} {D : NamedBlock}
    (hD : D ∉ st.bodies.elems) (hD' : D ∈ (receiptProcess c p s st o).bodies.elems) :
    slot (eraseBlock D) ≤ st.core.s := by
  cases o with
  | Block b =>
    obtain ⟨rfl, h⟩ := onBlockWith_entry c p CarriedAdmission.AlsoCarried s.e s.hc s.cfg hD hD'
    exact h
  | GfVote u => exact absurd hD' hD
  | Attest a =>
    have h : (receiptProcess c p s st (NamedObject.Attest a)).bodies = st.bodies := admitRow_bodies s.hc st a
    rw [h] at hD'
    exact absurd hD' hD

/-- 配送の処理で bodies に入ったブロックの slot は処理前の store の slot 以下。 -/
theorem nodeProcess_entry (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} {o : NamedObject} {D : NamedBlock}
    (hD : D ∉ n.st.bodies.elems) (hD' : D ∈ (nodeProcess c p s n o).st.bodies.elems) :
    slot (eraseBlock D) ≤ n.st.core.s :=
  receiptProcess_entry c p s hD hD'

theorem proposeBlockWith_entry (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} {D : NamedBlock} (hD : D ∉ st.bodies.elems)
    (hD' : D ∈ (proposeBlockWith c p nr cache e hc cfg nd st).1.bodies.elems) : slot (eraseBlock D) ≤ st.core.s := by
  unfold proposeBlockWith at hD'
  cases hm : proposalWith nr cache ProposalRowSource.PoolAndCarried e hc nd st with
  | none =>
    rw [hm] at hD'
    exact absurd hD' hD
  | some b =>
    rw [hm] at hD'
    obtain ⟨rfl, h⟩ := onBlockWith_entry c p CarriedAdmission.AlsoCarried e hc cfg hD hD'
    exact h

/-- 1 tick で bodies に入ったブロックの slot は tick の時刻の slot 以下(tick の冒頭で `s := slotOf e t`)。 -/
theorem tick_entry (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) {D : NamedBlock} (hD : D ∉ st.bodies.elems)
    (hD' : D ∈ (tick c p a nr cache e hc cfg nd st rec t).1.bodies.elems) : slot (eraseBlock D) ≤ slotOf e t := by
  unfold tick at hD'
  dsimp only at hD'
  split_ifs at hD'
  all_goals
    (try simp only [attestWith_bodies, namedUpdateConfirmationWith_bodies, namedGoldfishVoteWith_bodies] at hD')
  all_goals first
    | exact absurd hD' hD
    | exact proposeBlockWith_entry c p nr cache e hc cfg nd (st := { st with core := { st.core with t := t, s := slotOf e t } }) hD hD'

theorem nodeTick_entry (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) {D : NamedBlock} (hD : D ∉ n.st.bodies.elems)
    (hD' : D ∈ (nodeTick c p a nr s v n t).1.st.bodies.elems) : slot (eraseBlock D) ≤ slotOf s.e t := by
  unfold nodeTick profileTick at hD'
  dsimp only at hD'
  exact tick_entry c p a nr _ s.e s.hc s.cfg _ n.st n.signing t hD hD'

/-! ## run の中: bodies のブロックの提案時刻は、入った event の時刻以下 -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- `stateBefore i` のノード `u` の bodies の genesis でないブロックは、添字 `j < i` の `u` の event で入り、その提案時刻はその
event の時刻以下。 -/
theorem bodies_entry_slot (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (hδ : 0 < s.e.delta) : ∀ (i : Nat) (u : ValidatorId) (D : NamedBlock),
      D ∈ (worldAt (stateBefore c p a nr s rho i) u).st.bodies.elems →
      D = NamedBlock.Genesis ∨ ∃ (j : Nat) (ev : NamedEvent), j < i ∧ rho.events[j]? = some ev ∧ eventNode ev = u ∧
        proposalTime s.e (slot (eraseBlock D)) ≤ eventTime ev
  | 0, u, D, hD => by
    left
    have hD' : D ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hD
    exact (mem_singleton_iff _ _).mp hD'
  | i + 1, u, D, hD => by
    have lift : D = NamedBlock.Genesis ∨ (∃ (j : Nat) (ev : NamedEvent), j < i ∧ rho.events[j]? = some ev ∧
        eventNode ev = u ∧ proposalTime s.e (slot (eraseBlock D)) ≤ eventTime ev) →
        D = NamedBlock.Genesis ∨ ∃ (j : Nat) (ev : NamedEvent), j < i + 1 ∧ rho.events[j]? = some ev ∧
          eventNode ev = u ∧ proposalTime s.e (slot (eraseBlock D)) ≤ eventTime ev := by
      intro h
      rcases h with h | ⟨j, ev, hj, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, ev, Nat.lt_succ_of_lt hj, h⟩
    cases hev : rho.events[i]? with
    | none =>
      rw [stateBefore_succ_of_none c p a nr s rho hev] at hD
      exact lift (bodies_entry_slot hs hnn hδ i u D hD)
    | some ev =>
      rw [stateBefore_succ_of_get c p a nr s rho hev] at hD
      cases ev with
      | Tick w t =>
        unfold worldStep at hD
        dsimp only at hD
        by_cases hwu : w = u
        · subst hwu
          rw [worldAt_insert_self] at hD
          by_cases hold : D ∈ (worldAt (stateBefore c p a nr s rho i) w).st.bodies.elems
          · exact lift (bodies_entry_slot hs hnn hδ i w D hold)
          · right
            have hsl := nodeTick_entry c p a nr s w _ t hold hD
            refine ⟨i, NamedEvent.Tick w t, Nat.lt_succ_self i, hev, rfl, ?_⟩
            have ht : 0 ≤ t := hnn _ (List.mem_of_getElem? hev)
            exact (proposalTime_mono s.e hδ hsl).trans (proposalTime_slotOf_le s.e hδ ht)
        · rw [worldAt_insert_ne _ _ _ _ hwu] at hD
          exact lift (bodies_entry_slot hs hnn hδ i u D hD)
      | Deliver w o t =>
        unfold worldStep at hD
        dsimp only at hD
        by_cases hwu : w = u
        · subst hwu
          rw [worldAt_insert_self] at hD
          by_cases hold : D ∈ (worldAt (stateBefore c p a nr s rho i) w).st.bodies.elems
          · exact lift (bodies_entry_slot hs hnn hδ i w D hold)
          · right
            have hsl := nodeProcess_entry c p s hold hD
            rw [clock_slot c p a nr s rho i w] at hsl
            obtain ⟨h0, hle⟩ := clock_le_event c p a nr s rho hs hnn i w
            have hct := hle i (NamedEvent.Deliver w o t) (le_refl i) hev
            refine ⟨i, NamedEvent.Deliver w o t, Nat.lt_succ_self i, hev, rfl, ?_⟩
            show proposalTime s.e (slot (eraseBlock D)) ≤ t
            exact (proposalTime_mono s.e hδ hsl).trans ((proposalTime_slotOf_le s.e hδ h0).trans hct)
        · rw [worldAt_insert_ne _ _ _ _ hwu] at hD
          exact lift (bodies_entry_slot hs hnn hδ i u D hD)

/-- `EventsSorted` の下で `readAt t` はある `stateBefore i` で、その接頭辞の event の時刻は `t` 以下。 -/
theorem readAt_eq_stateBefore' (hs : EventsSorted rho) (t : Int) :
    ∃ i, readAt c p a nr s rho t = stateBefore c p a nr s rho i ∧
      ∀ (j : Nat) (ev : NamedEvent), j < i → rho.events[j]? = some ev → eventTime ev ≤ t := by
  obtain ⟨i, hi⟩ := filter_le_eq_take t rho.events (pairwise_of_eventsSorted rho hs)
  refine ⟨i, by unfold readAt stateBefore; rw [hi], fun j ev hj hev => ?_⟩
  have hmem : ev ∈ rho.events.take i := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, by rw [List.getElem?_take_of_lt hj]; exact hev⟩
  rw [← hi] at hmem
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

/-- 時刻 `t` の読みの tree の genesis でないブロックの提案時刻は `t` 以下。手書き `block_slot_lt_of_mem_storeAt`。 -/
theorem tree_block_slot (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (hδ : 0 < s.e.delta) (u : ValidatorId) (t : Int) {B : Block}
    (hB : B ∈ (storeAt c p a nr s rho u t).core.tree.elems) :
    B = Block.Genesis ∨ proposalTime s.e (slot B) ≤ t := by
  obtain ⟨i₀, hi₀, hbound⟩ := readAt_eq_stateBefore' c p a nr s rho hs t
  unfold storeAt at hB
  rw [hi₀] at hB
  obtain ⟨D, hD, rfl⟩ := (stateBefore_inv c p a nr s rho i₀ u).named B hB
  rcases bodies_entry_slot c p a nr s rho hs hnn hδ i₀ u D hD with rfl | ⟨j, ev, hj, hev, -, hle⟩
  · exact Or.inl rfl
  · exact Or.inr (hle.trans (hbound j ev hj hev))

/-! ## honest な提案の形 -/

/-- `proposalWith` の結果は、store の slot を持つ genesis でないブロック。 -/
theorem proposalWith_slot {nr : ValidatorId → Nat → BlockId} {cache : Model.Consensus.Protocol.Grades.Cache}
    {src : ProposalRowSource} {e : ProtocolEnv} {hc : Model.Consensus.Protocol.Grades.HealConfig}
    {nd : Model.Consensus.Protocol.Schedule.Node} {st : NamedStore} {D : NamedBlock}
    (h : proposalWith nr cache src e hc nd st = some D) : D ≠ NamedBlock.Genesis ∧ slot (eraseBlock D) = st.core.s := by
  unfold proposalWith at h
  dsimp only at h
  obtain ⟨parent, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨fun h => NamedBlock.noConfusion h, rfl⟩

/-- slot `k` の honest な提案 `proposedBlockAt k` は、slot `k` の genesis でないブロック(提案の時計は `proposalTime k`)。
手書き `proposedBlockAt_slot` / `proposedBlockAt_proposer`。 -/
theorem proposedBlockAt_slot (hδ : 0 < s.e.delta) {k : Nat} {D : NamedBlock}
    (h : proposedBlockAt c p a nr s rho k = some D) : D ≠ NamedBlock.Genesis ∧ slot (eraseBlock D) = k := by
  unfold proposedBlockAt at h
  dsimp only at h
  obtain ⟨hne, hslot⟩ := proposalWith_slot h
  refine ⟨hne, ?_⟩
  rw [hslot]
  show slotOf s.e (proposalTime s.e k) = k
  exact slotOf_proposalTime s.e hδ k

theorem eraseBlock_eq_genesis {D : NamedBlock} (h : eraseBlock D = Block.Genesis) : D = NamedBlock.Genesis := by
  cases D with
  | Genesis => rfl
  | Node p s r v sup rows i => cases h

/-! ## 本体 -/

/-- 出力 `g` の読みはどれも tree の要素なので、未来の honest な提案を接頭辞に含まない。 -/
theorem noFutureRead (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (hδ : 0 < s.e.delta) (g : Output) : NoFutureRead c p a nr s rho g := by
  unfold NoFutureRead
  intro v t k b hh hpre
  obtain ⟨⟨-, hprop⟩, hlt⟩ := hh
  unfold HonestProposalAt at hprop
  obtain ⟨-, hpb⟩ := hprop
  unfold proposedBlock at hpb
  obtain ⟨D, hD, rfl⟩ := Option.map_eq_some_iff.mp hpb
  obtain ⟨hne, hslot⟩ := proposedBlockAt_slot c p a nr s rho hδ hD
  have hmem : eraseBlock D ∈ (storeAt c p a nr s rho v t).core.tree.elems :=
    ancestor_mem_tree (tree_closed (readAt_inv c p a nr s rho t v)) hpre (outputAt_mem c p a nr g s rho v t)
  rcases tree_block_slot c p a nr s rho hs hnn hδ v t hmem with hgen | hle
  · exact hne (eraseBlock_eq_genesis hgen)
  · rw [hslot] at hle
    exact absurd hlt (not_lt.mpr hle)

/-- `ScheduleWellFormed` から `EventsSorted` と event の時刻の非負。 -/
theorem schedule_facts (hsch : ScheduleWellFormed s rho) :
    EventsSorted rho ∧ ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := by
  unfold ScheduleWellFormed at hsch
  obtain ⟨⟨⟨⟨⟨⟨-, hsorted⟩, -⟩, htimes⟩, -⟩, -⟩, -⟩ := hsch
  refine ⟨hsorted, fun ev hev => ?_⟩
  exact (htimes ev ((List.contains_iff_mem).mpr hev)).1

/-- `ExecutionValid` の下で、どの出力も未来の提案を含まない(Δ > 0)。 -/
theorem noFutureRead_of_executionValid (hexec : ExecutionValid c p a nr s rho) (hδ : 0 < s.e.delta) (g : Output) :
    NoFutureRead c p a nr s rho g := by
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, -⟩, -⟩ := hexec
  obtain ⟨hs, hnn⟩ := schedule_facts s rho hsch
  exact noFutureRead c p a nr s rho hs hnn hδ g

end Run

end Proofs.Consensus.NoFutureRead
