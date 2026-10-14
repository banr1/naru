import Model.Consensus.Execution.Run
import Model.Consensus.Protocol.Schedule
import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.Runs
import Proofs.Consensus.Signing
import Mathlib.Tactic

/-!
# 時計と slot(C71 の補題)

生成 Model の store(`Model/Consensus/Protocol/Store.lean`)の時計 `t` と slot `s` について:
- 時刻の算術: `slotStart δ k = (δ · 4) · k`、`slotOfTime δ t = ⌊t / (δ · 4)⌋`(`Int.fdiv`、`toNat`)で、Δ > 0 なら
  `slotStart δ (slotOfTime δ t) ≤ t`(`t ≥ 0`)、`slotOfTime` / `slotStart` は単調、`slotOfTime δ (slotStart δ k) = k`。
- store のハンドラのうち時計を書くのは tick の冒頭(`t := t`、`s := slotOf e t`)だけで、配送の処理(`nodeProcess`)と tick の務め
  (提案・投票・確認・attestation)は `t` / `s` を変えない(`SameClock`)。したがって `nodeTick` の後の時計は `(t, slotOf e t)`
  (`nodeTick_clockIs`)。
- run では、ノード `v` の `stateBefore i` の時計は初期値 `(0, 0)` か `v` の最後の tick の時刻で、常に `s = slotOf e t`(`clock_slot`)。
  event が整列していて時刻が非負なら、時計は非負で、添字 `i` 以降のどの event の時刻以下(`clock_le_event`)。
手書き `NamedStoreBridge.slotOfClock_stateBefore` / `NamedRuntime.stateBefore_clock_le_event` / `stateBefore_clock_mono`
(`DecoupledConsensusProofs/Protocol/Handlers/StoreBridge.lean` / `Execution/Runtime.lean`)に当たる。
-/

namespace Proofs.Consensus.Clocks

open Model.Consensus.Objects.Time Model.Consensus.Objects.Parameters Model.Consensus.Objects.Identifiers
open Model.Consensus.Objects.Blocks
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals
open Model.Consensus.Protocol.Tick Model.Consensus.Protocol.Schedule
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Runs Proofs.Consensus.Signing

/-! ## slot と時刻の算術 -/

/-- slot の開始時刻はその時刻以前(`t ≥ 0`、Δ > 0)。 -/
theorem slotStart_slotOfTime_le (δ : Int) (hδ : 0 < δ) {t : Int} (ht : 0 ≤ t) :
    slotStart δ (slotOfTime δ t) ≤ t := by
  unfold slotStart slotOfTime
  have hb : (0 : Int) < δ * 4 := by linarith
  rw [Int.fdiv_eq_ediv_of_nonneg _ hb.le]
  have hnn : 0 ≤ t / (δ * 4) := Int.ediv_nonneg ht hb.le
  rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg hnn, mul_comm]
  exact Int.ediv_mul_le t hb.ne'

/-- `slotOfTime` は時刻について単調(Δ > 0)。 -/
theorem slotOfTime_mono (δ : Int) (hδ : 0 < δ) {t t' : Int} (h : t ≤ t') :
    slotOfTime δ t ≤ slotOfTime δ t' := by
  unfold slotOfTime
  have hb : (0 : Int) < δ * 4 := by linarith
  rw [Int.fdiv_eq_ediv_of_nonneg _ hb.le, Int.fdiv_eq_ediv_of_nonneg _ hb.le]
  exact Int.toNat_le_toNat (Int.ediv_le_ediv hb h)

/-- slot の開始時刻の slot はその slot(Δ > 0)。 -/
theorem slotOfTime_slotStart (δ : Int) (hδ : 0 < δ) (k : Nat) : slotOfTime δ (slotStart δ k) = k := by
  unfold slotOfTime slotStart
  have hb : (0 : Int) < δ * 4 := by linarith
  rw [Int.fdiv_eq_ediv_of_nonneg _ hb.le, Int.mul_ediv_cancel_left _ hb.ne']
  simp

/-- `slotStart` は slot について単調(Δ > 0)。 -/
theorem slotStart_mono (δ : Int) (hδ : 0 < δ) {k k' : Nat} (h : k ≤ k') :
    slotStart δ k ≤ slotStart δ k' := by
  unfold slotStart
  have hb : (0 : Int) ≤ δ * 4 := by linarith
  simp only [Int.ofNat_eq_natCast]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) hb

/-- `proposalTime e k = slotTime e k = slotStart e.delta k`。 -/
theorem proposalTime_eq (e : ProtocolEnv) (k : Nat) : proposalTime e k = slotStart e.delta k := rfl

theorem proposalTime_slotOf_le (e : ProtocolEnv) (hδ : 0 < e.delta) {t : Int} (ht : 0 ≤ t) :
    proposalTime e (slotOf e t) ≤ t :=
  slotStart_slotOfTime_le e.delta hδ ht

theorem proposalTime_mono (e : ProtocolEnv) (hδ : 0 < e.delta) {k k' : Nat} (h : k ≤ k') :
    proposalTime e k ≤ proposalTime e k' :=
  slotStart_mono e.delta hδ h

theorem slotOf_proposalTime (e : ProtocolEnv) (hδ : 0 < e.delta) (k : Nat) :
    slotOf e (proposalTime e k) = k :=
  slotOfTime_slotStart e.delta hδ k

theorem slotOf_mono (e : ProtocolEnv) (hδ : 0 < e.delta) {t t' : Int} (h : t ≤ t') :
    slotOf e t ≤ slotOf e t' :=
  slotOfTime_mono e.delta hδ h

/-! ## `Store` のハンドラは時計を変えない -/

/-- 時計の欄(`t` / `s`)が等しい。 -/
structure SameClock (a b : Store) : Prop where
  t : a.t = b.t
  s : a.s = b.s

theorem SameClock.refl (a : Store) : SameClock a a := ⟨rfl, rfl⟩

theorem SameClock.trans {a b c : Store} (h1 : SameClock a b) (h2 : SameClock b c) : SameClock a c :=
  ⟨h1.t.trans h2.t, h1.s.trans h2.s⟩

theorem onGoldfishVote_clock (st : Store) (u : GoldfishVote) : SameClock (onGoldfishVote st u) st := by
  unfold onGoldfishVote
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem onGoldfishVoteChecked_clock (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    SameClock (onGoldfishVoteChecked c st u) st := by
  unfold onGoldfishVoteChecked
  split_ifs
  · exact SameClock.refl _
  · exact onGoldfishVote_clock st u

theorem foldl_clock {β : Type} (g : Store → β → Store) (hg : ∀ s x, SameClock (g s x) s) :
    ∀ (l : List β) (s : Store), SameClock (List.foldl g s l) s
  | [], _ => SameClock.refl _
  | x :: l, s => by
    rw [List.foldl_cons]
    exact (foldl_clock g hg l _).trans (hg s x)

theorem onSgVote_clock (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (a : CombinedAttestation) :
    SameClock (onSgVote hc st a) st := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem updateConfirmationWith_clock (c : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (k : Nat) :
    SameClock (updateConfirmationWith c e hc st k) st := ⟨rfl, rfl⟩

theorem goldfishVoteWith_clock (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : Store) : SameClock (goldfishVoteWith c cache e hc nd st).1 st := by
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · exact onGoldfishVoteChecked_clock c st _
  · exact SameClock.refl _

theorem updateFinality_clock (st : Store) (σ : Model.Consensus.Protocol.ChainState.ChainState) :
    SameClock (updateFinality st σ) st := by
  unfold updateFinality
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem onBlockUsing_clock (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : Model.Consensus.Protocol.ChainState.ChainState → Model.Consensus.Protocol.ChainState.ChainState) :
    SameClock (onBlockUsing c p st b build) st := by
  unfold onBlockUsing
  split_ifs
  · exact SameClock.refl _
  · exact SameClock.refl _
  · exact SameClock.refl _
  · exact SameClock.refl _
  · dsimp only
    exact (updateFinality_clock _ _).trans
      ((foldl_clock _ (fun s u => onGoldfishVoteChecked_clock c s u) _ _).trans ⟨rfl, rfl⟩)

theorem onBlockCheckedUsing_clock (handle : Store → Store) (hh : ∀ s, SameClock (handle s) s)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : Store) (b : Block) :
    SameClock (onBlockCheckedUsing handle hc st b) st := by
  unfold onBlockCheckedUsing
  split_ifs
  · exact hh st
  · exact SameClock.refl _

/-! ## `NamedStore` のハンドラ -/

theorem commitBlock_clock (before : NamedStore) (after : Store) (b : Model.Consensus.Objects.NamedBlocks.NamedBlock) :
    SameClock (commitBlock before after b).core after := by
  unfold commitBlock
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem processBlockCore_clock (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    (st : NamedStore) (B : Model.Consensus.Objects.NamedBlocks.NamedBlock) :
    SameClock (processBlockCore c p e hc cfg st B).core st.core := by
  unfold processBlockCore
  split_ifs
  · exact SameClock.refl _
  · dsimp only
    exact (commitBlock_clock _ _ _).trans
      (onBlockCheckedUsing_clock _ (fun s => onBlockUsing_clock c p s _ _) hc _ _)

theorem admitRow_clock (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : NamedStore)
    (row : Model.Consensus.Objects.NamedBlocks.NamedAttestation) : SameClock (admitRow hc st row).core st.core := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact onSgVote_clock hc st.core _

theorem admitRows_clock (hc : Model.Consensus.Protocol.Grades.HealConfig) :
    ∀ (rows : List Model.Consensus.Objects.NamedBlocks.NamedAttestation) (st : NamedStore),
      SameClock (admitRows hc st rows).core st.core
  | [], _ => SameClock.refl _
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_clock hc rows (admitRow hc st row)
    unfold admitRows at ih
    exact ih.trans (admitRow_clock hc st row)

theorem admitCarried_clock (adm : CarriedAdmission) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (before after : NamedStore) (b : Model.Consensus.Objects.NamedBlocks.NamedBlock) :
    SameClock (admitCarried adm hc before after b).core after.core := by
  unfold admitCarried
  split_ifs
  · exact admitRows_clock hc _ _
  · exact SameClock.refl _

theorem onBlockWith_clock (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (st : NamedStore)
    (b : Model.Consensus.Objects.NamedBlocks.NamedBlock) :
    SameClock (onBlockWith c p adm e hc cfg st b).core st.core := by
  unfold onBlockWith
  exact (admitCarried_clock _ _ _ _ _).trans (processBlockCore_clock c p e hc cfg st b)

theorem receiptProcess_clock (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (st : NamedStore) (o : Model.Consensus.Execution.Objects.NamedObject) :
    SameClock (receiptProcess c p s st o).core st.core := by
  cases o with
  | Block b => exact onBlockWith_clock c p _ _ _ _ st b
  | GfVote u => exact onGoldfishVoteChecked_clock c st.core u
  | Attest a => exact admitRow_clock s.hc st a

/-- 配送の処理は時計を変えない。 -/
theorem nodeProcess_clock (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState) (o : Model.Consensus.Execution.Objects.NamedObject) :
    SameClock (nodeProcess c p s n o).st.core n.st.core :=
  receiptProcess_clock c p s n.st o

/-! ## tick の後の時計は `(t, slotOf e t)` -/

/-- store の時計が `(t, sl)`。 -/
def ClockIs (st : NamedStore) (t : Int) (sl : Nat) : Prop := st.core.t = t ∧ st.core.s = sl

theorem ClockIs.of_same {st st' : NamedStore} {t : Int} {sl : Nat} (h : ClockIs st t sl)
    (hs : SameClock st'.core st.core) : ClockIs st' t sl :=
  ⟨hs.t.trans h.1, hs.s.trans h.2⟩

theorem proposeBlockWith_clockIs (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {e : ProtocolEnv} {cfg : Model.Consensus.Protocol.ChainState.HeightConfig} {st : NamedStore} {t : Int} {sl : Nat}
    (h : ClockIs st t sl) : ClockIs (proposeBlockWith c p nr cache e hc cfg nd st).1 t sl := by
  unfold proposeBlockWith
  split
  · exact h
  · rename_i b _
    exact h.of_same (onBlockWith_clock c p CarriedAdmission.AlsoCarried e hc cfg st b)

theorem namedGoldfishVoteWith_clockIs (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {e : ProtocolEnv} {st : NamedStore} {t : Int} {sl : Nat} (h : ClockIs st t sl) :
    ClockIs (namedGoldfishVoteWith c cache e hc nd st).1 t sl := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out hm
  show ClockIs { st with core := core } t sl
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [hm]
  refine h.of_same ?_
  show SameClock core st.core
  rw [h1]
  exact goldfishVoteWith_clock c cache e hc nd st.core

theorem namedUpdateConfirmationWith_clockIs (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) {e : ProtocolEnv} {st : NamedStore} {t : Int} {sl : Nat}
    (h : ClockIs st t sl) (k : Nat) : ClockIs (namedUpdateConfirmationWith cache e hc st k) t sl :=
  h.of_same (updateConfirmationWith_clock cache e hc st.core k)

theorem attestWith_clockIs (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {e : ProtocolEnv} {st : NamedStore} {t : Int} {sl : Nat} (h : ClockIs st t sl)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    ClockIs (attestWith cache e hc nd st rec).1 t sl := by
  unfold attestWith
  split
  exact h.of_same (admitRow_clock hc st _)

/-- 1 tick の後の時計は `(t, slotOf e t)`(冒頭で合わせた時計を務めが変えない。`tick_inv` と同じ 16 経路)。 -/
theorem tick_clockIs (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    ClockIs (tick c p a nr cache e hc cfg nd st rec t).1 t (slotOf e t) := by
  have h0 : ClockIs { st with core := { st.core with t := t, s := slotOf e t } } t (slotOf e t) := ⟨rfl, rfl⟩
  unfold tick
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact attestWith_clockIs cache hc nd (namedUpdateConfirmationWith_clockIs cache hc (namedGoldfishVoteWith_clockIs c cache hc nd (proposeBlockWith_clockIs c p nr cache hc nd h0)) _) _
    | with_reducible exact attestWith_clockIs cache hc nd (namedUpdateConfirmationWith_clockIs cache hc (namedGoldfishVoteWith_clockIs c cache hc nd h0) _) _
    | with_reducible exact attestWith_clockIs cache hc nd (namedUpdateConfirmationWith_clockIs cache hc (proposeBlockWith_clockIs c p nr cache hc nd h0) _) _
    | with_reducible exact attestWith_clockIs cache hc nd (namedUpdateConfirmationWith_clockIs cache hc h0 _) _
    | with_reducible exact attestWith_clockIs cache hc nd (namedGoldfishVoteWith_clockIs c cache hc nd (proposeBlockWith_clockIs c p nr cache hc nd h0)) _
    | with_reducible exact attestWith_clockIs cache hc nd (namedGoldfishVoteWith_clockIs c cache hc nd h0) _
    | with_reducible exact attestWith_clockIs cache hc nd (proposeBlockWith_clockIs c p nr cache hc nd h0) _
    | with_reducible exact attestWith_clockIs cache hc nd h0 _
    | with_reducible exact namedUpdateConfirmationWith_clockIs cache hc (namedGoldfishVoteWith_clockIs c cache hc nd (proposeBlockWith_clockIs c p nr cache hc nd h0)) _
    | with_reducible exact namedUpdateConfirmationWith_clockIs cache hc (namedGoldfishVoteWith_clockIs c cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_clockIs cache hc (proposeBlockWith_clockIs c p nr cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_clockIs cache hc h0 _
    | with_reducible exact namedGoldfishVoteWith_clockIs c cache hc nd (proposeBlockWith_clockIs c p nr cache hc nd h0)
    | with_reducible exact namedGoldfishVoteWith_clockIs c cache hc nd h0
    | with_reducible exact proposeBlockWith_clockIs c p nr cache hc nd h0
    | with_reducible exact h0

/-- Tick の処理の後の時計は `(t, slotOf e t)`。 -/
theorem nodeTick_clockIs (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) (t : Int) : ClockIs (nodeTick c p a nr s v n t).1.st t (slotOf s.e t) := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_clockIs c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-! ## run の中の時計 -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- run のどの添字・どのノードでも `s = slotOf e t`(初期は `(0, 0)`、変わるのは自分の tick だけ)。
手書き `slotOfClock_stateBefore`。 -/
theorem clock_slot : ∀ (i : Nat) (v : ValidatorId),
    (worldAt (stateBefore c p a nr s rho i) v).st.core.s = slotOf s.e (worldAt (stateBefore c p a nr s rho i) v).st.core.t
  | 0, _ => rfl
  | i + 1, v => by
    cases hev : rho.events[i]? with
    | none =>
      rw [stateBefore_succ_of_none c p a nr s rho hev]
      exact clock_slot i v
    | some ev =>
      rw [stateBefore_succ_of_get c p a nr s rho hev]
      cases ev with
      | Tick w t =>
        unfold worldStep
        dsimp only
        by_cases hwv : w = v
        · subst hwv
          rw [worldAt_insert_self]
          have h := nodeTick_clockIs c p a nr s w (worldAt (stateBefore c p a nr s rho i) w) t
          rw [h.1, h.2]
        · rw [worldAt_insert_ne _ _ _ _ hwv]
          exact clock_slot i v
      | Deliver w o t =>
        unfold worldStep
        dsimp only
        by_cases hwv : w = v
        · subst hwv
          rw [worldAt_insert_self]
          have h := nodeProcess_clock c p s (worldAt (stateBefore c p a nr s rho i) w) o
          rw [h.s, h.t]
          exact clock_slot i w
        · rw [worldAt_insert_ne _ _ _ _ hwv]
          exact clock_slot i v

/-- event が整列していて時刻が非負なら、`stateBefore i` の時計は非負で、添字 `i` 以降の event の時刻以下。
手書き `stateBefore_clock_le_event` / `stateBefore_clock_mono`。 -/
theorem clock_le_event (hs : Statements.Consensus.Spec.Conditions.EventsSorted rho)
    (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev) : ∀ (i : Nat) (v : ValidatorId),
      0 ≤ (worldAt (stateBefore c p a nr s rho i) v).st.core.t ∧
      ∀ (j : Nat) (ev : NamedEvent), i ≤ j → rho.events[j]? = some ev →
        (worldAt (stateBefore c p a nr s rho i) v).st.core.t ≤ eventTime ev
  | 0, v => by
    refine ⟨?_, fun j ev _ hj => ?_⟩
    · show (0 : Int) ≤ 0
      exact le_refl _
    · show (0 : Int) ≤ eventTime ev
      exact hnn ev (List.mem_of_getElem? hj)
  | i + 1, v => by
    obtain ⟨ih0, ihle⟩ := clock_le_event hs hnn i v
    cases hev : rho.events[i]? with
    | none =>
      rw [stateBefore_succ_of_none c p a nr s rho hev]
      exact ⟨ih0, fun j ev hij hj => ihle j ev (Nat.le_of_succ_le hij) hj⟩
    | some ev =>
      rw [stateBefore_succ_of_get c p a nr s rho hev]
      cases ev with
      | Tick w t =>
        unfold worldStep
        dsimp only
        by_cases hwv : w = v
        · subst hwv
          rw [worldAt_insert_self]
          rw [(nodeTick_clockIs c p a nr s w (worldAt (stateBefore c p a nr s rho i) w) t).1]
          refine ⟨hnn _ (List.mem_of_getElem? hev), fun j ev' hij hj => ?_⟩
          have hs' := hs i j hij
          simp only [hev, hj] at hs'
          exact time_le_of_key_ne_gt hs'
        · rw [worldAt_insert_ne _ _ _ _ hwv]
          exact ⟨ih0, fun j ev' hij hj => ihle j ev' (Nat.le_of_succ_le hij) hj⟩
      | Deliver w o t =>
        unfold worldStep
        dsimp only
        by_cases hwv : w = v
        · subst hwv
          rw [worldAt_insert_self]
          rw [(nodeProcess_clock c p s (worldAt (stateBefore c p a nr s rho i) w) o).t]
          exact ⟨ih0, fun j ev' hij hj => ihle j ev' (Nat.le_of_succ_le hij) hj⟩
        · rw [worldAt_insert_ne _ _ _ _ hwv]
          exact ⟨ih0, fun j ev' hij hj => ihle j ev' (Nat.le_of_succ_le hij) hj⟩

end Run

end Proofs.Consensus.Clocks
