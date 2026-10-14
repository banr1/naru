import Proofs.Consensus.Clocks
import Proofs.Consensus.Delivery
import Proofs.Consensus.Voting
import Mathlib.Tactic

/-!
# 受信の直前の slot の窓(C71 の補題)

`Delivery.lean` の配送の経路は、受信の直前の受信者の slot `st.s` が投票の slot `u.slot` か `u.slot + 1`(`InWindow`)であることを
仮定する。配送(`nodeProcess`)は時計を進めないので、受信者の slot は受信の前の受信者自身の最後の tick で決まる(`Clocks.clock_slot`)。
ここではそれを run の事実から示す:
- 時計は添字について単調(`clock_mono`。自分の tick は時計をその event の時刻にし、それは直前の時計以上 — `Clocks.clock_le_event`)。
  したがって添字 `j < i` の自分の tick の時刻は `stateBefore i` の時計以下(`tick_le_clock`)。
- event が整列していれば、時刻が狭義に早い event は添字も前(`lt_of_time_lt`)。
- `ScheduleWellFormed` は honest なノードの公開時刻の tick を horizon まで run に入れ、slot の開始時刻(提案の時刻 `proposalTime k`、
  Δ の `4k` 倍)は公開時刻(`publicTime_proposalTime`)。
- よって honest な受信者への時刻 `t2` の配送の直前の slot は、`proposalTime k < t2` なら `k` 以上(その slot の開始の tick が配送より前、
  `slot_ge_of_deliver`)、`t2 < proposalTime (k + 1)` なら `k` 以下(時計は `t2` 以下、`slot_le_of_deliver`)。
- 投票の時刻は `proposalTime k + Δ` で slot の長さは `4Δ` なので、GST 以後に時刻 `t` に発行された投票が締切 `t + Δ` より前に
  (発行の時刻 `t` 以後に)配送されると、受信の直前の slot はちょうど `u.slot`(`slot_eq_of_deliver_gfVote`)で `InWindow`(`inWindow_of_deliver_gfVote`)。
  GST と無関係に(発行が GST の前でも)、配送の時刻が `proposalTime u.slot` より後で `proposalTime (u.slot + 2)` より前なら `InWindow`
  (`inWindow_of_deliver`)。
手書きの対応: `NamedRuntime.stateBefore_clock_mono`(`DecoupledConsensusProofs/Execution/Runtime.lean`)。窓の補題には手書きに同名のものは無く、
`on_goldfish_vote_insert` の窓の仮定を満たす側に当たる。
-/

namespace Proofs.Consensus.Window

open Model.Consensus.Objects.Time Model.Consensus.Objects.Parameters Model.Consensus.Objects.Identifiers
open Model.Consensus.Objects.Blocks
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Schedule
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Runs Proofs.Consensus.Signing Proofs.Consensus.Clocks

/-! ## slot と時刻の算術 -/

/-- slot の開始時刻は非負(Δ ≥ 0)。 -/
theorem proposalTime_nonneg (e : ProtocolEnv) (hδ : 0 ≤ e.delta) (k : Nat) : 0 ≤ proposalTime e k := by
  rw [proposalTime_eq]
  unfold slotStart
  have : (0 : Int) ≤ Int.ofNat k := Int.natCast_nonneg k
  positivity

/-- 次の slot の開始は `4Δ` 後。 -/
theorem proposalTime_succ (e : ProtocolEnv) (k : Nat) : proposalTime e (k + 1) = proposalTime e k + e.delta * 4 := by
  rw [proposalTime_eq, proposalTime_eq]
  unfold slotStart
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

/-- 投票の時刻は slot の開始の Δ 後。 -/
theorem voteTime_eq (e : ProtocolEnv) (k : Nat) : voteTime e k = proposalTime e k + e.delta := rfl

/-- slot の開始時刻は公開時刻(Δ の `4k` 倍)。 -/
theorem publicTime_proposalTime (e : ProtocolEnv) (k : Nat) : PublicTime e (proposalTime e k) := by
  refine ⟨4 * k, ?_⟩
  rw [proposalTime_eq]
  unfold slotStart
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

/-- `t < proposalTime (k + 1)` なら `slotOf t ≤ k`(`t ≥ 0`、Δ > 0)。 -/
theorem slotOf_le_of_lt (e : ProtocolEnv) (hδ : 0 < e.delta) {t : Int} (ht : 0 ≤ t) {k : Nat}
    (h : t < proposalTime e (k + 1)) : slotOf e t ≤ k := by
  by_contra hk
  have h1 := proposalTime_mono e hδ (show k + 1 ≤ slotOf e t by omega)
  have h2 := proposalTime_slotOf_le e hδ ht
  linarith

/-- `proposalTime k ≤ t` なら `k ≤ slotOf t`(Δ > 0)。 -/
theorem le_slotOf_of_le (e : ProtocolEnv) (hδ : 0 < e.delta) {t : Int} {k : Nat}
    (h : proposalTime e k ≤ t) : k ≤ slotOf e t := by
  have h1 := slotOf_mono e hδ h
  rwa [slotOf_proposalTime e hδ] at h1

/-! ## run の時計 -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 1 つの event で時計は戻らない(自分の tick はその event の時刻にし、それは直前の時計以上)。 -/
theorem clock_succ_ge (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (i : Nat) (v : ValidatorId) :
    (worldAt (stateBefore c p a nr s rho i) v).st.core.t ≤
      (worldAt (stateBefore c p a nr s rho (i + 1)) v).st.core.t := by
  cases hev : rho.events[i]? with
  | none =>
    rw [stateBefore_succ_of_none c p a nr s rho hev]
  | some ev =>
    rw [stateBefore_succ_of_get c p a nr s rho hev]
    cases ev with
    | Tick w t =>
      unfold worldStep
      dsimp only
      by_cases hwv : w = v
      · subst hwv
        rw [worldAt_insert_self, (nodeTick_clockIs c p a nr s w (worldAt (stateBefore c p a nr s rho i) w) t).1]
        exact (clock_le_event c p a nr s rho hs hnn i w).2 i _ le_rfl hev
      · rw [worldAt_insert_ne _ _ _ _ hwv]
    | Deliver w o t =>
      unfold worldStep
      dsimp only
      by_cases hwv : w = v
      · subst hwv
        rw [worldAt_insert_self, (nodeProcess_clock c p s (worldAt (stateBefore c p a nr s rho i) w) o).t]
      · rw [worldAt_insert_ne _ _ _ _ hwv]

/-- **時計は添字について単調**(手書き `stateBefore_clock_mono`)。 -/
theorem clock_mono (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    {i i' : Nat} (h : i ≤ i') (v : ValidatorId) :
    (worldAt (stateBefore c p a nr s rho i) v).st.core.t ≤
      (worldAt (stateBefore c p a nr s rho i') v).st.core.t := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (clock_succ_ge c p a nr s rho hs hnn _ v)

/-- 添字 `j < i` の `v` 自身の tick の時刻は、`stateBefore i` の `v` の時計以下。 -/
theorem tick_le_clock (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    {j i : Nat} (hji : j < i) {v : ValidatorId} {τ : Int}
    (hj : rho.events[j]? = some (NamedEvent.Tick v τ)) :
    τ ≤ (worldAt (stateBefore c p a nr s rho i) v).st.core.t := by
  have h1 : (worldAt (stateBefore c p a nr s rho (j + 1)) v).st.core.t = τ := by
    rw [stateBefore_succ_of_get c p a nr s rho hj]
    unfold worldStep
    dsimp only
    rw [worldAt_insert_self]
    exact (nodeTick_clockIs c p a nr s v (worldAt (stateBefore c p a nr s rho j) v) τ).1
  rw [← h1]
  exact clock_mono c p a nr s rho hs hnn hji v

end Run

/-- **時刻が狭義に早い event は添字も前**(event の整列)。 -/
theorem lt_of_time_lt {rho : NamedRun} (hs : EventsSorted rho) {i j : Nat} {x y : NamedEvent}
    (hi : rho.events[i]? = some x) (hj : rho.events[j]? = some y) (h : eventTime x < eventTime y) : i < j := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · exact hij
  · rw [hi] at hj
    cases hj
    exact absurd h (lt_irrefl _)
  · have hs' := hs j i hji
    simp only [hj, hi] at hs'
    exact absurd (time_le_of_key_ne_gt hs') (not_le.mpr h)

/-- honest なノードの公開時刻の tick は(horizon 以内なら)run のどこかの添字にある。 -/
theorem honest_tick_index {s : Model.Consensus.Execution.Setup.Setup} {rho : NamedRun}
    (hsch : ScheduleWellFormed s rho) {w : ValidatorId} (hw : rho.honest.contains w = true) {t : Int}
    (hpt : PublicTime s.e t) (h0 : 0 ≤ t) (hh : t ≤ rho.horizon) :
    ∃ j : Nat, rho.events[j]? = some (NamedEvent.Tick w t) := by
  obtain ⟨-, hticks⟩ := hsch
  have hin := hticks w t ⟨⟨⟨hw, hpt⟩, h0⟩, hh⟩
  rw [List.contains_iff_mem] at hin
  exact List.mem_iff_getElem?.mp hin

/-- `ScheduleWellFormed` の時刻の範囲: run の event の時刻は 0 以上 horizon 以下。 -/
theorem eventTime_bounds {s : Model.Consensus.Execution.Setup.Setup} {rho : NamedRun}
    (hsch : ScheduleWellFormed s rho) {ev : NamedEvent} (hev : ev ∈ rho.events) :
    0 ≤ eventTime ev ∧ eventTime ev ≤ rho.horizon := by
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hb⟩, -⟩, -⟩, -⟩ := hsch
  exact hb ev (List.contains_iff_mem.mpr hev)

/-- `ScheduleWellFormed` から event の整列。 -/
theorem eventsSorted_of_schedule {s : Model.Consensus.Execution.Setup.Setup} {rho : NamedRun}
    (hsch : ScheduleWellFormed s rho) : EventsSorted rho := by
  obtain ⟨⟨⟨⟨⟨⟨-, hs⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hsch
  exact hs

/-! ## 配送の直前の slot -/

section Deliver

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **配送の直前の slot の下限**: honest な `w` への時刻 `t2` の配送の直前、`proposalTime k < t2` なら `w` の slot は `k` 以上
(slot `k` の開始の tick は公開時刻で、配送より時刻が早いので添字も前)。 -/
theorem slot_ge_of_deliver (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {j : Nat} {w : ValidatorId}
    {o : NamedObject} {t2 : Int} (hw : rho.honest.contains w = true)
    (hj : rho.events[j]? = some (NamedEvent.Deliver w o t2)) {k : Nat} (hlo : proposalTime s.e k < t2) :
    k ≤ (worldAt (stateBefore c p a nr s rho j) w).st.core.s := by
  have hs := eventsSorted_of_schedule hsch
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev hev => (eventTime_bounds hsch hev).1
  have hb := eventTime_bounds hsch (List.mem_of_getElem? hj)
  obtain ⟨j', hj'⟩ := honest_tick_index hsch hw (publicTime_proposalTime s.e k)
    (proposalTime_nonneg s.e hδ.le k) (le_trans hlo.le hb.2)
  have hlt : j' < j := lt_of_time_lt hs hj' hj hlo
  have hle := tick_le_clock c p a nr s rho hs hnn hlt hj'
  rw [clock_slot c p a nr s rho j w]
  exact le_slotOf_of_le s.e hδ hle

/-- **配送の直前の slot の上限**: `t2 < proposalTime (k + 1)` なら `w` の slot は `k` 以下(配送の直前の時計は `t2` 以下)。 -/
theorem slot_le_of_deliver (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {j : Nat} {w : ValidatorId}
    {o : NamedObject} {t2 : Int} (hj : rho.events[j]? = some (NamedEvent.Deliver w o t2)) {k : Nat}
    (hhi : t2 < proposalTime s.e (k + 1)) :
    (worldAt (stateBefore c p a nr s rho j) w).st.core.s ≤ k := by
  have hs := eventsSorted_of_schedule hsch
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev hev => (eventTime_bounds hsch hev).1
  obtain ⟨h0, hle⟩ := clock_le_event c p a nr s rho hs hnn j w
  have hle' := hle j _ le_rfl hj
  rw [clock_slot c p a nr s rho j w]
  exact slotOf_le_of_lt s.e hδ h0 (lt_of_le_of_lt hle' hhi)

/-- **配送の直前の窓**: honest な `w` への時刻 `t2` の配送で `proposalTime u.slot < t2 < proposalTime (u.slot + 2)` なら、
受信の直前の `w` の store は `InWindow`。 -/
theorem inWindow_of_deliver (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {j : Nat} {w : ValidatorId}
    {u : GoldfishVote} {t2 : Int} (hw : rho.honest.contains w = true)
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.GfVote u) t2))
    (hlo : proposalTime s.e u.slot < t2) (hhi : t2 < proposalTime s.e (u.slot + 1 + 1)) :
    Proofs.Consensus.Delivery.InWindow (worldAt (stateBefore c p a nr s rho j) w).st.core u :=
  ⟨slot_ge_of_deliver c p a nr s rho hsch hδ hw hj hlo, slot_le_of_deliver c p a nr s rho hsch hδ hj hhi⟩

/-- **GST 以後の投票の配送の直前の slot はちょうど `u.slot`**: honest な `v` が時刻 `t`(`tGST ≤ t`)に発行した投票 `u` の、
honest な `w` への配送の時刻 `t2` が `t ≤ t2 < max t tGST + Δ` なら、`t = voteTime u.slot = proposalTime u.slot + Δ` で
`t2 < proposalTime u.slot + 2Δ < proposalTime (u.slot + 1)`。 -/
theorem slot_eq_of_deliver_gfVote (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {v w : ValidatorId}
    {u : GoldfishVote} {t t2 : Int} (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t)
    (hgst : s.e.tGST ≤ t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.GfVote u) t2))
    (ht : t ≤ t2) (ht2 : t2 < max t s.e.tGST + s.e.delta) :
    (worldAt (stateBefore c p a nr s rho j) w).st.core.s = u.slot := by
  obtain ⟨-, htv, -, hsl, -⟩ := Proofs.Consensus.Voting.emits_gfVote_shape c p a nr s rho hem
  rw [← hsl, voteTime_eq] at htv
  rw [max_eq_left hgst] at ht2
  have hsucc := proposalTime_succ s.e u.slot
  apply le_antisymm
  · exact slot_le_of_deliver c p a nr s rho hsch hδ hj (by linarith)
  · exact slot_ge_of_deliver c p a nr s rho hsch hδ hw hj (by linarith)

/-- GST 以後の投票の配送は受信の直前に `InWindow`(`Delivery.deliver_gfVote_mem` の窓の仮定)。 -/
theorem inWindow_of_deliver_gfVote (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {v w : ValidatorId}
    {u : GoldfishVote} {t t2 : Int} (hem : Emits c p a nr s rho v (NamedObject.GfVote u) t)
    (hgst : s.e.tGST ≤ t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.GfVote u) t2))
    (ht : t ≤ t2) (ht2 : t2 < max t s.e.tGST + s.e.delta) :
    Proofs.Consensus.Delivery.InWindow (worldAt (stateBefore c p a nr s rho j) w).st.core u := by
  have h := slot_eq_of_deliver_gfVote c p a nr s rho hsch hδ hem hgst hw hj ht ht2
  exact ⟨h.ge, by omega⟩

end Deliver

end Proofs.Consensus.Window
