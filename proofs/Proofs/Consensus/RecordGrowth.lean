import Model.Consensus.Spec.Interface
import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.ConfirmationRecords
import Proofs.Consensus.Signing
import Proofs.Consensus.Runs
import Proofs.Consensus.FinalizedAccountable
import Mathlib.Tactic

/-!
# run に沿った確認・stable の記録(C71 の liveness 系 claim の足場)

`ConfirmationRecords.lean` の店の事実(記録を書くのは自分の tick の `updateConfirmationWith` だけで、それは互換な接頭辞を保つ)を
run に沿って積み上げる。ノード `v` の記録 `recAt R v i`(`R` は `latestConfirmed` か `latestStable`)が変わるのは `v` 自身の tick の
添字だけで(`recAt_succ`)、添字 `m` の記録の接頭辞 `B` は、`[m, n)` の `v` の各 tick の直後の記録と互換なら添字 `n` でも接頭辞
(`prefix_preserved`。手書き `latest_prefix_preserved`)。
時刻の読み `storeAt v t` は `filter (eventTime ≤ t)` の長さ `idx t` の `stateBefore`(`storeAt_eq_recAt`)で、`EventsSorted` の下で
`idx` より前の event の時刻は `t` 以下(`time_le_of_lt_idx`)、`idx` 以降の event の時刻は `t` より後(`lt_of_idx_le`。ここでは event の
重複の無さ `List.Nodup`(`EventsNodup` から `nodup_of_eventsNodup`)を使って示す)。`v` の tick(添字 `i`、時刻 `τ`)の直後の記録は時刻 `τ` の
読みの記録(`recAt_tick_eq_storeAt`。手書き `latest_after_tick_eq_storeAt`: 同じ時刻の後続の event に `v` の tick は無い — ここで重複の無さが
本質的に要る: 同じ `Tick v τ` が 2 度あれば結論は偽)。
これらから、「`v` の記録は時刻 `t` 以後のどの時刻の記録とも互換」(一致)なら「`v` の記録は時刻 `t` から単調」
(`record_mono_of_compatible`。手書き `latest_confirmed_mono_of_agreement`)。claim `available` の `SafeFrom` の単調性の側を
一致の側に還元する補題で、`Outputs.lean` が出力 `getConfirmed` / `getStable` に転送する。
手書き `DecoupledConsensusProofs/Protocol/Handlers/Monotone.lean` の後半の筋。
-/

namespace Proofs.Consensus.RecordGrowth

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Protocol.Store Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Blocks Proofs.Consensus.ConfirmationRecords Proofs.Consensus.Signing Proofs.Consensus.Runs
open Proofs.Consensus.FinalizedAccountable

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字 `i` の直前のノード `v` の記録 `R`。 -/
def recAt (R : Store → Block) (v : ValidatorId) (i : Nat) : Block :=
  R (worldAt (stateBefore c p a nr s rho i) v).st.core

/-- 添字 `i` の event がノード `v` のものでなければ `v` の状態は変わらない。 -/
theorem node_succ_other {i : Nat} {ev : NamedEvent} (hi : rho.events[i]? = some ev) (v : ValidatorId)
    (hne : eventNode ev ≠ v) :
    worldAt (stateBefore c p a nr s rho (i + 1)) v = worldAt (stateBefore c p a nr s rho i) v := by
  rw [stateBefore_succ_of_get c p a nr s rho hi]
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    exact worldAt_insert_ne _ _ _ _ hne
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    exact worldAt_insert_ne _ _ _ _ hne

/-- `v` 自身の tick の直後の状態はその tick の出力。 -/
theorem node_succ_tick {i : Nat} {v : ValidatorId} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t)) :
    worldAt (stateBefore c p a nr s rho (i + 1)) v =
      (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).1 := by
  rw [stateBefore_succ_of_get c p a nr s rho hi]
  unfold worldStep
  dsimp only
  rw [worldAt_insert_self]

/-- `v` への配送の直後の状態はその処理の出力。 -/
theorem node_succ_deliver {i : Nat} {v : ValidatorId} {o : Model.Consensus.Execution.Objects.NamedObject} {t : Int}
    (hi : rho.events[i]? = some (NamedEvent.Deliver v o t)) :
    worldAt (stateBefore c p a nr s rho (i + 1)) v =
      nodeProcess c p s (worldAt (stateBefore c p a nr s rho i) v) o := by
  rw [stateBefore_succ_of_get c p a nr s rho hi]
  unfold worldStep
  dsimp only
  rw [worldAt_insert_self]

/-- 配送で変わらない記録 `R` は、添字 `i` の event が `v` 自身の tick でなければ変わらず、tick ならその tick の出力の記録。 -/
theorem recAt_succ (R : Store → Block) (hProc : ∀ n o, R (nodeProcess c p s n o).st.core = R n.st.core)
    (i : Nat) (v : ValidatorId) :
    recAt c p a nr s rho R v (i + 1) = recAt c p a nr s rho R v i ∨
      ∃ t, rho.events[i]? = some (NamedEvent.Tick v t) ∧
        recAt c p a nr s rho R v (i + 1) =
          R (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).1.st.core := by
  unfold recAt
  cases hev : rho.events[i]? with
  | none => exact Or.inl (by rw [stateBefore_succ_of_none c p a nr s rho hev])
  | some ev =>
    cases ev with
    | Tick u t =>
      by_cases huv : u = v
      · subst huv
        exact Or.inr ⟨t, rfl, by rw [node_succ_tick c p a nr s rho hev]⟩
      · left
        rw [node_succ_other c p a nr s rho hev v huv]
    | Deliver u o t =>
      left
      by_cases huv : u = v
      · subst huv
        rw [node_succ_deliver c p a nr s rho hev, hProc]
      · rw [node_succ_other c p a nr s rho hev v huv]

/-- `[m, n)` に `v` の tick が無ければ記録は変わらない。手書き `latest_at_prefix_eq_of_no_tick`。 -/
theorem recAt_const (R : Store → Block) (hProc : ∀ n o, R (nodeProcess c p s n o).st.core = R n.st.core)
    (v : ValidatorId) {m : Nat} :
    ∀ n, m ≤ n → (∀ i t, m ≤ i → i < n → rho.events[i]? ≠ some (NamedEvent.Tick v t)) →
      recAt c p a nr s rho R v n = recAt c p a nr s rho R v m := by
  intro n
  induction n with
  | zero => intro hm _; rw [Nat.le_zero.mp hm]
  | succ n ih =>
    intro hm hno
    by_cases hmn : m ≤ n
    · rw [← ih hmn (fun i t hmi hin => hno i t hmi (Nat.lt_succ_of_lt hin))]
      rcases recAt_succ c p a nr s rho R hProc n v with h | ⟨t, ht, -⟩
      · exact h
      · exact absurd ht (hno n t hmn (Nat.lt_succ_self n))
    · have : m = n + 1 := by omega
      rw [this]

/-- 添字 `m` の記録の接頭辞 `B` は、`[m, n)` の `v` の各 tick の直後の記録と互換なら、添字 `n` でも接頭辞。
手書き `latest_prefix_preserved`。 -/
theorem prefix_preserved (R : Store → Block) (hProc : ∀ n o, R (nodeProcess c p s n o).st.core = R n.st.core)
    (hTick : ∀ v n t, Keeps (R n.st.core) (R (nodeTick c p a nr s v n t).1.st.core))
    (v : ValidatorId) {B : Block} {m : Nat} (hold : preceq B (recAt c p a nr s rho R v m) = true) :
    ∀ n, m ≤ n →
      (∀ i t, m ≤ i → i < n → rho.events[i]? = some (NamedEvent.Tick v t) →
        compatible B (recAt c p a nr s rho R v (i + 1)) = true) →
      preceq B (recAt c p a nr s rho R v n) = true := by
  intro n
  induction n with
  | zero => intro hm _; rw [Nat.le_zero.mp hm] at hold; exact hold
  | succ n ih =>
    intro hm hcompat
    by_cases hmn : m ≤ n
    · have hprev := ih hmn (fun i t hmi hin hev => hcompat i t hmi (Nat.lt_succ_of_lt hin) hev)
      rcases recAt_succ c p a nr s rho R hProc n v with h | ⟨t, ht, h⟩
      · rw [h]; exact hprev
      · have hc := hcompat n t hmn (Nat.lt_succ_self n) ht
        rw [h] at hc ⊢
        exact hTick v _ t B hprev hc
    · have : m = n + 1 := by omega
      rw [this] at hold
      exact hold

/-! ## 時刻の読みと添字 -/

/-- 時刻 `t` の読みの添字: `filter (eventTime ≤ t)` の長さ。 -/
def idx (t : Int) : Nat := (rho.events.filter (fun ev => decide (eventTime ev ≤ t))).length

/-- `EventsSorted` の下で `filter (≤ t)` は長さ `idx t` の接頭辞。 -/
theorem filter_eq_take_idx (hs : EventsSorted rho) (t : Int) :
    rho.events.filter (fun ev => decide (eventTime ev ≤ t)) = rho.events.take (idx rho t) := by
  unfold idx
  obtain ⟨i, hi⟩ := filter_le_eq_take t rho.events (pairwise_of_eventsSorted rho hs)
  rw [hi, List.length_take]
  rcases le_total i rho.events.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.take_length, List.take_of_length_le h]

/-- 時刻 `t` の読みは添字 `idx t` の直前の状態。 -/
theorem readAt_eq_stateBefore_idx (hs : EventsSorted rho) (t : Int) :
    readAt c p a nr s rho t = stateBefore c p a nr s rho (idx rho t) := by
  unfold readAt stateBefore
  rw [filter_eq_take_idx rho hs]

theorem storeAt_eq_recAt (hs : EventsSorted rho) (R : Store → Block) (v : ValidatorId) (t : Int) :
    R (storeAt c p a nr s rho v t).core = recAt c p a nr s rho R v (idx rho t) := by
  unfold storeAt recAt
  rw [readAt_eq_stateBefore_idx c p a nr s rho hs]

/-- `t ≤ t2` なら `idx t ≤ idx t2`(`filter (≤ t)` は `filter (≤ t2)` の接頭辞)。 -/
theorem idx_mono (hs : EventsSorted rho) {t t2 : Int} (h : t ≤ t2) : idx rho t ≤ idx rho t2 := by
  unfold idx
  obtain ⟨l2, hl2⟩ := filter_le_append t t2 h rho.events (pairwise_of_eventsSorted rho hs)
  rw [hl2, List.length_append]
  exact Nat.le_add_right _ _

/-- `idx t` より前の event の時刻は `t` 以下。 -/
theorem time_le_of_lt_idx (hs : EventsSorted rho) {t : Int} {j : Nat} (hj : j < idx rho t) {ev : NamedEvent}
    (hev : rho.events[j]? = some ev) : eventTime ev ≤ t := by
  have hmem : ev ∈ rho.events.take (idx rho t) := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, by rw [List.getElem?_take_of_lt hj]; exact hev⟩
  rw [← filter_eq_take_idx rho hs] at hmem
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

/-- `EventsNodup` から `List.Nodup`。 -/
theorem nodup_of_eventsNodup (hnd : EventsNodup rho) : rho.events.Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj
  have h := hnd i j hij
  cases hi' : rho.events[i]? with
  | none => rw [List.getElem?_eq_none_iff] at hi'; omega
  | some x =>
    cases hj' : rho.events[j]? with
    | none => rw [List.getElem?_eq_none_iff] at hj'; omega
    | some y =>
      simp only [hi', hj'] at h
      intro hxy
      exact h (Option.some.inj hxy)

/-- `idx t` 以降の event の時刻は `t` より後(event の重複が無いとき)。 -/
theorem lt_of_idx_le (hs : EventsSorted rho) (hnd : rho.events.Nodup) {t : Int} {j : Nat} (hj : idx rho t ≤ j)
    {ev : NamedEvent} (hev : rho.events[j]? = some ev) : t < eventTime ev := by
  by_contra hle
  have hle' : eventTime ev ≤ t := not_lt.mp hle
  have hmem : ev ∈ rho.events.filter (fun ev => decide (eventTime ev ≤ t)) :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? hev, decide_eq_true hle'⟩
  rw [filter_eq_take_idx rho hs, List.mem_iff_getElem?] at hmem
  obtain ⟨k, hk⟩ := hmem
  rw [List.getElem?_take] at hk
  split at hk
  · rename_i hki
    have hkl : k < rho.events.length := (List.getElem?_eq_some_iff.mp hk).1
    have hkj : k = j := (List.Nodup.getElem?_inj hkl hnd).mp (hk.trans hev.symm)
    omega
  · exact absurd hk (by simp)

/-- `v` の tick(添字 `i`、時刻 `τ`)の直後の記録は時刻 `τ` の読みの記録: 添字 `i + 1` から `idx τ` までの event はすべて時刻 `τ` で、
その中に `v` の tick は無い(あれば添字 `i` の event と同じで重複)。手書き `latest_after_tick_eq_storeAt`。 -/
theorem recAt_tick_eq_storeAt (hs : EventsSorted rho) (hnd : rho.events.Nodup) (R : Store → Block)
    (hProc : ∀ n o, R (nodeProcess c p s n o).st.core = R n.st.core) {v : ValidatorId} {i : Nat} {τ : Int}
    (hi : rho.events[i]? = some (NamedEvent.Tick v τ)) :
    recAt c p a nr s rho R v (i + 1) = R (storeAt c p a nr s rho v τ).core := by
  rw [storeAt_eq_recAt c p a nr s rho hs R v τ]
  have hlt : i < idx rho τ := by
    by_contra hge
    have := lt_of_idx_le rho hs hnd (not_lt.mp hge) hi
    exact absurd this (lt_irrefl _)
  symm
  apply recAt_const c p a nr s rho R hProc v (idx rho τ) hlt
  intro k τ' hik hk hev
  have hτ' : τ' ≤ τ := time_le_of_lt_idx rho hs hk hev
  have hpair := pairwise_of_eventsSorted rho hs
  have hil : i < rho.events.length := (List.getElem?_eq_some_iff.mp hi).1
  have hkl : k < rho.events.length := (List.getElem?_eq_some_iff.mp hev).1
  have hττ' : τ ≤ τ' := by
    have := List.pairwise_iff_getElem.mp hpair i k hil hkl (by omega)
    rw [List.getElem?_eq_some_iff] at hi hev
    obtain ⟨_, hi⟩ := hi
    obtain ⟨_, hev⟩ := hev
    rw [hi, hev] at this
    exact this
  have heq : τ' = τ := le_antisymm hτ' hττ'
  subst heq
  have : k = i := (List.Nodup.getElem?_inj hkl hnd).mp (hev.trans hi.symm)
  omega

/-! ## 一致から単調性 -/

/-- 記録 `R` の時刻 `t` の値が時刻 `t` 以後(`t2` まで)のどの時刻の値とも互換なら、時刻 `t` の値は時刻 `t2` の値の接頭辞。
`EventsSorted` と event の重複の無さだけを使う。手書き `latest_confirmed_mono_of_agreement`。 -/
theorem record_mono_of_compatible (hs : EventsSorted rho) (hnd : rho.events.Nodup) (R : Store → Block)
    (hProc : ∀ n o, R (nodeProcess c p s n o).st.core = R n.st.core)
    (hTick : ∀ v n t, Keeps (R n.st.core) (R (nodeTick c p a nr s v n t).1.st.core))
    (v : ValidatorId) {t t2 : Int} (htt2 : t ≤ t2)
    (hcompat : ∀ τ, t ≤ τ → τ ≤ t2 →
      compatible (R (storeAt c p a nr s rho v t).core) (R (storeAt c p a nr s rho v τ).core) = true) :
    preceq (R (storeAt c p a nr s rho v t).core) (R (storeAt c p a nr s rho v t2).core) = true := by
  rw [storeAt_eq_recAt c p a nr s rho hs R v t2]
  apply prefix_preserved c p a nr s rho R hProc hTick v
    (by rw [storeAt_eq_recAt c p a nr s rho hs R v t]; exact preceq_self _) (idx rho t2) (idx_mono rho hs htt2)
  intro j τ hij hj hev
  rw [recAt_tick_eq_storeAt c p a nr s rho hs hnd R hProc hev]
  have h1 : t < τ := lt_of_idx_le rho hs hnd hij hev
  have h2 : τ ≤ t2 := time_le_of_lt_idx rho hs hj hev
  exact hcompat τ h1.le h2

/-- 確認の記録 `latestConfirmed` に対する `record_mono_of_compatible`。 -/
theorem confirmed_mono_of_compatible (hs : EventsSorted rho) (hnd : rho.events.Nodup) (v : ValidatorId) {t t2 : Int}
    (htt2 : t ≤ t2)
    (hcompat : ∀ τ, t ≤ τ → τ ≤ t2 →
      compatible (storeAt c p a nr s rho v t).core.latestConfirmed (storeAt c p a nr s rho v τ).core.latestConfirmed = true) :
    preceq (storeAt c p a nr s rho v t).core.latestConfirmed (storeAt c p a nr s rho v t2).core.latestConfirmed = true :=
  record_mono_of_compatible c p a nr s rho hs hnd (fun st => st.latestConfirmed)
    (fun n o => (nodeProcess_rec c p s n o).confirmed) (fun v n t => nodeTick_confirmed_keeps c p a nr s v n t) v htt2 hcompat

/-- stable の記録 `latestStable` に対する `record_mono_of_compatible`。 -/
theorem stable_mono_of_compatible (hs : EventsSorted rho) (hnd : rho.events.Nodup) (v : ValidatorId) {t t2 : Int}
    (htt2 : t ≤ t2)
    (hcompat : ∀ τ, t ≤ τ → τ ≤ t2 →
      compatible (storeAt c p a nr s rho v t).core.latestStable (storeAt c p a nr s rho v τ).core.latestStable = true) :
    preceq (storeAt c p a nr s rho v t).core.latestStable (storeAt c p a nr s rho v t2).core.latestStable = true :=
  record_mono_of_compatible c p a nr s rho hs hnd (fun st => st.latestStable)
    (fun n o => (nodeProcess_rec c p s n o).stable) (fun v n t => nodeTick_stable_keeps c p a nr s v n t) v htt2 hcompat

end Run

end Proofs.Consensus.RecordGrowth
