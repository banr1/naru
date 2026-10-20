import Proofs.Consensus.Stamps
import Proofs.Consensus.Settled
import Proofs.Consensus.Voting
import Mathlib.Tactic

/-!
# 配送で pool に入った投票の印はその時の時計で、受理の時刻は印の次の公開時刻より前(C71 の補題)

`Stamps` は pool の投票の受信の印の上界(印は時計以下。`Stamps.Fresh` / `Stamps.stamp_le_of_mem`)を示す。この節は配送の 1 段に
限って下界を足す: 配送の処理(`nodeProcess`)で鍵 `u.slot` の pool に新しく入った投票 `u` の印は、ちょうどその時の時計
(`Stamp.At st.t`)。印を書くのは `onGoldfishVote` だけで、配送の処理は時計を変えないので、`Stamps.Step` の `Fresh` の不等号を
等号にした `EStep` が配送の処理の各ハンドラで成り立つ(`nodeProcess_estep`)。

honest なノードは公開時刻(Δ の倍数)ごとに tick する(`ScheduleWellFormed`)ので、時刻 `t0` の配送の前の時計は `t0` 以下の最大の
公開時刻以上(`deliver_lt_clock_add`)。したがって配送で受理された投票の印が公開時刻 `γ` より前なら、受理の時刻 `t0` も `γ` より前。
自分の tick で受理した投票は自分の投票で、その時刻は投票時刻(`Voting.emits_gfVote_shape`)。合わせて、honest なノードの pool の
投票のうち印が支持の締切より前のものは、支持の締切より前に受理された(`acceptsAt_lt_supportCutoff`)。

手書きでは `DecoupledConsensusProofs/Protocol/Handlers/AcceptanceTiming.lean` の `confirmationVotesAcceptedInWindow_of_admissible`
(最初の受理と一度だけ書かれる印の運び)に当たる。手書きの印は受理の時刻そのものなので、時計と公開時刻の差を埋める段は naru の
Model の時計(直前の tick の時刻)に合わせたもの。
-/

namespace Proofs.Consensus.StampExact

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Time Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Tables Proofs.Consensus.Carrier
open Proofs.Consensus.Votes Proofs.Consensus.Clocks Proofs.Consensus.Signing
open Proofs.Consensus.Stamps (Keep gv_get?_insert_self gv_get?_insert_ne onGoldfishVote_cases)

/-- 新しい投票の印は時計そのもの: `b` の鍵 `u.slot` の pool の投票は `a` にもあったか、受信の印が `b` の時計の時刻。 -/
def FreshAt (a b : Store) : Prop :=
  ∀ u, u ∈ poolList b u.slot → u ∈ poolList a u.slot ∨ b.timestampVote.get? u = some (Stamp.At b.t)

/-- 時計を変えないハンドラの 1 段で、新しい投票の印が時計そのもの(`Stamps.Step` の `Fresh` を等号にしたもの)。 -/
structure EStep (a b : Store) : Prop where
  keep : Keep a b
  fresh : FreshAt a b
  clock : SameClock b a

theorem EStep.refl (a : Store) : EStep a a := ⟨Stamps.Keep.refl a, fun _ h => Or.inl h, SameClock.refl a⟩

theorem EStep.trans {a b d : Store} (h1 : EStep a b) (h2 : EStep b d) : EStep a d := by
  refine ⟨h1.keep.trans h2.keep, fun u hu => ?_, h2.clock.trans h1.clock⟩
  rcases h2.fresh u hu with hb | hd
  · rcases h1.fresh u hb with ha | hτ
    · exact Or.inl ha
    · obtain ⟨-, heq⟩ := h2.keep u hb
      exact Or.inr (by rw [heq, hτ, h2.clock.t])
  · exact Or.inr hd

/-- pool・印の表・時計が等しい store の間は 1 段(何も増えない)。 -/
theorem EStep.of_same {a b : Store} (hg : b.gfVotes = a.gfVotes) (htv : b.timestampVote = a.timestampVote)
    (hc : SameClock b a) : EStep a b := by
  have hp : ∀ k, poolList b k = poolList a k := fun k => by unfold poolList; rw [hg]
  exact ⟨fun u hu => ⟨by rw [hp]; exact hu, by rw [htv]⟩, fun u hu => Or.inl (by rw [← hp]; exact hu), hc⟩

theorem onGoldfishVote_estep (st : Store) (x : GoldfishVote) : EStep st (onGoldfishVote st x) := by
  rcases onGoldfishVote_cases st x with h | ⟨hx, htv⟩
  · rw [h]; exact EStep.refl st
  · refine ⟨fun u hu => ⟨?_, ?_⟩, fun u hu => ?_, onGoldfishVote_clock st x⟩
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
          refine Or.inr ?_
          rw [htv, (onGoldfishVote_clock st u).t]
          exact gv_get?_insert_self _ _ _

theorem onGoldfishVoteChecked_estep (c : Nat → NaruStd.Set ValidatorId) (st : Store) (u : GoldfishVote) :
    EStep st (onGoldfishVoteChecked c st u) := by
  unfold onGoldfishVoteChecked
  split_ifs
  · exact EStep.refl st
  · exact onGoldfishVote_estep st u

theorem foldl_estep {β : Type} (g : Store → β → Store) (hg : ∀ s x, EStep s (g s x)) :
    ∀ (l : List β) (s : Store), EStep s (List.foldl g s l)
  | [], _ => EStep.refl _
  | x :: l, s => by
    rw [List.foldl_cons]
    exact (hg s x).trans (foldl_estep g hg l (g s x))

theorem onSgVote_estep (hc : HealConfig) (st : Store) (a : CombinedAttestation) : EStep st (onSgVote hc st a) := by
  unfold onSgVote
  dsimp only
  split_ifs <;> exact EStep.of_same rfl rfl ⟨rfl, rfl⟩

theorem updateFinality_estep (st : Store) (σ : ChainState) : EStep st (updateFinality st σ) := by
  unfold updateFinality
  dsimp only
  split_ifs <;> exact EStep.of_same rfl rfl ⟨rfl, rfl⟩

theorem storedOf_estep (st : Store) (b : Block) (post : ChainState) : EStep st (storedOf st b post) :=
  EStep.of_same rfl rfl ⟨rfl, rfl⟩

theorem unpackedOf_estep (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    EStep st (unpackedOf c st b post) :=
  (storedOf_estep st b post).trans (foldl_estep _ (fun s u => onGoldfishVoteChecked_estep c s u) _ _)

theorem acceptBody_estep (c : Nat → NaruStd.Set ValidatorId) (st : Store) (b : Block) (post : ChainState) :
    EStep st (acceptBody c st b post) :=
  (unpackedOf_estep c st b post).trans (updateFinality_estep _ _)

theorem onBlockUsing_estep (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) : EStep st (onBlockUsing c p st b build) := by
  rcases Proofs.Consensus.Carrier.onBlockUsing_eq c p st b build with h | ⟨-, -, h⟩
  · rw [h]; exact EStep.refl st
  · rw [h]; exact acceptBody_estep c st b _

theorem onBlockCheckedUsing_estep (handle : Store → Store) (hh : ∀ s, EStep s (handle s)) (hc : HealConfig)
    (st : Store) (b : Block) : EStep st (onBlockCheckedUsing handle hc st b) := by
  rcases Proofs.Consensus.Carrier.onBlockCheckedUsing_eq handle hc st b with h | h
  · rw [h]; exact hh st
  · rw [h]; exact EStep.refl st

theorem processBlockCore_estep (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    EStep st.core (processBlockCore c p e hc cfg st b).core := by
  unfold processBlockCore
  dsimp only
  split_ifs
  · exact EStep.refl _
  · rw [Proofs.Consensus.Stores.commitBlock_core]
    exact onBlockCheckedUsing_estep _ (fun cur => onBlockUsing_estep c p cur _ _) hc st.core _

theorem admitRow_estep (hc : HealConfig) (st : NamedStore) (row : NamedAttestation) :
    EStep st.core (admitRow hc st row).core := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact onSgVote_estep hc st.core _

theorem admitRows_estep (hc : HealConfig) :
    ∀ (rows : List NamedAttestation) (st : NamedStore), EStep st.core (admitRows hc st rows).core
  | [], _ => EStep.refl _
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_estep hc rows (admitRow hc st row)
    unfold admitRows at ih
    exact (admitRow_estep hc st row).trans ih

theorem admitCarried_estep (adm : CarriedAdmission) (hc : HealConfig) (before after : NamedStore) (b : NamedBlock) :
    EStep after.core (admitCarried adm hc before after b).core := by
  unfold admitCarried
  split_ifs
  · exact admitRows_estep hc _ after
  · exact EStep.refl _

theorem onBlockWith_estep (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig) (st : NamedStore) (b : NamedBlock) :
    EStep st.core (onBlockWith c p adm e hc cfg st b).core := by
  unfold onBlockWith
  exact (processBlockCore_estep c p e hc cfg st b).trans (admitCarried_estep adm hc st _ b)

theorem receiptProcess_estep (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (st : NamedStore) (o : NamedObject) :
    EStep st.core (receiptProcess c p s st o).core := by
  cases o with
  | Block b => exact onBlockWith_estep c p _ _ _ _ st b
  | GfVote u =>
    show EStep st.core (onGoldfishVoteChecked c st.core u)
    exact onGoldfishVoteChecked_estep c st.core u
  | Attest a =>
    show EStep st.core (admitRow s.hc st a).core
    exact admitRow_estep s.hc st a

/-- 配送の処理は `EStep`。 -/
theorem nodeProcess_estep (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState) (o : NamedObject) :
    EStep n.st.core (nodeProcess c p s n o).st.core :=
  receiptProcess_estep c p s n.st o

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **配送で新しく pool に入った投票の印は配送の前の時計**: 添字 `i` の event が `w` への配送で、その前の `w` の鍵 `u.slot` の
pool に無い `u` が後にあれば、後の印は `Stamp.At`(前の `w` の時計)。 -/
theorem deliver_stamp_exact {i : Nat} {w : ValidatorId} {o : NamedObject} {t0 : Int}
    (hev : rho.events[i]? = some (NamedEvent.Deliver w o t0)) {u : GoldfishVote}
    (hnot : u ∉ poolList (worldAt (stateBefore c p a nr s rho i) w).st.core u.slot)
    (hin : u ∈ poolList (worldAt (stateBefore c p a nr s rho (i + 1)) w).st.core u.slot) :
    (worldAt (stateBefore c p a nr s rho (i + 1)) w).st.core.timestampVote.get? u =
      some (Stamp.At (worldAt (stateBefore c p a nr s rho i) w).st.core.t) := by
  rw [stateBefore_succ_of_get c p a nr s rho hev] at hin ⊢
  unfold worldStep at hin ⊢
  dsimp only at hin ⊢
  rw [worldAt_insert_self] at hin ⊢
  have h := nodeProcess_estep c p s (worldAt (stateBefore c p a nr s rho i) w) o
  rcases h.fresh u hin with h' | h'
  · exact absurd h' hnot
  · rw [h', h.clock.t]

/-- **時刻 `t0` の配送の前の honest なノードの時計は `t0 - Δ` より後**: honest な `w` は `t0` 以下の最大の公開時刻 `T` に tick する
(`ScheduleWellFormed`。tick は同じ時刻の配送より前の添字)ので、`T = k · Δ ≤` 時計、`t0 < T + Δ`。 -/
theorem deliver_lt_clock_add (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {w : ValidatorId}
    (hw : rho.honest.contains w = true) {i : Nat} {o : NamedObject} {t0 : Int}
    (hev : rho.events[i]? = some (NamedEvent.Deliver w o t0)) :
    ∃ k : Int, 0 ≤ k ∧ k * s.e.delta ≤ (worldAt (stateBefore c p a nr s rho i) w).st.core.t ∧
      t0 < k * s.e.delta + s.e.delta := by
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev h =>
    (Proofs.Consensus.Window.eventTime_bounds hsch h).1
  have hb := Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? hev)
  simp only [eventTime] at hb
  set T : Int := (t0 / s.e.delta) * s.e.delta with hT
  have hk : 0 ≤ t0 / s.e.delta := Int.ediv_nonneg hb.1 hδ.le
  have hTle : T ≤ t0 := by rw [hT, mul_comm]; exact Int.mul_ediv_self_le hδ.ne'
  have hTlt : t0 < T + s.e.delta := by
    rw [hT]
    have := Int.lt_mul_ediv_self_add (x := t0) hδ
    linarith [mul_comm (t0 / s.e.delta) s.e.delta]
  have hpt : PublicTime s.e T := ⟨(t0 / s.e.delta).toNat, by rw [hT, Int.ofNat_eq_natCast, Int.toNat_of_nonneg hk]⟩
  have hT0 : 0 ≤ T := by rw [hT]; exact mul_nonneg hk hδ.le
  obtain ⟨j, hj⟩ := Proofs.Consensus.Window.honest_tick_index hsch hw hpt hT0 (le_trans hTle hb.2)
  have hji : j < i := by
    rcases lt_or_eq_of_le hTle with hlt | heq
    · exact Proofs.Consensus.Window.lt_of_time_lt hs hj hev hlt
    · exact Proofs.Consensus.Settled.tick_index_lt_deliver hs hj hev heq.le
  have hc := Proofs.Consensus.Window.tick_le_clock c p a nr s rho hs hnn hji hj
  exact ⟨t0 / s.e.delta, hk, hc, hTlt⟩

/-- **印が支持の締切より前の pool の投票は、支持の締切より前に受理された**: honest な `w` の添字 `n` の前の鍵 `u.slot` の pool に
ある投票 `u`(投票者は byzantine でもよい)の受信の印が `supportCutoff e u.slot` より前なら、`n` より前の最初の受理の添字 `i0` の
時刻 `t0` も `supportCutoff e u.slot` より前。受理が自分の tick なら `u` は自分の投票で `t0` は投票時刻。配送なら印は配送の前の時計
(`deliver_stamp_exact`)で、時計は `t0` 以下の最大の公開時刻 `k · Δ` 以上(`deliver_lt_clock_add`)、支持の締切も公開時刻なので
`k · Δ < supportCutoff` から `t0 < (k + 1) · Δ ≤ supportCutoff`。 -/
theorem pool_acceptedBeforeCutoff (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {w : ValidatorId}
    (hw : rho.honest.contains w = true) {n : Nat} {u : GoldfishVote}
    (hu : u ∈ poolList (worldAt (stateBefore c p a nr s rho n) w).st.core u.slot)
    (hst : occurrenceBefore ((worldAt (stateBefore c p a nr s rho n) w).st.core.timestampVote.get? u)
      (supportCutoff s.e u.slot) = true) :
    ∃ i0 t0, i0 < n ∧ AcceptsAt c p a nr s rho i0 w (NamedObject.GfVote u) t0 ∧ t0 < supportCutoff s.e u.slot := by
  obtain ⟨i0, t0, hi0, hacc⟩ := Proofs.Consensus.Settled.pool_accepted c p a nr s rho w u n hu
  refine ⟨i0, t0, hi0, hacc, ?_⟩
  have hnot : u ∉ poolList (worldAt (stateBefore c p a nr s rho i0) w).st.core u.slot := fun h =>
    hacc.1.2 ((Proofs.Consensus.Delivery.processed_gfVote_iff _ u).mpr h)
  have hin := (Proofs.Consensus.Delivery.processed_gfVote_iff _ u).mp hacc.2
  obtain ⟨ev, ⟨⟨hev, hn⟩, hte⟩, -⟩ := hacc.1.1
  cases ev with
  | Tick v τ =>
    simp only [eventNode, eventTime] at hn hte
    subst hn hte
    have hin' := hin
    rw [stateBefore_succ_of_get c p a nr s rho hev] at hin'
    unfold worldStep at hin'
    dsimp only at hin'
    rw [worldAt_insert_self] at hin'
    rcases Proofs.Consensus.PoolFrom.nodeTick_from c p a nr s v _ τ hin' with h | h | ⟨B, hB, huB⟩
    · exact absurd h hnot
    · have hem : Emits c p a nr s rho v (NamedObject.GfVote u) τ :=
        (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ τ).mpr ⟨i0, hev, h⟩
      obtain ⟨-, htv, -, hsl, -⟩ := Proofs.Consensus.Voting.emits_gfVote_shape c p a nr s rho hem
      have hτ : τ = voteTime s.e u.slot := by rw [hsl]; exact htv
      rw [hτ]
      unfold voteTime supportCutoff
      linarith
    · exact absurd (Proofs.Consensus.Settled.tick_block_gfVote_mem c p a nr s rho hB huB) hnot
  | Deliver v o τ =>
    simp only [eventNode, eventTime] at hn hte
    subst hn hte
    have hstamp := deliver_stamp_exact c p a nr s rho hev hnot hin
    obtain ⟨-, heq⟩ := Proofs.Consensus.Stamps.stateBefore_keep c p a nr s rho (Nat.succ_le_of_lt hi0) v u hin
    rw [heq, hstamp] at hst
    have hclk : (worldAt (stateBefore c p a nr s rho i0) v).st.core.t < supportCutoff s.e u.slot := by
      unfold occurrenceBefore at hst
      rcases (Proofs.Consensus.Majority.stampBefore_iff _ _).mp hst with h | ⟨τ', h, hτ'⟩
      · cases h
      · cases h
        exact hτ'
    obtain ⟨k, -, hkc, hlt⟩ := deliver_lt_clock_add c p a nr s rho hsch hδ hw hev
    have hkΔ : k * s.e.delta < (4 * (u.slot : Int) + 2) * s.e.delta := by
      have : supportCutoff s.e u.slot = (4 * (u.slot : Int) + 2) * s.e.delta := by
        unfold supportCutoff slotTime slotStart
        simp only [Int.ofNat_eq_natCast]
        ring
      linarith
    have hk : k + 1 ≤ 4 * (u.slot : Int) + 2 := by
      have := lt_of_mul_lt_mul_right hkΔ hδ.le
      omega
    have : supportCutoff s.e u.slot = (4 * (u.slot : Int) + 2) * s.e.delta := by
      unfold supportCutoff slotTime slotStart
      simp only [Int.ofNat_eq_natCast]
      ring
    rw [this]
    nlinarith

end Run

end Proofs.Consensus.StampExact
