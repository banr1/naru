import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Constants
import Proofs.Consensus.FinalizedMonotone
import Proofs.Consensus.NoFutureRead
import Mathlib.Tactic

/-!
# 包含から活性へ(C71 の liveness 系 claim の共有の足場)

残りの claim のうち `confirmedLive` / `stableLive`(property `LiveFrom`)と `finalized` の後半(`FinalizedAt` の `LiveFrom`)は、
出力が時間について単調で(`MonotoneFrom`)、未来の提案を含まず(`NoFutureRead`、`NoFutureRead.lean`)、honest な提案が期限 `D` 以内に
包含され(`IncludedFrom`)、honest な提案者が間隔 `gap · period` 以内に現れ続ける(`SingleProposerRecurrence`)なら、
遅れ `gap · period + D` で読みが増え続ける、という generic な補題 `liveFrom_of_includedFrom`(手書き
`Generic.liveFrom_of_includedFrom`、`DecoupledConsensusProofs/Generic/Lemmas.lean`)に帰着する:
時刻 `t` から `gap · period` 以内の honest な提案 `b` を取り、包含で `t' = proposalTime k + D` の読みに入り、単調性で `t + gap · period + D` の
読みにも入る。`t` の読みと `b` は共通の延長(その読み)の接頭辞どうしなので互換で、`b` は `t` の読みの接頭辞ではない
(未来の提案)ので、`t` の読みは `b` の真の接頭辞。
これを使って、`confirmedLive` / `stableLive` は claim `available` の結論 `AvailableAt`(confirmed / stable の `SafeFrom` と
`IncludedFrom`)に還元し(`confirmedLive_of_available` / `stableLive_of_available`)、`finalized` の活性は finalized の包含
`IncludedFrom … Finalized t₁ (finalityDeadline s gap)` に還元する(`finalizedLive_of_included`。単調性は `finalizedMonotone` の補題、
再発は `StrongMultiProposerRecurrence` から)。手書き `concreteConsensus` の `confirmedLive` / `stableLive` の項と
`finalized_growth`(`Bridge/FinalizedLive.lean`)の筋。残るのは `available` / `finalized_included` 自身(回復と finality gadget の
liveness)で、これらはまだ証明していない。
-/

namespace Proofs.Consensus.Liveness

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.Parameters
open Model.Consensus.Protocol.Schedule Model.Consensus.Execution.Run Model.Consensus.Spec.Interface
open Model.Consensus.Spec.Constants
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions Statements.Consensus.Spec.Regimes
open Statements.Consensus.Spec.Claims
open Proofs.Consensus.Blocks Proofs.Consensus.Constants Proofs.Consensus.NoFutureRead

section Generic

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 包含(`IncludedFrom … D`)と単調性・未来の提案の不在・間隔 `gap` の再発から、遅れ `gap · period + D` の活性(`LiveFrom`)。
手書き `liveFrom_of_includedFrom`。 -/
theorem liveFrom_of_includedFrom (g : Output) (t0 D : Int) (gap : Nat)
    (hmono : MonotoneFrom c p a nr s rho g t0) (hfuture : NoFutureRead c p a nr s rho g)
    (hincl : IncludedFrom c p a nr s rho g t0 D) (hrec : SingleProposerRecurrence p s rho t0 gap)
    (hD : 0 ≤ D) (hperiod : 0 < period s) :
    LiveFrom c p a nr s rho g t0 (Int.ofNat gap * period s + D) := by
  unfold LiveFrom
  intro t ht
  obtain ⟨ht0, hdead⟩ := ht
  have hGnn : 0 ≤ Int.ofNat gap * period s := by
    have hg : (0 : Int) ≤ Int.ofNat gap := Int.natCast_nonneg gap
    exact mul_nonneg hg hperiod.le
  have hgapDead : t + Int.ofNat gap * period s ≤ rho.horizon := by linarith
  obtain ⟨k, ⟨hkAfter, hkUpper⟩, hkHonest⟩ := hrec t ⟨ht0, hgapDead⟩
  have htincl : t0 < proposalTime s.e k := lt_of_le_of_lt ht0 hkAfter
  have hpropD : proposalTime s.e k + D ≤ rho.horizon := by linarith
  obtain ⟨b, hbprop, hbin⟩ := hincl k ⟨⟨htincl, hkHonest⟩, hpropD⟩
  have hfinalle : proposalTime s.e k + D ≤ t + (Int.ofNat gap * period s + D) := by linarith
  have ht0propD : t0 ≤ proposalTime s.e k + D := by linarith
  have hBfinal : ∀ v, rho.honest.contains v = true →
      preceq b (outputAt c p a nr g s rho v (t + (Int.ofNat gap * period s + D))) = true := fun v hv =>
    preceq_trans (hbin v hv)
      (hmono v (proposalTime s.e k + D) (t + (Int.ofNat gap * period s + D)) ⟨⟨⟨hv, ht0propD⟩, hfinalle⟩, hdead⟩)
  refine ⟨b, ⟨⟨k, hkAfter, hbprop⟩, fun v hv => ?_⟩, fun v hv => hBfinal v hv⟩
  have hnf := hfuture v t k b ⟨⟨hv, hbprop⟩, hkAfter⟩
  have hmono_t := hmono v t (t + (Int.ofNat gap * period s + D)) ⟨⟨⟨hv, ht0⟩, by linarith⟩, hdead⟩
  have hcompat := compatible_of_preceq_common hmono_t (hBfinal v hv)
  unfold compatible at hcompat
  rw [Bool.or_eq_true] at hcompat
  rcases hcompat with hrb | hbr
  · unfold prec
    rw [Bool.and_eq_true, bne_iff_ne]
    refine ⟨fun heq => hnf ?_, hrb⟩
    rw [← heq]
    exact preceq_self _
  · exact absurd hbr hnf

/-- 強い多提案者の再発(`tGST` から)は、`tGST` 以後の時刻からの単一提案者の再発を与える(period > 0、`proposerSlots = 3 > 0`)。
手書き `StrongMultiProposerRecurrence.toMultiProposerRecurrence` / `MultiProposerRecurrence.toSingleProposerRecurrence`。 -/
theorem singleRecurrence_of_strong {start t1 : Int} {gap : Nat}
    (h : StrongMultiProposerRecurrence p s rho start gap) (hle : start ≤ t1) (hperiod : 0 < period s) :
    SingleProposerRecurrence p s rho t1 gap := by
  intro t ht
  obtain ⟨ht1, hhor⟩ := ht
  obtain ⟨k, ⟨⟨hlo, hhi⟩, hmulti⟩, -⟩ := h t ⟨hle.trans ht1, hhor⟩
  refine ⟨k, ⟨?_, hhi⟩, ?_⟩
  · have h2 : 0 < 2 * period s := by linarith
    linarith
  · unfold MultiProposerAt at hmulti
    have h0 := hmulti.2 0 (by unfold proposerSlots; norm_num)
    rw [Nat.add_zero] at h0
    exact h0

end Generic

/-! ## `SetupWellFormed` の数値の前提 -/

theorem wf_facts {c : Nat → NaruStd.Set ValidatorId} {p : Nat → ValidatorId} {s : Model.Consensus.Execution.Setup.Setup}
    (hwf : SetupWellFormed c p s) : 0 < s.e.delta ∧ 0 ≤ s.e.tGST ∧ 3 ≤ s.hc.r := by
  unfold SetupWellFormed at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hδ, hgst⟩, hr⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hwf
  exact ⟨hδ, hgst, hr⟩

theorem confirmationDelay_nonneg (s : Model.Consensus.Execution.Setup.Setup) (hδ : 0 < s.e.delta) :
    0 ≤ confirmationDelay s := by
  unfold confirmationDelay
  linarith

theorem stableInclusionDelay_nonneg (s : Model.Consensus.Execution.Setup.Setup) (hδ : 0 < s.e.delta) (hr : 3 ≤ s.hc.r) :
    0 ≤ stableInclusionDelay s := by
  unfold stableInclusionDelay
  have hp := period_pos s hδ hr
  have hη : (0 : Int) ≤ Int.ofNat (1 + s.hc.etaSG) := Int.natCast_nonneg _
  have h1 : 0 ≤ Int.ofNat (1 + s.hc.etaSG) * period s := mul_nonneg hη hp.le
  linarith

theorem finalityStartup_nonneg (s : Model.Consensus.Execution.Setup.Setup) (hδ : 0 < s.e.delta) (gap : Nat) :
    0 ≤ finalityStartup s gap := by
  unfold finalityStartup
  exact healingBoundary_nonneg s hδ _

theorem finalityDeadline_nonneg (s : Model.Consensus.Execution.Setup.Setup) (hδ : 0 < s.e.delta) (gap : Nat) :
    0 ≤ finalityDeadline s gap := by
  unfold finalityDeadline
  have h := healingBoundary_nonneg s hδ (finalityDeadlineRound s gap (extraRounds s) + 1)
  linarith

/-! ## claim への還元 -/

section Claims

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- `SleepyRegime` から `ExecutionValid`(未来の提案の不在に使う)。 -/
theorem executionValid_of_sleepy {t0 : Int} (h : SleepyRegime c p a nr s rho t0) : ExecutionValid c p a nr s rho := by
  unfold SleepyRegime at h
  obtain ⟨⟨⟨⟨⟨hexec, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact hexec

/-- claim `confirmedLive` の結論は、`AvailableAt`(claim `available` の結論)から従う:
confirmed の `SafeFrom` の単調性と `IncludedFrom … confirmationDelay` に、未来の提案の不在と再発を合わせる。 -/
theorem confirmedLive_of_available (t0 : Int) (gap : Nat) (hwf : SetupWellFormed c p s)
    (hreg : LiveSleepyRegime c p a nr s rho t0 gap) (hav : AvailableAt c p a nr s rho t0) :
    LiveFrom c p a nr s rho Output.Confirmed t0 (growthDelay s gap) := by
  obtain ⟨hδ, -, hr⟩ := wf_facts hwf
  unfold LiveSleepyRegime at hreg
  obtain ⟨hsleep, hrec⟩ := hreg
  have hfuture := noFutureRead_of_executionValid c p a nr s rho (executionValid_of_sleepy c p a nr s rho hsleep) hδ
    Output.Confirmed
  unfold AvailableAt at hav
  obtain ⟨⟨⟨hsafe, hincl⟩, -⟩, -⟩ := hav
  unfold SafeFrom at hsafe
  obtain ⟨-, hmono⟩ := hsafe
  show LiveFrom c p a nr s rho Output.Confirmed t0 (Int.ofNat gap * period s + confirmationDelay s)
  exact liveFrom_of_includedFrom c p a nr s rho Output.Confirmed t0 (confirmationDelay s) gap hmono hfuture hincl hrec
    (confirmationDelay_nonneg s hδ) (period_pos s hδ hr)

/-- claim `stableLive` の結論は、`AvailableAt` の stable の `SafeFrom` と `IncludedFrom … stableInclusionDelay` から従う。 -/
theorem stableLive_of_available (t0 : Int) (gap : Nat) (hwf : SetupWellFormed c p s)
    (hreg : LiveSleepyRegime c p a nr s rho t0 gap) (hav : AvailableAt c p a nr s rho t0) :
    LiveFrom c p a nr s rho Output.Stable t0 (stableGrowthDelay s gap) := by
  obtain ⟨hδ, -, hr⟩ := wf_facts hwf
  unfold LiveSleepyRegime at hreg
  obtain ⟨hsleep, hrec⟩ := hreg
  have hfuture := noFutureRead_of_executionValid c p a nr s rho (executionValid_of_sleepy c p a nr s rho hsleep) hδ
    Output.Stable
  unfold AvailableAt at hav
  obtain ⟨⟨-, hsafe⟩, hincl⟩ := hav
  unfold SafeFrom at hsafe
  obtain ⟨-, hmono⟩ := hsafe
  show LiveFrom c p a nr s rho Output.Stable t0 (Int.ofNat gap * period s + stableInclusionDelay s)
  exact liveFrom_of_includedFrom c p a nr s rho Output.Stable t0 (stableInclusionDelay s) gap hmono hfuture hincl hrec
    (stableInclusionDelay_nonneg s hδ hr) (period_pos s hδ hr)

/-- claim `finalized` の活性(`FinalizedAt` の後半)は、finalized の包含 `IncludedFrom … Finalized t₁ (finalityDeadline s gap)`
(`t₁ = t0 + finalityStartup s gap`)から従う: 単調性は `finalizedMonotone` の補題、再発は `FinalityRegime` の
`StrongMultiProposerRecurrence`。手書き `finalized_growth`。 -/
theorem finalizedLive_of_included (t0 : Int) (gap : Nat) (hwf : SetupWellFormed c p s)
    (hreg : FinalityRegime c p a nr s rho t0 gap)
    (hincl : IncludedFrom c p a nr s rho Output.Finalized (t0 + finalityStartup s gap) (finalityDeadline s gap)) :
    LiveFrom c p a nr s rho Output.Finalized (t0 + finalityStartup s gap)
      (Int.ofNat gap * period s + finalityDeadline s gap) := by
  obtain ⟨hδ, hgst0, hr⟩ := wf_facts hwf
  unfold FinalityRegime at hreg
  obtain ⟨⟨⟨hbft, hstrong⟩, -⟩, -⟩ := hreg
  unfold BFTRegime at hbft
  obtain ⟨⟨⟨⟨⟨hexec, -⟩, hgst⟩, -⟩, -⟩, -⟩ := hbft
  have hsorted : EventsSorted rho := by
    unfold ExecutionValid at hexec
    obtain ⟨⟨⟨hsch, -⟩, -⟩, -⟩ := hexec
    exact (schedule_facts s rho hsch).1
  have hperiod := period_pos s hδ hr
  have hstartup := finalityStartup_nonneg s hδ gap
  have ht1 : 0 ≤ t0 + finalityStartup s gap := add_nonneg (hgst0.trans hgst) hstartup
  have hmono0 := Proofs.Consensus.FinalizedMonotone.monotoneFrom_finalized c p a nr s rho hsorted
  have hmono : MonotoneFrom c p a nr s rho Output.Finalized (t0 + finalityStartup s gap) := by
    unfold MonotoneFrom at hmono0 ⊢
    intro v t t2 h
    exact hmono0 v t t2 ⟨⟨⟨h.1.1.1, ht1.trans h.1.1.2⟩, h.1.2⟩, h.2⟩
  have hfuture := noFutureRead_of_executionValid c p a nr s rho hexec hδ Output.Finalized
  have hrec : SingleProposerRecurrence p s rho (t0 + finalityStartup s gap) gap :=
    singleRecurrence_of_strong p s rho hstrong (hgst.trans (le_add_of_nonneg_right hstartup)) hperiod
  exact liveFrom_of_includedFrom c p a nr s rho Output.Finalized (t0 + finalityStartup s gap) (finalityDeadline s gap) gap
    hmono hfuture hincl hrec (finalityDeadline_nonneg s hδ gap) hperiod

end Claims

end Proofs.Consensus.Liveness
