import Proofs.Consensus.RecordGrowth
import Proofs.Consensus.Liveness
import Proofs.Consensus.ParentSlot
import Proofs.Consensus.FinalizedSource
import Mathlib.Tactic

/-!
# 最初の確認より前に終わる run の確認の記録と finalized(C71 / C77 の補題)

確認の記録 `latestConfirmed` / `latestStable` を書くのは tick の確認評価 `updateConfirmationWith` だけで
(`ConfirmationRecords.tick_rec_shape`)、それが走るのは `0 < slotOf e t` かつ `t = supportCutoff e (slotOf e t)` の tick だけ
(`tick_rec_of_noCutoff`)。正の slot の `supportCutoff` は最初の確認の時刻 `confirmationTime e 0` 以後
(`confirmationTime_zero_le_supportCutoff`。`Δ ≥ 0`)なので、どの event の時刻も `confirmationTime e 0` より前なら、
run のどの添字・どの読みでも 2 つの記録は genesis のまま(`recAt_rec_short` / `storeAt_rec_short`)。
`ScheduleWellFormed` は event の時刻を `horizon` 以下にするので、`horizon < confirmationTime e 0` の run が該当する。

同じ run では finalized も genesis(`storeAt_f_short`。周回 220): 読みの時計の slot は 1 以下で、tree のブロックの slot は時計の slot 以下
(`ParentSlot.stateBefore_slotInv`)、genesis でない tree のブロックの親の slot はブロックの slot より小さい(`ParentSlot.stateBefore_parentInv`)ので、
finality carrier(`Carrier.StoreInv.carrier`)の担い手は genesis か親が genesis のブロックで、その導出の `f` は genesis
(`FinalizedSource.deriveNamed_f_node`)。

手書き `latestConfirmedAt_eq_genesis_of_short_horizon`
(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)に当たる。手書きは確認の記録の由来
(`ConfirmationOrigin.stateBefore_latest_confirmed_origin`)から示すが、ここでは tick の形から直接示す。
-/

namespace Proofs.Consensus.ShortHorizon

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.Parameters
open Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals
open Model.Consensus.Protocol.Tick Model.Consensus.Protocol.Grades Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Schedule
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Conditions
open Proofs.Consensus.ConfirmationRecords Proofs.Consensus.RecordGrowth

/-! ## 時刻 -/

/-- 正の slot の支持の締切は、最初の確認の時刻 `confirmationTime e 0` 以後(`Δ ≥ 0`)。 -/
theorem confirmationTime_zero_le_supportCutoff {e : ProtocolEnv} (hδ : 0 ≤ e.delta) {k : Nat} (hk : 0 < k) :
    confirmationTime e 0 ≤ supportCutoff e k := by
  unfold confirmationTime supportCutoff slotTime Model.Consensus.Objects.Time.slotStart
  have hk' : (1 : Int) ≤ (k : Int) := by exact_mod_cast hk
  have hmul : e.delta * 4 * 1 ≤ e.delta * 4 * (k : Int) :=
    mul_le_mul_of_nonneg_left hk' (by linarith)
  simp only [Int.ofNat_eq_natCast, Nat.cast_zero, mul_zero, zero_add] at hmul ⊢
  linarith

/-! ## 確認評価の無い tick -/

/-- 確認評価の時刻でない tick(`0 < slotOf e t` かつ `t = supportCutoff e (slotOf e t)` でない)は 2 つの記録を変えない。 -/
theorem tick_rec_of_noCutoff (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) {t : Int}
    (hno : ¬ (0 < slotOf e t ∧ t = supportCutoff e (slotOf e t))) :
    SameRec (tick c p a nr cache e hc cfg nd st rec t).1.core st.core := by
  have hb : (decide (0 < slotOf e t) && (t == supportCutoff e (slotOf e t))) = false := by
    by_cases h1 : 0 < slotOf e t
    · have h2 : t ≠ supportCutoff e (slotOf e t) := fun h => hno ⟨h1, h⟩
      simp [h1, h2]
    · simp [h1]
  have h0 : SameRec ({ st with core := { st.core with t := t, s := slotOf e t } } : NamedStore).core st.core := ⟨rfl, rfl⟩
  unfold tick
  dsimp only
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  split_ifs
  all_goals first
    | with_reducible exact (attestWith_rec cache e hc nd _ rec).trans ((namedGoldfishVoteWith_rec c cache e hc nd _).trans ((proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0))
    | with_reducible exact (attestWith_rec cache e hc nd _ rec).trans ((namedGoldfishVoteWith_rec c cache e hc nd _).trans h0)
    | with_reducible exact (attestWith_rec cache e hc nd _ rec).trans ((proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0)
    | with_reducible exact (attestWith_rec cache e hc nd _ rec).trans h0
    | with_reducible exact (namedGoldfishVoteWith_rec c cache e hc nd _).trans ((proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0)
    | with_reducible exact (namedGoldfishVoteWith_rec c cache e hc nd _).trans h0
    | with_reducible exact (proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0
    | with_reducible exact h0

/-- 確認評価の時刻でない `nodeTick` は 2 つの記録を変えない。 -/
theorem nodeTick_rec_of_noCutoff (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    (n : NamedNodeState) {t : Int} (hno : ¬ (0 < slotOf s.e t ∧ t = supportCutoff s.e (slotOf s.e t))) :
    SameRec (nodeTick c p a nr s v n t).1.st.core n.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_rec_of_noCutoff c p a nr _ s.e s.hc s.cfg _ n.st n.signing hno

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- どの event の時刻も最初の確認の時刻より前なら、どの添字・どのノードでも 2 つの記録は genesis。 -/
theorem recAt_rec_short (hδ : 0 ≤ s.e.delta)
    (hshort : ∀ ev, ev ∈ rho.events → eventTime ev < confirmationTime s.e 0) :
    ∀ (i : Nat) (v : ValidatorId),
      recAt c p a nr s rho (fun st => st.latestConfirmed) v i = Block.Genesis ∧
        recAt c p a nr s rho (fun st => st.latestStable) v i = Block.Genesis
  | 0, _ => ⟨rfl, rfl⟩
  | i + 1, v => by
    have ih := recAt_rec_short hδ hshort i v
    have hstep : ∀ R : Store → Block, (∀ x y : Store, SameRec x y → R x = R y) →
        recAt c p a nr s rho R v (i + 1) = recAt c p a nr s rho R v i := by
      intro R hR
      rcases recAt_succ c p a nr s rho R (fun n o => hR _ _ (nodeProcess_rec c p s n o)) i v with h | ⟨t, ht, h⟩
      · exact h
      · rw [h]
        have htime : t < confirmationTime s.e 0 := hshort _ (List.mem_of_getElem? ht)
        have hno : ¬ (0 < slotOf s.e t ∧ t = supportCutoff s.e (slotOf s.e t)) := by
          rintro ⟨hk, heq⟩
          have hle := confirmationTime_zero_le_supportCutoff hδ hk
          rw [← heq] at hle
          exact absurd htime (not_lt.mpr hle)
        exact hR _ _ (nodeTick_rec_of_noCutoff c p a nr s v _ hno)
    refine ⟨?_, ?_⟩
    · rw [hstep _ (fun x y h => h.confirmed)]
      exact ih.1
    · rw [hstep _ (fun x y h => h.stable)]
      exact ih.2

/-- **最初の確認より前に終わる run の記録**: `horizon < confirmationTime e 0` なら、どの時刻の読みでも確認の記録と stable の
記録は genesis。手書き `latestConfirmedAt_eq_genesis_of_short_horizon`。 -/
theorem storeAt_rec_short (hsch : ScheduleWellFormed s rho) (hδ : 0 ≤ s.e.delta)
    (hshort : rho.horizon < confirmationTime s.e 0) (v : ValidatorId) (t : Int) :
    (storeAt c p a nr s rho v t).core.latestConfirmed = Block.Genesis ∧
      (storeAt c p a nr s rho v t).core.latestStable = Block.Genesis := by
  unfold ScheduleWellFormed at hsch
  obtain ⟨⟨⟨⟨⟨⟨-, hsorted⟩, -⟩, htimes⟩, -⟩, -⟩, -⟩ := hsch
  have hev : ∀ ev, ev ∈ rho.events → eventTime ev < confirmationTime s.e 0 := fun ev hmem =>
    lt_of_le_of_lt (htimes ev ((List.contains_iff_mem).mpr hmem)).2 hshort
  have h := recAt_rec_short c p a nr s rho hδ hev (idx rho t) v
  exact ⟨(storeAt_eq_recAt c p a nr s rho hsorted (fun st => st.latestConfirmed) v t).trans h.1,
    (storeAt_eq_recAt c p a nr s rho hsorted (fun st => st.latestStable) v t).trans h.2⟩

/-- **最初の確認より前に終わる run の finalized**: `horizon < confirmationTime e 0` なら、どの時刻の読みでも finalized は genesis。
手書き `confirmedOutputCompatibleFrom_of_weakGenesis_named` の短い horizon の枝の局所の事実 `hfinalized` に当たる。
読みの時計は 0 か `horizon` 以下の tick の時刻なので `confirmationTime e 0 = 6Δ` より前、したがって `proposalTime e 2 = 8Δ` より前で、
時計の slot は 1 以下。
finality carrier(`Carrier.StoreInv.carrier`)の `D` が genesis でなければ、その消去は tree にあって slot は 1 以下
(`ParentSlot.stateBefore_slotInv`)、親の slot はそれより小さい(`ParentSlot.stateBefore_parentInv`)ので 0 で、名前付きの親は
genesis(親も tree にあり、genesis でなければその親の slot が 0 より小さくなる)。したがって `D` の導出の `f` は genesis の導出の
`j` か `f`(`FinalizedSource.deriveNamed_f_node`)で genesis。 -/
theorem storeAt_f_short (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta)
    (hshort : rho.horizon < confirmationTime s.e 0) (v : ValidatorId) (t : Int) :
    (storeAt c p a nr s rho v t).core.f = Block.Genesis := by
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev hev =>
    (Proofs.Consensus.Window.eventTime_bounds hsch hev).1
  have hread : storeAt c p a nr s rho v t = (worldAt (stateBefore c p a nr s rho (idx rho t)) v).st := by
    unfold storeAt
    rw [readAt_eq_stateBefore_idx c p a nr s rho hs]
  rw [hread]
  generalize idx rho t = i
  have hslot : (worldAt (stateBefore c p a nr s rho i) v).st.core.s ≤ 1 := by
    rw [Proofs.Consensus.Clocks.clock_slot c p a nr s rho i v]
    have h0 := (Proofs.Consensus.Clocks.clock_le_event c p a nr s rho hs hnn i v).1
    apply Proofs.Consensus.Window.slotOf_le_of_lt s.e hδ h0
    have hlt : (worldAt (stateBefore c p a nr s rho i) v).st.core.t < confirmationTime s.e 0 := by
      rcases Proofs.Consensus.ParentSlot.clock_origin c p a nr s rho i v with h | ⟨j, -, hj⟩
      · rw [h]
        unfold confirmationTime slotTime Model.Consensus.Objects.Time.slotStart
        simp only [Int.ofNat_eq_natCast, Nat.cast_zero, mul_zero, zero_add]
        linarith
      · exact lt_of_le_of_lt (Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? hj)).2 hshort
    have hle : confirmationTime s.e 0 ≤ proposalTime s.e (1 + 1) := by
      unfold confirmationTime proposalTime slotTime Model.Consensus.Objects.Time.slotStart
      simp only [Int.ofNat_eq_natCast]
      push_cast
      linarith
    exact lt_of_lt_of_le hlt hle
  have hinv := Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i v
  have hsl := Proofs.Consensus.ParentSlot.stateBefore_slotInv c p a nr s rho hs hnn hδ i v
  have hpi := Proofs.Consensus.ParentSlot.stateBefore_parentInv c p a nr s rho i v
  obtain ⟨D, hD, hDf⟩ := hinv.carrier
  rw [← hDf]
  cases D with
  | Genesis => rfl
  | Node q k r vs sup rows w =>
    have hq := hinv.closed _ hD
    have hqg : q = NamedBlock.Genesis := by
      cases q with
      | Genesis => rfl
      | Node q' k' r' vs' sup' rows' w' =>
        exfalso
        have hDt := hinv.tree _ hD
        have hqt := hinv.tree _ hq
        have h1 := hpi _ hDt (fun h => Block.noConfusion h)
        have h2 := hpi _ hqt (fun h => Block.noConfusion h)
        have h3 := hsl _ hDt
        change k' < k at h1
        change slot (eraseBlock q') < k' at h2
        change k ≤ _ at h3
        omega
    subst hqg
    rcases Proofs.Consensus.FinalizedSource.deriveNamed_f_node s.e s.cfg NamedBlock.Genesis k r vs sup rows w with
      ⟨hf, -⟩ | ⟨hf, -⟩
    · rw [hf]; rfl
    · rw [hf]; rfl

end Run

end Proofs.Consensus.ShortHorizon
