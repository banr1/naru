import Proofs.Consensus.RootWitness
import Proofs.Consensus.ShortHorizon
import Mathlib.Tactic

/-!
# 確認の記録の由来(C71 / C77 の補題)

run の添字 `n` の手前のノード `v` の確認の記録 `latestConfirmed` は、genesis か、それより前の `v` の確認評価の tick
(`0 < slotOf e t` かつ `t = supportCutoff e (slotOf e t)`)で、確認の更新の前の段の store `preUpdateStoreAt`
(`RootWitness.lean`。時計合わせ・提案・投票の後)の fork choice の head(確認の walk)か grade の stable root
`frameStableRoot`(`frameSgCandidate` の値は stable root と同じ)のどちらか(`recAt_confirmed_origin`)。stable の記録
`latestStable` は genesis か stable root(`recAt_stable_origin`)。手書き `ConfirmationOrigin.stateBefore_latest_confirmed_origin`
(`DecoupledConsensusProofs/Protocol/Handlers/ConfirmationRecordOrigin.lean`)に当たる(手書きの 3 枝 genesis / 選択(walk か
SG candidate)/ stable root と同じ分け方。SG candidate は stable root の枝にまとめた)。

tick の後の記録は務めの store `tickDutyStore` の記録と同じ(attestation は記録を変えない。`tick_rec_dutyStore`)で、務めの store は
確認の更新の前の段に `updateConfirmationWith` を高々 1 回掛けたもの(`AttestationSource.tickDutyStore_eq_preUpdate`)。前の段は記録を
変えない(`tickPreUpdateStore_rec`)。確認の更新の後の確認の記録は元の記録か stable の記録か head か grade の候補
(`Goldfish.latestConfirmed_shape`)、stable の記録は元の記録か stable root(`Goldfish.stableRec_cases`)なので、添字の帰納法で
2 つの記録を一緒に追う。
-/

namespace Proofs.Consensus.ConfirmedOrigin

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.Parameters
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.Grades Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Schedule
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Conditions
open Proofs.Consensus.ConfirmationRecords Proofs.Consensus.RecordGrowth

/-! ## tick の記録 -/

/-- 確認の更新の前の段(時計合わせ・提案・投票)は 2 つの記録を変えない。 -/
theorem tickPreUpdateStore_rec (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) (t : Int) :
    SameRec (Proofs.Consensus.AttestationSource.tickPreUpdateStore c p nr cache e hc cfg nd st t).core st.core := by
  have h0 : SameRec ({ st with core := { st.core with t := t, s := slotOf e t } } : NamedStore).core st.core := ⟨rfl, rfl⟩
  unfold Proofs.Consensus.AttestationSource.tickPreUpdateStore
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact (namedGoldfishVoteWith_rec c cache e hc nd _).trans ((proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0)
    | with_reducible exact (namedGoldfishVoteWith_rec c cache e hc nd _).trans h0
    | with_reducible exact (proposeBlockWith_rec c p nr cache e hc cfg nd _).trans h0
    | with_reducible exact h0

/-- tick の後の 2 つの記録は務めの store `tickDutyStore` の記録(その後の attestation は記録を変えない)。 -/
theorem tick_rec_dutyStore (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    SameRec (tick c p a nr cache e hc cfg nd st rec t).1.core
      (Proofs.Consensus.AttestationSource.tickDutyStore c p nr cache e hc cfg nd st t).core := by
  unfold tick Proofs.Consensus.AttestationSource.tickDutyStore
  dsimp only
  split_ifs
  all_goals first
    | exact attestWith_rec cache e hc nd _ rec
    | exact SameRec.refl _

/-- `frameSgCandidate` の値は(同じ store の round の)stable root。 -/
theorem frameSgCandidate_stableRoot (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (st : Model.Consensus.Protocol.ForkChoice.Goldfish.FGStore) (k : Nat) {g : Block}
    (h : frameSgCandidate cache e hc st k = some g) :
    frameStableRoot cache e hc st (roundOf hc st.s) = some g := by
  unfold frameSgCandidate at h
  unfold frameStableRoot
  rw [h]

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- ノード `w` の添字 `i` の時刻 `t` の tick の cache(`nodeTick` が `onPhaseTick` で準備するもの)。 -/
def confCacheAt (w : ValidatorId) (i : Nat) (t : Int) : Cache :=
  onPhaseTick s.e s.hc (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
    (worldAt (stateBefore c p a nr s rho i) w).cache

/-- 確認評価の tick: event `i` が `w` の時刻 `t` の tick で、その tick が確認の更新を通る(`0 < slotOf e t` かつ
`t = supportCutoff e (slotOf e t)`)。 -/
def ConfTick (w : ValidatorId) (i : Nat) (t : Int) : Prop :=
  rho.events[i]? = some (NamedEvent.Tick w t) ∧ 0 < slotOf s.e t ∧ t = supportCutoff s.e (slotOf s.e t)

/-- 確認評価の tick の確認の walk: 確認の更新の前の段の fork choice の head(slot `slotOf e t - 1`)。手書き
`namedConfirmationWalk S (confirmationInputRead S rho w q) q` に当たる。 -/
def confWalkAt (w : ValidatorId) (i : Nat) (t : Int) : Block :=
  Proofs.Consensus.Goldfish.head (confCacheAt c p a nr s rho w i t) s.e s.hc
    (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)

/-- 確認評価の tick の grade の stable root(確認の更新の前の段の store の round)。手書き
`(gradeContract read.cache).stableRoot S.E S.hc read.st.core.toHealing (round_of read.st.core.s)` に当たる。 -/
def confStableRootAt (w : ValidatorId) (i : Nat) (t : Int) : Option Block :=
  frameStableRoot (confCacheAt c p a nr s rho w i t) s.e s.hc
    (storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
    (roundOf s.hc (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)

/-- stable の記録の由来: genesis か、添字 `n` より前の確認評価の tick の stable root。 -/
def StableOrigin (w : ValidatorId) (n : Nat) (B : Block) : Prop :=
  B = Block.Genesis ∨ ∃ i t, i < n ∧ ConfTick s rho w i t ∧ confStableRootAt c p a nr s rho w i t = some B

/-- 確認の記録の由来: genesis か、添字 `n` より前の確認評価の tick の確認の walk か stable root。 -/
def ConfOrigin (w : ValidatorId) (n : Nat) (B : Block) : Prop :=
  B = Block.Genesis ∨ ∃ i t, i < n ∧ ConfTick s rho w i t ∧
    (B = confWalkAt c p a nr s rho w i t ∨ confStableRootAt c p a nr s rho w i t = some B)

theorem StableOrigin.mono {w : ValidatorId} {n m : Nat} {B : Block} (h : StableOrigin c p a nr s rho w n B)
    (hnm : n ≤ m) : StableOrigin c p a nr s rho w m B := by
  rcases h with h | ⟨i, t, hi, ht, hB⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, t, by omega, ht, hB⟩

theorem ConfOrigin.mono {w : ValidatorId} {n m : Nat} {B : Block} (h : ConfOrigin c p a nr s rho w n B)
    (hnm : n ≤ m) : ConfOrigin c p a nr s rho w m B := by
  rcases h with h | ⟨i, t, hi, ht, hB⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, t, by omega, ht, hB⟩

theorem ConfOrigin.of_stable {w : ValidatorId} {n : Nat} {B : Block} (h : StableOrigin c p a nr s rho w n B) :
    ConfOrigin c p a nr s rho w n B := by
  rcases h with h | ⟨i, t, hi, ht, hB⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, t, hi, ht, Or.inr hB⟩

/-- 添字 `i` の event が `w` の時刻 `t` の tick なら、その後の 2 つの記録は、確認評価の tick でなければ前のまま、確認評価の
tick なら確認の更新の前の段に `updateConfirmationWith`(slot `slotOf e t - 1`)を掛けたものの記録。 -/
theorem recAt_tick_cases (R : Store → Block) (hR : ∀ x y : Store, SameRec x y → R x = R y) {w : ValidatorId} {i : Nat}
    {t : Int} (ht : rho.events[i]? = some (NamedEvent.Tick w t)) :
    R (nodeTick c p a nr s w (worldAt (stateBefore c p a nr s rho i) w) t).1.st.core = recAt c p a nr s rho R w i ∨
      (ConfTick s rho w i t ∧
        R (nodeTick c p a nr s w (worldAt (stateBefore c p a nr s rho i) w) t).1.st.core =
          R (updateConfirmationWith (confCacheAt c p a nr s rho w i t) s.e s.hc
            (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1))) := by
  have hduty : R (nodeTick c p a nr s w (worldAt (stateBefore c p a nr s rho i) w) t).1.st.core =
      R (Proofs.Consensus.AttestationSource.tickDutyStore c p nr (confCacheAt c p a nr s rho w i t) s.e s.hc s.cfg
        (Model.Consensus.Execution.Setup.setupNode w) (worldAt (stateBefore c p a nr s rho i) w).st t).core := by
    apply hR
    unfold nodeTick profileTick
    dsimp only
    exact tick_rec_dutyStore c p a nr _ s.e s.hc s.cfg _ _ _ t
  rw [hduty, Proofs.Consensus.AttestationSource.tickDutyStore_eq_preUpdate]
  split_ifs with hcut
  · right
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcut
    exact ⟨⟨ht, hcut.1, hcut.2⟩, rfl⟩
  · left
    unfold recAt
    exact hR _ _ (tickPreUpdateStore_rec c p nr _ s.e s.hc s.cfg _ _ t)

/-- **2 つの記録の由来**(前提なし): 添字 `n` の手前の `w` の stable の記録は `StableOrigin`、確認の記録は `ConfOrigin`。
手書き `ConfirmationOrigin.stateBefore_latest_confirmed_origin`。 -/
theorem recAt_origin (w : ValidatorId) :
    ∀ n : Nat, StableOrigin c p a nr s rho w n (recAt c p a nr s rho (fun st => st.latestStable) w n) ∧
      ConfOrigin c p a nr s rho w n (recAt c p a nr s rho (fun st => st.latestConfirmed) w n)
  | 0 => ⟨Or.inl rfl, Or.inl rfl⟩
  | n + 1 => by
    obtain ⟨ihS, ihC⟩ := recAt_origin w n
    have hS : ∀ x y : Store, SameRec x y → x.latestStable = y.latestStable := fun _ _ h => h.stable
    have hC : ∀ x y : Store, SameRec x y → x.latestConfirmed = y.latestConfirmed := fun _ _ h => h.confirmed
    have hpre : ∀ t, (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w n t).core.latestStable =
        recAt c p a nr s rho (fun st => st.latestStable) w n :=
      fun t => (tickPreUpdateStore_rec c p nr _ s.e s.hc s.cfg _ _ t).stable
    have hpreC : ∀ t, (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w n t).core.latestConfirmed =
        recAt c p a nr s rho (fun st => st.latestConfirmed) w n :=
      fun t => (tickPreUpdateStore_rec c p nr _ s.e s.hc s.cfg _ _ t).confirmed
    -- stable の記録の更新の値は、元の記録か stable root
    have hstab : ∀ t, ConfTick s rho w n t →
        StableOrigin c p a nr s rho w (n + 1)
          (Proofs.Consensus.Goldfish.stableRec (confCacheAt c p a nr s rho w n t) s.e s.hc
            (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w n t).core) := by
      intro t hct
      rcases Proofs.Consensus.Goldfish.stableRec_cases (confCacheAt c p a nr s rho w n t) s.e s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w n t).core with h | ⟨g, hg, h⟩
      · rw [h, hpre]
        exact ihS.mono c p a nr s rho (Nat.le_succ n)
      · rw [h]
        exact Or.inr ⟨n, t, Nat.lt_succ_self n, hct, hg⟩
    refine ⟨?_, ?_⟩
    · rcases recAt_succ c p a nr s rho (fun st => st.latestStable) (fun n o => hS _ _ (nodeProcess_rec c p s n o)) n w with
        h | ⟨t, ht, h⟩
      · rw [h]
        exact ihS.mono c p a nr s rho (Nat.le_succ n)
      · rw [h]
        rcases recAt_tick_cases c p a nr s rho (fun st => st.latestStable) hS ht with h' | ⟨hct, h'⟩
        · rw [h']
          exact ihS.mono c p a nr s rho (Nat.le_succ n)
        · rw [h', Proofs.Consensus.Goldfish.updateConfirmationWith_eq]
          exact hstab t hct
    · rcases recAt_succ c p a nr s rho (fun st => st.latestConfirmed) (fun n o => hC _ _ (nodeProcess_rec c p s n o)) n w with
        h | ⟨t, ht, h⟩
      · rw [h]
        exact ihC.mono c p a nr s rho (Nat.le_succ n)
      · rw [h]
        rcases recAt_tick_cases c p a nr s rho (fun st => st.latestConfirmed) hC ht with h' | ⟨hct, h'⟩
        · rw [h']
          exact ihC.mono c p a nr s rho (Nat.le_succ n)
        · rw [h']
          rcases Proofs.Consensus.Goldfish.latestConfirmed_shape (confCacheAt c p a nr s rho w n t) s.e s.hc
              (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w n t).core (slotOf s.e t - 1) with
            hold | hst | ⟨hhead, -, -⟩ | ⟨g, hg, hgv⟩
          · rw [hold, hpreC]
            exact ihC.mono c p a nr s rho (Nat.le_succ n)
          · rw [hst]
            exact ConfOrigin.of_stable c p a nr s rho (hstab t hct)
          · rw [hhead]
            exact Or.inr ⟨n, t, Nat.lt_succ_self n, hct, Or.inl rfl⟩
          · rw [hgv]
            exact Or.inr ⟨n, t, Nat.lt_succ_self n, hct, Or.inr (frameSgCandidate_stableRoot _ _ _ _ _ hg)⟩

/-- **読みの確認の記録の由来**: 時刻 `t` の読みの確認の記録は `ConfOrigin`(添字は `idx rho t`)。 -/
theorem storeAt_confirmed_origin (hs : EventsSorted rho) (w : ValidatorId) (t : Int) :
    ConfOrigin c p a nr s rho w (idx rho t) (storeAt c p a nr s rho w t).core.latestConfirmed := by
  rw [storeAt_eq_recAt c p a nr s rho hs (fun st => st.latestConfirmed) w t]
  exact (recAt_origin c p a nr s rho w (idx rho t)).2

/-- 確認評価の tick の時刻は slot `slotOf e t - 1` の確認の時刻(`supportCutoff (q + 1) = confirmationTime q`)。 -/
theorem confTick_time {w : ValidatorId} {i : Nat} {t : Int} (h : ConfTick s rho w i t) :
    t = confirmationTime s.e (slotOf s.e t - 1) := by
  obtain ⟨-, hpos, hcut⟩ := h
  have hk : slotOf s.e t - 1 + 1 = slotOf s.e t := Nat.sub_add_cancel hpos
  conv_lhs => rw [hcut, ← hk]
  unfold supportCutoff confirmationTime slotTime Model.Consensus.Objects.Time.slotStart
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

/-- 確認評価の tick の slot の確認の時刻は `horizon` 以下(`ScheduleWellFormed`)。 -/
theorem confTick_horizon (hsch : ScheduleWellFormed s rho) {w : ValidatorId} {i : Nat} {t : Int}
    (h : ConfTick s rho w i t) : confirmationTime s.e (slotOf s.e t - 1) ≤ rho.horizon := by
  rw [← confTick_time s rho h]
  exact (Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? h.1)).2

end Run

end Proofs.Consensus.ConfirmedOrigin
