import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Available
import Proofs.Consensus.ShortHorizon
import Proofs.Consensus.Voting
import Proofs.Consensus.ConfirmedOrigin
import Proofs.Consensus.ProposerRoot
import Proofs.Consensus.GradeSupporter
import Proofs.Consensus.GradeTransport
import Proofs.Consensus.SgStamps
import Proofs.Consensus.FrameCapture
import Mathlib.Tactic

/-!
# claim `available` の骨格(IDEAL.md C76)

claim `available` は `SetupWellFormed ∧ RunDomain ∧ SleepyRegime t0 → AvailableAt t0`。`Available.lean` の `availableAt_of_fields` が結論を
5 つの事実に還元しているので、骨格は次のとおり(入口は `Proofs/Consensus/Spec/Claims.lean` の theorem `available`):

1. 入口 `availableAt`: `t0 = 0`(GST-zero の枝。`RecoveredBy` の `genesis`)なら finalized の一致を `finalizedAgree_genesis`(確認の出力の一致
   `confirmedAgree_genesis` から `agreeFrom_finalized_of_confirmed` で下ろす。周回 214)から、
   `t0 ≠ 0`(回復の枝)なら証明済みの `agreeFrom_finalized_of_recovered` から取り、残る 4 つの事実を `availableAt_of_fields` で組み立てる。
2. GST-zero の枝の 3 つの一致(確認の記録の一致・finalized との交差の互換・確認の出力の一致)は、どれも `commonUpper_genesis`
   (2 つの読みの finalized と確認の記録の共通の上界 `CommonUpperFrom`。手書きの後の投票の務めの head)から証明済みの
   `recordAgreeFrom_of_commonUpper` / `crossAgreeFrom_of_commonUpper` / `agreeFrom_confirmed_of_commonUpper` で出す(周回 216)。
   `commonUpper_genesis` は最初の確認の時刻 `confirmationTime e 0` が `horizon` 以下なら `commonUpper_genesis_long`、より前に run が終わるなら
   確認の記録は genesis(証明済みの `ShortHorizon.storeAt_rec_short`)で finalized も genesis(証明済みの `ShortHorizon.storeAt_f_short`)なので
   上界は genesis(枝の分け方は周回 218、finalized の側は周回 220)。`commonUpper_genesis_long` は、確認の記録と finalized がそれぞれ
   ある slot 以後の投票の務めの head `voteDutyHeadAt` の祖先であることを言う `recordAt_preceq_laterVoteHead` / `finalizedAt_preceq_laterVoteHead`
   から、4 つの slot の最大で上界を揃えて証明する(周回 222)。`finalizedAt_preceq_laterVoteHead` は finalized ⪯ 読みの FG root
   (`ReceiverFinality.store_fgRoot_extends`)とし、FG root を `RootWitness.stateBeforeTime_fgRoot_confirmationWitness` で genesis か
   honest な行の務めの確認の証人に分け、後者は行の時刻(行の round の action 時刻 = opening slot の確認の時刻)の slot を `first` に
   とって穴 `fgWitness_preceq_laterVoteHead` に渡す(周回 248)。`recordAt_preceq_laterVoteHead` は確認の記録の由来(証明済みの
   `ConfirmedOrigin.storeAt_confirmed_origin`: genesis か、確認評価の tick の確認の walk か grade の stable root)で分け、
   `confWalk_preceq_laterVoteHead`(walk ⪯ 後の投票の head。穴ではない)と `confStableRoot_preceq_confWalk`(stable root ⪯ walk。穴ではない)から証明する(周回 224)。
   `confWalk_preceq_laterVoteHead` は walk が anchor のままか filtered tree の適格な要素か(`Goldfish.head_cases`)で分け、anchor の枝は
   `confAnchor_preceq_laterVoteHead`(g1 の frame の raw の active prefix か FG root なので穴 `confG1Raw_preceq_laterVoteHead` /
   `confFgRoot_preceq_laterVoteHead` から)、動いた枝は `confEligibleWalk_preceq_laterVoteHead` から証明する(周回 245)。
   `confEligibleWalk_preceq_laterVoteHead` は walk が genuine な確認なので穴 `genuineConf_preceq_laterVoteHead`(手書き
   `protectedVoteSlots_of_gstZero_v2` の `heads`)から(周回 250)。`fgWitness_preceq_laterVoteHead` は round の同時帰納
   `RootWitness.dutyStoreAt_jointRoundInduction_of_prior` を `base = cut = 0` で掛け、段の genuine な確認を
   `genuineConf_preceq_laterVoteHead`、SG block と grade 2 の候補を `fgStep_preceq_laterVoteHead` から供給する(周回 250)。
   `fgStep_preceq_laterVoteHead` は務めの store の round で分け、round 0 は `fgStep_round_zero`(round 0 の frame に G1 / G2 の root は
   無いので grade 2 の候補は空、SG block は `liveConfirmed` の祖先か FG root)で閉じ、正の round を穴
   `fgStep_preceq_laterVoteHead_positive`(手書きの帰納の段の `hformation` の側)に渡す(周回 251)。
   `confFgRoot_preceq_laterVoteHead` は FG root を tick の時刻の読みの FG root に移し(`confPreUpdate_fgRoot`: 確認の締切は提案時刻ではない
   `supportCutoff_ne_proposalTime`)、証明済みの `RootWitness.stateBeforeTime_fgRoot_confirmationWitness` で genesis か honest な行の務めの
   確認の証人に分け、後者を穴 `fgWitness_preceq_laterVoteHead` に渡す(周回 247)。
   `confG1Raw_preceq_laterVoteHead` は round 0 を矛盾(`confCache_g1_round_zero`: round 0 の凍結は空 `FrameCapture.freezeRoot_zero` で、
   cache の round 0 の結果も空 `FrameCapture.stateBefore_phase_zero`)で閉じ、正の round を穴 `confG1Raw_preceq_laterVoteHead_positive` に渡す(周回 246)。
   `confStableRoot_preceq_confWalk` は stable root が FG root に戻る枝を FG root ⪯ SG root ⪯ head で閉じ、g2 の frame の root がある枝を
   `confFrameRoot_preceq_confWalk`(穴ではない)に渡す(周回 226)。`confFrameRoot_preceq_confWalk` は確認の更新の前の段の store の round で分け、
   round 0 は g2 の frame に root が無いので矛盾(`confCache_g2_round_zero`。G2 の round 0 の domain 時刻は `-Δ` で、run の event の時刻は 0 以上)、
   正の round は `confFrameRoot_preceq_confWalk_positive`(穴ではない)に渡す(周回 228)。これは g1 の frame の anchor が fork choice の SG root で
   walk がそこから歩くので、`confFrameRoot_preceq_anchor_positive`(g2 の frame の root の active prefix ⪯ g1 の anchor。穴ではない)から証明する(周回 230)。
   これは `confFrameG2_g1Root_positive`(g2 の root の祖先で filtered tree にあるものは g1 の root の祖先。穴ではない)で g1 の root を取り、
   `activePrefix_exists`(tree の重複なし `preUpdateTree_nodup` を使う。周回 233 に閉じた)と `activePrefix_dominates` で anchor に移す(周回 232)。
   `confFrameG2_g1Root_positive` は g2 の root の出どころ `confCache_g2_origin`、`confFrameG1_slot_positive`(読みの G1 の欄。穴ではない)、
   `g1Freeze_of_g2Freeze_positive`(G1 の凍結は G2 の凍結以上。穴ではない)と `preceq_clipGrade_of_compatible` から証明する(周回 234)。
   `g1Freeze_of_g2Freeze_positive` は G2 の凍結の root を `g1Grade_of_g2Grade_positive`(grade の持ち越し。穴ではない)と `g1Tree_of_g2Tree`
   (tree の持ち越し。周回 236 に閉じた)で G1 の tick に運び、`freezeRoot_of_graded`(grade の通った tree の要素は凍結の root 以下)で G1 の凍結に移す(周回 235)。
   `g1Grade_of_g2Grade_positive` は抽象的な持ち越し `GradeTransport.gradeBool_transport` に 2 つの tick の間の包含
   `g1RawInputs_back` / `g1Interpreted_back` / `g1LocalCovers_fwd` / `g1InterpretedCover_fwd` を渡す(周回 238)。`g1LocalCovers_fwd` は
   tree のブロックが残り、run に root の衝突が無い(`tickTree_root_inj`)ので root の解決が変わらない(`findRoot?_of_subset`)ことで閉じた(周回 240)。
   `g1InterpretedCover_fwd` は SG 票の行と受信の印が残ること(`SgStamps.stateBefore_sgKeep`)と同じ root の解決で閉じた(周回 241)。
   `g1RawInputs_back` / `g1Interpreted_back` は、G2 の tick より後に入った SG 票とブロックの受信の印がその tick の時刻以上
   (`SgStamps.stateBefore_sgFresh` / `BlockStamps.stateBefore_fresh`)で `cut` は G2 の domain 時刻以下なので閉じた(周回 242)。
   `confFrameG1_slot_positive` は、欄が閉じていること(`confFrameG1_closed_positive`。周回 244 に閉じた: G1 の domain 時刻の tick は tick の網羅性で確認評価の tick より前にあり、
   間の tick の時計の round は同じなので欄が残る。`FrameCapture.stateBefore_closed` / `FrameCapture.onPhaseTick_closed`)と、完了した phase の結果の値
   (`FrameCapture.onPhaseTick_phase_some` / `FrameCapture.stateBefore_phase_origin`: domain の tick の凍結をいまの finalized で切り詰めたもの)から
   証明する(周回 243)。
   回復の枝の記録の一致と交差の互換は穴 `recordAgree_recovered` / `crossAgree_recovered`。
3. 穴(7 件): `genuineConf_preceq_laterVoteHead`(手書き `protectedVoteSlots_of_gstZero_v2` の `heads`、
   `DecoupledConsensusProofs/Execution/WeakGenesisGSTZeroActionSources.lean`)/
   `fgStep_preceq_laterVoteHead_positive`(手書き `WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut` の帰納の段の
   `hroots` の後の正の round の枝、`DecoupledConsensusProofs/Protocol/Grades/WeakBootstrapAction.lean`)/
   `confG1Raw_preceq_laterVoteHead_positive`(手書き
   `preparedG1Raw_preceq_voteDutyHead_of_gstZero` の正の round の枝、`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)/
   `recordAgree_recovered`(手書き `available_confirmedSafe` の `recovered` の枝)/ `crossAgree_recovered`(手書き
   `SettledBootstrapPreparedV4.latest_compatible_finalized_core`)/ `confirmedIncluded`(手書き `available_confirmedIncluded`)/
   `stableIncluded`(手書き `available_stableIncluded_any`)。

手書きは `RecoveredBy` の 2 枝で分ける: `genesis` は `WeakGenesis` に写して `gstZeroGuarantees_of_weakGenesis`
(`DecoupledConsensusProofs/Execution/GSTZeroSafetyClosedNamed.lean`)、`recovered` は `recoveryProducesHealedState` /
`boundedSafety`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の位相の保証から。一致の穴はすでに枝ごとに分けた(`commonUpper_genesis` は
`t0 = 0`、`_recovered` の 2 件は `hne : t0 ≠ 0` を受け取る)。包含の穴 2 件は義務の前提(`SetupWellFormed ∧ RunDomain ∧ SleepyRegime t0`)を
そのまま受け取り、細分するときはこの 2 枝から切る。`commonUpper_genesis` は手書きと同じく `confirmation_time S.E 0 ≤ rho.horizon` か否かでさらに分けた。
-/

namespace Proofs.Consensus.AvailableHoles

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Execution.Run Model.Consensus.Spec.Interface Model.Consensus.Spec.Constants
open Statements.Consensus.Spec.Properties Statements.Consensus.Spec.Conditions Statements.Consensus.Spec.Regimes
open Statements.Consensus.Spec.Claims
open Proofs.Consensus.Outputs Proofs.Consensus.Available

section Holes

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- ノード `x` の slot `k` の投票の務めの head(手書き `voterHeadAt`): 投票の時刻 `voteTime e k` より前の event を畳んだ `x` の状態に
時計を合わせ、`preparedCache`(tick の前の `onPhaseTick`)で読んだ fork choice の head(`Voting.voteHeadBlock`)。
`Voting.clocked` は `setClock` と同じ式なので、読みは生成 Model の `confirmationReadAt x (voteTime e k)`(手書き `voteDutyRead`)と同じ。 -/
def voteDutyHeadAt (x : ValidatorId) (k : Nat) : Block :=
  let tv := Model.Consensus.Protocol.Schedule.voteTime s.e k
  let n := worldAt (stateBeforeTime c p a nr s rho tv) x
  Proofs.Consensus.Voting.voteHeadBlock (preparedCache s n tv) s.e s.hc
    (Proofs.Consensus.Voting.clocked s.e n.st tv).core

/-- **確認の締切は提案時刻ではない**(Δ > 0): `4Δ · k + 2Δ = 4Δ · k'` なら `2 = 4 · (k' - k)` で、整数では成り立たない
(`RootWitness.actionTime_ne_proposalTime` と同じ運び。周回 247)。 -/
theorem supportCutoff_ne_proposalTime {e : Model.Consensus.Objects.Parameters.ProtocolEnv} (hδ : 0 < e.delta) (k k' : Nat) :
    Model.Consensus.Protocol.Schedule.supportCutoff e k ≠ Model.Consensus.Protocol.Schedule.proposalTime e k' := by
  unfold Model.Consensus.Protocol.Schedule.supportCutoff Model.Consensus.Protocol.Schedule.proposalTime
    Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
  simp only [Int.ofNat_eq_natCast]
  intro h
  have h0 : e.delta * (4 * (k' : Int) - 4 * (k : Int) - 2) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hδ.ne' h1
  · omega

/-- **確認評価の tick の確認の更新の前の段の FG root は tick の時刻の読みの FG root**(`EventsSorted` と重複なし、Δ > 0): 確認評価の
tick の時刻は確認の締切で提案時刻ではない(`supportCutoff_ne_proposalTime`)ので、務めの store の FG root は tick の前の store の
FG root(`RootWitness.dutyStoreAt_fgRoot_of_not_proposing`)で、確認の更新は FG root を変えない。tick の前の状態は時刻 `< t` の
読み(`RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime`)。手書きでは `confirmationInputRead` の store が定義上
`storeBeforeTime` なので `change` で済む段(周回 247)。 -/
theorem confPreUpdate_fgRoot (hδ : 0 < s.e.delta) (hs : Statements.Consensus.Spec.Conditions.EventsSorted rho)
    (hnd : Statements.Consensus.Spec.Conditions.EventsNodup rho) {w : ValidatorId} {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t) :
    Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core) =
      Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot
        (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho t) w).st.core) := by
  have hnp : ¬ ((decide (0 < Model.Consensus.Objects.Parameters.slotOf s.e t) &&
      (t == Model.Consensus.Protocol.Schedule.proposalTime s.e (Model.Consensus.Objects.Parameters.slotOf s.e t))) &&
      (p (Model.Consensus.Objects.Parameters.slotOf s.e t) == (Model.Consensus.Execution.Setup.setupNode w).valIndex)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    rintro ⟨⟨-, hp⟩, -⟩
    exact supportCutoff_ne_proposalTime hδ _ _ (ht.2.2.symm.trans hp)
  have hduty : Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot
      (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core) =
      Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core) := by
    have hpre : Proofs.Consensus.AttestationSource.tickPreUpdateStore c p nr
        (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
          (worldAt (stateBefore c p a nr s rho i) w).cache)
        s.e s.hc s.cfg (Model.Consensus.Execution.Setup.setupNode w) (worldAt (stateBefore c p a nr s rho i) w).st t =
        Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t := rfl
    unfold Proofs.Consensus.RootWitness.dutyStoreAt
    rw [Proofs.Consensus.AttestationSource.tickDutyStore_eq_preUpdate, hpre]
    split_ifs
    · exact (Proofs.Consensus.RootWitness.namedUpdateConfirmationWith_fgRoot _ _ _ _ _).symm
    · rfl
  rw [hduty, Proofs.Consensus.RootWitness.dutyStoreAt_fgRoot_of_not_proposing c p a nr s rho w i t hnp,
    Proofs.Consensus.RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime c p a nr s rho hs
      (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) ht.1]

/-- 確認評価の tick の時刻(slot `q = slotOf e t - 1` の確認の時刻)は、`q < d` なら slot `d + 1` の投票時刻より前
(`6Δ + 4Δq < Δ + 4Δ(d + 1)`。手書き `confirmationTime_lt_nextVote_local`。周回 247)。 -/
theorem confTick_lt_nextVote (hδ : 0 < s.e.delta) {w : ValidatorId} {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t) {d : Nat}
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) :
    t < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) := by
  rw [Proofs.Consensus.ConfirmedOrigin.confTick_time s rho ht]
  have hq : ((Model.Consensus.Objects.Parameters.slotOf s.e t - 1 : Nat) : Int) + 1 ≤ (d : Int) := by exact_mod_cast hqd
  unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
    Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
  simp only [Int.ofNat_eq_natCast]
  push_cast
  nlinarith

/-- **行を出した tick は確認評価の tick**(Δ > 0): 行の時刻は行の round の action 時刻
(`RootWitness.emits_attest_actionTime_round`)で、action 時刻の slot は正で、時刻はその slot の確認の締切
(`AttestationSource.supportCutoff_actionTime`。周回 250)。 -/
theorem emits_confTick (hδ : 0 < s.e.delta) {w : ValidatorId} {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation}
    {i : Nat} {t : Int}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho w
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t)
    (hev : rho.events[i]? = some (NamedEvent.Tick w t)) :
    Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t := by
  have h := Proofs.Consensus.AttestationSource.supportCutoff_actionTime hδ s.hc row.round
  rw [← Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨hev, h.1, h.2⟩

/-- 行を出した tick の時刻(slot `q = slotOf e t - 1` の確認の時刻)が slot `d + 1` の投票時刻より前なら `q < d`
(`d ≤ q` なら `Δ + 4Δ(d + 1) ≤ 6Δ + 4Δq`。`confTick_lt_nextVote` の逆向き。周回 250)。 -/
theorem emits_slot_lt_of_lt_nextVote (hδ : 0 < s.e.delta) {w : ValidatorId}
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} {t : Int}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho w
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t) {d : Nat}
    (ht : t < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) :
    Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d := by
  have hq := Proofs.Consensus.RootWitness.emits_attest_slotOf_pred c p a nr s rho hδ hem
  have htime : t = Model.Consensus.Protocol.Schedule.confirmationTime s.e
      (Model.Consensus.Protocol.Grades.openingSlot s.hc row.round) :=
    Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem
  rw [hq]
  rw [htime] at ht
  by_contra hcon
  have h' : (d : Int) ≤ ((Model.Consensus.Protocol.Grades.openingSlot s.hc row.round : Nat) : Int) := by
    exact_mod_cast not_lt.mp hcon
  unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
    Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart at ht
  simp only [Int.ofNat_eq_natCast] at ht
  push_cast at ht
  nlinarith

/-- 穴: GST-zero の枝で、honest なノード `w` の確認評価の tick(添字 `i`・時刻 `t`、slot `q = slotOf e t - 1`)の genuine な確認
(確認の更新の前の段の head で、その slot で eligible。`RootWitness.GenuineConfirmationAt`)は、`q < d ≤ last + 1`(`last` の
確認の時刻は `horizon` 以下)の honest なノード `x` の slot `d` の投票の務めの head の祖先。手書き `protectedVoteSlots_of_gstZero_v2`
の第 2 連言(`GenuineConfirmationWith … (confStore S rho w q) q B → ProtectedVoteSlot S rho d B`)の `heads`
(`DecoupledConsensusProofs/Execution/WeakGenesisGSTZeroActionSources.lean`)に当たる。
閉じるのに要るもの: 保護された投票の slot の slot についての帰納法(手書き `WeakJoint.protectedVoteSlots_of_historyCut_v2_after_gst`)
(周回 250)。 -/
theorem genuineConf_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1) {C : Block}
    (hC : Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C) :
    preceq C (voteDutyHeadAt c p a nr s rho x d) = true := by
  sorry

/-- **round 0 の g1 の frame に root は無い**: tick が準備する cache(`ConfirmedOrigin.confCacheAt`)の round 0 の frame をどの store で
読んでも、G1 の結果は `some (some r)` にならない。この tick の凍結は空(`FrameCapture.freezeRoot_zero`)で、tick の前の cache の
round 0 の結果も空(`FrameCapture.stateBefore_phase_zero`)。手書き `confirmationRead_g1_round_zero_no_root`
(`DecoupledConsensusProofs/Protocol/Grades/WeakGenesis.lean`)に当たる(周回 246)。 -/
theorem confCache_g1_round_zero {w : ValidatorId} {i : Nat} {t : Int}
    (st : Model.Consensus.Protocol.ForkChoice.Goldfish.FGStore) {r : Block}
    (h : (Model.Consensus.Protocol.Grades.readFrame (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) st 0).g1 =
      some (some r)) : False := by
  have h' : Model.Consensus.Protocol.Grades.phaseResult
      (Model.Consensus.Protocol.Grades.readFrame (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) st 0)
      Model.Consensus.Protocol.Grades.GradePhase.G1 = some (some r) := h
  rw [Proofs.Consensus.FrameCapture.phaseResult_readFrame] at h'
  obtain ⟨y, hy, hry⟩ := Proofs.Consensus.FrameCapture.clipResult_eq_some h'
  unfold Proofs.Consensus.ConfirmedOrigin.confCacheAt at hy
  rcases Proofs.Consensus.FrameCapture.onPhaseTick_phase_some hy with ⟨x0, hx0, rfl⟩ | ⟨-, rfl⟩
  · rw [Proofs.Consensus.FrameCapture.stateBefore_phase_zero c p a nr s rho i w _ hx0] at hry
    simp at hry
  · rw [Proofs.Consensus.FrameCapture.freezeRoot_zero] at hry
    simp at hry

/-- round 0 の G2 の domain 時刻は `-Δ`(round 0 の opening slot は 0)。 -/
theorem domainTime_zero_G2 (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) :
    Model.Consensus.Protocol.Grades.domainTime e hc 0 Model.Consensus.Protocol.Grades.GradePhase.G2 = -e.delta := by
  unfold Model.Consensus.Protocol.Grades.domainTime Model.Consensus.Protocol.Grades.openingTime
    Model.Consensus.Protocol.Schedule.proposalTime Model.Consensus.Objects.Parameters.slotTime
    Model.Consensus.Objects.Time.slotStart Model.Consensus.Protocol.Grades.openingSlot
  simp only [Model.Consensus.Protocol.Grades.domainOffset, Int.ofNat_eq_natCast]
  push_cast
  ring

/-- **round 0 の g2 の frame に root は無い**: run の添字 `i` の event が `w` の時刻 `t` の tick なら、その tick が準備する cache
(`ConfirmedOrigin.confCacheAt`)の round 0 の frame をどの store で読んでも、G2 の結果は `some (some r)` にならない。G2 の結果は
round 0 の G2 の domain 時刻 `-Δ`(`domainTime_zero_G2`)の tick でしか凍結されない(この tick か、より前の tick。
`Grade2Capture.onPhaseTick_g2_cases` / `stateBefore_g2_origin`)が、run の event の時刻は 0 以上(`Window.eventTime_bounds`)。
手書き `confirmationRead_g2_round_zero_no_root` / `readFrame_g2_round_zero_no_root`
(`DecoupledConsensusProofs/Protocol/Grades/WeakGenesis.lean`)に当たる(周回 228)。 -/
theorem confCache_g2_round_zero (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta)
    {w : ValidatorId} {i : Nat} {t : Int} (hev : rho.events[i]? = some (NamedEvent.Tick w t))
    (st : Model.Consensus.Protocol.ForkChoice.Goldfish.FGStore) {r : Block}
    (h : (Model.Consensus.Protocol.Grades.readFrame (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) st 0).g2 =
      some (some r)) : False := by
  have hneg : ∀ {j : Nat} {u : Int}, rho.events[j]? = some (NamedEvent.Tick w u) →
      u ≠ Model.Consensus.Protocol.Grades.domainTime s.e s.hc 0 Model.Consensus.Protocol.Grades.GradePhase.G2 := by
    intro j u hj hu
    have h0 : (0 : Int) ≤ u := (Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? hj)).1
    rw [hu, domainTime_zero_G2] at h0
    linarith
  change Model.Consensus.Protocol.Grades.clipResult st.f
    (Model.Consensus.Protocol.Grades.cacheAtRound (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) 0).g2 =
      some (some r) at h
  obtain ⟨b1, hb1, -⟩ := Proofs.Consensus.Grade2Capture.clipResult_some h (Proofs.Consensus.Blocks.preceq_self r)
  unfold Proofs.Consensus.ConfirmedOrigin.confCacheAt at hb1
  obtain ⟨b0, -, hold | ⟨ht, -⟩⟩ := Proofs.Consensus.Grade2Capture.onPhaseTick_g2_cases hb1
  · obtain ⟨j, u, -, -, hj, hu, -, -⟩ := Proofs.Consensus.Grade2Capture.stateBefore_g2_origin c p a nr s rho i w 0 hold
    exact hneg hj hu
  · exact hneg hev ht

/-- **round 0 の段**(`ScheduleWellFormed`、Δ > 0): 行を出した tick(添字 `i`・時刻 `t`)の務めの store の round が 0 なら、
務めの FG root とその tick の genuine な確認が `X` の祖先のとき、務めの SG block も `X` の祖先で、grade 2 の候補は無い。
round 0 の frame には G1 / G2 の root が無い(`confCache_g1_round_zero` / `confCache_g2_round_zero`)ので、grade 2 の候補は空、
anchor は FG root で、SG block は `liveConfirmed` の祖先(`AttestationSource.deepestClear_preceq`)か FG root。`liveConfirmed ⪯ X` は
`RootWitness.dutyStoreAt_live_preceq_of_prior`。手書き `WeakGenesis.actionSGBlock_eq_genesis_zero`(round 0 の SG block は genesis)
を、genesis まで下ろさず `X` の祖先で止めた形(周回 251)。 -/
theorem fgStep_round_zero (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta)
    {w : ValidatorId} {i : Nat} {t : Int} {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation}
    (hev : rho.events[i]? = some (NamedEvent.Tick w t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho w
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t)
    (hzero : Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core.s = 0) {X : Block}
    (hroot : preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
        (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core)) X = true)
    (hprior : ∀ C, Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C → preceq C X = true) :
    preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho w i t) X = true ∧
      ∀ q, Proofs.Consensus.RootWitness.grade2CandidateAt c p a nr s rho w i t = some q → preceq q X = true := by
  have hg2 : Proofs.Consensus.RootWitness.grade2CandidateAt c p a nr s rho w i t = none := by
    cases hq : Proofs.Consensus.RootWitness.grade2CandidateAt c p a nr s rho w i t with
    | none => rfl
    | some q =>
      exfalso
      unfold Proofs.Consensus.RootWitness.grade2CandidateAt at hq
      rw [hzero] at hq
      unfold Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith Model.Consensus.Protocol.Grades.frameGradeRead at hq
      dsimp only at hq
      unfold Model.Consensus.Protocol.Grades.grade2Block at hq
      split_ifs at hq
      obtain ⟨r', hr', -⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨y, hy, hyr⟩ := Option.bind_eq_some_iff.mp hr'
      subst hyr
      exact confCache_g2_round_zero c p a nr s rho hsch hδ hev _ hy
  refine ⟨?_, fun q hq => by rw [hg2] at hq; exact absurd hq (by simp)⟩
  have hlive := Proofs.Consensus.RootWitness.dutyStoreAt_live_preceq_of_prior c p a nr s rho hδ hem hroot hprior
  unfold Proofs.Consensus.RootWitness.sgBlockAt
  rw [hg2, hzero]
  unfold Model.Consensus.Protocol.Duties.Inputs.getSgVoteWith Model.Consensus.Protocol.Grades.currentSGVote
  split
  · rename_i b hb
    exact Proofs.Consensus.Blocks.preceq_trans (Proofs.Consensus.AttestationSource.deepestClear_preceq hb) hlive
  · dsimp only
    split_ifs
    · exact hroot
    · unfold Model.Consensus.Protocol.Grades.frameGradeRead Model.Consensus.Protocol.Grades.anchor
      dsimp only
      split
      · rename_i r hr
        exact (confCache_g1_round_zero c p a nr s rho _ hr).elim
      · exact hroot

/-- 穴: GST-zero の枝の round の帰納法の段の正の round。honest な `w` が時刻 `t < voteTime (d + 1)`(添字 `i` の tick)に行 `row` を出し、
務めの store の round が正で、前の round の行の tick の SG block と FG root・確認の証人、同じ round の行の tick の FG root、自分の FG root と
genuine な確認がどれも slot `d` の投票の務めの head `X` の祖先なら、自分の務めの SG block と grade 2 の候補も `X` の祖先。
手書き `WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut`(`DecoupledConsensusProofs/Protocol/Grades/WeakBootstrapAction.lean`)
の帰納の段のうち `hroots` の後で、`hformation` から grade の形成を取って SG block と確認の証人を押さえる枝に当たる(round 0 の枝は
`fgStep_round_zero`。周回 251)。
閉じるのに要るもの: grade の形成
`hformation`(手書き `actionSources_preceq_voteDutyHead_of_gstZero` が `WeakJoint.actionGradeFormationAt_of_awakeWindowMajority` と
`WeakJoint.relativeGradeCarrierAt_of_awakeWindowHistory_gstZero` で供給する。生成側の担い手の段は
`RootWitness.grade2CandidateAt_preceq_windowConfirmed_of_emits`)(周回 250)。 -/
theorem fgStep_preceq_laterVoteHead_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {x : ValidatorId} (hx : rho.honest.contains x = true)
    {w : ValidatorId} {i : Nat} {t : Int} {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation}
    (hw : w ∈ rho.honest.elems) (hev : rho.events[i]? = some (NamedEvent.Tick w t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho w
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t)
    (ht : t < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))
    (hpos : 0 < Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core.s)
    (hprevSg : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      w2 ∈ rho.honest.elems → rho.events[i2]? = some (NamedEvent.Tick w2 t2) →
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho w2
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      row2.round < row.round →
      preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho w2 i2 t2) (voteDutyHeadAt c p a nr s rho x d) = true)
    (hprev : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      w2 ∈ rho.honest.elems → rho.events[i2]? = some (NamedEvent.Tick w2 t2) →
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho w2
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      row2.round < row.round →
      preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
          (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w2 i2 t2).core))
        (voteDutyHeadAt c p a nr s rho x d) = true ∧
      ∀ T, Proofs.Consensus.RootWitness.fgConfirmationWitnessAt c p a nr s rho w2 i2 t2 = some T →
        preceq T (voteDutyHeadAt c p a nr s rho x d) = true)
    (hsame : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      w2 ∈ rho.honest.elems → rho.events[i2]? = some (NamedEvent.Tick w2 t2) →
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho w2
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      row2.round = row.round →
      preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
          (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w2 i2 t2).core))
        (voteDutyHeadAt c p a nr s rho x d) = true)
    (hroot : preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
        (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core))
      (voteDutyHeadAt c p a nr s rho x d) = true)
    (hprior : ∀ C, Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
      preceq C (voteDutyHeadAt c p a nr s rho x d) = true) :
    preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho w i t) (voteDutyHeadAt c p a nr s rho x d) = true ∧
      ∀ q, Proofs.Consensus.RootWitness.grade2CandidateAt c p a nr s rho w i t = some q →
        preceq q (voteDutyHeadAt c p a nr s rho x d) = true := by
  sorry

/-- GST-zero の枝の round の帰納法の段(`fgStep_preceq_laterVoteHead_positive` と同じ前提から、round の正を除いたもの)。
務めの store の round で分け、0 なら `fgStep_round_zero`、正なら穴 `fgStep_preceq_laterVoteHead_positive`(周回 251)。 -/
theorem fgStep_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {x : ValidatorId} (hx : rho.honest.contains x = true)
    {w : ValidatorId} {i : Nat} {t : Int} {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation}
    (hw : w ∈ rho.honest.elems) (hev : rho.events[i]? = some (NamedEvent.Tick w t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho w
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t)
    (ht : t < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))
    (hprevSg : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      w2 ∈ rho.honest.elems → rho.events[i2]? = some (NamedEvent.Tick w2 t2) →
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho w2
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      row2.round < row.round →
      preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho w2 i2 t2) (voteDutyHeadAt c p a nr s rho x d) = true)
    (hprev : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      w2 ∈ rho.honest.elems → rho.events[i2]? = some (NamedEvent.Tick w2 t2) →
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho w2
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      row2.round < row.round →
      preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
          (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w2 i2 t2).core))
        (voteDutyHeadAt c p a nr s rho x d) = true ∧
      ∀ T, Proofs.Consensus.RootWitness.fgConfirmationWitnessAt c p a nr s rho w2 i2 t2 = some T →
        preceq T (voteDutyHeadAt c p a nr s rho x d) = true)
    (hsame : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      w2 ∈ rho.honest.elems → rho.events[i2]? = some (NamedEvent.Tick w2 t2) →
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho w2
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      row2.round = row.round →
      preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
          (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w2 i2 t2).core))
        (voteDutyHeadAt c p a nr s rho x d) = true)
    (hroot : preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
        (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core))
      (voteDutyHeadAt c p a nr s rho x d) = true)
    (hprior : ∀ C, Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
      preceq C (voteDutyHeadAt c p a nr s rho x d) = true) :
    preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho w i t) (voteDutyHeadAt c p a nr s rho x d) = true ∧
      ∀ q, Proofs.Consensus.RootWitness.grade2CandidateAt c p a nr s rho w i t = some q →
        preceq q (voteDutyHeadAt c p a nr s rho x d) = true := by
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, -⟩, -⟩ := hexec
  rcases Nat.eq_zero_or_pos (Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core.s) with hzero | hpos
  · exact fgStep_round_zero c p a nr s rho hsch hfacts.1 hev hem hzero hroot hprior
  · exact fgStep_preceq_laterVoteHead_positive c p a nr s rho hwf hdom hsleep hhor hd hupper hx hw hev hem ht hpos
      hprevSg hprev hsame hroot hprior

/-- GST-zero の枝で、honest な `u` が時刻 `t2`(添字 `i2` の tick)に行を出し、`t2` が slot `d + 1` の投票時刻より前なら、
その tick の務めの確認の証人 `T` は、`1 ≤ d ≤ last + 1`(`last` の確認の時刻は `horizon` 以下)の honest なノード `x` の slot `d` の
投票の務めの head の祖先。手書き `actionSources_preceq_voteDutyHead_of_gstZero` の 3 つ目の結論(`fgConfirmationWitness S
(actionStoreAt S rho w r) = some T → T ⪯ voteDutyHead S rho x d`。`DecoupledConsensusProofs/Execution/WeakGenesisGSTZeroActionSources.lean`)
に当たり、手書きの round の境 `S.a r < vote_time (d + 1)` を行の時刻の境に置き換えた(周回 247)。
手書きと同じ運び: round の同時帰納(`RootWitness.dutyStoreAt_jointRoundInduction_of_prior`。手書き
`WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut`)を `base = cut = 0`、`limit = voteTime (d + 1)`、
行ごとの性質を SG block ⪯ X(手書きの第 1 連言)に置いて掛ける。`cut = 0` なので bootstrap と古い根の前提は空。段の genuine な確認
(手書きの `hprior`)は、行を出した tick が確認評価の tick(`emits_confTick`)で slot が `d` 未満(`emits_slot_lt_of_lt_nextVote`)
なので穴 `genuineConf_preceq_laterVoteHead` から、SG block と grade 2 の候補は `fgStep_preceq_laterVoteHead`(round 0 は証明済み、正の round は穴。周回 251)から(周回 250)。 -/
theorem fgWitness_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {x : ValidatorId} (hx : rho.honest.contains x = true)
    {u : ValidatorId} (hu : rho.honest.contains u = true)
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} {i2 : Nat} {t2 : Int}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2)
    (hev : rho.events[i2]? = some (NamedEvent.Tick u t2))
    (ht2 : t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) {T : Block}
    (hT : Proofs.Consensus.RootWitness.fgConfirmationWitnessAt c p a nr s rho u i2 t2 = some T) :
    preceq T (voteDutyHeadAt c p a nr s rho x d) = true := by
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho (Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep)).2
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, hunf⟩, -⟩ := hexec
  unfold UnforgeableSignatures at hunf
  obtain ⟨-, hcar⟩ := hunf
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  unfold ScheduleWellFormed at hsch
  obtain ⟨⟨⟨⟨⟨⟨hhor0, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := hsch
  have hlag : (0 : Int) ≤ Model.Consensus.Spec.Constants.participationLag s :=
    (Proofs.Consensus.Constants.period_pos s hfacts.1 hfacts.2.2).le
  have hqh := Proofs.Consensus.JustificationCertificate.quorumHonest_of_sleepyRegime
    (Proofs.Consensus.JustificationCertificate.sorted_validators hwf) hsleep hlag le_rfl (by rw [sub_self]; exact hhor0)
  have hum : u ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hu
  refine ((Proofs.Consensus.RootWitness.dutyStoreAt_jointRoundInduction_of_prior c p a nr s rho hfacts.1 (by omega) hs hnd
    hqh hcar hcf (base := 0) (cut := 0) (limit := Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))
    (X := voteDutyHeadAt c p a nr s rho x d)
    (fun w i t _ => preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho w i t)
      (voteDutyHeadAt c p a nr s rho x d) = true) le_rfl
    (fun _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)) ?_
    u i2 t2 row hum hev hem ht2 (Nat.zero_le _)).2 (Nat.zero_le _)).2 T hT
  intro w i t row' hw hi hem' hlim _ hprevQ hprev hsame hroot
  have hprior : ∀ C, Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
      preceq C (voteDutyHeadAt c p a nr s rho x d) = true := fun C hC =>
    genuineConf_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor
      ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hw) hx
      (emits_confTick c p a nr s rho hfacts.1 hem' hi) (emits_slot_lt_of_lt_nextVote c p a nr s rho hfacts.1 hem' hlim)
      hupper hC
  obtain ⟨hq, hg⟩ := fgStep_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hd hupper hx hw hi hem' hlim
    (fun w2 i2 t2 row2 hw2 hi2 hem2 hlt => hprevQ w2 i2 t2 row2 hw2 hi2 hem2 (Nat.zero_le _) hlt)
    (fun w2 i2 t2 row2 hw2 hi2 hem2 hlt => hprev w2 i2 t2 row2 hw2 hi2 hem2 (Nat.zero_le _) hlt)
    hsame hroot hprior
  exact ⟨hq, hprior, hg⟩

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick(添字 `i`・時刻 `t`、slot `q = slotOf e t - 1`)の確認の更新の前の段の
store の FG root は、`q < d ≤ last + 1`(`last` の確認の時刻は `horizon` 以下)の honest なノードの slot `d` の投票の務めの head の祖先。
手書き `preparedFGRoot_preceq_voteDutyHead_of_gstZero`(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。
手書きと同じ運び: FG root を tick の時刻の読みの FG root に移し(`confPreUpdate_fgRoot`)、その確認の証人
(`RootWitness.stateBeforeTime_fgRoot_confirmationWitness`。手書き `WeakFG.fgRoot_confirmationWitness_at_read`)で genesis か、
時刻 `< t` に honest な署名者が行を出した tick の務めの確認の証人に分け、後者は `t` が slot `d + 1` の投票時刻より前
(`confTick_lt_nextVote`)なので穴 `fgWitness_preceq_laterVoteHead` から(周回 247)。 -/
theorem confFgRoot_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1) :
    preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core))
      (voteDutyHeadAt c p a nr s rho x d) = true := by
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho (Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep)).2
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, hunf⟩, -⟩ := hexec
  unfold UnforgeableSignatures at hunf
  obtain ⟨-, hcar⟩ := hunf
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  unfold ScheduleWellFormed at hsch
  obtain ⟨⟨⟨⟨⟨⟨hhor0, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := hsch
  have hlag : (0 : Int) ≤ Model.Consensus.Spec.Constants.participationLag s :=
    (Proofs.Consensus.Constants.period_pos s hfacts.1 hfacts.2.2).le
  have hqh := Proofs.Consensus.JustificationCertificate.quorumHonest_of_sleepyRegime
    (Proofs.Consensus.JustificationCertificate.sorted_validators hwf) hsleep hlag le_rfl (by rw [sub_self]; exact hhor0)
  have hwm : w ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hw
  rw [confPreUpdate_fgRoot c p a nr s rho hfacts.1 hs hnd ht]
  rcases Proofs.Consensus.RootWitness.stateBeforeTime_fgRoot_confirmationWitness c p a nr s rho hs hqh hcar hcf hwm t with
    hg | ⟨-, row, -, t2, i2, -, -, hH, -, ht2, hem, hev, hT⟩
  · rw [hg]
    exact Proofs.Consensus.Blocks.preceq_genesis _
  · exact fgWitness_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor (by omega) hupper hx
      ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hH) hem hev
      (lt_trans ht2 (confTick_lt_nextVote s rho hfacts.1 ht hqd)) hT

/-- 穴: `confFgRoot_preceq_laterVoteHead` と同じ前提で、確認の更新の前の段の store の round が正なら、その round の g1 の frame の
raw ブロックは slot `d` の投票の務めの head の祖先。手書き `preparedG1Raw_preceq_voteDutyHead_of_gstZero` の正の round の枝
(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。
閉じるのに要るもの: raw が G1 の grade を通ること(手書き `WeakSG.phaseGrade_of_preparedFrame_g1`。値は `confFrameG1_slot_positive`)と、
grade の carrier(手書き `relativeGradeCarrierAt_of_awakeWindowMajority`)の honest な投票の務めの出どころ(手書き
`actionSources_preceq_voteDutyHead_of_gstZero`)。 -/
theorem confG1Raw_preceq_laterVoteHead_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1)
    (hpos : 0 < Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) {raw : Block}
    (hraw : (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g1 = some (some raw)) :
    preceq raw (voteDutyHeadAt c p a nr s rho x d) = true := by
  sorry

/-- `confFgRoot_preceq_laterVoteHead` と同じ前提で、確認の更新の前の段の store の round の g1 の frame の raw ブロックは、
slot `d` の投票の務めの head の祖先。手書き `preparedG1Raw_preceq_voteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。round 0 は g1 の frame に root が無いので矛盾
(`confCache_g1_round_zero`)、正の round は穴 `confG1Raw_preceq_laterVoteHead_positive` から(周回 246)。 -/
theorem confG1Raw_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1) {raw : Block}
    (hraw : (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g1 = some (some raw)) :
    preceq raw (voteDutyHeadAt c p a nr s rho x d) = true := by
  rcases Nat.eq_zero_or_pos (Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) with h0 | hpos
  · rw [h0] at hraw
    exact (confCache_g1_round_zero c p a nr s rho _ hraw).elim
  · exact confG1Raw_preceq_laterVoteHead_positive c p a nr s rho hwf hdom hsleep hhor hw hx ht hqd hupper hpos hraw

/-- `confFgRoot_preceq_laterVoteHead` と同じ前提で、確認の walk が anchor から動いた(filtered tree の要素で、得点の 2 倍が
遅い投票の参加者の数を超える。genuine な確認)なら、walk は slot `d` の投票の務めの head の祖先。手書き
`preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero` の genuine な枝(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。
walk は eligible なので genuine な確認(`RootWitness.GenuineConfirmationAt`。`Goldfish.eligible_iff`)で、手書きと同じく
保護された投票の slot の `heads`(穴 `genuineConf_preceq_laterVoteHead`)から(周回 250)。 -/
theorem confEligibleWalk_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1)
    (hmem : Proofs.Consensus.ConfirmedOrigin.confWalkAt c p a nr s rho w i t ∈
      (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)).elems)
    (hel : Proofs.Consensus.Goldfish.lateCount s.e (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core
        (Model.Consensus.Objects.Parameters.slotOf s.e t - 1) <
      2 * Proofs.Consensus.Goldfish.score s.e (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core
        (Model.Consensus.Objects.Parameters.slotOf s.e t - 1) (Proofs.Consensus.ConfirmedOrigin.confWalkAt c p a nr s rho w i t)) :
    preceq (Proofs.Consensus.ConfirmedOrigin.confWalkAt c p a nr s rho w i t) (voteDutyHeadAt c p a nr s rho x d) = true :=
  genuineConf_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hw hx ht hqd hupper
    ⟨rfl, (Proofs.Consensus.Goldfish.eligible_iff _ _ _ _).mpr hel⟩

/-- GST-zero の枝で、確認評価の tick の確認の walk の anchor(確認の更新の前の段の store の SG root)は、slot `d` の投票の務めの head の祖先。
手書き `preparedConfirmationAnchor_preceq_voteDutyHead_of_gstZero`(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。
anchor は g1 の frame の raw の active prefix(`Grade2Capture.activePrefix_preceq` で raw の祖先)か FG root なので、穴
`confG1Raw_preceq_laterVoteHead` / `confFgRoot_preceq_laterVoteHead` から。 -/
theorem confAnchor_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1) :
    preceq (Proofs.Consensus.Goldfish.sgRoot (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) s.e s.hc
        (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
      (voteDutyHeadAt c p a nr s rho x d) = true := by
  have hfg := confFgRoot_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hw hx ht hqd hupper
  show preceq (Model.Consensus.Protocol.Grades.anchor s.e s.hc
      (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
      (Model.Consensus.Protocol.Grades.roundOf s.hc
        (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)
      (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g1)
    (voteDutyHeadAt c p a nr s rho x d) = true
  unfold Model.Consensus.Protocol.Grades.anchor
  split
  · rename_i raw hraw
    have hhead := confG1Raw_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hw hx ht hqd hupper hraw
    cases hA : Model.Consensus.Protocol.Grades.activePrefix
        (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree
          (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core))
        raw with
    | none => exact hfg
    | some A => exact Proofs.Consensus.Blocks.preceq_trans (Proofs.Consensus.Grade2Capture.activePrefix_preceq hA) hhead
  · exact hfg

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick(添字 `i`・時刻 `t`、slot `q = slotOf e t - 1`)の確認の walk
(`ConfirmedOrigin.confWalkAt`: 確認の更新の前の段の fork choice の head)は、`q < d ≤ last + 1`(`last` の確認の時刻は `horizon` 以下)の
honest などのノードの slot `d` の投票の務めの head の祖先。手書き `preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。
walk は anchor のままか(`Goldfish.head_cases`)、filtered tree の適格な要素なので、`confAnchor_preceq_laterVoteHead` と穴
`confEligibleWalk_preceq_laterVoteHead` から(周回 245)。 -/
theorem confWalk_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1) :
    preceq (Proofs.Consensus.ConfirmedOrigin.confWalkAt c p a nr s rho w i t) (voteDutyHeadAt c p a nr s rho x d) = true := by
  rcases Proofs.Consensus.Goldfish.head_cases (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) s.e s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core
      (Model.Consensus.Objects.Parameters.slotOf s.e t - 1) with h | ⟨hmem, hel⟩
  · unfold Proofs.Consensus.ConfirmedOrigin.confWalkAt
    rw [h]
    exact confAnchor_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hw hx ht hqd hupper
  · exact confEligibleWalk_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hw hx ht hqd hupper hmem hel

/-- **g2 の frame の root の出どころ**: run の添字 `i` の event が `w` の時刻 `t` の tick なら、その tick が準備する cache
(`ConfirmedOrigin.confCacheAt`)の round `k` の frame をどの store で読んでも、G2 の結果 `some (some raw)` の祖先 `P` は、
添字 `j ≤ i` の event `Tick w (domainTime e hc k G2)` の前の store で `freezeRoot` が凍結した `g2v` の祖先。読みの切り詰めを
`clipResult_some` で外し、この tick の凍結か tick の前の結果(`Grade2Capture.onPhaseTick_g2_cases`)、後者は run の帰納
(`Grade2Capture.stateBefore_g2_origin`)に渡す。手書き `q10_g1_slot_of_g2_slot` の前半(`frame_phase_completed_in_round` の G2 の枝を
祖先の関係に弱めた形)に当たる(周回 234)。 -/
theorem confCache_g2_origin {w : ValidatorId} {i : Nat} {t : Int} (hev : rho.events[i]? = some (NamedEvent.Tick w t))
    (st : Model.Consensus.Protocol.ForkChoice.Goldfish.FGStore) {k : Nat} {P raw : Block}
    (h : (Model.Consensus.Protocol.Grades.readFrame (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) st k).g2 =
      some (some raw)) (hP : preceq P raw = true) :
    ∃ (j : Nat) (g2v : Block), j ≤ i ∧
      rho.events[j]? = some (NamedEvent.Tick w
        (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)) ∧
      Model.Consensus.Protocol.Grades.freezeRoot s.e
          (Model.Consensus.Protocol.Grades.gradeView
            (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core))
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core).f s.hc.etaSG k
          (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)
          (Model.Consensus.Protocol.Grades.lateTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2) = some g2v ∧
      preceq P g2v = true := by
  change Model.Consensus.Protocol.Grades.clipResult st.f
    (Model.Consensus.Protocol.Grades.cacheAtRound (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) k).g2 =
      some (some raw) at h
  obtain ⟨b1, hb1, hPb1⟩ := Proofs.Consensus.Grade2Capture.clipResult_some h hP
  unfold Proofs.Consensus.ConfirmedOrigin.confCacheAt at hb1
  obtain ⟨b0, hb10, hold | ⟨ht, hfz⟩⟩ := Proofs.Consensus.Grade2Capture.onPhaseTick_g2_cases hb1
  · obtain ⟨j, u, b2, hj, hju, hu, hfz, hb02⟩ := Proofs.Consensus.Grade2Capture.stateBefore_g2_origin c p a nr s rho i w k hold
    subst hu
    exact ⟨j, b2, hj.le, hju, hfz,
      Proofs.Consensus.Blocks.preceq_trans hPb1 (Proofs.Consensus.Blocks.preceq_trans hb10 hb02)⟩
  · subst ht
    exact ⟨i, b0, le_rfl, hev, hfz, Proofs.Consensus.Blocks.preceq_trans hPb1 hb10⟩

/-- **切り詰めは finalized と互換な祖先を保つ**: `P ⪯ g` で `P` が `f` と互換なら `P ⪯ clipGrade g f`。`g` の親を遡る帰納法で、
`g` が `f` と互換なら `clipGrade` は `g` のまま、そうでなければ `P ≠ g`(`P` は互換)なので `P` は親の祖先。手書き `q10_retained_prefix`
(`Protocol/Grades/Q10Frame.lean`)の向きの一方(周回 234)。 -/
theorem preceq_clipGrade_of_compatible {P g f : Block} (hPg : preceq P g = true) (hPf : compatible P f = true) :
    preceq P (Model.Consensus.Protocol.Grades.clipGrade g f) = true := by
  induction g with
  | Genesis =>
    rw [Model.Consensus.Protocol.Grades.clipGrade]
    exact hPg
  | Node q sl r v sup ats i ih =>
    rw [Model.Consensus.Protocol.Grades.clipGrade]
    split_ifs with hc
    · exact hPg
    · simp only [preceq, Bool.or_eq_true, beq_iff_eq] at hPg
      rcases hPg with rfl | hPq
      · exact absurd hPf hc
      · exact ih hPq

/-- 要素がすべて `m` で `m` を含む重複なしのリストは `[m]`。 -/
theorem list_eq_singleton_of_nodup {α : Type} {l : List α} {m : α} (hnd : l.Nodup) (hall : ∀ x ∈ l, x = m)
    (hm : m ∈ l) : l = [m] := by
  cases l with
  | nil => simp at hm
  | cons a rest =>
    have ha : a = m := hall a (List.mem_cons_self ..)
    subst ha
    cases rest with
    | nil => rfl
    | cons b rest' =>
      have hb : b = a := hall b (by simp)
      subst hb
      simp at hnd

/-- **active prefix の支配**: `g` が tree にあり `g ⪯ r` で、`activePrefix tree r = some d` なら `g ⪯ d`。
`r` の祖先は鎖(`Blocks.preceq_linear`)で、`d` は tree の `r` の祖先のうち最も深い(`isDeepestIn`)ので、`d ⪯ g` なら深さが等しく
`d = g`(`Goldfish.preceq_eq_of_depth_le`)。手書き `q10_activePrefix_dominates`(`Protocol/Grades/Q10Frame.lean`)の支配の半分(周回 232)。 -/
theorem activePrefix_dominates {tree : NaruStd.Set Block} {r g d : Block} (hg : g ∈ tree.elems)
    (hgr : preceq g r = true) (hd : Model.Consensus.Protocol.Grades.activePrefix tree r = some d) :
    preceq g d = true := by
  unfold Model.Consensus.Protocol.Grades.activePrefix deepest? at hd
  obtain ⟨hdm, hdeep⟩ := Proofs.Consensus.Trees.findUnique?_mem hd
  have hdr := ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hdm).2
  have hgf : g ∈ (tree.filter fun b => preceq b r).elems :=
    (Proofs.Consensus.Trees.mem_filter_iff _ _ _).mpr ⟨hg, hgr⟩
  unfold isDeepestIn NaruStd.Set.all at hdeep
  have hnot := List.all_eq_true.mp hdeep g hgf
  simp only [deeper, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hnot
  rcases Proofs.Consensus.Blocks.preceq_linear hgr hdr with h | h
  · exact h
  · have := Proofs.Consensus.Goldfish.preceq_eq_of_depth_le h (by omega)
    subst this
    exact Proofs.Consensus.Blocks.preceq_self _

/-- **active prefix の存在**: tree の要素に重複が無く、`g` が tree にあり `g ⪯ r` なら、`activePrefix tree r` は `some`。
tree の `r` の祖先は鎖なので、最も深いもの `m` は `isDeepestIn` を満たす唯一の要素(同じ深さの 2 つの祖先は等しい)で、
重複なしなので `findUnique?` が `m` を返す。手書き `q10_activePrefix_dominates` の存在の半分(手書きの tree は `Finset` なので
重複なしは要らない。naru の `Set` は表現のリストを読むので要る。周回 232)。 -/
theorem activePrefix_exists {tree : NaruStd.Set Block} {r g : Block} (hnd : tree.elems.Nodup)
    (hg : g ∈ tree.elems) (hgr : preceq g r = true) :
    ∃ d, Model.Consensus.Protocol.Grades.activePrefix tree r = some d := by
  classical
  let F := tree.filter fun b => preceq b r
  have hgf : g ∈ F.elems := (Proofs.Consensus.Trees.mem_filter_iff _ _ _).mpr ⟨hg, hgr⟩
  have hFr : ∀ x ∈ F.elems, preceq x r = true := fun x hx => ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hx).2
  obtain ⟨m, hmF, hmax⟩ := Finset.exists_max_image F.elems.toFinset depth ⟨g, List.mem_toFinset.mpr hgf⟩
  rw [List.mem_toFinset] at hmF
  have hmax' : ∀ x ∈ F.elems, depth x ≤ depth m := fun x hx => hmax x (List.mem_toFinset.mpr hx)
  have hsame : ∀ x ∈ F.elems, ∀ y ∈ F.elems, depth x = depth y → x = y := by
    intro x hx y hy hxy
    rcases Proofs.Consensus.Blocks.preceq_linear (hFr x hx) (hFr y hy) with h | h
    · exact Proofs.Consensus.Goldfish.preceq_eq_of_depth_le h (by omega)
    · exact (Proofs.Consensus.Goldfish.preceq_eq_of_depth_le h (by omega)).symm
  have hdeepm : isDeepestIn F m = true := by
    unfold isDeepestIn NaruStd.Set.all
    refine List.all_eq_true.mpr fun c hc => ?_
    simp only [deeper, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨by have := hmax' c hc; omega, ?_⟩
    by_cases hdc : depth m = depth c
    · have := hsame m hmF c hc hdc
      subst this
      have : compare (root m) (root m) = .eq := (Proofs.Consensus.Orders.bid_compare_eq_iff _ _).mpr rfl
      simp [this]
    · simp [hdc]
  have hD : F.elems.filter (fun b => isDeepestIn F b) = [m] := by
    refine list_eq_singleton_of_nodup ((hnd.filter _).filter _) ?_ (List.mem_filter.mpr ⟨hmF, hdeepm⟩)
    intro x hx
    obtain ⟨hxF, hxd⟩ := List.mem_filter.mp hx
    unfold isDeepestIn NaruStd.Set.all at hxd
    have hnot := List.all_eq_true.mp hxd m hmF
    simp only [deeper, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hnot
    exact hsame x hxF m hmF (by have := hmax' x hxF; omega)
  refine ⟨m, ?_⟩
  unfold Model.Consensus.Protocol.Grades.activePrefix deepest? NaruStd.Set.findUnique?
  rw [hD]

/-- filtered tree(store の tree の絞り込み)は、store の tree の要素に重複が無ければ重複が無い。 -/
theorem getFilteredBlockTree_nodup {hs : Model.Consensus.Protocol.ForkChoice.Goldfish.FGStore} (hnd : hs.tree.elems.Nodup) :
    (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree hs).elems.Nodup := by
  unfold Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree
    Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTreeFrom
    Model.Consensus.Protocol.ForkChoice.Goldfish.viableTree
    Model.Consensus.Protocol.ForkChoice.Goldfish.finalizedDescendants NaruStd.Set.filter
  exact ((hnd.filter _).filter _).filter _

/-- 確認の更新の前の段の store(`RootWitness.preUpdateStoreAt`)の tree の要素に重複は無い。tree を変えるのは初期 store の
`Set.singleton Genesis` と受理の `Set.insert` だけ(`Handlers.naru`)で、受理はまだ tree に無いブロックだけを入れるので、
`TreeInv` の欄 `nodup`(`Trees.nodup_insertSorted`)が run の帰納で保たれる。確認の更新の前の段は `tickDutyStore` と同じ運びで
tick の前の store の `TreeInv` を受け継ぐ(`AttestationSource.tickPreUpdateStore_treeInv`)。
手書き `q10_activePrefix_dominates`(`Protocol/Grades/Q10Frame.lean`)の存在の半分で、手書きの tree は `Finset` なのでこの事実は要らない
(naru の `activePrefix` は表現のリストの `findUnique?` なので要る。周回 232 に穴として置き、周回 233 に閉じた)。 -/
theorem preUpdateTree_nodup (w : ValidatorId) (i : Nat) (t : Int) :
    (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.tree.elems.Nodup :=
  (Proofs.Consensus.AttestationSource.tickPreUpdateStore_treeInv c p nr _ s.hc _ t (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i w)
    (Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho i w)).nodup

/-- 確認の更新の前の段 `tickPreUpdateStore` は `f` を延ばすだけ(時計合わせは `f` 不変、提案は `Stores.proposeBlockWith_f`、
投票は `f` 不変)。 -/
theorem tickPreUpdateStore_f (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : Model.Consensus.Protocol.Handlers.NamedStore) (t : Int) :
    preceq st.core.f (Proofs.Consensus.AttestationSource.tickPreUpdateStore c p nr cache e hc cfg nd st t).core.f = true := by
  unfold Proofs.Consensus.AttestationSource.tickPreUpdateStore
  dsimp only
  split_ifs
  all_goals simp only [Proofs.Consensus.Stores.namedGoldfishVoteWith_f]
  all_goals first
    | exact Proofs.Consensus.Stores.proposeBlockWith_f' c p nr cache e hc cfg nd rfl
    | exact Proofs.Consensus.Blocks.preceq_self _

open Proofs.Consensus.Clocks in
/-- 確認の更新の前の段 `tickPreUpdateStore` の後の時計は `(t, slotOf e t)`(冒頭で合わせた時計を提案と投票が変えない)。 -/
theorem tickPreUpdateStore_clockIs (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : Model.Consensus.Protocol.Handlers.NamedStore) (t : Int) :
    Proofs.Consensus.Clocks.ClockIs (Proofs.Consensus.AttestationSource.tickPreUpdateStore c p nr cache e hc cfg nd st t) t
      (Model.Consensus.Objects.Parameters.slotOf e t) := by
  have h0 : Proofs.Consensus.Clocks.ClockIs { st with core := { st.core with t := t, s := Model.Consensus.Objects.Parameters.slotOf e t } }
      t (Model.Consensus.Objects.Parameters.slotOf e t) := ⟨rfl, rfl⟩
  unfold Proofs.Consensus.AttestationSource.tickPreUpdateStore
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact namedGoldfishVoteWith_clockIs c cache hc nd (proposeBlockWith_clockIs c p nr cache hc nd h0)
    | with_reducible exact namedGoldfishVoteWith_clockIs c cache hc nd h0
    | with_reducible exact proposeBlockWith_clockIs c p nr cache hc nd h0
    | with_reducible exact h0

/-- round `R` の G1 の domain 時刻は round `R` の opening slot の開始(`domainOffset G1 = 0`)。 -/
theorem domainTime_G1 (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (R : Nat) :
    Model.Consensus.Protocol.Grades.domainTime e hc R Model.Consensus.Protocol.Grades.GradePhase.G1 =
      Model.Consensus.Protocol.Schedule.proposalTime e (Model.Consensus.Protocol.Grades.openingSlot hc R) := by
  unfold Model.Consensus.Protocol.Grades.domainTime Model.Consensus.Protocol.Grades.openingTime
  simp [Model.Consensus.Protocol.Grades.domainOffset]

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick の、確認の更新の前の段の store の round `R` が正なら、その tick が
準備する cache(`ConfirmedOrigin.confCacheAt`)の round `R` の frame の G1 の結果は完了している(`none` でない)。
手書き `FrameCompleted.frame_phase_completed_of_tick_in_round`(`Protocol/Grades/FrameCompleted.lean`)の段 1・2(domain の tick が欄を閉じ、読みまで残る)と、
`frame_phase_completed_in_round` の domain の tick の存在(`tick_total`)に当たる(周回 243 に `confFrameG1_slot_positive` から切り出し、周回 244 に閉じた)。
確認の更新の前の段の slot は確認評価の tick の slot `S = slotOf e t`(`tickPreUpdateStore_clockIs`)で、`R = roundOf hc S`。
G1 の domain 時刻 `T1 = proposalTime (R * r)`(`domainTime_G1`)は公開時刻で `0 ≤ T1 < t ≤ horizon`(`t = supportCutoff S`)なので、
`ScheduleWellFormed` の tick の網羅性から `w` の tick `Tick w T1` が添字 `j < i` にある(`Window.honest_tick_index` / `Window.lt_of_time_lt`)。
`j` と `i` の間の `w` の tick の時刻は `T1` 以上 `t` 以下(event の整列)なので、その slot は `R * r` 以上 `S` 以下で round は `R`。
よって `FrameCapture.stateBefore_closed` で tick の前の cache の round は `R` で G1 の欄は閉じていて、確認評価の tick の
`onPhaseTick` も同じ round なので欄を残す(`FrameCapture.onPhaseTick_closed`)。 -/
theorem confFrameG1_closed_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hpos : 0 < Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) :
    (Model.Consensus.Protocol.Grades.cacheAtRound (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
      (Model.Consensus.Protocol.Grades.roundOf s.hc
        (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g1 ≠ none := by
  have hsch : ScheduleWellFormed s rho := by
    have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
    unfold ExecutionValid at hexec
    exact hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  obtain ⟨hδ, -, hr⟩ := Proofs.Consensus.Liveness.wf_facts hwf
  have hS : (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s =
      Model.Consensus.Objects.Parameters.slotOf s.e t :=
    (tickPreUpdateStore_clockIs c p nr _ s.e s.hc s.cfg _ _ t).2
  rw [hS]
  set S := Model.Consensus.Objects.Parameters.slotOf s.e t with hSdef
  set R := Model.Consensus.Protocol.Grades.roundOf s.hc S with hRdef
  set T1 := Model.Consensus.Protocol.Grades.domainTime s.e s.hc R Model.Consensus.Protocol.Grades.GradePhase.G1 with hT1def
  have hT1 : T1 = Model.Consensus.Protocol.Schedule.proposalTime s.e (R * s.hc.r) := domainTime_G1 s.e s.hc R
  have hRS : R * s.hc.r ≤ S := Nat.div_mul_le_self S s.hc.r
  -- 時刻の範囲: `0 ≤ T1 < t ≤ horizon`
  have hT1nn : 0 ≤ T1 := hT1 ▸ Proofs.Consensus.Window.proposalTime_nonneg s.e hδ.le _
  have hT1t : T1 < t := by
    have h1 := Proofs.Consensus.Clocks.proposalTime_mono s.e hδ hRS
    have h2 : t = Model.Consensus.Protocol.Schedule.proposalTime s.e S + 2 * s.e.delta := ht.2.2
    rw [hT1]
    linarith
  have hth : t ≤ rho.horizon := (Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? ht.1)).2
  -- domain の tick
  obtain ⟨j, hj⟩ := Proofs.Consensus.Window.honest_tick_index hsch hw
    (hT1 ▸ Proofs.Consensus.Window.publicTime_proposalTime s.e _) hT1nn (by linarith)
  have hji : j < i := Proofs.Consensus.Window.lt_of_time_lt hs hj ht.1 hT1t
  have hr0 : 0 < s.hc.r := by omega
  have hround : ∀ x : Nat, R * s.hc.r ≤ x → x ≤ S → Model.Consensus.Protocol.Grades.roundOf s.hc x = R := by
    intro x h1 h2
    unfold Model.Consensus.Protocol.Grades.roundOf
    have h3 : x / s.hc.r ≤ S / s.hc.r := Nat.div_le_div_right h2
    have h4 : R * s.hc.r / s.hc.r ≤ x / s.hc.r := Nat.div_le_div_right h1
    rw [Nat.mul_div_cancel _ hr0] at h4
    exact le_antisymm h3 h4
  have hτR : Model.Consensus.Protocol.Grades.roundOf s.hc (Model.Consensus.Objects.Parameters.slotOf s.e T1) = R := by
    rw [hT1, Proofs.Consensus.Clocks.slotOf_proposalTime s.e hδ]
    exact hround _ le_rfl hRS
  -- 間の tick の round は `R`
  have hmid : ∀ (m : Nat) (u : Int), j < m → m < i →
      rho.events[m]? = some (NamedEvent.Tick w u) →
      Model.Consensus.Protocol.Grades.roundOf s.hc (Model.Consensus.Objects.Parameters.slotOf s.e u) = R := by
    intro m u hjm hmi hm
    have hle1 : T1 ≤ u := by
      have h := hs j m hjm
      simp only [hj, hm] at h
      exact Proofs.Consensus.Runs.time_le_of_key_ne_gt h
    have hle2 : u ≤ t := by
      have h := hs m i hmi
      simp only [hm, ht.1] at h
      exact Proofs.Consensus.Runs.time_le_of_key_ne_gt h
    refine hround _ ?_ (Proofs.Consensus.Clocks.slotOf_mono s.e hδ hle2)
    have h := Proofs.Consensus.Clocks.slotOf_mono s.e hδ hle1
    rwa [hT1, Proofs.Consensus.Clocks.slotOf_proposalTime s.e hδ] at h
  obtain ⟨hc1, hc2⟩ := Proofs.Consensus.FrameCapture.stateBefore_closed c p a nr s rho w hj hτR hT1def hji hmid
  obtain ⟨hc3, hc4⟩ := Proofs.Consensus.FrameCapture.onPhaseTick_closed
    (st := Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core)
    (P := Model.Consensus.Protocol.Grades.GradePhase.G1) (R := R) rfl (Or.inl ⟨hc1, hc2⟩)
  unfold Proofs.Consensus.ConfirmedOrigin.confCacheAt
  rw [Proofs.Consensus.FrameCapture.cacheAtRound_self hc3]
  exact hc4

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick の、確認の更新の前の段の store の round `R` が正なら、読みの frame の
G1 の欄は閉じていて、添字 `j1 ≤ i` の event `Tick w (domainTime e hc R G1)` の前の store で凍結した `freezeRoot` を読みの store の
finalized `F` で切り詰めたもの。その store の finalized は `F` の祖先。手書き `FrameCompleted.frame_phase_completed_in_round`
(`Protocol/Grades/FrameCompleted.lean`)の G1 の枝と、手書き `q10_g1_slot_of_g2_slot` の `hFmono`(`stateBefore_F_mono`)に当たる(周回 234)。
欄が閉じていることは `confFrameG1_closed_positive`(周回 244 に閉じた)、値は確認評価の tick の phase tick の段 `FrameCapture.onPhaseTick_phase_some`
(この tick の凍結か tick の前の結果)と run の帰納 `FrameCapture.stateBefore_phase_origin`(完了した結果は domain の tick の凍結を
いまの finalized で切り詰めたもの)から、切り詰めを `FrameCapture.map_clip_clip` でまとめて出す。finalized の単調性は
`ReceiverFinality.stateBefore_f_mono` と `tickPreUpdateStore_f`(周回 243)。 -/
theorem confFrameG1_slot_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hpos : 0 < Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) :
    ∃ j1 : Nat, j1 ≤ i ∧
      rho.events[j1]? = some (NamedEvent.Tick w
        (Model.Consensus.Protocol.Grades.domainTime s.e s.hc
          (Model.Consensus.Protocol.Grades.roundOf s.hc
            (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)
          Model.Consensus.Protocol.Grades.GradePhase.G1)) ∧
      preceq (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j1) w).st.core).f
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core).f = true ∧
      (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g1 =
        some ((Model.Consensus.Protocol.Grades.freezeRoot s.e
          (Model.Consensus.Protocol.Grades.gradeView
            (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j1) w).st.core))
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j1) w).st.core).f s.hc.etaSG
          (Model.Consensus.Protocol.Grades.roundOf s.hc
            (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)
          (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc
              (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G1)
          (Model.Consensus.Protocol.Grades.lateTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc
              (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G1)).map
          (fun b => Model.Consensus.Protocol.Grades.clipGrade b
            (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core).f)) := by
  have hcl := confFrameG1_closed_positive c p a nr s rho hwf hdom hsleep hw ht hpos
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hcl
  have hfpre : preceq (worldAt (stateBefore c p a nr s rho i) w).st.core.f
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.f = true :=
    tickPreUpdateStore_f c p nr _ s.e s.hc s.cfg _ _ t
  have hy' : Model.Consensus.Protocol.Grades.phaseResult
      (Model.Consensus.Protocol.Grades.cacheAtRound
        (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
          (worldAt (stateBefore c p a nr s rho i) w).cache)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s))
      Model.Consensus.Protocol.Grades.GradePhase.G1 = some y := hy
  have hread : ∀ X : Model.Consensus.Protocol.Grades.Frame,
      X.g1 = Model.Consensus.Protocol.Grades.phaseResult X Model.Consensus.Protocol.Grades.GradePhase.G1 := fun _ => rfl
  rcases Proofs.Consensus.FrameCapture.onPhaseTick_phase_some hy' with ⟨x0, hx0, rfl⟩ | ⟨htd, rfl⟩
  · obtain ⟨j1, hj1, hev1, rfl⟩ :=
      Proofs.Consensus.FrameCapture.stateBefore_phase_origin c p a nr s rho i w hpos _ hx0
    refine ⟨j1, hj1.le, hev1,
      Proofs.Consensus.Blocks.preceq_trans (Proofs.Consensus.ReceiverFinality.stateBefore_f_mono c p a nr s rho hj1.le w) hfpre, ?_⟩
    rw [hread, Proofs.Consensus.FrameCapture.phaseResult_readFrame]
    unfold Proofs.Consensus.ConfirmedOrigin.confCacheAt
    rw [hy']
    simp only [Model.Consensus.Protocol.Grades.clipResult, Option.map_some, Proofs.Consensus.FrameCapture.storeToHealing_f]
    rw [Proofs.Consensus.FrameCapture.map_clip_clip (Proofs.Consensus.Blocks.preceq_self _),
      Proofs.Consensus.FrameCapture.map_clip_clip hfpre]
  · refine ⟨i, le_rfl, htd ▸ ht.1, hfpre, ?_⟩
    rw [hread, Proofs.Consensus.FrameCapture.phaseResult_readFrame]
    unfold Proofs.Consensus.ConfirmedOrigin.confCacheAt
    rw [hy']
    simp only [Model.Consensus.Protocol.Grades.clipResult, Option.map_some, Proofs.Consensus.FrameCapture.storeToHealing_f]
    rw [Proofs.Consensus.FrameCapture.map_clip_clip hfpre]

/-- **互換な要素の集合の最も深い要素**: 重複なしで要素が互いに互換な集合 `F` に `g` があれば、`deepest? F` は `some m` で
`g ⪯ m`。深さが最大の `m` を取ると、互換な `x` は `x ⪯ m` か `m ⪯ x`(このとき深さが等しく `x = m`。`Goldfish.preceq_eq_of_depth_le`)で、
同じ深さの要素は等しいので `isDeepestIn` を満たすのは `m` だけ。手書き `HealingSurface.deepest?_isSome_of_compatible` と
`HealingLemmas.deepest?_dominates`(手書きの集合は `Finset` なので重複なしは要らない。周回 235)。 -/
theorem deepest?_of_compatible {F : NaruStd.Set Block} (hnd : F.elems.Nodup)
    (hcmp : ∀ x ∈ F.elems, ∀ y ∈ F.elems, compatible x y = true) {g : Block} (hg : g ∈ F.elems) :
    ∃ m, deepest? F = some m ∧ preceq g m = true := by
  classical
  obtain ⟨m, hmF, hmax⟩ := Finset.exists_max_image F.elems.toFinset depth ⟨g, List.mem_toFinset.mpr hg⟩
  rw [List.mem_toFinset] at hmF
  have hmax' : ∀ x ∈ F.elems, depth x ≤ depth m := fun x hx => hmax x (List.mem_toFinset.mpr hx)
  have hlin : ∀ x ∈ F.elems, ∀ y ∈ F.elems, preceq x y = true ∨ preceq y x = true := by
    intro x hx y hy
    have := hcmp x hx y hy
    unfold compatible at this
    rwa [Bool.or_eq_true] at this
  have hsame : ∀ x ∈ F.elems, ∀ y ∈ F.elems, depth x = depth y → x = y := by
    intro x hx y hy hxy
    rcases hlin x hx y hy with h | h
    · exact Proofs.Consensus.Goldfish.preceq_eq_of_depth_le h (by omega)
    · exact (Proofs.Consensus.Goldfish.preceq_eq_of_depth_le h (by omega)).symm
  have hdom : ∀ x ∈ F.elems, preceq x m = true := by
    intro x hx
    rcases hlin x hx m hmF with h | h
    · exact h
    · have := Proofs.Consensus.Goldfish.preceq_eq_of_depth_le h (hmax' x hx)
      subst this
      exact Proofs.Consensus.Blocks.preceq_self _
  have hdeepm : isDeepestIn F m = true := by
    unfold isDeepestIn NaruStd.Set.all
    refine List.all_eq_true.mpr fun c hc => ?_
    simp only [deeper, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨by have := hmax' c hc; omega, ?_⟩
    by_cases hdc : depth m = depth c
    · have := hsame m hmF c hc hdc
      subst this
      have : compare (root m) (root m) = .eq := (Proofs.Consensus.Orders.bid_compare_eq_iff _ _).mpr rfl
      simp [this]
    · simp [hdc]
  have hD : F.elems.filter (fun b => isDeepestIn F b) = [m] := by
    refine list_eq_singleton_of_nodup (hnd.filter _) ?_ (List.mem_filter.mpr ⟨hmF, hdeepm⟩)
    intro x hx
    obtain ⟨hxF, hxd⟩ := List.mem_filter.mp hx
    unfold isDeepestIn NaruStd.Set.all at hxd
    have hnot := List.all_eq_true.mp hxd m hmF
    simp only [deeper, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hnot
    exact hsame x hxF m hmF (by have := hmax' x hxF; omega)
  refine ⟨m, ?_, hdom g hg⟩
  unfold deepest? NaruStd.Set.findUnique?
  rw [hD]

/-- **grade の通った tree の要素があれば凍結の root はそれ以上**: grade view の tree に重複が無く、`early ≤ late` で、tree の要素 `b` が
`gradeBool` を満たせば、`freezeRoot` は `some raw` で `b ⪯ raw`。grade の通った要素は互いに互換
(`GradeSupporter.graded_compatible`)なので `deepest?_of_compatible` に渡す。手書き `q10_freeze_of_graded`
(`SGFromSupport.sg_freeze_of_graded`、`Protocol/Grades/Q10Frame.lean`。周回 235)。 -/
theorem freezeRoot_of_graded {e : Model.Consensus.Objects.Parameters.ProtocolEnv}
    (hv : Proofs.Consensus.Sets.Sorted (Model.Consensus.Objects.Weights.validators e.electorate))
    {gv : Model.Consensus.Protocol.Grades.GradeView} {f : Block} {eta r : Nat} {early late : Int} (hel : early ≤ late)
    (hnd : gv.tree.elems.Nodup) {b : Block} (hmem : b ∈ gv.tree.elems)
    (hgrade : Model.Consensus.Protocol.Grades.gradeBool e gv f eta r early late b = true) :
    ∃ raw, Model.Consensus.Protocol.Grades.freezeRoot e gv f eta r early late = some raw ∧ preceq b raw = true := by
  unfold Model.Consensus.Protocol.Grades.freezeRoot
  refine deepest?_of_compatible (hnd.filter _) ?_ ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mpr ⟨hmem, hgrade⟩)
  intro x hx y hy
  exact Proofs.Consensus.GradeSupporter.graded_compatible e hv gv f eta r hel
    ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hx).2 ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hy).2

/-- G2 の domain 時刻は同じ round の G1 の domain 時刻より `Δ` 前(`0 < Δ` なら狭義に早い)。 -/
theorem domainTime_G2_lt_G1 (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (hδ : 0 < e.delta) (k : Nat) :
    Model.Consensus.Protocol.Grades.domainTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G2 <
      Model.Consensus.Protocol.Grades.domainTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G1 := by
  unfold Model.Consensus.Protocol.Grades.domainTime
  simp only [Model.Consensus.Protocol.Grades.domainOffset]
  linarith

/-- ノード `w` の round `k` の G2 の domain 時刻の tick(添字 `j2`)の前の store の tree の要素は、同じ round の G1 の domain 時刻の
tick(添字 `j1`)の前の store の tree にもある。手書き `q10_tree_fwd`(`Protocol/Grades/Q10Frame.lean`)に当たる(周回 235 に穴として置き、
周回 236 に証明した)。G2 の domain 時刻は G1 より `Δ` 前(`domainTime_G2_lt_G1`)で run の event は時刻の順(`SleepyRegime` の
`ScheduleWellFormed`)なので `j2 < j1`(`Window.lt_of_time_lt`)、tree のブロックは run の添字について残る
(`BlockStamps.stateBefore_keep`。手書き `q10_strict_body_carry`)。 -/
theorem g1Tree_of_g2Tree (hwf : SetupWellFormed c p s) (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} {k j2 j1 : Nat}
    (hj2 : rho.events[j2]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)))
    (hj1 : rho.events[j1]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)))
    {b : Block} (hb : b ∈ (worldAt (stateBefore c p a nr s rho j2) w).st.core.tree.elems) :
    b ∈ (worldAt (stateBefore c p a nr s rho j1) w).st.core.tree.elems := by
  have hlt : j2 < j1 :=
    Proofs.Consensus.Window.lt_of_time_lt (Proofs.Consensus.Available.sorted_nodup_of_sleepy c p a nr s rho hsleep).1 hj2 hj1
      (domainTime_G2_lt_G1 s.e s.hc (Proofs.Consensus.Liveness.wf_facts hwf).1 k)
  exact (Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho hlt.le w b hb).1

/-- run の添字 `j` の event の前の、ノード `w` の store の grade view。 -/
def tickGradeView (j : Nat) (w : ValidatorId) : Model.Consensus.Protocol.Grades.GradeView :=
  Model.Consensus.Protocol.Grades.gradeView
    (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core)

/-- run の添字 `j` の event の前の、ノード `w` の store の finalized。 -/
def tickF (j : Nat) (w : ValidatorId) : Block :=
  (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core).f

/-- round `k` の G2 の late 時刻は G2 の domain 時刻(どちらも opening の `Δ` 前)。手書き `q10_late_g2_eq_domain_g2`。 -/
theorem lateTime_G2_eq_domainTime (e : Model.Consensus.Objects.Parameters.ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (k : Nat) :
    Model.Consensus.Protocol.Grades.lateTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G2 =
      Model.Consensus.Protocol.Grades.domainTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G2 := by
  unfold Model.Consensus.Protocol.Grades.lateTime Model.Consensus.Protocol.Grades.domainTime
  rfl

/-- `0 ≤ Δ` なら round `k` の G1 の early / late 時刻は G2 の domain 時刻以下で、G2 の early 時刻は G1 の early 時刻以下。
手書き `q10_early_g1_le_domain_g2` / `q10_late_g1_le_domain_g2` / `q10_early_g2_le_early_g1`。 -/
theorem g1Times_le_domainTime_G2 (e : Model.Consensus.Objects.Parameters.ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (hδ : 0 ≤ e.delta) (k : Nat) :
    Model.Consensus.Protocol.Grades.earlyTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G1 ≤
        Model.Consensus.Protocol.Grades.domainTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G2 ∧
      Model.Consensus.Protocol.Grades.lateTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G1 ≤
        Model.Consensus.Protocol.Grades.domainTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G2 ∧
      Model.Consensus.Protocol.Grades.earlyTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G2 ≤
        Model.Consensus.Protocol.Grades.earlyTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G1 := by
  unfold Model.Consensus.Protocol.Grades.earlyTime Model.Consensus.Protocol.Grades.lateTime
    Model.Consensus.Protocol.Grades.domainTime
  simp only [Model.Consensus.Protocol.Grades.earlyOffset, Model.Consensus.Protocol.Grades.lateOffset,
    Model.Consensus.Protocol.Grades.domainOffset]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- `SleepyRegime` の下で run の event は時刻の順で、時刻は非負(`ScheduleWellFormed` から)。 -/
theorem sorted_nonneg_of_sleepy (hsleep : SleepyRegime c p a nr s rho 0) :
    EventsSorted rho ∧ ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, -⟩, -⟩ := hexec
  exact ⟨Proofs.Consensus.Window.eventsSorted_of_schedule hsch, fun ev hev =>
    (Proofs.Consensus.Window.eventTime_bounds hsch hev).1⟩

/-- G1 の early か late の時刻 `cut` は G2 の domain 時刻以下(`0 ≤ Δ`)。 -/
theorem g1Cut_le_domainTime_G2 (hwf : SetupWellFormed c p s) {k : Nat} {cut : Int}
    (hcut : cut = Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1 ∨
      cut = Model.Consensus.Protocol.Grades.lateTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1) :
    cut ≤ Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2 := by
  obtain ⟨hel, hll, -⟩ := g1Times_le_domainTime_G2 s.e s.hc (Proofs.Consensus.Liveness.wf_facts hwf).1.le k
  rcases hcut with rfl | rfl
  · exact hel
  · exact hll

/-- 印 `At τ` が `γ` より前なら `τ < γ`。 -/
theorem lt_of_occurrenceBefore_at {τ γ : Int}
    (h : Model.Consensus.Objects.Time.occurrenceBefore (some (Model.Consensus.Objects.Time.Stamp.At τ)) γ = true) :
    τ < γ := by
  unfold Model.Consensus.Objects.Time.occurrenceBefore at h
  rcases (Proofs.Consensus.Majority.stampBefore_iff _ _).mp h with h | ⟨τ', h, hτ'⟩
  · cases h
  · cases h
    exact hτ'

/-- honest なノード `w` の添字 `j` の前の store の tree では root が要素を決める: 2 つの要素の root が等しければ同じブロック。
tree の要素は bodies の名前付きブロックの消去(`Carrier.StoreInv.named`)で、bodies のブロックは run の中のブロック(`BlockInRun`)なので、
`SleepyRegime` の `Idealization`(= `NamedRootCollisionFree`)から `FinalizedAccountable.rootInjective_of_collisionFree` で取る。
手書き `held_find_at_strict` の root の衝突なしの半分(周回 240)。 -/
theorem tickTree_root_inj (hsleep : SleepyRegime c p a nr s rho 0) {w : ValidatorId} (hw : rho.honest.contains w = true) (j : Nat)
    {x y : Block} (hx : x ∈ (worldAt (stateBefore c p a nr s rho j) w).st.core.tree.elems)
    (hy : y ∈ (worldAt (stateBefore c p a nr s rho j) w).st.core.tree.elems)
    (hr : root x = root y) : x = y := by
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho (Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep)).2
  have hinv := Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho j w
  have hin : ∀ D, D ∈ (worldAt (stateBefore c p a nr s rho j) w).st.bodies.elems →
      Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho D := fun D hD =>
    ⟨D, Or.inr ⟨w, hw, j, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hD⟩,
      Proofs.Consensus.NamedBlocks.namedPreceq_self D⟩
  obtain ⟨X, hX, rfl⟩ := hinv.named x hx
  obtain ⟨Y, hY, rfl⟩ := hinv.named y hy
  exact Proofs.Consensus.FinalizedAccountable.rootInjective_of_collisionFree c p a nr s rho hcf (hin X hX) (hin Y hY)
    _ _ ⟨⟨Or.inl (Proofs.Consensus.Blocks.preceq_self _), Or.inr (Proofs.Consensus.Blocks.preceq_self _)⟩, hr⟩

/-- 重複が無く root が要素を決める tree では、要素 `hd` の root `r` は `hd` に解決する。 -/
theorem findRoot?_of_mem {t : NaruStd.Set Block} (hnd : t.elems.Nodup)
    (hinj : ∀ x ∈ t.elems, ∀ y ∈ t.elems, root x = root y → x = y) {r : BlockId} {hd : Block} (hm : hd ∈ t.elems)
    (hroot : root hd = r) : findRoot? t r = some hd := by
  unfold findRoot? NaruStd.Set.findUnique?
  have hl : t.elems.filter (fun b => root b == r) = [hd] :=
    list_eq_singleton_of_nodup (hnd.filter _) (fun x hx => by
      obtain ⟨hx1, hxr⟩ := List.mem_filter.mp hx
      exact hinj x hx1 hd hm ((beq_iff_eq.mp hxr).trans hroot.symm))
      (List.mem_filter.mpr ⟨hm, beq_iff_eq.mpr hroot⟩)
  rw [hl]

/-- root の解決は tree が育っても変わらない: `t2` の要素が `t1` にもあり、`t1` に重複が無く root が要素を決めるなら、`t2` で root `r` が
`hd` に解決すれば `t1` でも `hd` に解決する。手書き `q10_find_fwd` の抽象的な半分(周回 240)。 -/
theorem findRoot?_of_subset {t1 t2 : NaruStd.Set Block} (hnd : t1.elems.Nodup)
    (hinj : ∀ x ∈ t1.elems, ∀ y ∈ t1.elems, root x = root y → x = y) (hsub : ∀ x ∈ t2.elems, x ∈ t1.elems)
    {r : BlockId} {hd : Block} (h : findRoot? t2 r = some hd) : findRoot? t1 r = some hd := by
  obtain ⟨hm, hroot⟩ := Proofs.Consensus.BlockStamps.findRoot?_mem h
  exact findRoot?_of_mem hnd hinj (hsub hd hm) hroot

/-- GST-zero の枝で、honest なノード `w` の正の round `k` の G2 / G1 の domain 時刻の tick(添字 `j2` / `j1`)について、
G1 の early か late の時刻 `cut` で、G1 の tick の前の store の生の入力は G2 の tick の前の store の生の入力でもある
(`cut` は G2 の domain 時刻以下)。手書き `NamedOutageClosure.q10_rawInputs_back`(`Protocol/Grades/Q10Frame.lean`)に当たる(周回 238 に
穴として置き、周回 242 に証明した)。G1 の tick の行の票は、G2 の tick の前の行にもあったか、受信の印が G2 の tick の時刻以上
(`SgStamps.stateBefore_sgFresh`。新しい票の印はその時点の時計で、時計は G2 の tick でその時刻になり戻らない)。後者は印が
`cut` より前であることと両立しないので前者で、印は変わらない(`SgStamps.stateBefore_sgKeep`)。手書きは公の時刻 `cut` の strict read を
経由する(`q10_row_at_public_cut`)が、ここでは G2 の tick を直接の境にするので `0 < k` は使わない。 -/
theorem g1RawInputs_back (hwf : SetupWellFormed c p s) (_hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (_hw : rho.honest.contains w = true) {k j2 j1 : Nat} (_hk : 0 < k)
    (hj2 : rho.events[j2]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)))
    (hj1 : rho.events[j1]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)))
    {cut : Int}
    (hcut : cut = Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1 ∨
      cut = Model.Consensus.Protocol.Grades.lateTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)
    (v : ValidatorId) {y : Model.Consensus.Protocol.ForkChoice.Goldfish.SGVote}
    (hy : y ∈ (Model.Consensus.Protocol.Grades.rawInputs (tickGradeView c p a nr s rho j1 w) s.hc.etaSG k cut v).elems) :
    y ∈ (Model.Consensus.Protocol.Grades.rawInputs (tickGradeView c p a nr s rho j2 w) s.hc.etaSG k cut v).elems := by
  obtain ⟨hs, hnn⟩ := sorted_nonneg_of_sleepy c p a nr s rho hsleep
  have hlt : j2 < j1 :=
    Proofs.Consensus.Window.lt_of_time_lt hs hj2 hj1 (domainTime_G2_lt_G1 s.e s.hc (Proofs.Consensus.Liveness.wf_facts hwf).1 k)
  have hcutle := g1Cut_le_domainTime_G2 c p s hwf hcut
  rw [Proofs.Consensus.GradeSupporter.mem_rawInputs_iff] at hy ⊢
  obtain ⟨hwin, hv, hst⟩ := hy
  obtain ⟨r, hrw, hyr⟩ := (Proofs.Consensus.Sets.mem_flatMap_iff Proofs.Consensus.SgStamps.sgv_compare_eq_iff _ _ _).mp hwin
  obtain ⟨x, hx, rfl⟩ := (Proofs.Consensus.SgStamps.mem_viewRow_iff _ r _).mp hyr
  change Model.Consensus.Objects.Time.occurrenceBefore ((worldAt (stateBefore c p a nr s rho j1) w).st.core.timestampSgVote.get?
    (Model.Consensus.Protocol.Store.sgVote x)) cut = true at hst
  rcases Proofs.Consensus.SgStamps.stateBefore_sgFresh c p a nr s rho hs hnn hj2 hlt.le r x hx with hx2 | ⟨τ, hτ, hle⟩
  · obtain ⟨-, heq⟩ := Proofs.Consensus.SgStamps.stateBefore_sgKeep c p a nr s rho hlt.le w r x hx2
    refine ⟨(Proofs.Consensus.Sets.mem_flatMap_iff Proofs.Consensus.SgStamps.sgv_compare_eq_iff _ _ _).mpr
      ⟨r, hrw, (Proofs.Consensus.SgStamps.mem_viewRow_iff _ r _).mpr ⟨x, hx2, rfl⟩⟩, hv, ?_⟩
    change Model.Consensus.Objects.Time.occurrenceBefore ((worldAt (stateBefore c p a nr s rho j2) w).st.core.timestampSgVote.get?
      (Model.Consensus.Protocol.Store.sgVote x)) cut = true
    rw [← heq]
    exact hst
  · rw [hτ] at hst
    exact absurd (lt_of_lt_of_le (lt_of_occurrenceBefore_at hst) hcutle) (not_lt.mpr hle)

/-- `g1RawInputs_back` と同じ 2 つの tick と時刻 `cut` で、G1 の tick の前の store の解釈済みの入力(その store の finalized に
対する)は、G2 の tick の前の store の解釈済みの入力(その store の finalized に対する)でもある。手書き
`NamedOutageClosure.q10_interpreted_back`(`Protocol/Grades/Q10Frame.lean`)に当たる(周回 238 に穴として置き、周回 242 に証明した)。
生の入力は `g1RawInputs_back`。本体の head は、G2 の tick より後に tree に入ったなら受信の印が G2 の tick の時刻以上
(`BlockStamps.stateBefore_fresh`)で `cut` より前の印と両立しないので G2 の tick の tree に既にあり、印は変わらず
(`BlockStamps.stateBefore_keep`。手書き `q10_strict_body_carry`)、root の解決も同じ(`findRoot?_of_mem`。手書き `held_find_at_strict`)。
G2 の tick の finalized は G1 の tick の finalized の祖先(`ReceiverFinality.stateBefore_f_mono`)なので互換が戻る
(手書き `q10_compatible_back`)。 -/
theorem g1Interpreted_back (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {k j2 j1 : Nat} (hk : 0 < k)
    (hj2 : rho.events[j2]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)))
    (hj1 : rho.events[j1]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)))
    {cut : Int}
    (hcut : cut = Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1 ∨
      cut = Model.Consensus.Protocol.Grades.lateTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)
    (v : ValidatorId) {y : Model.Consensus.Protocol.ForkChoice.Goldfish.SGVote}
    (hy : y ∈ (Model.Consensus.Protocol.Grades.interpretedInputs (tickGradeView c p a nr s rho j1 w)
      (tickF c p a nr s rho j1 w) s.hc.etaSG k cut v).elems) :
    y ∈ (Model.Consensus.Protocol.Grades.interpretedInputs (tickGradeView c p a nr s rho j2 w)
      (tickF c p a nr s rho j2 w) s.hc.etaSG k cut v).elems := by
  obtain ⟨hs, hnn⟩ := sorted_nonneg_of_sleepy c p a nr s rho hsleep
  have hlt : j2 < j1 :=
    Proofs.Consensus.Window.lt_of_time_lt hs hj2 hj1 (domainTime_G2_lt_G1 s.e s.hc (Proofs.Consensus.Liveness.wf_facts hwf).1 k)
  have hcutle := g1Cut_le_domainTime_G2 c p s hwf hcut
  obtain ⟨hraw, hready⟩ := (Proofs.Consensus.GradeSupporter.mem_interpretedInputs_iff _ _ _ _ _ _ _).mp hy
  refine (Proofs.Consensus.GradeSupporter.mem_interpretedInputs_iff _ _ _ _ _ _ _).mpr
    ⟨g1RawInputs_back c p a nr s rho hwf hdom hsleep hw hk hj2 hj1 hcut v hraw, ?_⟩
  have hF : preceq (tickF c p a nr s rho j2 w) (tickF c p a nr s rho j1 w) = true :=
    Proofs.Consensus.ReceiverFinality.stateBefore_f_mono c p a nr s rho hlt.le w
  unfold Model.Consensus.Protocol.Grades.bodyReady at hready ⊢
  simp only [tickGradeView, tickF, Model.Consensus.Protocol.Grades.gradeView, Model.Consensus.Protocol.Store.storeToHealing]
    at hready hF ⊢
  cases hconf : y.confirmed with
  | none => rfl
  | some r =>
    rw [hconf] at hready
    dsimp only at hready ⊢
    cases hf : findRoot? (worldAt (stateBefore c p a nr s rho j1) w).st.core.tree r with
    | none => rw [hf] at hready; simp at hready
    | some hd =>
      rw [hf] at hready
      simp only [Bool.and_eq_true] at hready
      obtain ⟨hst, hcomp⟩ := hready
      obtain ⟨hm1, hroot⟩ := Proofs.Consensus.BlockStamps.findRoot?_mem hf
      rcases Proofs.Consensus.BlockStamps.stateBefore_fresh c p a nr s rho hs hnn hj2 hlt.le hd hm1 with hm2 | ⟨τ, hτ, hle⟩
      · rw [findRoot?_of_mem (Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho j2 w).nodup
          (fun x hx y hy hr => tickTree_root_inj c p a nr s rho hsleep hw j2 hx hy hr) hm2 hroot]
        simp only [Bool.and_eq_true]
        obtain ⟨-, heq⟩ := Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho hlt.le w hd hm2
        refine ⟨?_, ?_⟩
        · rw [← heq]
          exact hst
        · rw [Proofs.Consensus.Blocks.compatible_comm] at hcomp ⊢
          exact Proofs.Consensus.Available.compatible_of_preceq_of_compatible hF hcomp
      · rw [hτ] at hst
        exact absurd (lt_of_lt_of_le (lt_of_occurrenceBefore_at hst) hcutle) (not_lt.mpr hle)

/-- `g1RawInputs_back` と同じ 2 つの tick で、G2 の tick の前の store の tree で鍵 `key` の head が `b` を覆えば、G1 の tick の
前の store の tree でも覆う。手書き `NamedOutageClosure.q10_localCovers_fwd`(`Protocol/Grades/Q10Frame.lean`)に当たる(周回 238 に穴として
置き、周回 240 に証明した)。tree のブロックは残り(`g1Tree_of_g2Tree`)、G1 の tick の tree は重複が無く(`TreeInv`)root が要素を決める
(`tickTree_root_inj`)ので、root の解決 `findRoot?` は変わらない(`findRoot?_of_subset`。手書き `q10_find_fwd`)。 -/
theorem g1LocalCovers_fwd (hwf : SetupWellFormed c p s) (_hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {k j2 j1 : Nat}
    (hj2 : rho.events[j2]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)))
    (hj1 : rho.events[j1]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)))
    (key : Option BlockId) {b : Block}
    (h : Model.Consensus.Protocol.Grades.localCovers (tickGradeView c p a nr s rho j2 w) key b = true) :
    Model.Consensus.Protocol.Grades.localCovers (tickGradeView c p a nr s rho j1 w) key b = true := by
  unfold Model.Consensus.Protocol.Grades.localCovers Model.Consensus.Protocol.Grades.headCovers at h ⊢
  simp only [tickGradeView, Model.Consensus.Protocol.Grades.gradeView, Model.Consensus.Protocol.Store.storeToHealing] at h ⊢
  cases key with
  | none => exact h
  | some r =>
    dsimp only at h ⊢
    cases hf : findRoot? (worldAt (stateBefore c p a nr s rho j2) w).st.core.tree r with
    | none => rw [hf] at h; simp at h
    | some hd =>
      rw [hf] at h
      rw [findRoot?_of_subset (Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho j1 w).nodup
        (fun x hx y hy hr => tickTree_root_inj c p a nr s rho hsleep hw j1 hx hy hr)
        (fun x hx => g1Tree_of_g2Tree c p a nr s rho hwf hsleep hj2 hj1 hx) hf]
      exact h

/-- `g1RawInputs_back` と同じ 2 つの tick で、G2 の tick の前の store の G2 の early 時刻の解釈済みの入力 `y` の鍵が、その store の
tree で `b` を覆い、G1 の tick の前の store の finalized が `b` の祖先なら、`y` は G1 の tick の前の store の G1 の early 時刻の
解釈済みの入力でもある。手書き `NamedOutageClosure.q10_interpreted_fwd_cover`(`Protocol/Grades/Q10Frame.lean`)に当たる(周回 238 に穴として
置き、周回 241 に証明した)。生の入力は SG 票の行と受信の印が残る(`SgStamps.stateBefore_sgKeep`。手書き `strict_sg_row_carry`)ので
前へ運べ(`SgStamps.rawInputs_of_keep`。手書き `q10_rawInputs_fwd`)、本体の head は tree に残り印も変わらず(`BlockStamps.stateBefore_keep`。
手書き `q10_strict_body_carry`)root の解決も変わらない(`findRoot?_of_subset`。手書き `q10_find_fwd`)、head は `b` の子孫なので
G1 の tick の finalized ⪯ `b` ⪯ head で互換。G2 の early 時刻は G1 の early 時刻以下(`g1Times_le_domainTime_G2`)。 -/
theorem g1InterpretedCover_fwd (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {k j2 j1 : Nat}
    (hj2 : rho.events[j2]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)))
    (hj1 : rho.events[j1]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)))
    {b : Block} (hFB : preceq (tickF c p a nr s rho j1 w) b = true)
    (v : ValidatorId) {y : Model.Consensus.Protocol.ForkChoice.Goldfish.SGVote}
    (hy : y ∈ (Model.Consensus.Protocol.Grades.interpretedInputs (tickGradeView c p a nr s rho j2 w)
      (tickF c p a nr s rho j2 w) s.hc.etaSG k
      (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2) v).elems)
    (hcov : Model.Consensus.Protocol.Grades.localCovers (tickGradeView c p a nr s rho j2 w) y.confirmed b = true) :
    y ∈ (Model.Consensus.Protocol.Grades.interpretedInputs (tickGradeView c p a nr s rho j1 w)
      (tickF c p a nr s rho j1 w) s.hc.etaSG k
      (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1) v).elems := by
  have hlt : j2 < j1 :=
    Proofs.Consensus.Window.lt_of_time_lt (Proofs.Consensus.Available.sorted_nodup_of_sleepy c p a nr s rho hsleep).1 hj2 hj1
      (domainTime_G2_lt_G1 s.e s.hc (Proofs.Consensus.Liveness.wf_facts hwf).1 k)
  have hee := (g1Times_le_domainTime_G2 s.e s.hc (Proofs.Consensus.Liveness.wf_facts hwf).1.le k).2.2
  obtain ⟨hraw, hready⟩ := (Proofs.Consensus.GradeSupporter.mem_interpretedInputs_iff _ _ _ _ _ _ _).mp hy
  refine (Proofs.Consensus.GradeSupporter.mem_interpretedInputs_iff _ _ _ _ _ _ _).mpr
    ⟨Proofs.Consensus.SgStamps.rawInputs_of_keep (Proofs.Consensus.SgStamps.stateBefore_sgKeep c p a nr s rho hlt.le w)
      hee hraw, ?_⟩
  unfold Model.Consensus.Protocol.Grades.bodyReady at hready ⊢
  unfold Model.Consensus.Protocol.Grades.localCovers Model.Consensus.Protocol.Grades.headCovers at hcov
  simp only [tickGradeView, tickF, Model.Consensus.Protocol.Grades.gradeView, Model.Consensus.Protocol.Store.storeToHealing]
    at hready hcov hFB ⊢
  cases hconf : y.confirmed with
  | none => rfl
  | some r =>
    rw [hconf] at hready hcov
    dsimp only at hready hcov ⊢
    cases hf : findRoot? (worldAt (stateBefore c p a nr s rho j2) w).st.core.tree r with
    | none => rw [hf] at hcov; simp at hcov
    | some hd =>
      rw [hf] at hready hcov
      simp only [Bool.and_eq_true] at hready
      rw [findRoot?_of_subset (Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho j1 w).nodup
        (fun x hx y hy hr => tickTree_root_inj c p a nr s rho hsleep hw j1 hx hy hr)
        (fun x hx => g1Tree_of_g2Tree c p a nr s rho hwf hsleep hj2 hj1 hx) hf]
      simp only [Bool.and_eq_true]
      obtain ⟨-, hstamp⟩ := Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho hlt.le w hd
        (Proofs.Consensus.BlockStamps.findRoot?_mem hf).1
      refine ⟨?_, ?_⟩
      · rw [hstamp]
        exact Proofs.Consensus.GradeSupporter.occurrenceBefore_mono hready.1 hee
      · rw [Proofs.Consensus.Blocks.compatible_comm]
        exact Proofs.Consensus.Blocks.compatible_of_preceq_common (Proofs.Consensus.Blocks.preceq_trans hFB hcov)
          (Proofs.Consensus.Blocks.preceq_self hd)

/-- GST-zero の枝で、honest なノード `w` の正の round `k` の G2 の domain 時刻の tick(添字 `j2`)の前の store で G2 の
`gradeBool` を満たすブロック `b` を、同じ round の G1 の domain 時刻の tick(添字 `j1`)の前の store の finalized が延ばすなら、`b` は
その store でも G1 の `gradeBool` を満たす。手書き `NamedOutageClosure.q10_grade_cross`(`Protocol/Grades/Q10Frame.lean`)に当たる
(周回 235 に穴として置き、周回 238 に手書きと同じ運びで証明した)。抽象的な持ち越し `GradeTransport.gradeBool_transport`
(手書き `q10_gradeBool_transport`)に、G1 の early / late 時刻は G2 の domain 時刻(= G2 の late 時刻)以下であること
(`g1Times_le_domainTime_G2`)と、2 つの tick の間の包含(周回 242 に閉じた `g1Interpreted_back` / `g1RawInputs_back` と
周回 240 / 241 に閉じた `g1LocalCovers_fwd` / `g1InterpretedCover_fwd`)を渡す。 -/
theorem g1Grade_of_g2Grade_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {k j2 j1 : Nat} (hk : 0 < k)
    (hj2 : rho.events[j2]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)))
    (hj1 : rho.events[j1]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)))
    {b : Block}
    (hFB : preceq (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j1) w).st.core).f b = true)
    (hgrade : Model.Consensus.Protocol.Grades.gradeBool s.e
      (Model.Consensus.Protocol.Grades.gradeView
        (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j2) w).st.core))
      (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j2) w).st.core).f s.hc.etaSG k
      (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)
      (Model.Consensus.Protocol.Grades.lateTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2) b = true) :
    Model.Consensus.Protocol.Grades.gradeBool s.e
      (Model.Consensus.Protocol.Grades.gradeView
        (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j1) w).st.core))
      (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j1) w).st.core).f s.hc.etaSG k
      (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)
      (Model.Consensus.Protocol.Grades.lateTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1) b = true := by
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1.le
  obtain ⟨hearly, hlate, hee⟩ := g1Times_le_domainTime_G2 s.e s.hc hδ k
  rw [← lateTime_G2_eq_domainTime] at hearly hlate
  refine Proofs.Consensus.GradeTransport.gradeBool_transport s.e
    (Proofs.Consensus.JustificationCertificate.sorted_validators hwf)
    (tickGradeView c p a nr s rho j2 w) (tickGradeView c p a nr s rho j1 w)
    (tickF c p a nr s rho j2 w) (tickF c p a nr s rho j1 w) s.hc.etaSG k
    (Proofs.Consensus.GradeSupporter.earlyTime_le_lateTime s.e s.hc k _ hδ)
    (Proofs.Consensus.GradeSupporter.earlyTime_le_lateTime s.e s.hc k _ hδ) b
    (fun v x hx => ?_) (fun v x hx => ?_) (fun v x hx => ?_) (fun v u hu hcov => ?_)
    (fun key h => g1LocalCovers_fwd c p a nr s rho hwf hdom hsleep hw hj2 hj1 key h) hgrade
  · obtain ⟨y, hy, rfl⟩ := (Proofs.Consensus.GradeSupporter.mem_readyView_iff _ _ _ _ _ _ _).mp hx
    exact (Proofs.Consensus.GradeSupporter.mem_readyView_iff _ _ _ _ _ _ _).mpr
      ⟨y, Proofs.Consensus.GradeSupporter.interpretedInputs_mono hearly
        (g1Interpreted_back c p a nr s rho hwf hdom hsleep hw hk hj2 hj1 (Or.inl rfl) v hy), rfl⟩
  · obtain ⟨y, hy, rfl⟩ := (Proofs.Consensus.GradeSupporter.mem_readyView_iff _ _ _ _ _ _ _).mp hx
    exact (Proofs.Consensus.GradeSupporter.mem_readyView_iff _ _ _ _ _ _ _).mpr
      ⟨y, Proofs.Consensus.GradeSupporter.interpretedInputs_mono hlate
        (g1Interpreted_back c p a nr s rho hwf hdom hsleep hw hk hj2 hj1 (Or.inr rfl) v hy), rfl⟩
  · obtain ⟨y, hy, rfl⟩ := (Proofs.Consensus.GradeTransport.mem_rawView_iff _ _ _ _ _ _).mp hx
    exact (Proofs.Consensus.GradeTransport.mem_rawView_iff _ _ _ _ _ _).mpr
      ⟨y, Proofs.Consensus.GradeTransport.rawInputs_mono hlate
        (g1RawInputs_back c p a nr s rho hwf hdom hsleep hw hk hj2 hj1 (Or.inr rfl) v hy), rfl⟩
  · obtain ⟨y, hy, rfl⟩ := (Proofs.Consensus.GradeSupporter.mem_readyView_iff _ _ _ _ _ _ _).mp hu
    exact (Proofs.Consensus.GradeSupporter.mem_readyView_iff _ _ _ _ _ _ _).mpr
      ⟨y, g1InterpretedCover_fwd c p a nr s rho hwf hdom hsleep hw hj2 hj1 hFB v hy hcov, rfl⟩

/-- GST-zero の枝で、honest なノード `w` の正の round `k` の G2 の domain 時刻の tick(添字 `j2`)の前の store で凍結した
G2 の root `g2v` を、同じ round の G1 の domain 時刻の tick(添字 `j1`)の前の store の finalized が延ばすなら、その store でも G1 の
`freezeRoot` が `g2v` 以上の root `g1v` を凍結する。手書き `NamedOutageClosure.q10_g1_of_g2_freeze`(`Protocol/Grades/Q10Frame.lean`)に
当たる(周回 234 に穴として置き、周回 235 に手書きと同じ運びで証明した)。`g2v` は tree にあり G2 の `gradeBool` を満たし
(`Grade2Capture.freezeRoot_mem`)、`g1Grade_of_g2Grade_positive` で G1 の grade に、`g1Tree_of_g2Tree` で G1 の tick の tree に
持ち越し、`freezeRoot_of_graded`(tree の重複なしは `TreeInv`、`early ≤ late` は `0 < Δ`)で G1 の凍結に移す。 -/
theorem g1Freeze_of_g2Freeze_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {k j2 j1 : Nat} (hk : 0 < k)
    (hj2 : rho.events[j2]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)))
    (hj1 : rho.events[j1]? = some (NamedEvent.Tick w
      (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)))
    {g2v : Block}
    (hfz2 : Model.Consensus.Protocol.Grades.freezeRoot s.e
      (Model.Consensus.Protocol.Grades.gradeView
        (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j2) w).st.core))
      (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j2) w).st.core).f s.hc.etaSG k
      (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2)
      (Model.Consensus.Protocol.Grades.lateTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G2) = some g2v)
    (hFB : preceq (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j1) w).st.core).f g2v = true) :
    ∃ g1v : Block, Model.Consensus.Protocol.Grades.freezeRoot s.e
        (Model.Consensus.Protocol.Grades.gradeView
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j1) w).st.core))
        (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j1) w).st.core).f s.hc.etaSG k
        (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1)
        (Model.Consensus.Protocol.Grades.lateTime s.e s.hc k Model.Consensus.Protocol.Grades.GradePhase.G1) = some g1v ∧
      preceq g2v g1v = true := by
  obtain ⟨hmem2, hgrade2⟩ := Proofs.Consensus.Grade2Capture.freezeRoot_mem hfz2
  have hgrade1 := g1Grade_of_g2Grade_positive c p a nr s rho hwf hdom hsleep hw hk hj2 hj1 hFB hgrade2
  have hmem1 := g1Tree_of_g2Tree c p a nr s rho hwf hsleep hj2 hj1 hmem2
  exact freezeRoot_of_graded (Proofs.Consensus.JustificationCertificate.sorted_validators hwf)
    (Proofs.Consensus.GradeSupporter.earlyTime_le_lateTime s.e s.hc k _ (Proofs.Consensus.Liveness.wf_facts hwf).1.le)
    (Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho j1 w).nodup hmem1 hgrade1

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick の、確認の更新の前の段の store の round が正なら、その round の
frame の g2 の root `raw` の祖先 `P` で filtered tree にあるものは、同じ frame の g1 の root `root1` の祖先でもある。
手書き `NamedOutageClosure.q10_g1_slot_of_g2_slot`(`Protocol/Grades/Q10Frame.lean`)に当たる(周回 232 に穴として置き、周回 234 に
手書きと同じ運びで証明した)。g2 の root の出どころ(`confCache_g2_origin`: G2 の domain 時刻の tick で凍結した `g2v`、`P ⪯ g2v`)と、
読みの G1 の欄(`confFrameG1_slot_positive`: G1 の domain 時刻の tick の凍結の切り詰め)を取り、`P` は filtered tree にあるので
読みの finalized `F` を延ばす(`ProposerFinality.filtered_extends`)。G1 の tick の finalized は `F` の祖先なので `g2v` の祖先で、
`g1Freeze_of_g2Freeze_positive` が G1 の凍結 `g1v`(`g2v ⪯ g1v`)を返す。`P` は `F` と互換なので切り詰めの後も `g1v` の切り詰めの祖先
(`preceq_clipGrade_of_compatible`)。 -/
theorem confFrameG2_g1Root_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hpos : 0 < Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) {P raw : Block}
    (hg2 : (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g2 = some (some raw))
    (hPraw : preceq P raw = true)
    (hPtree : P ∈ (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)).elems) :
    ∃ root1 : Block, (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g1 = some (some root1) ∧
      preceq P root1 = true := by
  obtain ⟨j2, g2v, -, hj2, hfz2, hPg2v⟩ := confCache_g2_origin c p a nr s rho ht.1 _ hg2 hPraw
  obtain ⟨j1, -, hj1, hFmono, hg1⟩ := confFrameG1_slot_positive c p a nr s rho hwf hdom hsleep hw ht hpos
  have hFP := Proofs.Consensus.ProposerFinality.filtered_extends hPtree
  obtain ⟨g1v, hfz1, hg21⟩ := g1Freeze_of_g2Freeze_positive c p a nr s rho hwf hdom hsleep hw hpos hj2 hj1 hfz2
    (Proofs.Consensus.Blocks.preceq_trans hFmono (Proofs.Consensus.Blocks.preceq_trans hFP hPg2v))
  rw [hfz1] at hg1
  refine ⟨_, hg1, preceq_clipGrade_of_compatible (Proofs.Consensus.Blocks.preceq_trans hPg2v hg21) ?_⟩
  unfold compatible
  rw [Bool.or_eq_true]
  exact Or.inr hFP

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick の grade の g2 の frame の root の active prefix(`frameStableRoot` が
FG root に戻らない枝の値)は、確認の更新の前の段の store の round が正なら、同じ frame の g1 の anchor(`Grades.anchor`。
fork choice の SG root `getSgRootWith` の値)の祖先。手書き `preparedStableRoot_preceq_confWalk_positive`
(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)の `hfinish` に渡す前の半分に当たる。
手書きと同じく、g2 の root `raw` の active prefix `g` は filtered tree にあり `g ⪯ raw` なので、穴 `confFrameG2_g1Root_positive` で
g1 の root `root1` を取り(`g ⪯ root1`)、filtered tree の重複なし(穴 `preUpdateTree_nodup`)から `activePrefix_exists` で
anchor が FG root に戻らないことを、`activePrefix_dominates` で `g` が anchor の祖先であることを示す(周回 232)。 -/
theorem confFrameRoot_preceq_anchor_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hpos : 0 < Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) {g : Block}
    (hg : Option.bind (Option.bind (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g2 (fun x => x))
        (fun r => Model.Consensus.Protocol.Grades.activePrefix
          (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree
            (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core))
          r) = some g) :
    preceq g (Model.Consensus.Protocol.Grades.anchor s.e s.hc
      (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
      (Model.Consensus.Protocol.Grades.roundOf s.hc
        (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)
      (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g1) = true := by
  obtain ⟨raw', hraw', hgraw⟩ := Option.bind_eq_some_iff.mp hg
  obtain ⟨raw, hraw, hrr⟩ := Option.bind_eq_some_iff.mp hraw'
  subst hrr
  have hgT := Proofs.Consensus.Trees.activePrefix_mem hgraw
  obtain ⟨root1, hg1, hgr1⟩ := confFrameG2_g1Root_positive c p a nr s rho hwf hdom hsleep hw ht hpos hraw
    (Proofs.Consensus.Grade2Capture.activePrefix_preceq hgraw) hgT
  have hnd := getFilteredBlockTree_nodup (hs := Model.Consensus.Protocol.Store.storeToHealing
    (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core) (preUpdateTree_nodup c p a nr s rho w i t)
  obtain ⟨d, hd⟩ := activePrefix_exists hnd hgT hgr1
  rw [hg1]
  simp only [Model.Consensus.Protocol.Grades.anchor, hd, Option.getD_some]
  exact activePrefix_dominates hgT hgr1 hd

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick の grade の g2 の frame の root の active prefix(`frameStableRoot` が
FG root に戻らない枝の値)は、確認の更新の前の段の store の round が正なら、同じ tick の確認の walk の祖先。手書き
`preparedStableRoot_preceq_confWalk_positive`(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。
手書きの `hfinish` と同じく、g1 の anchor は fork choice の SG root(`getSgRootWith` は `frameGradeRead` の `anchor`)で、
walk はそこから歩く(`Goldfish.sgRoot_preceq_head`)ので、`confFrameRoot_preceq_anchor_positive` から(周回 230)。 -/
theorem confFrameRoot_preceq_confWalk_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hpos : 0 < Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) {g : Block}
    (hg : Option.bind (Option.bind (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g2 (fun x => x))
        (fun r => Model.Consensus.Protocol.Grades.activePrefix
          (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree
            (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core))
          r) = some g) :
    preceq g (Proofs.Consensus.ConfirmedOrigin.confWalkAt c p a nr s rho w i t) = true :=
  Proofs.Consensus.Blocks.preceq_trans
    (confFrameRoot_preceq_anchor_positive c p a nr s rho hwf hdom hsleep hw ht hpos hg)
    (Proofs.Consensus.Goldfish.sgRoot_preceq_head _ _ _ _ _)

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick の grade の g2 の frame の root の active prefix(`frameStableRoot` が
FG root に戻らない枝の値)は、同じ tick の確認の walk の祖先。手書き `preparedStableRoot_preceq_confWalk_of_gstZero_clean`
(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)の g2 の root がある枝に当たる。手書きと同じく
確認の更新の前の段の store の round で分け、round 0 は g2 の frame に root が無いので矛盾(`confCache_g2_round_zero`)、
正の round は穴 `confFrameRoot_preceq_confWalk_positive` から(周回 228)。 -/
theorem confFrameRoot_preceq_confWalk (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t) {g : Block}
    (hg : Option.bind (Option.bind (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)).g2 (fun x => x))
        (fun r => Model.Consensus.Protocol.Grades.activePrefix
          (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree
            (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core))
          r) = some g) :
    preceq g (Proofs.Consensus.ConfirmedOrigin.confWalkAt c p a nr s rho w i t) = true := by
  rcases Nat.eq_zero_or_pos (Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) with h0 | hpos
  · exfalso
    have hsch : ScheduleWellFormed s rho := by
      have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
      unfold ExecutionValid at hexec
      exact hexec.1.1.1
    obtain ⟨r, hr, -⟩ := Option.bind_eq_some_iff.mp hg
    obtain ⟨x, hx, hxr⟩ := Option.bind_eq_some_iff.mp hr
    subst hxr
    rw [h0] at hx
    exact confCache_g2_round_zero c p a nr s rho hsch (Proofs.Consensus.Liveness.wf_facts hwf).1 ht.1 _ hx
  · exact confFrameRoot_preceq_confWalk_positive c p a nr s rho hwf hdom hsleep hw ht hpos hg

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick の grade の stable root(`ConfirmedOrigin.confStableRootAt`。
grade の候補が無ければ FG root)は、同じ tick の確認の walk の祖先。手書き `preparedStableRoot_preceq_confWalk_of_gstZero_clean`
(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。`frameStableRoot` の 2 枝で分け、FG root に戻る枝は
FG root ⪯ SG root(`ProposerRoot.getSgRootWith_extends_fgRoot`)⪯ head(`Goldfish.sgRoot_preceq_head`)で round によらず閉じ、
g2 の frame の root がある枝は `confFrameRoot_preceq_confWalk` から(周回 226)。 -/
theorem confStableRoot_preceq_confWalk (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t) {g : Block}
    (hg : Proofs.Consensus.ConfirmedOrigin.confStableRootAt c p a nr s rho w i t = some g) :
    preceq g (Proofs.Consensus.ConfirmedOrigin.confWalkAt c p a nr s rho w i t) = true := by
  unfold Proofs.Consensus.ConfirmedOrigin.confStableRootAt Model.Consensus.Protocol.Grades.frameStableRoot at hg
  split at hg
  · rename_i g' hg'
    simp only [Option.some.injEq] at hg
    subst hg
    exact confFrameRoot_preceq_confWalk c p a nr s rho hwf hdom hsleep hw ht hg'
  · simp only [Option.some.injEq] at hg
    subst hg
    exact Proofs.Consensus.Blocks.preceq_trans
      (Proofs.Consensus.ProposerRoot.getSgRootWith_extends_fgRoot _ _ _ _ _)
      (Proofs.Consensus.Goldfish.sgRoot_preceq_head _ _ _ _ _)

/-- GST-zero の枝で最初の確認の時刻が `horizon` 以下の run の、honest なノード `v` の時刻 `t` の読みの確認の記録 `latestConfirmed` は、
ある slot `first`(確認の時刻が `horizon` 以下)以後の確認の時刻が `horizon` 以下のどの slot `last` についても、honest などのノードの
slot `last + 1` の投票の務めの head の祖先。手書き `latestConfirmedAt_preceq_laterVoteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)と、その本体の
`latestConfirmed_preceq_laterVoteDutyHead_of_gstZero`(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。
確認の記録の由来(証明済みの `ConfirmedOrigin.storeAt_confirmed_origin`。周回 224)で分け、genesis なら `first = 0`、確認評価の tick
(slot `q`)の walk か stable root なら `first = q` とし、`confWalk_preceq_laterVoteHead`(と stable root は
`confStableRoot_preceq_confWalk`)から。 -/
theorem recordAt_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hzero : Model.Consensus.Protocol.Schedule.confirmationTime s.e 0 ≤ rho.horizon)
    {v : ValidatorId} (hv : rho.honest.contains v = true) (t : Int) :
    ∃ first : Nat, Model.Consensus.Protocol.Schedule.confirmationTime s.e first ≤ rho.horizon ∧
      ∀ last, first ≤ last → Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon →
        ∀ x, rho.honest.contains x = true →
          preceq (storeAt c p a nr s rho v t).core.latestConfirmed (voteDutyHeadAt c p a nr s rho x (last + 1)) = true := by
  have hsch : ScheduleWellFormed s rho := by
    have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
    unfold ExecutionValid at hexec
    exact hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  rcases Proofs.Consensus.ConfirmedOrigin.storeAt_confirmed_origin c p a nr s rho hs v t with
    hgen | ⟨i, t', -, hct, hB⟩
  · refine ⟨0, hzero, ?_⟩
    intro last _ _ x _
    rw [hgen]
    exact Proofs.Consensus.Blocks.preceq_genesis _
  · refine ⟨_, Proofs.Consensus.ConfirmedOrigin.confTick_horizon s rho hsch hct, ?_⟩
    intro last hql hlast x hx
    have hwalk := confWalk_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hlast hv hx hct
      (Nat.lt_succ_of_le hql) le_rfl
    rcases hB with hB | hB
    · rw [hB]
      exact hwalk
    · exact Proofs.Consensus.Blocks.preceq_trans
        (confStableRoot_preceq_confWalk c p a nr s rho hwf hdom hsleep hv hct hB) hwalk

/-- 時刻 `t` の読み(時刻 `≤ t`)は時刻 `< t + 1` の読み(手書き `finalizedAt_preceq_laterVoteDutyHead_of_gstZero` の `hstore`。周回 248)。 -/
theorem readAt_eq_stateBeforeTime_succ (t : Int) :
    readAt c p a nr s rho t = stateBeforeTime c p a nr s rho (t + 1) := by
  unfold readAt stateBeforeTime
  congr 1
  exact List.filter_congr (fun _ _ => by simp only [Int.lt_add_one_iff])

/-- round `r` の action 時刻は opening slot の確認の時刻(定義の展開。周回 248)。 -/
theorem actionTime_eq_confirmationTime (r : Nat) :
    Model.Consensus.Protocol.Grades.actionTime s.hc s.e.delta r =
      Model.Consensus.Protocol.Schedule.confirmationTime s.e (Model.Consensus.Protocol.Grades.openingSlot s.hc r) := rfl

/-- slot `first` の確認の時刻は、`first ≤ last` なら slot `last + 2` の投票時刻より前(`6Δ + 4Δ·first < Δ + 4Δ(last + 2)`。
手書き `confirmationTime_lt_nextVote_of_lt`。周回 248)。 -/
theorem confirmationTime_lt_nextVote (hδ : 0 < s.e.delta) {first last : Nat} (h : first ≤ last) :
    Model.Consensus.Protocol.Schedule.confirmationTime s.e first <
      Model.Consensus.Protocol.Schedule.voteTime s.e (last + 1 + 1) := by
  have h' : (first : Int) ≤ (last : Int) := by exact_mod_cast h
  unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
    Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
  simp only [Int.ofNat_eq_natCast]
  push_cast
  nlinarith

/-- `recordAt_preceq_laterVoteHead` の finalized の版。手書き `finalizedAt_preceq_laterVoteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)に当たる。
手書きと同じ運び: 時刻 `t` の読みを時刻 `< t + 1` の読みに移し(`readAt_eq_stateBeforeTime_succ`)、finalized ⪯ FG root
(`ReceiverFinality.store_fgRoot_extends`。読みの `f ⪯ j` は `ProposerFinality.readAt_fj`)とし、FG root を証明済みの
`RootWitness.stateBeforeTime_fgRoot_confirmationWitness` で genesis(`first = 0`)か honest な行の務めの確認の証人に分ける。
後者は行の時刻が行の round の action 時刻(`RootWitness.emits_attest_actionTime_round`)で、それは opening slot の確認の時刻
(`actionTime_eq_confirmationTime`)なので `first` を opening slot にとり(行の tick は run の event なので `horizon` 以下)、
`first ≤ last` なら行の時刻は slot `last + 2` の投票時刻より前(`confirmationTime_lt_nextVote`)なので穴
`fgWitness_preceq_laterVoteHead` から(周回 248)。genesis の枝は `SlashableBound` を与えないので `finalizedSafe` の本体は使えない。 -/
theorem finalizedAt_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hzero : Model.Consensus.Protocol.Schedule.confirmationTime s.e 0 ≤ rho.horizon)
    {v : ValidatorId} (hv : rho.honest.contains v = true) (t : Int) :
    ∃ first : Nat, Model.Consensus.Protocol.Schedule.confirmationTime s.e first ≤ rho.horizon ∧
      ∀ last, first ≤ last → Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon →
        ∀ x, rho.honest.contains x = true →
          preceq (storeAt c p a nr s rho v t).core.f (voteDutyHeadAt c p a nr s rho x (last + 1)) = true := by
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho (Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep)).2
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, hunf⟩, -⟩ := hexec
  unfold UnforgeableSignatures at hunf
  obtain ⟨-, hcar⟩ := hunf
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hhor0 : (0 : Int) ≤ rho.horizon := by
    have h := hsch
    unfold ScheduleWellFormed at h
    exact h.1.1.1.1.1.1
  have hlag : (0 : Int) ≤ Model.Consensus.Spec.Constants.participationLag s :=
    (Proofs.Consensus.Constants.period_pos s hfacts.1 hfacts.2.2).le
  have hqh := Proofs.Consensus.JustificationCertificate.quorumHonest_of_sleepyRegime
    (Proofs.Consensus.JustificationCertificate.sorted_validators hwf) hsleep hlag le_rfl (by rw [sub_self]; exact hhor0)
  have hvm : v ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hv
  have hF := Proofs.Consensus.ReceiverFinality.store_fgRoot_extends
    (Proofs.Consensus.ProposerFinality.readAt_fj c p a nr s rho t v)
  rw [readAt_eq_stateBeforeTime_succ] at hF
  have hst : storeAt c p a nr s rho v t = (worldAt (stateBeforeTime c p a nr s rho (t + 1)) v).st := by
    unfold storeAt
    rw [readAt_eq_stateBeforeTime_succ]
  rw [hst]
  rcases Proofs.Consensus.RootWitness.stateBeforeTime_fgRoot_confirmationWitness c p a nr s rho hs hqh hcar hcf hvm (t + 1) with
    hg | ⟨-, row, -, t2, i2, -, -, hH, -, -, hem, hev, hT⟩
  · refine ⟨0, hzero, ?_⟩
    intro last _ _ x _
    rw [hg] at hF
    exact Proofs.Consensus.Blocks.preceq_trans hF (Proofs.Consensus.Blocks.preceq_genesis _)
  · have hconf : Model.Consensus.Protocol.Schedule.confirmationTime s.e
        (Model.Consensus.Protocol.Grades.openingSlot s.hc row.round) = t2 := by
      rw [Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem, actionTime_eq_confirmationTime]
    have h2 : t2 ≤ rho.horizon := (Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? hev)).2
    refine ⟨Model.Consensus.Protocol.Grades.openingSlot s.hc row.round, hconf ▸ h2, ?_⟩
    intro last hlast hlastHor x hx
    have ht2 : t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (last + 1 + 1) :=
      hconf ▸ confirmationTime_lt_nextVote s hfacts.1 hlast
    exact Proofs.Consensus.Blocks.preceq_trans hF
      (fgWitness_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hlastHor (by omega) le_rfl hx
        ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hH) hem hev ht2 hT)

/-- GST-zero の枝(`t0 = 0`)で最初の確認の時刻 `confirmationTime e 0` が `horizon` 以下の run の、honest な 2 ノードの時刻 0 以後の
2 つの読みの finalized と確認の記録 `latestConfirmed` の共通の上界(`CommonUpperFrom`): `finalizedAt_preceq_laterVoteHead` /
`recordAt_preceq_laterVoteHead` の 4 つの `first` の最大を `last` とし、`u` の slot `last + 1` の投票の務めの head を上界にする
(`last` は 4 つのどれかなので確認の時刻は `horizon` 以下)。手書き `latestConfirmed_compatible_finalized_of_weakGenesis` /
`confirmedOutputCompatibleFrom_of_weakGenesis_named` の上界の揃え方。 -/
theorem commonUpper_genesis_long (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hzero : Model.Consensus.Protocol.Schedule.confirmationTime s.e 0 ≤ rho.horizon) :
    CommonUpperFrom c p a nr s rho 0 := by
  intro u v t t2 hu hv _ _ _ _
  obtain ⟨f1, h1, hb1⟩ := finalizedAt_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hzero hu t
  obtain ⟨f2, h2, hb2⟩ := recordAt_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hzero hu t
  obtain ⟨f3, h3, hb3⟩ := finalizedAt_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hzero hv t2
  obtain ⟨f4, h4, hb4⟩ := recordAt_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hzero hv t2
  have hmax : ∀ x y : Nat, Model.Consensus.Protocol.Schedule.confirmationTime s.e x ≤ rho.horizon →
      Model.Consensus.Protocol.Schedule.confirmationTime s.e y ≤ rho.horizon →
      Model.Consensus.Protocol.Schedule.confirmationTime s.e (max x y) ≤ rho.horizon := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy]; exact hy
    · rw [max_eq_left hyx]; exact hx
  let last := max (max f1 f2) (max f3 f4)
  have hlast : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon :=
    hmax _ _ (hmax _ _ h1 h2) (hmax _ _ h3 h4)
  refine ⟨voteDutyHeadAt c p a nr s rho u (last + 1), ?_, ?_, ?_, ?_⟩
  · exact hb1 last (by omega) hlast u hu
  · exact hb2 last (by omega) hlast u hu
  · exact hb3 last (by omega) hlast u hu
  · exact hb4 last (by omega) hlast u hu

/-- 最初の確認の時刻 `confirmationTime e 0` より前に終わる run では、どのノード・どの時刻の読みでも finalized は genesis
(証明済みの `ShortHorizon.storeAt_f_short`。周回 220)。手書き `confirmedOutputCompatibleFrom_of_weakGenesis_named`
(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)の短い horizon の枝の局所の事実 `hfinalized` に当たる。 -/
theorem finalized_genesis_short (hwf : SetupWellFormed c p s)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hshort : rho.horizon < Model.Consensus.Protocol.Schedule.confirmationTime s.e 0) (v : ValidatorId) (t : Int) :
    (storeAt c p a nr s rho v t).core.f = Block.Genesis := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  exact Proofs.Consensus.ShortHorizon.storeAt_f_short c p a nr s rho hexec.1.1.1
    (Proofs.Consensus.Liveness.wf_facts hwf).1 hshort v t

/-- GST-zero の枝(`t0 = 0`)の共通の上界: 最初の確認の時刻が `horizon` 以下なら `commonUpper_genesis_long` から、
そうでなければ確認の記録は genesis(`ShortHorizon.storeAt_rec_short`。手書き `latestConfirmedAt_eq_genesis_of_short_horizon`)で
finalized も genesis(`finalized_genesis_short`)なので、上界は genesis。 -/
theorem commonUpper_genesis (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) :
    CommonUpperFrom c p a nr s rho 0 := by
  by_cases hzero : Model.Consensus.Protocol.Schedule.confirmationTime s.e 0 ≤ rho.horizon
  · exact commonUpper_genesis_long c p a nr s rho hwf hdom hsleep hzero
  · have hshort := lt_of_not_ge hzero
    have hsch : ScheduleWellFormed s rho := by
      have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
      unfold ExecutionValid at hexec
      exact hexec.1.1.1
    have hδ : 0 ≤ s.e.delta := (Proofs.Consensus.Liveness.wf_facts hwf).1.le
    have hL (w : ValidatorId) (r : Int) : (storeAt c p a nr s rho w r).core.latestConfirmed = Block.Genesis :=
      (Proofs.Consensus.ShortHorizon.storeAt_rec_short c p a nr s rho hsch hδ hshort w r).1
    have hF (w : ValidatorId) (r : Int) : (storeAt c p a nr s rho w r).core.f = Block.Genesis :=
      finalized_genesis_short c p a nr s rho hwf hsleep hshort w r
    intro u v t t2 _ _ _ _ _ _
    refine ⟨Block.Genesis, ?_, ?_, ?_, ?_⟩
    all_goals first
      | rw [hF]; exact Proofs.Consensus.Blocks.preceq_self _
      | rw [hL]; exact Proofs.Consensus.Blocks.preceq_self _

/-- 穴: 回復の枝(`t0 ≠ 0`。`RecoveredBy` の `recovered`)の確認の記録 `latestConfirmed` の honest な 2 ノード・`t0` 以後の読みの一致。
手書き `available_confirmedSafe`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)の `recovered` の枝に当たる。
閉じるのに要るもの: `boundedSafety`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の位相の `UserConfirmationAfterHealing.latestCompatible`。 -/
theorem recordAgree_recovered {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) (hne : t0 ≠ 0) :
    RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  sorry

/-- 穴: 回復の枝(`t0 ≠ 0`)の確認の記録 `latestConfirmed` と finalized の、honest な 2 ノード・`t0` 以後の読みの交差の互換。
手書き `SettledBootstrapPreparedV4.latest_compatible_finalized_core`
(`DecoupledConsensusProofs/Execution/PreparedV4LatestFinalizedCompatibilityClosed.lean`)に当たる。
閉じるのに要るもの: 確認の記録が finalized を延ばすこと(記録についての事実。`Nested.lean` は出力 `getConfirmed` についてだけ)と、
`recordAgree_recovered` と同じ位相の一致。 -/
theorem crossAgree_recovered {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) (hne : t0 ≠ 0) :
    CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  sorry

/-- 確認の記録の一致: GST-zero の枝は共通の上界(穴 `commonUpper_genesis`)から、回復の枝は穴 `recordAgree_recovered` から。
手書き `available_confirmedSafe` の一致の半分(`RecoveredBy` の 2 枝で分ける)。 -/
theorem recordAgree {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    RecordAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  by_cases h0 : t0 = 0
  · subst h0
    exact recordAgreeFrom_of_commonUpper c p a nr s rho (commonUpper_genesis c p a nr s rho hwf hdom hsleep)
  · exact recordAgree_recovered c p a nr s rho hwf hdom hsleep h0

/-- 確認の記録と finalized の交差の互換: GST-zero の枝は共通の上界から(手書き `latestConfirmed_compatible_finalized_of_weakGenesis`)、
回復の枝は穴 `crossAgree_recovered` から。 -/
theorem crossAgree {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    CrossAgreeFrom c p a nr s rho (fun st => st.latestConfirmed) t0 := by
  by_cases h0 : t0 = 0
  · subst h0
    exact crossAgreeFrom_of_commonUpper c p a nr s rho (commonUpper_genesis c p a nr s rho hwf hdom hsleep)
  · exact crossAgree_recovered c p a nr s rho hwf hdom hsleep h0

/-- GST-zero の枝(`t0 = 0`)の確認の出力の一致: 共通の上界(穴 `commonUpper_genesis`)から `agreeFrom_confirmed_of_commonUpper`。
手書き `gstZeroGuarantees_of_weakGenesis` の欄 `outputCompatible`(`confirmedOutputCompatibleFrom_of_weakGenesis_named`)に当たる。 -/
theorem confirmedAgree_genesis (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) :
    AgreeFrom c p a nr s rho Output.Confirmed 0 :=
  agreeFrom_confirmed_of_commonUpper c p a nr s rho (commonUpper_genesis c p a nr s rho hwf hdom hsleep)

/-- GST-zero の枝(`t0 = 0`)の finalized の一致: 確認の出力の一致(`confirmedAgree_genesis`)を `agreeFrom_finalized_of_confirmed` で
finalized に下ろす。手書き `available_stableSafe` の `genesis` の枝の `finalized_compatible_of_confirmed_compatible` の筋。
回復の枝は `agreeFrom_finalized_of_recovered`(証明済み)。 -/
theorem finalizedAgree_genesis (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) :
    AgreeFrom c p a nr s rho Output.Finalized 0 :=
  agreeFrom_finalized_of_confirmed c p a nr s rho (confirmedAgree_genesis c p a nr s rho hwf hdom hsleep)

/-- 穴: honest な提案の確認の出力への期限 `confirmationDelay` 以内の包含。
手書き `available_confirmedIncluded`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)に当たる。
閉じるのに要るもの: `genesis` の枝は `gstZeroGuarantees_of_weakGenesis` の `userProposals`、`recovered` の枝は位相の `userConfirmation.proposals`。
どちらも honest な提案が適格な子の一意な最大になって `ghost_reaches`(`Goldfish.lean`)で選ばれることと、提案が締切までに各ノードの tree に入ること
(`ProposerRoot.lean` の `partialSynchrony_emitted_block_mem_of_fgRoot`。FG root の上界 = 手書き `hreadBound`)。 -/
theorem confirmedIncluded {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    IncludedFrom c p a nr s rho Output.Confirmed t0 (confirmationDelay s) := by
  sorry

/-- 穴: honest な提案の stable の出力への期限 `stableInclusionDelay` 以内の包含。
手書き `available_stableIncluded_any`(`DecoupledConsensusProofs/Bridge/StableIncludedAnySlot.lean`)に当たる。
閉じるのに要るもの: `confirmedIncluded` と同じ包含を grade の候補 `frameSgCandidate` と stable の記録の床 `floorOnStable` に移すこと。 -/
theorem stableIncluded {t0 : Int} (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho t0) :
    IncludedFrom c p a nr s rho Output.Stable t0 (stableInclusionDelay s) := by
  sorry

end Holes

/-- claim `available` の骨格の入口: `t0` が 0 か否かで finalized の一致の出どころを分け、残りの 4 つの事実を穴から取って組み立てる。
手書き `concreteConsensus`(`DecoupledConsensusProofs/ReviewTheorem.lean`)の `available` の枝に当たる。 -/
theorem availableAt (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (t0 : Int)
    (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho) (hsleep : SleepyRegime c p a nr s rho t0) :
    AvailableAt c p a nr s rho t0 := by
  have hL := recordAgree c p a nr s rho hwf hdom hsleep
  have hX := crossAgree c p a nr s rho hwf hdom hsleep
  have hIc := confirmedIncluded c p a nr s rho hwf hdom hsleep
  have hIs := stableIncluded c p a nr s rho hwf hdom hsleep
  by_cases h0 : t0 = 0
  · subst h0
    exact availableAt_of_fields c p a nr s rho hsleep hL hX (finalizedAgree_genesis c p a nr s rho hwf hdom hsleep) hIc hIs
  · exact availableAt_of_fields_recovered c p a nr s rho hwf hdom hsleep h0 hL hX hIc hIs

end Proofs.Consensus.AvailableHoles
