import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Available
import Proofs.Consensus.ShortHorizon
import Proofs.Consensus.Voting
import Proofs.Consensus.ConfirmedOrigin
import Proofs.Consensus.ProposerRoot
import Proofs.Consensus.GradeSupporter
import Proofs.Consensus.GradeTransport
import Proofs.Consensus.SgStamps
import Proofs.Consensus.SgFrom
import Proofs.Consensus.SgAdmit
import Proofs.Consensus.FrameCapture
import Proofs.Consensus.CarriedSupport
import Proofs.Consensus.CarriedCommittee
import Proofs.Consensus.ProcessedAncestor
import Proofs.Consensus.EntryHeight
import Proofs.Consensus.MaxCarrier
import Proofs.Consensus.MaxCrossing
import Proofs.Consensus.HeightRowWitness
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
   とって `fgWitness_preceq_laterVoteHead` に渡す(周回 248)。`recordAt_preceq_laterVoteHead` は確認の記録の由来(証明済みの
   `ConfirmedOrigin.storeAt_confirmed_origin`: genesis か、確認評価の tick の確認の walk か grade の stable root)で分け、
   `confWalk_preceq_laterVoteHead`(walk ⪯ 後の投票の head。穴ではない)と `confStableRoot_preceq_confWalk`(stable root ⪯ walk。穴ではない)から証明する(周回 224)。
   `confWalk_preceq_laterVoteHead` は walk が anchor のままか filtered tree の適格な要素か(`Goldfish.head_cases`)で分け、anchor の枝は
   `confAnchor_preceq_laterVoteHead`(g1 の frame の raw の active prefix か FG root なので `confG1Raw_preceq_laterVoteHead` /
   `confFgRoot_preceq_laterVoteHead` から)、動いた枝は `confEligibleWalk_preceq_laterVoteHead` から証明する(周回 245)。
   `confEligibleWalk_preceq_laterVoteHead` は walk が genuine な確認なので `genuineConf_preceq_laterVoteHead`(手書き
   `protectedVoteSlots_of_gstZero_v2` の `heads`)から(周回 250)。`genuineConf_preceq_laterVoteHead` は周回 270 に、手書きと同じ
   保護された投票の slot(`ProtectedVoteSlot`: 投票の head の `heads` と投票の cone)の slot の帰納法 `protectedVoteSlots_gstZero` で
   証明した。cone はどの slot でも `heads` から出る(`voteCone_of_heads`。周回 273。種の cone `voteCone_genesis` は周回 272 に証明し、
   周回 273 からその特別な場合)、slot 0 の確認は `genuineConf_slot_zero`(周回 271 に証明した)、段の `heads` は `protectedVoteSlot_preserve`(古い確認。周回 297 に閉じた)と
   `protectedVoteSlot_succ_of_genuineConf`(slot `d` の確認。周回 298 に閉じ、`C` の支持者の過半 `genuineConf_supporterMajority` は
   周回 299 に手書き `AdoptionTransport` の数え上げで閉じて、移送の境界を穴 `genuineConf_adoptionTransport` に切り出した)で、段の補題は帰納法の仮定 `PriorConfsBelow d` を受け取る。行の源は
   この前提で `laterVoteHead_rowSources_of_prior` から取れる。`fgWitness_preceq_laterVoteHead` は round の同時帰納
   `RootWitness.dutyStoreAt_jointRoundInduction_of_prior` を `base = cut = 0` で掛け、段の genuine な確認を
   `genuineConf_preceq_laterVoteHead`、SG block と grade 2 の候補を `fgStep_preceq_laterVoteHead` から供給する(周回 250)。
   `fgStep_preceq_laterVoteHead` は務めの store の round で分け、round 0 は `fgStep_round_zero`(round 0 の frame に G1 / G2 の root は
   無いので grade 2 の候補は空、SG block は `liveConfirmed` の祖先か FG root)で閉じ、正の round を
   `fgStep_preceq_laterVoteHead_positive`(手書きの帰納の段の `hformation` の側。周回 252 から穴ではない)に渡す(周回 251)。
   `fgStep_preceq_laterVoteHead_positive` は SG block を `sgBlockAt_preceq_of_candidate_anchor`(`currentSGVote` の 4 つの枝)で
   grade 2 の候補と anchor に下ろす(周回 252)。anchor は `frameAnchor_preceq_of_g1Prefix` で FG root と G1 の root の active prefix に
   下ろす(周回 253)。G1 の root の active prefix(`fgStep_g1Prefix_positive`。周回 255 に閉じた)と grade 2 の候補(`fgStep_candidate_positive`)は、
   どちらも凍結した root を窓の round の honest な行の SG block の祖先に下ろし、前の round の SG block の前提で閉じる。G1 の root の出どころは
   `confCache_phase_origin`、grade の担い手は `fgStep_gradeCarrier_positive`(周回 254)。
   `confFgRoot_preceq_laterVoteHead` は FG root を tick の時刻の読みの FG root に移し(`confPreUpdate_fgRoot`: 確認の締切は提案時刻ではない
   `supportCutoff_ne_proposalTime`)、証明済みの `RootWitness.stateBeforeTime_fgRoot_confirmationWitness` で genesis か honest な行の務めの
   確認の証人に分け、後者を `fgWitness_preceq_laterVoteHead` に渡す(周回 247)。
   `confG1Raw_preceq_laterVoteHead` は round 0 を矛盾(`confCache_g1_round_zero`: round 0 の凍結は空 `FrameCapture.freezeRoot_zero` で、
   cache の round 0 の結果も空 `FrameCapture.stateBefore_phase_zero`)で閉じ、正の round を `confG1Raw_preceq_laterVoteHead_positive` に渡す(周回 246)。
   これは raw を G1 の domain 時刻の tick で凍結した root に下ろし(`confCache_phase_origin`)、その grade の担い手(`confG1Carrier_positive`)の
   窓の round の honest な行の SG block を `sgBlock_preceq_laterVoteHead`(`fgWitness_preceq_laterVoteHead` と同じ round の同時帰納
   `laterVoteHead_rowSources` の SG block の連言)で閉じる(周回 256。`confWindowCarrier_preceq_laterVoteHead`)。
   2 つの担い手 `fgStep_gradeCarrier_positive` / `confG1Carrier_positive` は、共通の上界 `D`(ここでは `X`)が窓の round の honest な
   行の SG block と、phase の読みのすべての honest なノードの finalized の上にあれば担い手がある、という共通の構成
   `relativeGradeCarrierAt_of_commonUpper` から証明する。finalized の側は `stateBeforeTime_f_preceq_of_witnesses` で読みより前の
   honest な行の確認の証人に下ろす(周回 257)。共通の構成は、解釈済みの入力を持つ honest な多数派
   (`honestInterpretedMajority_of_commonUpper`。`SleepyRegime` の `WindowMajority` を round の action 時刻で使った窓の awake な
   honest の集合で、窓の時刻の action round は round の窓にある `actionRound_mem_latestWindow`。周回 260。各元が解釈済みの入力を
   持つことは `awakeWindowVote_interpreted_of_commonUpper`: 元は round の action 時刻に行を出し(`awake_emits_actionRow`)、その行の
   SG 票と SG block が早い cutoff より前に読み手に届くことは `honestActionRow_delivered`。周回 261。その行の側の運びは周回 262 に証明した:
   `PartialSynchrony` で `t + Δ` より前に扱われ、扱いの後の行の attestation(`honestActionRow_handled_row`。周回 263 に
   `SgAdmit.handlesAt_honestRow_mem` で閉じた: `onSgVote` の受理の窓と、honest な送り手の行の `confirmed` が 1 通りであること)の印は
   扱いの時刻以下で残る(`SgStamps.sg_stamp_le_of_mem`)。SG block の側 `honestActionRow_sgBlock_delivered` は周回 264 に、読み手の tree に
   `t + Δ` より前に入れば印と root の解決が出ること(`BlockStamps.tree_stamped`・`findRoot?_of_mem`)と、読み手が `u` 自身の場合で証明し、
   `u` でない読み手の tree に入ることは周回 265 に `u` の受理(`bodies_accepted_before`)と `PartialSynchrony` の中継の連言で
   `honestActionRow_sgBlock_held` に証明した。扱ったブロックが扱いの後の tree にあること `acceptedBlock_handled_held` は周回 266 に
   受理の守り(`acceptedBlock_static`・`processBlockCore_guards`)と finalized の祖先が tree にあることで閉じた)から grade の honest な支持者の
   入力を取り(`GradeSupporter.phase_graded_has_honest_supporter`)、それを送り手が出した行に戻し(`SgFrom.sg_genuine`)、その `confirmed` の解決を行の SG block と同一視する(`sgBlockAt_findRoot_eq`)
   (周回 258)。`sgBlockAt_findRoot_eq` は、SG block が務めの store の tree にあり(`sgBlockAt_mem_dutyTree`)、その bodies が tick の後の
   bodies(`stateBefore_succ_bodies_of_emits`)なので run の中のブロックで、run に root の衝突が無いことで閉じた(周回 259)。
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
3. 穴(6 件): `protectedVoteSlot_preserve`(手書き `protectedVoteSlots_of_historyCut_v2_w` の `hpreserve`、
   `DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/WeakBootstrapSlot.lean`)/ `protectedVoteSlot_succ_of_genuineConf`(手書き
   `protectedVoteSlot_succ_of_genuineConfirmationWith`、`DecoupledConsensusProofs/Protocol/ForkChoice/Views/WeakConfirmationHead.lean`)/
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

section TickAttest

open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Handlers
open Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick Model.Consensus.Execution.Objects
open Proofs.Consensus.Clocks

/-- 務めの store `tickDutyStore` の時計は `(t, slotOf e t)`(冒頭で合わせた時計を務めが変えない。`Clocks.tick_clockIs` と
同じ運びで、`tickDutyStore` の提案・投票・確認の更新の有無の 8 経路。周回 261)。 -/
theorem tickDutyStore_clockIs {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) (t : Int) :
    ClockIs (Proofs.Consensus.AttestationSource.tickDutyStore c p nr cache e hc cfg nd st t) t (slotOf e t) := by
  have h0 : ClockIs { st with core := { st.core with t := t, s := slotOf e t } } t (slotOf e t) := ⟨rfl, rfl⟩
  unfold Proofs.Consensus.AttestationSource.tickDutyStore
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact namedUpdateConfirmationWith_clockIs cache hc (namedGoldfishVoteWith_clockIs c cache hc nd (proposeBlockWith_clockIs c p nr cache hc nd h0)) _
    | with_reducible exact namedUpdateConfirmationWith_clockIs cache hc (namedGoldfishVoteWith_clockIs c cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_clockIs cache hc (proposeBlockWith_clockIs c p nr cache hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_clockIs cache hc h0 _
    | with_reducible exact namedGoldfishVoteWith_clockIs c cache hc nd (proposeBlockWith_clockIs c p nr cache hc nd h0)
    | with_reducible exact namedGoldfishVoteWith_clockIs c cache hc nd h0
    | with_reducible exact proposeBlockWith_clockIs c p nr cache hc nd h0
    | with_reducible exact h0

/-- **action 時刻の awake な tick は行を出す**: tick の時刻 `t` が `t` の slot の round の action 時刻で、ノードがその round に awake
なら、tick の出力に行がある(生成 `tick` の attestation の条件 `t == actionTime r && awake valIndex r` の `r` は務めの store の slot の
round で、務めの store の slot は `slotOf e t`: `tickDutyStore_clockIs`)。手書き `honest_emits_exact_actionAttestationAt_of_awake`
(`Protocol/Schedule/Action.lean`)の tick の段(周回 261)。 -/
theorem tick_attest_of_awake {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int)
    (ht : t = Model.Consensus.Protocol.Grades.actionTime hc e.delta
      (Model.Consensus.Protocol.Grades.roundOf hc (slotOf e t)))
    (haw : a nd.valIndex (Model.Consensus.Protocol.Grades.roundOf hc (slotOf e t)) = true) :
    ∃ row : Model.Consensus.Objects.NamedBlocks.NamedAttestation,
      NamedObject.Attest row ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2 := by
  have hs := (tickDutyStore_clockIs (e := e) (cfg := cfg) c p nr cache hc nd st t).2
  have hcond : (t == Model.Consensus.Protocol.Grades.actionTime hc e.delta
      (Model.Consensus.Protocol.Grades.roundOf hc
        (Proofs.Consensus.AttestationSource.tickDutyStore c p nr cache e hc cfg nd st t).core.s) &&
      a nd.valIndex (Model.Consensus.Protocol.Grades.roundOf hc
        (Proofs.Consensus.AttestationSource.tickDutyStore c p nr cache e hc cfg nd st t).core.s)) = true := by
    rw [hs]
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨ht, haw⟩
  revert hcond
  unfold tick Proofs.Consensus.AttestationSource.tickDutyStore
  dsimp only
  split_ifs
  all_goals intro hcond
  -- 行を出さない経路は条件と矛盾し、行を出す経路は出力の末尾が行
  all_goals first
    | exact absurd hcond ‹_›
    | ((repeat' split) <;> exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩)

end TickAttest

section AcceptGuards

open Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Handlers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.Store

/-- **`onBlockUsing` が tree に新しく入れたブロックは受理の守りを通った**: slot は store の slot 以下、提案者は slot の提案者、
親の slot はブロックの slot より小さい(`NoFutureRead.onBlockUsing_slot_le` の守り全部の版。周回 266)。 -/
theorem onBlockUsing_guards (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (st : Store) (b : Block)
    (build : ChainState → ChainState) (hnb : b ∉ st.tree.elems) (hb : b ∈ (onBlockUsing c p st b build).tree.elems) :
    slot b ≤ st.s ∧ proposer? b = some (p (slot b)) ∧ slot (parent b) < slot b := by
  unfold onBlockUsing at hb
  split_ifs at hb with h1 h2 h3 h4
  · exact absurd hb hnb
  · exact absurd hb hnb
  · exact absurd hb hnb
  · exact absurd hb hnb
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1
    refine ⟨Nat.le_of_not_lt h1.1.1, ?_, by simpa using h4⟩
    simpa using h3

/-- **`processBlockCore` で bodies に新しく入ったブロックは守りを通った**: 処理したブロックそのもので、運ばれた attestation は
受け入れ可能(`onBlockCheckedUsing`)、`onBlockUsing` の守り(`onBlockUsing_guards`)を満たす(`NoFutureRead.processBlockCore_entry`
の守り全部の版。周回 266)。 -/
theorem processBlockCore_guards (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : HeightConfig) {st : NamedStore} {B D : NamedBlock} (hD : D ∉ st.bodies.elems)
    (hD' : D ∈ (processBlockCore c p e hc cfg st B).bodies.elems) :
    D = B ∧ carriedAttestationsAdmissible hc (eraseBlock B) = true ∧ slot (eraseBlock B) ≤ st.core.s ∧
      proposer? (eraseBlock B) = some (p (slot (eraseBlock B))) ∧
      slot (parent (eraseBlock B)) < slot (eraseBlock B) := by
  unfold processBlockCore at hD'
  split_ifs at hD' with hpar
  · exact absurd hD' hD
  · dsimp only at hD'
    unfold commitBlock at hD'
    dsimp only at hD'
    split_ifs at hD' with hcom
    · have hDB : D = B := by
        have h' : D ∈ (st.bodies.insert B).elems := hD'
        rw [Proofs.Consensus.Sets.mem_insert_iff Proofs.Consensus.Orders.nb_compare_eq_iff] at h'
        rcases h' with rfl | h'
        · rfl
        · exact absurd h' hD
      subst hDB
      obtain ⟨hnot, hin⟩ := (Bool.and_eq_true _ _).mp hcom
      have hnb : eraseBlock D ∉ st.core.tree.elems := by
        intro hm
        rw [← Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.block_compare_eq_iff] at hm
        rw [hm] at hnot
        simp at hnot
      rw [Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.block_compare_eq_iff] at hin
      unfold onBlockCheckedUsing at hin
      split_ifs at hin with hca
      · exact ⟨rfl, hca, onBlockUsing_guards c p st.core (eraseBlock D) _ hnb hin⟩
      · exact absurd hin hnb
    · exact absurd hD' hD

end AcceptGuards

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

/-- **務めの SG block は、grade 2 の候補と anchor の共通の上界の祖先**(Δ > 0、round を問わない): 行を出した tick(添字 `i`・時刻 `t`)の
務めの FG root・その tick の genuine な確認・務めの grade 2 の候補・務めの round の frame の anchor がどれも `X` の祖先なら、務めの
SG block も `X` の祖先。`currentSGVote` の 4 つの枝(`deepestClear` の結果は `liveConfirmed` の祖先(`AttestationSource.deepestClear_preceq`
と `RootWitness.dutyStoreAt_live_preceq_of_prior`)、grade 2 の候補、rawG2 なら FG root、それ以外は anchor)をそれぞれ閉じる
(`fgStep_round_zero` の SG block の運びを、round 0 の事実の代わりに前提 `hq2` / `hanchor` で一般化した形。周回 252)。 -/
theorem sgBlockAt_preceq_of_candidate_anchor (hδ : 0 < s.e.delta)
    {w : ValidatorId} {i : Nat} {t : Int} {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho w
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t) {X : Block}
    (hroot : preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
        (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core)) X = true)
    (hprior : ∀ C, Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C → preceq C X = true)
    (hq2 : ∀ q, Proofs.Consensus.RootWitness.grade2CandidateAt c p a nr s rho w i t = some q → preceq q X = true)
    (hanchor : preceq (Model.Consensus.Protocol.Grades.frameGradeRead
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) s.e s.hc
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core.s)).anchor X = true) :
    preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho w i t) X = true := by
  have hlive := Proofs.Consensus.RootWitness.dutyStoreAt_live_preceq_of_prior c p a nr s rho hδ hem hroot hprior
  unfold Proofs.Consensus.RootWitness.sgBlockAt
  unfold Model.Consensus.Protocol.Duties.Inputs.getSgVoteWith Model.Consensus.Protocol.Grades.currentSGVote
  split
  · rename_i b hb
    exact Proofs.Consensus.Blocks.preceq_trans (Proofs.Consensus.AttestationSource.deepestClear_preceq hb) hlive
  · dsimp only
    split
    · rename_i q hq
      exact hq2 q hq
    · split_ifs
      · exact hroot
      · exact hanchor

/-- **frame の anchor は、FG root と G1 の root の active prefix の共通の上界の祖先**(store・cache・round を問わない): anchor は
G1 の結果が root `g` を持てば filtered tree の中の `g` の active prefix(無ければ FG root)、持たなければ FG root(生成 Model の
`Grades.anchor`)。FG root ⪯ `X` と、active prefix があるときのそれ ⪯ `X` から anchor ⪯ `X`(周回 253)。 -/
theorem frameAnchor_preceq_of_g1Prefix {e : Model.Consensus.Objects.Parameters.ProtocolEnv}
    {hc : Model.Consensus.Protocol.Grades.HealConfig} {cache : Model.Consensus.Protocol.Grades.Cache}
    {st : Model.Consensus.Protocol.ForkChoice.Goldfish.FGStore} {r : Nat} {X : Block}
    (hroot : preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot st) X = true)
    (hg1 : ∀ g b, (Model.Consensus.Protocol.Grades.readFrame cache st r).g1 = some (some g) →
      Model.Consensus.Protocol.Grades.activePrefix (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree st) g =
        some b → preceq b X = true) :
    preceq (Model.Consensus.Protocol.Grades.frameGradeRead cache e hc st r).anchor X = true := by
  unfold Model.Consensus.Protocol.Grades.frameGradeRead Model.Consensus.Protocol.Grades.anchor
  dsimp only
  split
  · rename_i g hg
    cases hb : Model.Consensus.Protocol.Grades.activePrefix
        (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree st) g with
    | none => simpa only [Option.getD_none] using hroot
    | some b => simpa only [Option.getD_some] using hg1 g b hg hb
  · exact hroot

/-- **frame の phase の root の出どころ**(正の round): run の添字 `i` の event が `w` の時刻 `t` の tick なら、その tick が準備する
cache(`ConfirmedOrigin.confCacheAt`)の正の round `k` の frame をどの store で読んでも、phase `P` の結果 `some (some raw)` の祖先 `P'` は、
添字 `j ≤ i` の event `Tick w (domainTime e hc k P)` の前の store で `freezeRoot` が凍結した `g0` の祖先。読みの切り詰めを
`clipResult_some` で外し、この tick の凍結か tick の前の結果(`FrameCapture.onPhaseTick_phase_some`)、後者は run の帰納
(`FrameCapture.stateBefore_phase_origin`)に渡す。`confCache_g2_origin` を phase を問わない形にしたもの(round が正であることを使う。
周回 255)。 -/
theorem confCache_phase_origin {w : ValidatorId} {i : Nat} {t : Int} (hev : rho.events[i]? = some (NamedEvent.Tick w t))
    (st : Model.Consensus.Protocol.ForkChoice.Goldfish.FGStore) {k : Nat} (hk : 0 < k)
    (P : Model.Consensus.Protocol.Grades.GradePhase) {P' raw : Block}
    (h : Model.Consensus.Protocol.Grades.phaseResult
      (Model.Consensus.Protocol.Grades.readFrame (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t) st k) P =
      some (some raw)) (hP : preceq P' raw = true) :
    ∃ (j : Nat) (g0 : Block), j ≤ i ∧
      rho.events[j]? = some (NamedEvent.Tick w (Model.Consensus.Protocol.Grades.domainTime s.e s.hc k P)) ∧
      Model.Consensus.Protocol.Grades.freezeRoot s.e
          (Model.Consensus.Protocol.Grades.gradeView
            (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core))
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core).f s.hc.etaSG k
          (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc k P)
          (Model.Consensus.Protocol.Grades.lateTime s.e s.hc k P) = some g0 ∧
      preceq P' g0 = true := by
  rw [Proofs.Consensus.FrameCapture.phaseResult_readFrame] at h
  obtain ⟨old, hold, hPold⟩ := Proofs.Consensus.Grade2Capture.clipResult_some h hP
  unfold Proofs.Consensus.ConfirmedOrigin.confCacheAt at hold
  rcases Proofs.Consensus.FrameCapture.onPhaseTick_phase_some hold with ⟨x0, hx0, hxe⟩ | ⟨ht, hxe⟩
  · obtain ⟨old0, rfl, hclip⟩ := Option.map_eq_some_iff.mp hxe.symm
    obtain ⟨j, hj, hevj, hx0e⟩ := Proofs.Consensus.FrameCapture.stateBefore_phase_origin c p a nr s rho i w hk P hx0
    obtain ⟨g0, hfz, hclip0⟩ := Option.map_eq_some_iff.mp hx0e.symm
    refine ⟨j, g0, hj.le, hevj, hfz, ?_⟩
    refine Proofs.Consensus.Blocks.preceq_trans hPold ?_
    rw [← hclip, ← hclip0]
    exact Proofs.Consensus.Blocks.preceq_trans (Proofs.Consensus.Grade2Capture.clipGrade_preceq _ _)
      (Proofs.Consensus.Grade2Capture.clipGrade_preceq _ _)
  · subst ht
    obtain ⟨g0, hfz, hclip⟩ := Option.map_eq_some_iff.mp hxe.symm
    refine ⟨i, g0, le_rfl, hev, hfz, ?_⟩
    rw [← hclip] at hPold
    exact Proofs.Consensus.Blocks.preceq_trans hPold (Proofs.Consensus.Grade2Capture.clipGrade_preceq _ _)

/-- 窓の round は読みの round より小さい: `latestWindow eta r` の元 `k` は `k < r`(周回 254)。 -/
theorem lt_of_mem_latestWindow {eta r k : Nat}
    (h : k ∈ Model.Consensus.Protocol.ForkChoice.Goldfish.latestWindow eta r) : k < r := by
  unfold Model.Consensus.Protocol.ForkChoice.Goldfish.latestWindow at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hj
  omega

/-- 時刻 `t` の読み(時刻 `≤ t`)は時刻 `< t + 1` の読み(手書き `finalizedAt_preceq_laterVoteDutyHead_of_gstZero` の `hstore`。周回 248)。 -/
theorem readAt_eq_stateBeforeTime_succ (t : Int) :
    readAt c p a nr s rho t = stateBeforeTime c p a nr s rho (t + 1) := by
  unfold readAt stateBeforeTime
  congr 1
  exact List.filter_congr (fun _ _ => by simp only [Int.lt_add_one_iff])

/-- **行の時刻が round `r` の phase の domain 時刻より前なら、行の round は `r` より小さい**(Δ > 0): 行の時刻は行の round の
action 時刻(opening slot の確認の時刻 `slotStart + 6Δ`。`RootWitness.emits_attest_actionTime_round`)で、domain 時刻は
round `r` の opening slot の開始から高々 `Δ` 後(`domainOffset ≤ 1`)。手書き `FrameForward.domain_le_a` の向き(周回 257)。 -/
theorem emits_round_lt_of_lt_domainTime (hδ : 0 < s.e.delta) {u : ValidatorId}
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} {t2 : Int}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2)
    {r : Nat} {ph : Model.Consensus.Protocol.Grades.GradePhase}
    (ht2 : t2 < Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph) : row.round < r := by
  have ha : Model.Consensus.Protocol.Grades.actionTime s.hc s.e.delta row.round =
      Model.Consensus.Protocol.Schedule.confirmationTime s.e (Model.Consensus.Protocol.Grades.openingSlot s.hc row.round) := rfl
  rw [Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem, ha] at ht2
  by_contra hcon
  have hle : Model.Consensus.Protocol.Grades.openingSlot s.hc r ≤
      Model.Consensus.Protocol.Grades.openingSlot s.hc row.round :=
    Nat.mul_le_mul_right _ (not_lt.mp hcon)
  have hm := Proofs.Consensus.Clocks.slotStart_mono s.e.delta hδ hle
  have hoff : Model.Consensus.Protocol.Grades.domainOffset ph * s.e.delta ≤ s.e.delta := by
    cases ph <;> simp only [Model.Consensus.Protocol.Grades.domainOffset] <;> linarith
  unfold Model.Consensus.Protocol.Grades.domainTime Model.Consensus.Protocol.Grades.openingTime at ht2
  unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.proposalTime
    Model.Consensus.Objects.Parameters.slotTime at ht2
  linarith

/-- **honest な読み手の finalized は、それより前の honest な行の確認の証人の共通の上界の祖先**(GST-zero の枝): 時刻 `< τ` に
honest なノードが出した行の tick の務めの確認の証人がどれも `D` の祖先なら、honest なノード `v` の時刻 `< τ` の読みの
finalized は `D` の祖先。finalized ⪯ FG root(`ReceiverFinality.store_fgRoot_extends`。読みの `f ⪯ j` は
`ProposerFinality.readAt_fj`)とし、FG root を `RootWitness.stateBeforeTime_fgRoot_confirmationWitness` で genesis か
時刻 `< τ` の honest な行の務めの確認の証人に分ける(`finalizedAt_preceq_laterVoteHead` と同じ筋。手書き
`relativeGradeCarrierAt_of_awakeWindowHistory_gstZero` の `hFD` に当たる。周回 257)。 -/
theorem stateBeforeTime_f_preceq_of_witnesses (hwf : SetupWellFormed c p s) (hsleep : SleepyRegime c p a nr s rho 0)
    {v : ValidatorId} (hv : v ∈ rho.honest.elems) (τ : Int) {D : Block}
    (hwit : ∀ (u : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      u ∈ rho.honest.elems → rho.events[i2]? = some (NamedEvent.Tick u t2) →
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      t2 < τ → ∀ T, Proofs.Consensus.RootWitness.fgConfirmationWitnessAt c p a nr s rho u i2 t2 = some T →
        preceq T D = true) :
    preceq (Model.Consensus.Protocol.Store.storeToHealing
      (worldAt (stateBeforeTime c p a nr s rho τ) v).st.core).f D = true := by
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
  have hF := Proofs.Consensus.ReceiverFinality.store_fgRoot_extends
    (Proofs.Consensus.ProposerFinality.readAt_fj c p a nr s rho (τ - 1) v)
  rw [readAt_eq_stateBeforeTime_succ, sub_add_cancel] at hF
  rcases Proofs.Consensus.RootWitness.stateBeforeTime_fgRoot_confirmationWitness c p a nr s rho hs hqh hcar hcf hv τ with
    hg | ⟨-, row2, -, t2, i2, -, -, hH, -, ht2, hem, hev, hT⟩
  · rw [hg] at hF
    exact Proofs.Consensus.Blocks.preceq_trans hF (Proofs.Consensus.Blocks.preceq_genesis _)
  · exact Proofs.Consensus.Blocks.preceq_trans hF (hwit _ i2 t2 row2 hH hev hem ht2 _ hT)

/-- 窓の round はちょうど `r - eta ≤ k < r` の round: `latestWindow eta r` は `r - eta` から `min r eta` 個の round を並べた
もの(`lt_of_mem_latestWindow` の両向き。手書き `NamedOutageClosure.window_bounds` / `mem_latest_window`。周回 260)。 -/
theorem mem_latestWindow_iff {eta r k : Nat} :
    k ∈ Model.Consensus.Protocol.ForkChoice.Goldfish.latestWindow eta r ↔ r - eta ≤ k ∧ k < r := by
  unfold Model.Consensus.Protocol.ForkChoice.Goldfish.latestWindow
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
    have := List.mem_range.mp hj
    omega
  · rintro ⟨h1, h2⟩
    refine List.mem_map.mpr ⟨k - (r - eta), List.mem_range.mpr ?_, ?_⟩ <;> omega

/-- round `j` の action 時刻は `4ΔR · j + 6Δ`(周回 260)。 -/
theorem setupActionTime_eq (j : Nat) :
    Model.Consensus.Execution.Setup.setupActionTime s j = s.e.delta * 4 * (s.hc.r : Int) * (j : Int) + 6 * s.e.delta := by
  unfold Model.Consensus.Execution.Setup.setupActionTime Model.Consensus.Protocol.Grades.actionTime
    Model.Consensus.Objects.Time.slotStart Model.Consensus.Protocol.Grades.openingSlot
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

/-- **参加の窓の時刻の action round は round の窓にある**(Δ > 0、`R ≥ 1`、`r > 0`): 時刻 `u` が round `r` の action 時刻で
終わる参加の窓 `[setupActionTime r - participationWindow, setupActionTime r)` にあれば、`u` の action round(`envAwake` が見る
round)は `latestWindow η_SG r` にある。`u` が round 0 の action 時刻より前なら action round は 0 で、そのとき `r < η_SG` なので
窓は `0` から始まる。そうでなければ action round は `(u - 6Δ) / 4ΔR` の床で、窓の端の不等式を 4ΔR で割る。手書き
`awakeIn_action_window` の `→` の向き(`DecoupledConsensusProofs/Bridge/GenericParticipation.lean`。周回 260)。 -/
theorem actionRound_mem_latestWindow (hδ : 0 < s.e.delta) (hR : 1 ≤ s.hc.r) {r : Nat} (hr : 0 < r) {u : Int}
    (hlo : Model.Consensus.Execution.Setup.setupActionTime s r - Model.Consensus.Spec.Constants.participationWindow s ≤ u)
    (hhi : u < Model.Consensus.Execution.Setup.setupActionTime s r) :
    Model.Consensus.Spec.Interface.actionRound s u ∈
      Model.Consensus.Protocol.ForkChoice.Goldfish.latestWindow s.hc.etaSG r := by
  rw [mem_latestWindow_iff]
  obtain ⟨L, hLdef⟩ : ∃ L : Int, L = s.e.delta * 4 * (s.hc.r : Int) := ⟨_, rfl⟩
  have hR' : (1 : Int) ≤ (s.hc.r : Int) := by exact_mod_cast hR
  have hL : 0 < L := by rw [hLdef]; nlinarith
  have hact : ∀ j : Nat, Model.Consensus.Execution.Setup.setupActionTime s j = L * (j : Int) + 6 * s.e.delta := by
    intro j
    rw [setupActionTime_eq, hLdef]
  have hperiod : Model.Consensus.Execution.Setup.setupActionTime s 1 -
      Model.Consensus.Execution.Setup.setupActionTime s 0 = L := by
    rw [hact, hact]
    push_cast
    ring
  unfold Model.Consensus.Spec.Constants.participationWindow Model.Consensus.Spec.Constants.period at hlo
  rw [hperiod, hact] at hlo
  rw [hact] at hhi
  simp only [Int.ofNat_eq_natCast] at hlo
  unfold Model.Consensus.Spec.Interface.actionRound
  rw [hperiod]
  split_ifs with h0
  · simp only [hact, decide_eq_true_eq, Nat.cast_zero, mul_zero, zero_add] at h0
    refine ⟨?_, hr⟩
    have hlt : (r : Int) < (s.hc.etaSG : Int) := by
      by_contra hc
      push_neg at hc
      nlinarith
    have : r < s.hc.etaSG := by exact_mod_cast hlt
    omega
  · simp only [hact, ne_eq, decide_eq_true_eq, not_lt, Nat.cast_zero, mul_zero, zero_add] at h0
    rw [Int.fdiv_eq_ediv_of_nonneg _ hL.le]
    have hlow : (u - 6 * s.e.delta) / L * L ≤ u - 6 * s.e.delta := Int.ediv_mul_le _ hL.ne'
    have hup : u - 6 * s.e.delta < ((u - 6 * s.e.delta) / L + 1) * L := Int.lt_ediv_add_one_mul_self _ hL
    have hq0 : 0 ≤ (u - 6 * s.e.delta) / L := Int.ediv_nonneg (by linarith) hL.le
    generalize (u - 6 * s.e.delta) / L = q at hlow hup hq0
    have hqr : q < (r : Int) := by
      by_contra hc
      push_neg at hc
      nlinarith
    have hqe : (r : Int) - (s.hc.etaSG : Int) ≤ q := by
      by_contra hc
      push_neg at hc
      nlinarith
    constructor <;> omega

/-- **窓の round に awake な honest は round の action 時刻に行を出す**(`ScheduleWellFormed`、Δ > 0、`R ≥ 3`): honest な `u` が
round `k` に awake(`a u k`)で、round `k` の action 時刻が horizon 以内なら、その時刻の `u` の tick(添字 `i`)があり、`u` はそこで
round `k` の行 `row` を出す。tick は `ScheduleWellFormed` の honest な tick の網羅(action 時刻は Δ の倍数)から、行は
`tick_attest_of_awake`(action 時刻の slot `k · R + 1` の round は `k`: `AttestationSource.slotOf_actionTime` / `Constants.roundOf_slot`)
から、行の round は action 時刻の単調性(`RootWitness.actionTime_lt_actionTime_iff`)から。手書き
`honest_emits_exact_actionAttestationAt_of_awake`(`Protocol/Schedule/Action.lean`)に当たる(周回 261)。 -/
theorem awake_emits_actionRow (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) (hR : 3 ≤ s.hc.r)
    {u : ValidatorId} (hu : u ∈ rho.honest.elems) {k : Nat} (huk : a u k = true)
    (hhor : Model.Consensus.Execution.Setup.setupActionTime s k ≤ rho.horizon) :
    ∃ (i : Nat) (row : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      rho.events[i]? = some (NamedEvent.Tick u (Model.Consensus.Execution.Setup.setupActionTime s k)) ∧
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho u (Model.Consensus.Execution.Objects.NamedObject.Attest row) (Model.Consensus.Execution.Setup.setupActionTime s k) ∧
      row.round = k := by
  have hslot : Model.Consensus.Objects.Parameters.slotOf s.e (Model.Consensus.Execution.Setup.setupActionTime s k) = k * s.hc.r + 1 :=
    Proofs.Consensus.AttestationSource.slotOf_actionTime hδ s.hc k
  have hround : Model.Consensus.Protocol.Grades.roundOf s.hc
      (Model.Consensus.Objects.Parameters.slotOf s.e (Model.Consensus.Execution.Setup.setupActionTime s k)) = k := by
    rw [hslot]
    exact Proofs.Consensus.Constants.roundOf_slot s hR k
  have h0 : 0 ≤ Model.Consensus.Execution.Setup.setupActionTime s k := by
    rw [setupActionTime_eq]
    have : (0 : Int) ≤ s.e.delta * 4 * (s.hc.r : Int) * (k : Int) := by positivity
    linarith
  have hpub : PublicTime s.e (Model.Consensus.Execution.Setup.setupActionTime s k) := by
    refine ⟨4 * s.hc.r * k + 6, ?_⟩
    rw [setupActionTime_eq]
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  have hmem : (rho.events.contains
      (NamedEvent.Tick u (Model.Consensus.Execution.Setup.setupActionTime s k))) = true :=
    hsch.2 u _ ⟨⟨⟨(Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu, hpub⟩, h0⟩, hhor⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.contains_iff_mem.mp hmem)
  obtain ⟨row, hrow⟩ := tick_attest_of_awake (e := s.e) (cfg := s.cfg) c p a nr
    (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
      (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho i) u).st.core)
      (Model.Consensus.Execution.Setup.setupActionTime s k) (worldAt (stateBefore c p a nr s rho i) u).cache)
    s.hc (Model.Consensus.Execution.Setup.setupNode u) (worldAt (stateBefore c p a nr s rho i) u).st
    (worldAt (stateBefore c p a nr s rho i) u).signing _ (by rw [hround]; rfl) (by rw [hround]; exact huk)
  have hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u (Model.Consensus.Execution.Objects.NamedObject.Attest row) (Model.Consensus.Execution.Setup.setupActionTime s k) := by
    refine (Proofs.Consensus.Signing.emits_iff c p a nr s rho u _ _).mpr ⟨i, hi, ?_⟩
    rw [Proofs.Consensus.Signing.nodeTick_out]
    exact hrow
  refine ⟨i, row, hi, hem, ?_⟩
  have ht := Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem
  have hr0 : 0 < s.hc.r := by omega
  rcases lt_trichotomy row.round k with h | h | h
  · exact absurd ht (ne_of_gt ((Proofs.Consensus.RootWitness.actionTime_lt_actionTime_iff hδ hr0 _ _).mpr h))
  · exact h
  · exact absurd ht (ne_of_lt ((Proofs.Consensus.RootWitness.actionTime_lt_actionTime_iff hδ hr0 _ _).mpr h))

/-- **honest な行の扱いの後の行**(行の側): GST-zero の枝で、honest な `u` が添字 `i` の tick(時刻 `t`)で行 `row` を出し、
honest な `w` が時刻 `t2`(`t ≤ t2 < t + Δ ≤ horizon`)に添字 `j` でその行を扱う(`HandlesAt`)なら、`j` の event の後の `w` の store の
鍵 `row.round` の SG 票の行に、送り手が `u` で `confirmed` が `row.confirmed` の attestation がある。手書き
`NamedSGArrival.honest_row_after_call`(`Protocol/Handlers/SGArrival.lean` 758 行)に当たる(周回 262 に `honestActionRow_delivered` から
穴として切り出し、周回 263 に `SgAdmit.handlesAt_honestRow_mem` で閉じた): `HandlesAt` の 3 つの経路(自分の tick の `attestWith`・
配送の `admitRow`・受理したブロックが運ぶ行の `admitRows`。自分の提案は提案の時刻にだけ起き、`t2` は提案の時刻ではない)で、
受理の窓は扱いの時点の slot `k · R + 1`(`k = row.round`)の round、守りの大きさ 2 は honest な送り手の行の `confirmed` が
1 通りであること(`SgAdmit.honest_rows_confirmed_eq`)で外す。 -/
theorem honestActionRow_handled_row (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : u ∈ rho.honest.elems) {i : Nat} {t : Int}
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} (hev : rho.events[i]? = some (NamedEvent.Tick u t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u (Model.Consensus.Execution.Objects.NamedObject.Attest row) t) {w : ValidatorId} (hw : w ∈ rho.honest.elems)
    {j : Nat} {t2 : Int} (ht : t ≤ t2) (ht2 : t2 < t + s.e.delta) (hhor : t + s.e.delta ≤ rho.horizon)
    (hh : Statements.Consensus.Spec.Execution.HandlesAt c p a nr s rho j w
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2) :
    ∃ x ∈ Proofs.Consensus.SgStamps.rows (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core row.round,
      x.valIndex = u ∧ x.confirmed = row.confirmed :=
  Proofs.Consensus.SgAdmit.handlesAt_honestRow_mem c p a nr s rho hwf hsleep hu hem hw ht ht2 hh

/-- **務めの SG block は務めの store の tree の要素**(前提なし): `currentSGVote` の 4 つの枝 — `deepestClear` の結果は
`liveConfirmed`(`TreeInv.live`)の祖先で tree は親について閉じている(`Trees.tree_closed`)、grade 2 の候補は filtered tree の
`activePrefix`(`AttestationSource.grade2BlockWith_mem`)、FG root は `j` か `f`(`Trees.getFgRoot_cases`)、anchor は filtered tree の
`activePrefix` か FG root — がどれも務めの store の tree にある。不変条件は `stateBefore` の `StoreInv` / `TreeInv` を
`tickDutyStore` が受け継ぐ(周回 259)。 -/
theorem sgBlockAt_mem_dutyTree (w : ValidatorId) (i : Nat) (t : Int) :
    Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho w i t ∈
      (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core.tree.elems := by
  have hi : Proofs.Consensus.Carrier.StoreInv s.e s.cfg (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t) :=
    Proofs.Consensus.AttestationSource.tickDutyStore_inv c p nr _ s.hc _ t
      (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i w)
  have ht : Proofs.Consensus.Trees.TreeInv (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core :=
    Proofs.Consensus.AttestationSource.tickDutyStore_treeInv c p nr _ s.hc _ t
      (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i w)
      (Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho i w)
  have hfg : Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
      (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core) ∈
      (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core.tree.elems := by
    rcases Proofs.Consensus.Trees.getFgRoot_cases (Model.Consensus.Protocol.Store.storeToHealing
        (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core) with h | h
    · rw [h]; exact ht.j
    · rw [h]; exact ht.f
  unfold Proofs.Consensus.RootWitness.sgBlockAt
  unfold Model.Consensus.Protocol.Duties.Inputs.getSgVoteWith Model.Consensus.Protocol.Grades.currentSGVote
  split
  · rename_i b hb
    exact Proofs.Consensus.Trees.ancestor_mem_tree (Proofs.Consensus.Trees.tree_closed hi)
      (Proofs.Consensus.AttestationSource.deepestClear_preceq hb) ht.live
  · dsimp only
    split
    · rename_i q hq
      exact Proofs.Consensus.AttestationSource.grade2BlockWith_mem hq
    · split_ifs
      · exact hfg
      · unfold Model.Consensus.Protocol.Grades.frameGradeRead Model.Consensus.Protocol.Grades.anchor
        dsimp only
        split
        · rename_i g _
          cases hb : Model.Consensus.Protocol.Grades.activePrefix
              (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree (Model.Consensus.Protocol.Store.storeToHealing
                (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core)) g with
          | none => simpa only [Option.getD_none] using hfg
          | some b =>
            rw [Option.getD_some]
            exact Proofs.Consensus.Trees.getFilteredBlockTree_sub (Proofs.Consensus.Trees.activePrefix_mem hb)
        · exact hfg

/-- **行を出した tick の後の bodies は務めの store の bodies**(重複なし): `u` が時刻 `t` に行を出し、添字 `i` の event が
`Tick u t` なら、`stateBefore (i + 1)` の `u` の bodies は務めの store `dutyStoreAt u i t` の bodies(tick の後の store は務めの
store での `attestWith` の後の store で、`attestWith` は bodies を変えない。`AttestationSource.emits_vote_source` の bodies の段を
height pair を問わずに取り出した形。添字は `EventsNodup` で揃える。周回 259)。 -/
theorem stateBefore_succ_bodies_of_emits (hnd : EventsNodup rho) {u : ValidatorId} {i : Nat} {t : Int}
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation}
    (hev : rho.events[i]? = some (NamedEvent.Tick u t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t) :
    (worldAt (stateBefore c p a nr s rho (i + 1)) u).st.bodies =
      (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho u i t).bodies := by
  obtain ⟨i', hev', hrow⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho u _ t).mp hem
  have hil : i' < rho.events.length := (List.getElem?_eq_some_iff.mp hev').1
  have hii : i' = i := (List.Nodup.getElem?_inj hil
    (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd)).mp (hev'.trans hev.symm)
  subst hii
  rw [Proofs.Consensus.Signing.nodeTick_out] at hrow
  obtain ⟨st3, -, -, hst, -, -, hd⟩ :=
    Proofs.Consensus.AttestationSource.tick_attest_store c p a nr _ s.hc _ _ _ t hrow
  rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev]
  unfold Model.Consensus.Execution.Run.worldStep
  dsimp only
  rw [Proofs.Consensus.Signing.worldAt_insert_self]
  unfold Model.Consensus.Execution.Node.nodeTick Model.Consensus.Execution.Node.profileTick
  dsimp only
  rw [hst, Proofs.Consensus.Attribution.attestWith_bodies, hd]
  rfl

/-- honest な `u` が添字 `i2` の tick(時刻 `t2`)で行を出したなら、その務めの SG block の root は、どの honest なノード `w` の
どの時刻の読みの tree でも、解決すればその SG block 自身に解決する(GST-zero を使わない)。手書き
`relativeGradeCarrierAt_of_awakeWindowMajority`(`Protocol/Grades/RelativeOneChain.lean` 221 行)の `hhead` の段に当たる(手書きは
前提 `htransport` の `Block.find?` の連言で受け取り、`WeakBootstrapAction.lean` が供給する。周回 258 に
`relativeGradeCarrierAt_of_commonUpper` から穴として切り出し、周回 259 に証明した)。解決した `head` は `w` の読みの tree の要素なので
bodies の名前付きブロックの消去(`Carrier.StoreInv.named`)で、run の中のブロック。SG block は務めの store の tree の要素
(`sgBlockAt_mem_dutyTree`)なので務めの store の bodies の消去で、その bodies は tick の後の `u` の bodies
(`stateBefore_succ_bodies_of_emits`)なので run の中のブロック。root が等しいので、`FinalizedAccountable.rootInjective_of_collisionFree`
(`hsleep` の `Idealization`)で `head` と等しい(`tickTree_root_inj` と同じ運び)。 -/
theorem sgBlockAt_findRoot_eq (hwf : SetupWellFormed c p s) (hsleep : SleepyRegime c p a nr s rho 0)
    {u : ValidatorId} (hu : u ∈ rho.honest.elems) {i2 : Nat} {t2 : Int}
    {row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation}
    (hev : rho.events[i2]? = some (NamedEvent.Tick u t2))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
      (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2)
    {w : ValidatorId} (hw : w ∈ rho.honest.elems) (τ : Int) {head : Block}
    (h : Model.Consensus.Objects.Blocks.findRoot?
      (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.tree
      (root (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i2 t2)) = some head) :
    head = Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i2 t2 := by
  have _ := hwf
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho hexec).2
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hnd : EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  -- `head` は `w` の読みの bodies の消去
  obtain ⟨hm, hroot⟩ := Proofs.Consensus.BlockStamps.findRoot?_mem h
  obtain ⟨i0, hi0⟩ := Proofs.Consensus.FinalizedAccountable.readAt_eq_stateBefore c p a nr s rho hs (τ - 1)
  have hst : stateBeforeTime c p a nr s rho τ = stateBefore c p a nr s rho i0 := by
    rw [← hi0, readAt_eq_stateBeforeTime_succ, sub_add_cancel]
  rw [hst] at hm
  obtain ⟨X, hX, rfl⟩ := (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i0 w).named _ hm
  have hwc : rho.honest.contains w = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hw
  have huc : rho.honest.contains u = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu
  have hXr : Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho X :=
    ⟨X, Or.inr ⟨w, hwc, i0, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hX⟩,
      Proofs.Consensus.NamedBlocks.namedPreceq_self X⟩
  -- SG block は tick の後の `u` の bodies の消去
  have hsgi : Proofs.Consensus.Carrier.StoreInv s.e s.cfg (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho u i2 t2) :=
    Proofs.Consensus.AttestationSource.tickDutyStore_inv c p nr _ s.hc _ t2
      (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i2 u)
  obtain ⟨Y, hY, hYe⟩ := hsgi.named _ (sgBlockAt_mem_dutyTree c p a nr s rho u i2 t2)
  rw [← stateBefore_succ_bodies_of_emits c p a nr s rho hnd hev hem] at hY
  have hYr : Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho Y :=
    ⟨Y, Or.inr ⟨u, huc, i2 + 1,
      (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hY⟩,
      Proofs.Consensus.NamedBlocks.namedPreceq_self Y⟩
  rw [← hYe] at hroot ⊢
  exact Proofs.Consensus.FinalizedAccountable.rootInjective_of_collisionFree c p a nr s rho hcf hXr hYr
    _ _ ⟨⟨Or.inl (Proofs.Consensus.Blocks.preceq_self _), Or.inr (Proofs.Consensus.Blocks.preceq_self _)⟩, hroot⟩

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

/-- **bodies の名前付きブロックは genesis か、ある添字で新しく受理された**: `u` の添字 `i` の直前の bodies の `X` は genesis か、
`i` より前のある添字 `j` の event で `u` が `X` を扱い、その直前の bodies に無く直後の bodies にある(`AcceptsAt`)。
`JustificationCertificate.bodies_processed_before` の受理の版(bodies に新しく入るのは `u` 自身の tick の出力か `u` への配送:
`Attribution.nodeTick_bodies` / `nodeProcess_bodies`。周回 265)。 -/
theorem bodies_accepted_before (u : ValidatorId) :
    ∀ (i : Nat) (X : Model.Consensus.Objects.NamedBlocks.NamedBlock),
      X ∈ (worldAt (stateBefore c p a nr s rho i) u).st.bodies.elems →
      X = Model.Consensus.Objects.NamedBlocks.NamedBlock.Genesis ∨ ∃ (j : Nat) (ev : NamedEvent), j < i ∧
        rho.events[j]? = some ev ∧
        Statements.Consensus.Spec.Execution.AcceptsAt c p a nr s rho j u
          (Model.Consensus.Execution.Objects.NamedObject.Block X) (eventTime ev)
  | 0, X, hX => by
    left
    have hX' : X ∈ (NaruStd.Set.singleton Model.Consensus.Objects.NamedBlocks.NamedBlock.Genesis).elems := hX
    exact (Proofs.Consensus.Sets.mem_singleton_iff _ _).mp hX'
  | i + 1, X, hX => by
    by_cases hXi : X ∈ (worldAt (stateBefore c p a nr s rho i) u).st.bodies.elems
    · rcases bodies_accepted_before u i X hXi with h | ⟨j, ev, hj, hev, hacc⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, ev, Nat.lt_succ_of_lt hj, hev, hacc⟩
    · right
      have hnp : ¬ Model.Consensus.Execution.Node.processed (worldAt (stateBefore c p a nr s rho i) u).st
          (Model.Consensus.Execution.Objects.NamedObject.Block X) = true := fun h =>
        hXi ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mp h)
      have hp : Model.Consensus.Execution.Node.processed (worldAt (stateBefore c p a nr s rho (i + 1)) u).st
          (Model.Consensus.Execution.Objects.NamedObject.Block X) = true :=
        (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hX
      cases hev : rho.events[i]? with
      | none =>
        rw [Proofs.Consensus.Signing.stateBefore_succ_of_none c p a nr s rho hev] at hX
        exact absurd hX hXi
      | some ev =>
        refine ⟨i, ev, Nat.lt_succ_self i, hev, ⟨⟨⟨ev, ⟨⟨hev, ?_⟩, rfl⟩, ?_⟩, hnp⟩, hp⟩⟩
        · rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev] at hX
          cases ev with
          | Tick w t =>
            by_contra hwu
            unfold worldStep at hX
            dsimp only at hX
            rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ (by simpa [eventNode] using hwu)] at hX
            exact hXi hX
          | Deliver w o t =>
            by_contra hwu
            unfold worldStep at hX
            dsimp only at hX
            rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ (by simpa [eventNode] using hwu)] at hX
            exact hXi hX
        · rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev] at hX
          cases ev with
          | Tick w t =>
            unfold worldStep at hX
            dsimp only at hX
            by_cases hwu : w = u
            · subst hwu
              rw [Proofs.Consensus.Signing.worldAt_insert_self] at hX
              rcases Proofs.Consensus.Attribution.nodeTick_bodies c p a nr s w _ t hX with h | h
              · exact absurd h hXi
              · refine Or.inl ⟨t, rfl, ?_⟩
                unfold Model.Consensus.Spec.Execution.tickEmits
                exact List.contains_iff_mem.mpr h
            · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwu] at hX
              exact absurd hX hXi
          | Deliver w o t =>
            unfold worldStep at hX
            dsimp only at hX
            by_cases hwu : w = u
            · subst hwu
              rw [Proofs.Consensus.Signing.worldAt_insert_self] at hX
              rcases Proofs.Consensus.Attribution.nodeProcess_bodies c p s hX with h | rfl
              · exact absurd h hXi
              · exact Or.inr ⟨t, rfl⟩
            · rw [Proofs.Consensus.Signing.worldAt_insert_ne _ _ _ _ hwu] at hX
              exact absurd hX hXi

/-- 時刻 `< d` の読みの添字は `d` について単調。 -/
theorem idxLt_mono {d τ : Int} (h : d ≤ τ) :
    Proofs.Consensus.ReceiverFinality.idxLt rho d ≤ Proofs.Consensus.ReceiverFinality.idxLt rho τ := by
  unfold Proofs.Consensus.ReceiverFinality.idxLt
  exact (List.monotone_filter_right _ (fun ev hev => by
    simp only [decide_eq_true_eq] at hev ⊢
    linarith)).length_le

/-- **受理されたブロックは静的な守りを満たす**: honest でなくてもよい `u` が添字 `j0`(時刻 `t0`)でブロック `X` を受理したなら
(`AcceptsAt`)、`X` の運ぶ attestation は受け入れ可能、提案者は slot の提案者、親の slot は `X` の slot より小さく、`X` の slot の
提案の時刻は `t0` 以下。tick の受理は `u` 自身の発行(`Proposal.emits_block_fields`・`ParentSlot.emits_block_parent_slot`)、配送の受理は
受信の処理の守り(`processBlockCore_guards`)と、配送の直前の slot が時計の slot で時計が `t0` 以下であること(`Clocks.clock_slot`・
`Clocks.clock_le_event`)から。手書き `accepted_block_static_guards` に当たる(周回 266)。 -/
theorem acceptedBlock_static (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {u : ValidatorId} {j0 : Nat}
    {X : Model.Consensus.Objects.NamedBlocks.NamedBlock} {t0 : Int}
    (hacc : Statements.Consensus.Spec.Execution.AcceptsAt c p a nr s rho j0 u
      (Model.Consensus.Execution.Objects.NamedObject.Block X) t0) :
    Model.Consensus.Protocol.Handlers.carriedAttestationsAdmissible s.hc
        (Model.Consensus.Objects.NamedBlocks.eraseBlock X) = true ∧
      proposer? (Model.Consensus.Objects.NamedBlocks.eraseBlock X) =
        some (p (slot (Model.Consensus.Objects.NamedBlocks.eraseBlock X))) ∧
      slot (parent (Model.Consensus.Objects.NamedBlocks.eraseBlock X)) <
        slot (Model.Consensus.Objects.NamedBlocks.eraseBlock X) ∧
      Model.Consensus.Protocol.Schedule.proposalTime s.e (slot (Model.Consensus.Objects.NamedBlocks.eraseBlock X)) ≤ t0 := by
  obtain ⟨⟨hh, hnp⟩, hp⟩ := hacc
  rcases Proofs.Consensus.BlockSynchrony.handlesAt_block_cases c p a nr s rho hh with ⟨hev, hco⟩ | hev
  · have hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
        (Model.Consensus.Execution.Objects.NamedObject.Block X) t0 := ⟨j0, hev, hco⟩
    obtain ⟨-, ht, hpr, hca⟩ := Proofs.Consensus.Proposal.emits_block_fields c p a nr s rho hem
    exact ⟨hca, hpr, Proofs.Consensus.ParentSlot.emits_block_parent_slot c p a nr s rho hsch hδ hem, ht ▸ le_refl _⟩
  · have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
    have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev h =>
      (Proofs.Consensus.Window.eventTime_bounds hsch h).1
    have hXn : X ∉ (worldAt (stateBefore c p a nr s rho j0) u).st.bodies.elems := fun h =>
      hnp ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr h)
    have hX : X ∈ (worldAt (stateBefore c p a nr s rho (j0 + 1)) u).st.bodies.elems :=
      (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mp hp
    rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev] at hX
    unfold worldStep at hX
    dsimp only at hX
    rw [Proofs.Consensus.Signing.worldAt_insert_self] at hX
    change X ∈ (Model.Consensus.Protocol.Handlers.onBlockWith c p Model.Consensus.Protocol.Handlers.CarriedAdmission.AlsoCarried s.e s.hc s.cfg
      (worldAt (stateBefore c p a nr s rho j0) u).st X).bodies.elems at hX
    unfold Model.Consensus.Protocol.Handlers.onBlockWith at hX
    rw [Proofs.Consensus.Attribution.admitCarried_bodies] at hX
    obtain ⟨-, hca, hsl, hpr, hps⟩ := processBlockCore_guards c p s.e s.hc s.cfg hXn hX
    refine ⟨hca, hpr, hps, ?_⟩
    obtain ⟨hc0, hcle⟩ := Proofs.Consensus.Clocks.clock_le_event c p a nr s rho hs hnn j0 u
    have hct := hcle j0 _ (le_refl _) hev
    rw [Proofs.Consensus.Clocks.clock_slot c p a nr s rho j0 u] at hsl
    calc Model.Consensus.Protocol.Schedule.proposalTime s.e (slot (Model.Consensus.Objects.NamedBlocks.eraseBlock X))
        ≤ Model.Consensus.Protocol.Schedule.proposalTime s.e (Model.Consensus.Objects.Parameters.slotOf s.e (worldAt (stateBefore c p a nr s rho j0) u).st.core.t) :=
          Proofs.Consensus.Clocks.proposalTime_mono s.e hδ hsl
      _ ≤ (worldAt (stateBefore c p a nr s rho j0) u).st.core.t :=
          Proofs.Consensus.Clocks.proposalTime_slotOf_le s.e hδ hc0
      _ ≤ t0 := hct

/-- **扱ったブロックの保持**: honest な `u` が添字 `j0`(時刻 `t0`)でブロック `X` を受理し(`AcceptsAt`)、honest な `w ≠ u` が
時刻 `t2 ≥ t0` に添字 `j` で `X` を扱い、`t2` より後の時刻 `τ`(horizon 以内)の読みの `w` の finalized が `X` の消去と互換なら、
扱いの後の `w` の tree に `X` の消去がある。手書き `NamedRelayGuards.handled_block_held_of_finalized_prefix`
(`Protocol/Handlers/RelayGuards.lean` 386 行)に当たる(周回 265 に `honestActionRow_sgBlock_held` から穴として切り出し、周回 266 に
証明した)。扱いが `w` の tick の出力なら発行の tick の後の tree にある(`ProposerReceipt.nodeTick_block_mem`)。配送なら、直前の tree に
既にあれば残り(`BlockStamps.stateBefore_keep`)、無ければ受理の守り `BlockReceipt.Admits` を外して入る(`BlockReceipt.deliver_block_mem`):
親は `DeliveryWellFormed`(`DeliveredBlock.deliver_deps` / `deliver_parent_tree`)、提案者・親の slot・運ばれた attestation の守りと
slot の提案の時刻 `≤ t0` は `u` の受理(`acceptedBlock_static`)、slot は `t0 ≤ t2` から(`BlockSynchrony.slot_ge_of_deliver_le`)。
`extends_f` は `hcompat` を finalized の単調性で扱いの直前へ移した互換で、`X ⪯ f` の向きなら `X` は finalized の祖先で直前の tree に
ある(`Trees.ancestor_mem_tree`・`TreeInv.f`)ので除かれる(手書き `no_geometry_alias`)。 -/
theorem acceptedBlock_handled_held (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : u ∈ rho.honest.elems) {j0 : Nat}
    {X : Model.Consensus.Objects.NamedBlocks.NamedBlock} {t0 : Int}
    (hacc : Statements.Consensus.Spec.Execution.AcceptsAt c p a nr s rho j0 u
      (Model.Consensus.Execution.Objects.NamedObject.Block X) t0)
    {w : ValidatorId} (hw : w ∈ rho.honest.elems) (hwu : w ≠ u) {j : Nat} {t2 : Int} (ht : t0 ≤ t2)
    (hh : Statements.Consensus.Spec.Execution.HandlesAt c p a nr s rho j w
      (Model.Consensus.Execution.Objects.NamedObject.Block X) t2)
    {τ : Int} (hτ : t2 < τ) (hhor : τ ≤ rho.horizon)
    (hcompat : Model.Consensus.Objects.Blocks.compatible (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.f
      (Model.Consensus.Objects.NamedBlocks.eraseBlock X) = true) :
    Model.Consensus.Objects.NamedBlocks.eraseBlock X ∈
      (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hdw : DeliveryWellFormed c p a nr s rho := hexec.1.1.2
  have hnd : EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  obtain ⟨hs, -⟩ := Proofs.Consensus.Available.schedule_sorted_nodup s rho hsch
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hw' : rho.honest.contains w = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hw
  rcases Proofs.Consensus.BlockSynchrony.handlesAt_block_cases c p a nr s rho hh with ⟨hev, hco⟩ | hev
  · -- `w` の tick が `X` を出した
    have hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho w
        (Model.Consensus.Execution.Objects.NamedObject.Block X) t2 := ⟨j, hev, hco⟩
    have hpsl := Proofs.Consensus.ParentSlot.emits_block_parent_slot c p a nr s rho hsch hδ hem
    rw [Proofs.Consensus.Signing.emittedAt_eq] at hco
    rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hev]
    unfold worldStep
    dsimp only
    rw [Proofs.Consensus.Signing.worldAt_insert_self]
    exact Proofs.Consensus.ProposerReceipt.nodeTick_block_mem c p a nr s w
      (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho j w)
      (Proofs.Consensus.ProposerFinality.stateBefore_fj c p a nr s rho j w) t2 (List.contains_iff_mem.mp hco) hpsl
  · -- `w` への配送
    by_cases hin : Model.Consensus.Objects.NamedBlocks.eraseBlock X ∈
        (worldAt (stateBefore c p a nr s rho j) w).st.core.tree.elems
    · exact (Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho (Nat.le_succ j) w _ hin).1
    · obtain ⟨hca, hpr, hpsl, hpt⟩ := acceptedBlock_static c p a nr s rho hsch hδ hacc
      -- 互換を扱いの直前の finalized へ移す
      have hlt : j < Proofs.Consensus.ReceiverFinality.idxLt rho τ :=
        Proofs.Consensus.ReceiverFinality.lt_idxLt_of_time_lt rho hs
          (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) hev
          (show eventTime (NamedEvent.Deliver w (Model.Consensus.Execution.Objects.NamedObject.Block X) t2) < τ from hτ)
      have hmono := Proofs.Consensus.ReceiverFinality.stateBefore_f_mono c p a nr s rho hlt.le w
      rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs] at hcompat
      rw [Proofs.Consensus.Blocks.compatible_comm] at hcompat
      have hcj := Proofs.Consensus.FrameCapture.compatible_of_preceq_right hmono hcompat
      unfold Model.Consensus.Objects.Blocks.compatible at hcj
      rcases Bool.or_eq_true_iff.mp hcj with hXf | hfX
      · -- `X ⪯ f`: `X` は直前の tree にある
        have hst := Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho j w
        exact absurd (Proofs.Consensus.Trees.ancestor_mem_tree (Proofs.Consensus.Trees.tree_closed hst) hXf
          (Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho j w).f) hin
      · exact Proofs.Consensus.BlockReceipt.deliver_block_mem c p a nr s rho hev
          (Proofs.Consensus.DeliveredBlock.deliver_deps c p a nr s rho hdw hev).1 hca
          { slot_le := Proofs.Consensus.BlockSynchrony.slot_ge_of_deliver_le c p a nr s rho hsch hδ hw' hev
              (le_trans hpt ht)
            parent_mem := Proofs.Consensus.DeliveredBlock.deliver_parent_tree c p a nr s rho hdw hev
            extends_f := hfX
            proposer := hpr
            parent_slot := hpsl }

/-- **SG block の保持、`u` でない読み手**: `honestActionRow_delivered` と同じ前提で `w ≠ u` なら、行の SG block
(`RootWitness.sgBlockAt u i t`)は初期の `w` の tree にあるか、時刻が `t + Δ` より前のある event の後の `w` の tree にある。手書き
`NamedOutageClosure.compatible_carrier_body_at_read_after_gst`(`Protocol/Grades/RoundVoterTransportTwoCutoff.lean` 210 行)の
受信の段に当たる(周回 262 に `honestActionRow_delivered` から切り出し、周回 264 にこの形に狭め、周回 265 に証明した)。
SG block は tick の後の `u` の bodies の名前付きブロック `Y` の消去(`sgBlockAt_mem_dutyTree`・`stateBefore_succ_bodies_of_emits`・
`Carrier.StoreInv.named`)なので、genesis(初期の bodies にあり、その消去は初期の tree にある)か、`u` がある添字 `j0`(時刻 `t0 ≤ t`)で
受理したブロック(`bodies_accepted_before`)。後者は `PartialSynchrony` の中継の連言(`tGST ≤ 0 ≤ t0` なので締切は `t0 + Δ ≤ t + Δ`)で、
`w` が受理の直後に既に bodies に持つ(その消去は tree にある)か、除外(締切の読みの finalized が `Y` と互換でない)が掛からず
締切より前に `w` が扱う。互換は `hcompat` と finalized の単調性(`ReceiverFinality.stateBefore_f_mono`・`idxLt_mono`・
`FrameCapture.compatible_of_preceq_right`)で締切の読みへ移す。扱いの後の tree は `acceptedBlock_handled_held`(周回 266 に証明した)。 -/
theorem honestActionRow_sgBlock_held (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : u ∈ rho.honest.elems) {i : Nat} {t : Int}
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} (hev : rho.events[i]? = some (NamedEvent.Tick u t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u (Model.Consensus.Execution.Objects.NamedObject.Attest row) t) {w : ValidatorId} (hw : w ∈ rho.honest.elems)
    (hwu : w ≠ u) {τ : Int} (hτ : t + s.e.delta ≤ τ) (hhor : τ ≤ rho.horizon)
    (hcompat : Model.Consensus.Objects.Blocks.compatible (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.f
      (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t) = true) :
    Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t ∈
        (worldAt (stateBefore c p a nr s rho 0) w).st.core.tree.elems ∨
      ∃ (j : Nat) (ev : NamedEvent), rho.events[j]? = some ev ∧ eventTime ev < t + s.e.delta ∧
        Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t ∈
          (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems := by
  have hps : Statements.Consensus.Spec.Conditions.PartialSynchrony c p a nr s rho := hsleep.1.1.1.1.2
  have hgst : s.e.tGST ≤ 0 := hsleep.1.1.1.2
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hnd : EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  obtain ⟨hs, -⟩ := Proofs.Consensus.Available.schedule_sorted_nodup s rho hsch
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev h =>
    (Proofs.Consensus.Window.eventTime_bounds hsch h).1
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hu' : rho.honest.contains u = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu
  have hw' : rho.honest.contains w = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hw
  -- SG block は tick の後の `u` の bodies の名前付きブロック `Y` の消去
  have hsgi : Proofs.Consensus.Carrier.StoreInv s.e s.cfg (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho u i t) :=
    Proofs.Consensus.AttestationSource.tickDutyStore_inv c p nr _ s.hc _ t
      (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i u)
  obtain ⟨Y, hY, hYe⟩ := hsgi.named _ (sgBlockAt_mem_dutyTree c p a nr s rho u i t)
  rw [← stateBefore_succ_bodies_of_emits c p a nr s rho hnd hev hem] at hY
  rw [← hYe] at hcompat ⊢
  rcases bodies_accepted_before c p a nr s rho u (i + 1) Y hY with hg | ⟨j0, ev0, hj0, hev0, hacc⟩
  · -- genesis は初期の bodies にあり、その消去は初期の tree にある
    left
    subst hg
    have hb : Model.Consensus.Objects.NamedBlocks.NamedBlock.Genesis ∈
        (worldAt (stateBefore c p a nr s rho 0) w).st.bodies.elems := by
      show Model.Consensus.Objects.NamedBlocks.NamedBlock.Genesis ∈
        (NaruStd.Set.singleton Model.Consensus.Objects.NamedBlocks.NamedBlock.Genesis).elems
      exact (Proofs.Consensus.Sets.mem_singleton_iff _ _).mpr rfl
    exact (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho 0 w).tree _ hb
  · right
    -- 受理の時刻 `t0` は行の時刻 `t` 以下
    have ht0 : eventTime ev0 ≤ t := by
      by_contra hlt
      have := Proofs.Consensus.Window.lt_of_time_lt hs hev hev0
        (show eventTime (NamedEvent.Tick u t) < eventTime ev0 from not_le.mp hlt)
      omega
    have ht00 : 0 ≤ eventTime ev0 := hnn _ (List.mem_of_getElem? hev0)
    have hmax : max (eventTime ev0) s.e.tGST = eventTime ev0 := max_eq_left (le_trans hgst ht00)
    have hd : eventTime ev0 + s.e.delta ≤ rho.horizon := by linarith
    by_cases hpw : Model.Consensus.Execution.Node.processed (worldAt (stateBefore c p a nr s rho (j0 + 1)) w).st
        (Model.Consensus.Execution.Objects.NamedObject.Block Y) = true
    · -- `w` は受理の直後に既に bodies に持つ
      have hYw : Y ∈ (worldAt (stateBefore c p a nr s rho (j0 + 1)) w).st.bodies.elems :=
        (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mp hpw
      exact ⟨j0, ev0, hev0, by linarith, (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho (j0 + 1) w).tree Y hYw⟩
    · -- 締切の読みの finalized も `Y` と互換
      have hcd : Model.Consensus.Objects.Blocks.compatible
          (worldAt (stateBeforeTime c p a nr s rho (eventTime ev0 + s.e.delta)) w).st.core.f
          (Model.Consensus.Objects.NamedBlocks.eraseBlock Y) = true := by
        rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs] at hcompat ⊢
        have hmono := Proofs.Consensus.ReceiverFinality.stateBefore_f_mono c p a nr s rho
          (idxLt_mono rho (show eventTime ev0 + s.e.delta ≤ τ by linarith)) w
        rw [Proofs.Consensus.Blocks.compatible_comm] at hcompat ⊢
        exact Proofs.Consensus.FrameCapture.compatible_of_preceq_right hmono hcompat
      have h := hps.2 u j0 (Model.Consensus.Execution.Objects.NamedObject.Block Y) (eventTime ev0) ⟨hu', hacc⟩ w
      dsimp only at h
      rw [hmax] at h
      obtain ⟨t2, ⟨ht2, ht2d⟩, j, hh⟩ := h ⟨⟨⟨hw', hpw⟩, hd⟩, by
        simp [Model.Consensus.Execution.Node.excludes, hcd]⟩
      have hheld := acceptedBlock_handled_held c p a nr s rho hwf hdom hsleep hu hacc hw hwu ht2 hh
        (show t2 < τ by linarith) hhor hcompat
      obtain ⟨ev, ⟨⟨hevj, -⟩, hte⟩, -⟩ := hh
      exact ⟨j, ev, hevj, by rw [hte]; linarith, hheld⟩

/-- **行の SG block は `t + Δ` より前に読み手の tree に入る**: `honestActionRow_delivered` と同じ前提で、行の SG block は初期の `w` の
tree にあるか、時刻が `t + Δ` より前のある event の後の `w` の tree にある。`w = u` なら、SG block は tick の後の `u` の bodies の消去
(`sgBlockAt_mem_dutyTree`・`stateBefore_succ_bodies_of_emits`)なので、添字 `i` の tick(時刻 `t < t + Δ`)の後の tree にある
(`Carrier.StoreInv.tree`)。`w ≠ u` は `honestActionRow_sgBlock_held`(周回 265 に証明した。扱いの後の tree の `acceptedBlock_handled_held` は周回 266)。 -/
theorem honestActionRow_sgBlock_entered (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : u ∈ rho.honest.elems) {i : Nat} {t : Int}
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} (hev : rho.events[i]? = some (NamedEvent.Tick u t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u (Model.Consensus.Execution.Objects.NamedObject.Attest row) t) {w : ValidatorId} (hw : w ∈ rho.honest.elems)
    {τ : Int} (hτ : t + s.e.delta ≤ τ) (hhor : τ ≤ rho.horizon)
    (hcompat : Model.Consensus.Objects.Blocks.compatible (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.f
      (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t) = true) :
    Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t ∈
        (worldAt (stateBefore c p a nr s rho 0) w).st.core.tree.elems ∨
      ∃ (j : Nat) (ev : NamedEvent), rho.events[j]? = some ev ∧ eventTime ev < t + s.e.delta ∧
        Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t ∈
          (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems := by
  by_cases hwu : w = u
  · subst hwu
    have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
    unfold ExecutionValid at hexec
    have hsch : ScheduleWellFormed s rho := hexec.1.1.1
    have hnd : EventsNodup rho := by
      have h := hsch
      unfold ScheduleWellFormed at h
      obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
      exact hnd
    have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
    refine Or.inr ⟨i, NamedEvent.Tick w t, hev, by show t < t + s.e.delta; linarith, ?_⟩
    have hsgi : Proofs.Consensus.Carrier.StoreInv s.e s.cfg (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t) :=
      Proofs.Consensus.AttestationSource.tickDutyStore_inv c p nr _ s.hc _ t
        (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i w)
    obtain ⟨Y, hY, hYe⟩ := hsgi.named _ (sgBlockAt_mem_dutyTree c p a nr s rho w i t)
    rw [← stateBefore_succ_bodies_of_emits c p a nr s rho hnd hev hem] at hY
    rw [← hYe]
    exact (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho (i + 1) w).tree Y hY
  · exact honestActionRow_sgBlock_held c p a nr s rho hwf hdom hsleep hu hev hem hw hwu hτ hhor hcompat

/-- **SG block の側**: `honestActionRow_delivered` と同じ前提で、`w` の時刻 `τ` の読みの tree での行の SG block
(`RootWitness.sgBlockAt u i t`)の root の解決は、受信の印が `t + Δ` より前の head を返す。手書き
`NamedOutageClosure.compatible_carrier_body_at_read_after_gst`(`Protocol/Grades/RoundVoterTransportTwoCutoff.lean` 210 行)・
`held_body_stampedBefore_stateBeforeTime`・`carrier_held_find_at_strict` に当たる(周回 262 に `honestActionRow_delivered` から穴として
切り出し、周回 264 に受信の段を `honestActionRow_sgBlock_entered` に移して証明した)。SG block は初期の tree か `t + Δ` より前の
event の後の tree にあるので、`τ` の読み(添字 `idxLt τ`)の tree にあって印は `t + Δ` より前(初期の tree のブロックの印は初期の時計
`0` 以下: `BlockStamps.stateBefore_stampInv`。後者は `BlockStamps.tree_stamped`)。読みの tree は重複が無く root が要素を決める
(`TreeInv.nodup`・`tickTree_root_inj`)ので、root の解決は SG block 自身(`findRoot?_of_mem`)。 -/
theorem honestActionRow_sgBlock_delivered (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : u ∈ rho.honest.elems) {i : Nat} {t : Int}
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} (hev : rho.events[i]? = some (NamedEvent.Tick u t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u (Model.Consensus.Execution.Objects.NamedObject.Attest row) t) {w : ValidatorId} (hw : w ∈ rho.honest.elems)
    {τ : Int} (hτ : t + s.e.delta ≤ τ) (hhor : τ ≤ rho.horizon)
    (hcompat : Model.Consensus.Objects.Blocks.compatible (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.f
      (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t) = true) :
    ∃ head, Model.Consensus.Objects.Blocks.findRoot? (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.tree
        (Model.Consensus.Objects.Blocks.root (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t)) = some head ∧
      Model.Consensus.Objects.Time.occurrenceBefore
        ((worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.timestampBlock.get? head) (t + s.e.delta) = true := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  obtain ⟨hs, hnd⟩ := Proofs.Consensus.Available.schedule_sorted_nodup s rho hsch
  have hnd' := Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev h =>
    (Proofs.Consensus.Window.eventTime_bounds hsch h).1
  have hw' : rho.honest.contains w = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hw
  have ht0 : 0 ≤ t := hnn _ (List.mem_of_getElem? hev)
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  -- 読みの tree にあり、受信の印が `t + Δ` より前
  have hheld : Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t ∈
        (worldAt (stateBefore c p a nr s rho (Proofs.Consensus.ReceiverFinality.idxLt rho τ)) w).st.core.tree.elems ∧
      Model.Consensus.Objects.Time.occurrenceBefore
        ((worldAt (stateBefore c p a nr s rho (Proofs.Consensus.ReceiverFinality.idxLt rho τ)) w).st.core.timestampBlock.get?
          (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t)) (t + s.e.delta) = true := by
    rcases honestActionRow_sgBlock_entered c p a nr s rho hwf hdom hsleep hu hev hem hw hτ hhor hcompat with
      h0 | ⟨j, ev, hj, hte, hB⟩
    · obtain ⟨hm, heq⟩ := Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho (Nat.zero_le _) w _ h0
      refine ⟨hm, ?_⟩
      rw [heq]
      exact (Proofs.Consensus.BlockStamps.stateBefore_stampInv c p a nr s rho hs hnn 0 w _ h0).before
        (show (0 : Int) < t + s.e.delta by linarith)
    · exact Proofs.Consensus.BlockStamps.tree_stamped c p a nr s rho hs hnn hj hte hB
        (Proofs.Consensus.ReceiverFinality.lt_idxLt_of_time_lt rho hs hnd' hj (lt_of_lt_of_le hte hτ))
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
  refine ⟨_, findRoot?_of_mem (Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho _ w).nodup
    (fun x hx y hy hr => tickTree_root_inj c p a nr s rho hsleep hw' _ hx hy hr) hheld.1 rfl, hheld.2⟩

/-- **honest な行の SG 票と SG block は `t + Δ` より前の印で読み手の store に入る**: GST-zero の枝で、honest な `u` が添字 `i` の
tick(時刻 `t`)で行 `row` を出し、honest な読み手 `w` の時刻 `τ`(`t + Δ ≤ τ ≤ horizon`)の読み(`stateBeforeTime τ`)の finalized が
行の SG block(`RootWitness.sgBlockAt u i t`)と互換なら、その読みの store の鍵 `row.round` の SG 票の行に、送り手が `u` で `confirmed` が
`row.confirmed` の attestation があってその SG 票の受信の印は `t + Δ` より前で、tree での SG block の root の解決は受信の印が `t + Δ`
より前の head を返す。手書き `NamedOutageClosure.honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible`
(`Protocol/Grades/RoundVoterTransportTwoCutoff.lean` 343 行)の配送の段に当たる(周回 261 に `awakeWindowVote_interpreted_of_commonUpper`
から穴として切り出した)。周回 262 に行の側を証明した: `PartialSynchrony` の第 1 連言(`tGST ≤ 0 ≤ t` なので締切は `t + Δ`、attestation は
`excludes` が偽)で `w` は時刻 `t2 < t + Δ` に添字 `j` で行を扱い、扱いの後の行の attestation(`honestActionRow_handled_row`。周回 263 に閉じた)の印は
`j` の event の時刻 `t2` 以下で `τ` の読みまで残る(`SgStamps.sg_stamp_le_of_mem`)。SG block の側は `honestActionRow_sgBlock_delivered`
(周回 264〜266。扱ったブロックが扱いの後の tree にある `acceptedBlock_handled_held` は周回 266 に証明した)。 -/
theorem honestActionRow_delivered (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : u ∈ rho.honest.elems) {i : Nat} {t : Int}
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} (hev : rho.events[i]? = some (NamedEvent.Tick u t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u (Model.Consensus.Execution.Objects.NamedObject.Attest row) t) {w : ValidatorId} (hw : w ∈ rho.honest.elems)
    {τ : Int} (hτ : t + s.e.delta ≤ τ) (hhor : τ ≤ rho.horizon)
    (hcompat : Model.Consensus.Objects.Blocks.compatible (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.f
      (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t) = true) :
    (∃ x ∈ Proofs.Consensus.SgStamps.rows (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core row.round,
      x.valIndex = u ∧ x.confirmed = row.confirmed ∧
      Model.Consensus.Objects.Time.occurrenceBefore
        ((worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.timestampSgVote.get?
          (Model.Consensus.Protocol.Store.sgVote x)) (t + s.e.delta) = true) ∧
    ∃ head, Model.Consensus.Objects.Blocks.findRoot? (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.tree
        (Model.Consensus.Objects.Blocks.root (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i t)) = some head ∧
      Model.Consensus.Objects.Time.occurrenceBefore
        ((worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.timestampBlock.get? head) (t + s.e.delta) = true := by
  refine ⟨?_, honestActionRow_sgBlock_delivered c p a nr s rho hwf hdom hsleep hu hev hem hw hτ hhor hcompat⟩
  have hps : Statements.Consensus.Spec.Conditions.PartialSynchrony c p a nr s rho := hsleep.1.1.1.1.2
  have hgst : s.e.tGST ≤ 0 := hsleep.1.1.1.2
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  obtain ⟨hs, hnd⟩ := Proofs.Consensus.Available.schedule_sorted_nodup s rho hsch
  have hnd' := Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev h =>
    (Proofs.Consensus.Window.eventTime_bounds hsch h).1
  have ht0 : 0 ≤ t := hnn _ (List.mem_of_getElem? hev)
  have hmax : max t s.e.tGST = t := max_eq_left (le_trans hgst ht0)
  have hu' : rho.honest.contains u = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu
  have hw' : rho.honest.contains w = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hw
  have hd : t + s.e.delta ≤ rho.horizon := le_trans hτ hhor
  have h := hps.1 u (Model.Consensus.Execution.Objects.NamedObject.Attest row) t ⟨hu', hem⟩ w
  dsimp only at h
  rw [hmax] at h
  obtain ⟨t2, ⟨ht, ht2⟩, j, hh⟩ := h ⟨⟨hw', hd⟩, by simp [Model.Consensus.Execution.Node.excludes]⟩
  obtain ⟨x, hx, hxu, hxc⟩ :=
    honestActionRow_handled_row c p a nr s rho hwf hdom hsleep hu hev hem hw ht ht2 hd hh
  obtain ⟨ev, ⟨⟨hevj, -⟩, hte⟩, -⟩ := hh
  have hlt : j < Proofs.Consensus.ReceiverFinality.idxLt rho τ :=
    Proofs.Consensus.ReceiverFinality.lt_idxLt_of_time_lt rho hs hnd' hevj (by rw [hte]; linarith)
  obtain ⟨hm, τ', hτ', hle⟩ := Proofs.Consensus.SgStamps.sg_stamp_le_of_mem c p a nr s rho hs hnn hevj hx hlt
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
  refine ⟨x, hm, hxu, hxc, ?_⟩
  rw [hτ']
  exact Proofs.Consensus.Stamps.occurrenceBefore_at (by rw [hte] at hle; linarith)

/-- GST-zero の枝で、正の round `r` の phase `ph` の domain 時刻が horizon 以内で、共通の上界 `D` が窓の round の honest な行の
SG block(`RootWitness.HonestWindowCarrierAt r`)と、その読みでのすべての honest なノードの finalized の上にあれば、窓の round `k`
(`latestWindow η_SG r`)に awake な honest な validator `u` は、honest な読み手 `w` の読み(domain 時刻の `stateBeforeTime`)で、早い
cutoff に解釈済みの入力を持つ。手書き `relativeGradeCarrierAt_of_awakeWindowMajority`(`Protocol/Grades/RelativeOneChain.lean` 221 行)
の前提 `htransport` の `∃ y ∈ interpretedInputs …` の段に当たり、手書き `WeakJoint.relativeGradeCarrierAt_of_awakeWindowHistory_gstZero`
(`Protocol/Grades/WeakBootstrapAction.lean` 106〜185 行)がそれを `hroots`(ここでは `hF`)と `hsg` から供給する(周回 260 に
`honestInterpretedMajority_of_commonUpper` から穴として切り出し、周回 261 に証明した)。`u` は round `k` の action 時刻に行を出し
(`awake_emits_actionRow`)、action 時刻 + Δ ≤ 早い cutoff ≤ domain 時刻(`R ≥ 3`、`k < r`。手書き `NamedOutageClosure.action_delta_le_early`)。
行の SG block と `w` の finalized はどちらも `D` の祖先なので互換で、`honestActionRow_delivered`(行の側は周回 262〜263、SG block の側は周回 264〜266 に証明した)から、行の SG 票が早い cutoff より前に
`w` の行にあり、SG block の root の解決が早い cutoff より前の印の head を返す。head は SG block 自身(`sgBlockAt_findRoot_eq`)で、
行の `confirmed` はその root(`RootWitness.emits_confirmed_sgBlockAt`)なので、その SG 票は生の入力で `bodyReady`。 -/
theorem awakeWindowVote_interpreted_of_commonUpper (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {r : Nat} (hr : 0 < r) (ph : Model.Consensus.Protocol.Grades.GradePhase)
    (hhor : Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph ≤ rho.horizon) {D : Block}
    (hsg : ∀ Y, Proofs.Consensus.RootWitness.HonestWindowCarrierAt c p a nr s rho r Y → preceq Y D = true)
    (hF : ∀ v ∈ rho.honest.elems,
      preceq (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho
        (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) v).st.core).f D = true)
    {w : ValidatorId} (hw : w ∈ rho.honest.elems) {u : ValidatorId} (hu : u ∈ rho.honest.elems) {k : Nat}
    (hk : k ∈ Model.Consensus.Protocol.ForkChoice.Goldfish.latestWindow s.hc.etaSG r) (huk : a u k = true) :
    (Model.Consensus.Protocol.Grades.interpretedInputs
      (Model.Consensus.Protocol.Grades.gradeView
        (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho
          (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) w).st.core))
      (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho
        (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) w).st.core).f
      s.hc.etaSG r (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc r ph) u).elems ≠ [] := by
  have _ := hr
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hδ := hfacts.1
  have hR : 3 ≤ s.hc.r := hfacts.2.2
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hkr := (mem_latestWindow_iff.mp hk).2
  -- 時刻: action 時刻 + Δ ≤ 早い cutoff ≤ domain 時刻
  have hdead : Model.Consensus.Execution.Setup.setupActionTime s k + s.e.delta ≤
      Model.Consensus.Protocol.Grades.earlyTime s.e s.hc r ph := by
    have hoff : -5 ≤ Model.Consensus.Protocol.Grades.earlyOffset ph := by cases ph <;> decide
    have hkr' : (k : Int) + 1 ≤ (r : Int) := by exact_mod_cast hkr
    have hR' : (3 : Int) ≤ (s.hc.r : Int) := by exact_mod_cast hR
    rw [setupActionTime_eq]
    unfold Model.Consensus.Protocol.Grades.earlyTime Model.Consensus.Protocol.Grades.openingTime
      Model.Consensus.Protocol.Schedule.proposalTime Model.Consensus.Objects.Parameters.slotTime
      Model.Consensus.Objects.Time.slotStart Model.Consensus.Protocol.Grades.openingSlot
    simp only [Int.ofNat_eq_natCast]
    push_cast
    have h1 : s.e.delta * 4 * (s.hc.r : Int) * ((k : Int) + 1) ≤ s.e.delta * 4 * (s.hc.r : Int) * (r : Int) := by
      apply mul_le_mul_of_nonneg_left hkr'
      positivity
    nlinarith
  have hed : Model.Consensus.Protocol.Grades.earlyTime s.e s.hc r ph ≤
      Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph := by
    unfold Model.Consensus.Protocol.Grades.earlyTime Model.Consensus.Protocol.Grades.domainTime
    cases ph <;> simp only [Model.Consensus.Protocol.Grades.earlyOffset, Model.Consensus.Protocol.Grades.domainOffset] <;>
      nlinarith
  have hact : Model.Consensus.Execution.Setup.setupActionTime s k ≤ rho.horizon := by linarith
  -- u の行(round k の action 時刻)
  obtain ⟨-, row, -, hem, hround⟩ := awake_emits_actionRow c p a nr s rho hsch hδ hR hu huk hact
  obtain ⟨i, hev, hconf, -⟩ := Proofs.Consensus.RootWitness.emits_confirmed_sgBlockAt c p a nr s rho hem
  -- 互換: SG block と w の finalized はどちらも D の祖先
  have hHD : preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i
      (Model.Consensus.Execution.Setup.setupActionTime s k)) D = true :=
    hsg _ ⟨u, i, _, row, hu, hev, hem, hround ▸ hk, rfl⟩
  have hFD := hF w hw
  have hcompat := Proofs.Consensus.Blocks.compatible_of_preceq_common hFD hHD
  obtain ⟨⟨x, hx, hxv, hxc, hxs⟩, head, hfind, hhs⟩ :=
    honestActionRow_delivered c p a nr s rho hwf hdom hsleep hu hev hem hw (le_trans hdead hed) hhor hcompat
  have hhead := sgBlockAt_findRoot_eq c p a nr s rho hwf hsleep hu hev hem hw _ hfind
  subst hhead
  apply List.ne_nil_of_mem (a := Model.Consensus.Protocol.Store.sgVote x)
  rw [Proofs.Consensus.GradeSupporter.mem_interpretedInputs_iff, Proofs.Consensus.GradeSupporter.mem_rawInputs_iff]
  refine ⟨⟨?_, hxv, ?_⟩, ?_⟩
  · refine (Proofs.Consensus.Sets.mem_flatMap_iff Proofs.Consensus.SgStamps.sgv_compare_eq_iff _ _ _).mpr
      ⟨row.round, ?_, (Proofs.Consensus.SgStamps.mem_viewRow_iff _ _ _).mpr ⟨x, hx, rfl⟩⟩
    rw [hround]
    exact (Proofs.Consensus.Sets.mem_toSet_iff Proofs.Consensus.Records.nat_compare_eq_iff _ _).mpr hk
  · exact Proofs.Consensus.GradeSupporter.occurrenceBefore_mono hxs hdead
  · unfold Model.Consensus.Protocol.Grades.bodyReady
    change (match x.confirmed with
      | none => true
      | some r => _) = true
    rw [hxc, hconf]
    dsimp only
    change (match Model.Consensus.Objects.Blocks.findRoot? (worldAt (stateBeforeTime c p a nr s rho
        (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) w).st.core.tree _ with
      | none => false
      | some h => _) = true
    rw [hfind]
    dsimp only
    rw [Bool.and_eq_true]
    refine ⟨Proofs.Consensus.GradeSupporter.occurrenceBefore_mono hhs hdead, ?_⟩
    rw [Proofs.Consensus.Blocks.compatible_comm]
    exact hcompat

/-- GST-zero の枝で、正の round `r` の phase `ph` の domain 時刻が horizon 以内で、共通の上界 `D` が窓の round の honest な行の
SG block(`RootWitness.HonestWindowCarrierAt r`)と、その読みでのすべての honest なノードの finalized の上にあれば、honest な読み手 `w`
の読み(domain 時刻の `stateBeforeTime`)で、早い cutoff に解釈済みの入力を持つ honest な validator の集合 `A` があって、その重みが
honest でない validator の重みより大きい(`GradeSupporter.phase_graded_has_honest_supporter` の前提 `hAH` / `hmaj` の形)。
手書き `relativeGradeCarrierAt_of_awakeWindowMajority`(`Protocol/Grades/RelativeOneChain.lean` 221 行)の `hmajority` と
`hawakePresent` に当たる(周回 258 に `relativeGradeCarrierAt_of_commonUpper` から穴として切り出し、周回 260 に証明した)。
`A` は `SleepyRegime` の `WindowMajority` を round `r` の action 時刻で使った窓の awake な honest の集合(手書き
`sleepy_windows_of_generic` / `windowMajority_of_generic`。時刻の条件は `R ≥ 3` で domain 時刻 ≤ horizon から出る)。その元は
窓の時刻に awake で、その action round は窓の round(`actionRound_mem_latestWindow`)なので、
`awakeWindowVote_interpreted_of_commonUpper`(周回 261 に証明した。配送の `honestActionRow_delivered` は周回 266 に穴が無くなった)で解釈済みの入力を持つ。 -/
theorem honestInterpretedMajority_of_commonUpper (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {r : Nat} (hr : 0 < r) (ph : Model.Consensus.Protocol.Grades.GradePhase)
    (hhor : Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph ≤ rho.horizon) {D : Block}
    (hsg : ∀ Y, Proofs.Consensus.RootWitness.HonestWindowCarrierAt c p a nr s rho r Y → preceq Y D = true)
    (hF : ∀ v ∈ rho.honest.elems,
      preceq (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho
        (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) v).st.core).f D = true)
    {w : ValidatorId} (hw : w ∈ rho.honest.elems) :
    ∃ A : NaruStd.Set ValidatorId, Proofs.Consensus.Sets.Sorted A ∧
      (∀ x ∈ A.elems, x ∈ rho.honest.elems ∧
        (Model.Consensus.Protocol.Grades.interpretedInputs
          (Model.Consensus.Protocol.Grades.gradeView
            (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho
              (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) w).st.core))
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho
            (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) w).st.core).f
          s.hc.etaSG r (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc r ph) x).elems ≠ []) ∧
      Model.Consensus.Objects.Weights.weightOf s.e.electorate
          ((Model.Consensus.Objects.Weights.validators s.e.electorate).diff rho.honest) <
        Model.Consensus.Objects.Weights.weightOf s.e.electorate A := by
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hδ := hfacts.1
  have hR : (3 : Int) ≤ (s.hc.r : Int) := by exact_mod_cast hfacts.2.2
  have hr' : (1 : Int) ≤ (r : Int) := by exact_mod_cast hr
  have hperiod : Model.Consensus.Spec.Constants.period s = s.e.delta * 4 * (s.hc.r : Int) := by
    unfold Model.Consensus.Spec.Constants.period
    rw [setupActionTime_eq, setupActionTime_eq]
    push_cast
    ring
  have hdt : s.e.delta * 4 * (s.hc.r : Int) * (r : Int) - s.e.delta ≤
      Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph := by
    have hoff : -1 ≤ Model.Consensus.Protocol.Grades.domainOffset ph := by
      cases ph <;> decide
    unfold Model.Consensus.Protocol.Grades.domainTime Model.Consensus.Protocol.Grades.openingTime
      Model.Consensus.Protocol.Schedule.proposalTime Model.Consensus.Objects.Parameters.slotTime
      Model.Consensus.Objects.Time.slotStart Model.Consensus.Protocol.Grades.openingSlot
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  have hL0 : (0 : Int) ≤ s.e.delta * 4 * (s.hc.r : Int) := by nlinarith
  have hLr : s.e.delta * 4 * (s.hc.r : Int) ≤ s.e.delta * 4 * (s.hc.r : Int) * (r : Int) := by
    nlinarith [mul_le_mul_of_nonneg_left hr' hL0]
  have h0 : (0 : Int) ≤ Model.Consensus.Execution.Setup.setupActionTime s r := by
    rw [setupActionTime_eq]
    linarith
  have hl : Model.Consensus.Spec.Constants.participationLag s ≤ Model.Consensus.Execution.Setup.setupActionTime s r := by
    unfold Model.Consensus.Spec.Constants.participationLag
    rw [hperiod, setupActionTime_eq]
    linarith
  have hh : Model.Consensus.Execution.Setup.setupActionTime s r - Model.Consensus.Spec.Constants.participationLag s ≤
      rho.horizon := by
    unfold Model.Consensus.Spec.Constants.participationLag
    rw [hperiod, setupActionTime_eq]
    nlinarith
  obtain ⟨members, hex, hlt⟩ := hsleep.1.2 _ ⟨⟨h0, hl⟩, hh⟩
  refine ⟨NaruStd.List.toSet members, Proofs.Consensus.Sets.Sorted.toSet members, fun x hx => ?_, hlt⟩
  have hxc : (NaruStd.List.toSet members).contains x = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ x).mpr hx
  obtain ⟨hxH, u, ⟨hlo, hhi⟩, haw⟩ := (hex x).mp hxc
  have hxm : x ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hxH
  exact ⟨hxm, awakeWindowVote_interpreted_of_commonUpper c p a nr s rho hwf hdom hsleep hr ph hhor hsg hF hw hxm
    (actionRound_mem_latestWindow s hδ (by have := hfacts.2.2; omega) hr hlo hhi) haw⟩

/-- GST-zero の枝で、正の round `r` の phase `ph` の domain 時刻が horizon 以内で、共通の上界 `D` が窓の round の honest な行の
SG block(`RootWitness.HonestWindowCarrierAt r`)と、その読みでのすべての honest なノードの finalized の上にあれば、round `r` の
phase `ph` の読みの grade に担い手がある(`RootWitness.RelativeGradeCarrierAt r ph`)。手書き
`WeakJoint.relativeGradeCarrierAt_of_awakeWindowHistory_gstZero`(`DecoupledConsensusProofs/Protocol/Grades/WeakBootstrapAction.lean`
106〜185 行)に当たる。手書きの前提 `hroots`(action の読みの FG root ⪯ `D`)は、そこから導く `hFD`(domain の読みの finalized ⪯ `D`)の
形で受け取る。`fgStep_gradeCarrier_positive` と `confG1Carrier_positive` の共通の構成(周回 257 に 2 つの穴から切り出した)。
運びは手書き `relativeGradeCarrierAt_of_awakeWindowMajority`(`Protocol/Grades/RelativeOneChain.lean` 221 行)に沿う(周回 258):
解釈済みの入力を持つ honest な多数派(`honestInterpretedMajority_of_commonUpper`。周回 260 に閉じた)から、grade の通った block の honest な支持者の
解釈済みの入力 `y` と、その `confirmed` の tree での解決 `head ⪰ B` を取る(`GradeSupporter.phase_graded_has_honest_supporter`)。
`y` は読みの SG 票の行の attestation `x` の `sgVote` で(`SgStamps.mem_viewRow_iff`)、round は窓の中(`SgStamps.stateBefore_sgInv`)。
送り手は honest なので `x` は送り手が出した行 `row2` の消去(`SgFrom.sg_genuine`。手書き `honest_rawInput_is_own_round_vote`)で、
`row2.confirmed` は務めの SG block の root(`RootWitness.emits_confirmed_sgBlockAt`)。その解決は SG block 自身
(`sgBlockAt_findRoot_eq`。周回 259 に閉じた)なので、`head` が担い手。 -/
theorem relativeGradeCarrierAt_of_commonUpper (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {r : Nat} (hr : 0 < r) (ph : Model.Consensus.Protocol.Grades.GradePhase)
    (hhor : Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph ≤ rho.horizon) {D : Block}
    (hsg : ∀ Y, Proofs.Consensus.RootWitness.HonestWindowCarrierAt c p a nr s rho r Y → preceq Y D = true)
    (hF : ∀ v ∈ rho.honest.elems,
      preceq (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho
        (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) v).st.core).f D = true) :
    Proofs.Consensus.RootWitness.RelativeGradeCarrierAt c p a nr s rho r ph := by
  intro w hw B hgrade
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, hunf⟩, -⟩ := hexec
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  obtain ⟨A, hA, hAH, hmaj⟩ :=
    honestInterpretedMajority_of_commonUpper c p a nr s rho hwf hdom hsleep hr ph hhor hsg hF hw
  obtain ⟨v, hvH, y, hy, k, head, hyk, hfind, hBh⟩ :=
    Proofs.Consensus.GradeSupporter.phase_graded_has_honest_supporter s.e s.hc hfacts.1.le
      (Proofs.Consensus.JustificationCertificate.sorted_validators hwf) _ _ r ph hA hAH hmaj hgrade
  -- 読みを添字 `i0` の `stateBefore` に置く
  obtain ⟨i0, hi0⟩ := Proofs.Consensus.FinalizedAccountable.readAt_eq_stateBefore c p a nr s rho hs
    (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph - 1)
  have hst : stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph) =
      stateBefore c p a nr s rho i0 := by
    rw [← hi0, readAt_eq_stateBeforeTime_succ, sub_add_cancel]
  -- 解釈済みの入力を読みの SG 票の行の attestation に戻す
  rw [Proofs.Consensus.GradeSupporter.mem_interpretedInputs_iff, Proofs.Consensus.GradeSupporter.mem_rawInputs_iff] at hy
  obtain ⟨⟨hwin, hyv, -⟩, -⟩ := hy
  obtain ⟨k', hk'w, hyk'⟩ :=
    (Proofs.Consensus.Sets.mem_flatMap_iff Proofs.Consensus.SgStamps.sgv_compare_eq_iff _ _ _).mp hwin
  rw [hst] at hyk'
  obtain ⟨x, hx, rfl⟩ := (Proofs.Consensus.SgStamps.mem_viewRow_iff _ k' _).mp hyk'
  have hk'w' : k' ∈ Model.Consensus.Protocol.ForkChoice.Goldfish.latestWindow s.hc.etaSG r :=
    (Proofs.Consensus.Sets.mem_toSet_iff Proofs.Consensus.Records.nat_compare_eq_iff _ _).mp hk'w
  have hxr : x.round = k' := Proofs.Consensus.SgStamps.stateBefore_sgInv c p a nr s rho i0 w k' x hx
  have hxv : x.valIndex = v := hyv
  have hvc : rho.honest.contains x.valIndex = true := by
    rw [hxv]
    exact (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hvH
  obtain ⟨row2, t2, hrow2, hem⟩ := Proofs.Consensus.SgFrom.sg_genuine c p a nr s rho hunf hx hvc
  rw [hxv] at hem
  obtain ⟨i2, hev2, hconf, -⟩ := Proofs.Consensus.RootWitness.emits_confirmed_sgBlockAt c p a nr s rho hem
  have hkr : k = root (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho v i2 t2) := by
    have h1 : (Model.Consensus.Protocol.Store.sgVote x).confirmed = row2.confirmed := by
      rw [← hrow2]; rfl
    rw [h1, hconf] at hyk
    exact (Option.some.inj hyk).symm
  subst hkr
  have hhead := sgBlockAt_findRoot_eq c p a nr s rho hwf hsleep hvH hev2 hem hw _ hfind
  refine ⟨_, ⟨v, i2, t2, row2, hvH, hev2, hem, ?_, rfl⟩, hhead ▸ hBh⟩
  have : row2.round = x.round := by rw [← hrow2]; rfl
  rw [this, hxr]
  exact hk'w'

/-- GST-zero の枝の round の帰納法の段の正の round の grade の担い手。`fgStep_preceq_laterVoteHead_positive` と同じ前提から、
務めの round の各 phase の domain 時刻が horizon 以内なら、その読みの grade に担い手(窓の round の honest な行の SG block)がある
(`RootWitness.RelativeGradeCarrierAt`)。手書き `WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut`
(`DecoupledConsensusProofs/Protocol/Grades/WeakBootstrapAction.lean`)の帰納の段の `hformation` の担い手の側に当たる(周回 254)。
G1 の root の active prefix(`fgStep_g1Prefix_positive`)と grade 2 の候補(`fgStep_candidate_positive`)はここから出す(周回 254・255)。
共通の構成 `relativeGradeCarrierAt_of_commonUpper` を `D = X` で掛ける。行の round は務めの round
(`RootWitness.emits_confirmed_sgBlockAt`)なので、窓の round の honest な行の SG block は前提 `hprevSg` で `X` の祖先
(`lt_of_mem_latestWindow`)。読み手の finalized は `stateBeforeTime_f_preceq_of_witnesses` で、domain 時刻より前の行の確認の証人に
下ろす。その行の round は務めの round より小さい(`emits_round_lt_of_lt_domainTime`)ので前提 `hprev` の第 2 連言で閉じる
(周回 254 に穴として置き、周回 257 に閉じた)。 -/
theorem fgStep_gradeCarrier_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (_hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (_hd : 1 ≤ d) (_hupper : d ≤ last + 1) {x : ValidatorId} (_hx : rho.honest.contains x = true)
    {w : ValidatorId} {i : Nat} {t : Int} {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation}
    (_hw : w ∈ rho.honest.elems) (hev : rho.events[i]? = some (NamedEvent.Tick w t))
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho w
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t)
    (_ht : t < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))
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
    (_hsame : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      w2 ∈ rho.honest.elems → rho.events[i2]? = some (NamedEvent.Tick w2 t2) →
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho w2
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      row2.round = row.round →
      preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
          (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w2 i2 t2).core))
        (voteDutyHeadAt c p a nr s rho x d) = true)
    (_hroot : preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
        (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core))
      (voteDutyHeadAt c p a nr s rho x d) = true)
    (_hprior : ∀ C, Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
      preceq C (voteDutyHeadAt c p a nr s rho x d) = true) :
    ∀ ph, Model.Consensus.Protocol.Grades.domainTime s.e s.hc
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core.s) ph ≤ rho.horizon →
      Proofs.Consensus.RootWitness.RelativeGradeCarrierAt c p a nr s rho
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core.s) ph := by
  intro ph hph
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hsch : ScheduleWellFormed s rho := by
    have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
    unfold ExecutionValid at hexec
    exact hexec.1.1.1
  have hnd : Statements.Consensus.Spec.Conditions.EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  have hnd' := Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd
  obtain ⟨i', hev', -, hround⟩ := Proofs.Consensus.RootWitness.emits_confirmed_sgBlockAt c p a nr s rho hem
  have hil : i' < rho.events.length := (List.getElem?_eq_some_iff.mp hev').1
  have hii : i' = i := (List.Nodup.getElem?_inj hil hnd').mp (hev'.trans hev.symm)
  subst hii
  refine relativeGradeCarrierAt_of_commonUpper c p a nr s rho hwf hdom hsleep hpos ph hph
    (D := voteDutyHeadAt c p a nr s rho x d) ?_ ?_
  · rintro Y ⟨u, i2, t2, row2, hu, hev2, hem2, hwin, rfl⟩
    exact hprevSg u i2 t2 row2 hu hev2 hem2 (hround ▸ lt_of_mem_latestWindow hwin)
  · intro v hv
    refine stateBeforeTime_f_preceq_of_witnesses c p a nr s rho hwf hsleep hv _ ?_
    intro u i2 t2 row2 hu hev2 hem2 ht2 T hT
    have hlt : row2.round < row.round := by
      rw [hround]
      exact emits_round_lt_of_lt_domainTime c p a nr s rho hδ hem2 ht2
    exact (hprev u i2 t2 row2 hu hev2 hem2 hlt).2 T hT

/-- GST-zero の枝の round の帰納法の段の正の round の G1 の root の active prefix: `fgStep_preceq_laterVoteHead_positive` と同じ前提から、
務めの round の frame の G1 の結果が root `g` を持ち、`g` の filtered tree の中の active prefix `b` があるなら `b` が slot `d` の投票の
務めの head `X` の祖先。手書き `WeakJoint.actionGradeFormationAt_of_awakeWindowMajority`(`DecoupledConsensusProofs/Protocol/Grades/WeakBootstrapAction.lean`)
の anchor の枝(`hgrade .g1` で raw を担い手の SG block に下ろし、A ⪯ clip ⪯ raw で閉じる)と同じ運び: `b ⪯ g`
(`Grade2Capture.activePrefix_preceq`)、`g` は G1 の domain 時刻の tick で凍結した `g0` の祖先(`confCache_phase_origin`)、`g0` は
その読みで grade が通る(`Grade2Capture.freezeRoot_mem`。読みは `RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime`)ので
grade の担い手(`fgStep_gradeCarrier_positive` の phase G1。domain 時刻は run の event の時刻なので horizon 以内)の下で窓の round の
honest な行の SG block の祖先、窓の round は務めの round より小さい(`lt_of_mem_latestWindow`)ので前提 `hprevSg` で閉じる
(周回 253 に穴として置き、周回 255 に閉じた)。 -/
theorem fgStep_g1Prefix_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
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
    ∀ g b, (Model.Consensus.Protocol.Grades.readFrame
        (Proofs.Consensus.ConfirmedOrigin.confCacheAt c p a nr s rho w i t)
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc
          (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core.s)).g1 = some (some g) →
      Model.Consensus.Protocol.Grades.activePrefix (Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTree
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho w i t).core)) g =
        some b →
      preceq b (voteDutyHeadAt c p a nr s rho x d) = true := by
  intro g b hg hb
  have hsch : ScheduleWellFormed s rho := by
    have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
    unfold ExecutionValid at hexec
    exact hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnd : Statements.Consensus.Spec.Conditions.EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  have hnd' := Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd
  obtain ⟨j, g0, -, hevj, hfz, hbg0⟩ := confCache_phase_origin c p a nr s rho hev _ hpos
    Model.Consensus.Protocol.Grades.GradePhase.G1 hg (Proofs.Consensus.Grade2Capture.activePrefix_preceq hb)
  obtain ⟨-, hgrade⟩ := Proofs.Consensus.Grade2Capture.freezeRoot_mem hfz
  rw [Proofs.Consensus.RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime c p a nr s rho hs hnd' hevj] at hgrade
  have hbounds := Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? hevj)
  simp only [eventTime] at hbounds
  obtain ⟨Y, ⟨u, i2, t2, row2, hu, hev2, hem2, hwin, rfl⟩, hg0Y⟩ :=
    fgStep_gradeCarrier_positive c p a nr s rho hwf hdom hsleep hhor hd hupper hx hw hev hem ht hpos
      hprevSg hprev hsame hroot hprior Model.Consensus.Protocol.Grades.GradePhase.G1 hbounds.2 w hw g0 hgrade
  obtain ⟨i', hev', -, hround⟩ := Proofs.Consensus.RootWitness.emits_confirmed_sgBlockAt c p a nr s rho hem
  have hil : i' < rho.events.length := (List.getElem?_eq_some_iff.mp hev').1
  have hii : i' = i := (List.Nodup.getElem?_inj hil hnd').mp (hev'.trans hev.symm)
  subst hii
  have hlt : row2.round < row.round := by
    rw [hround]
    exact lt_of_mem_latestWindow hwin
  exact Proofs.Consensus.Blocks.preceq_trans (Proofs.Consensus.Blocks.preceq_trans hbg0 hg0Y)
    (hprevSg u i2 t2 row2 hu hev2 hem2 hlt)

/-- GST-zero の枝の round の帰納法の段の正の round の grade 2 の候補: `fgStep_preceq_laterVoteHead_positive` と同じ前提から、
務めの grade 2 の候補は slot `d` の投票の務めの head `X` の祖先。候補は grade の担い手(`fgStep_gradeCarrier_positive`)の下で
窓の round の honest な行の SG block の祖先(`RootWitness.grade2CandidateAt_preceq_honestWindowCarrier_of_emits`)で、窓の round は
務めの round(= 行の round、`RootWitness.emits_confirmed_sgBlockAt`)より小さい(`lt_of_mem_latestWindow`)ので、その SG block は
前提 `hprevSg` で `X` の祖先(周回 254)。 -/
theorem fgStep_candidate_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
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
    ∀ q, Proofs.Consensus.RootWitness.grade2CandidateAt c p a nr s rho w i t = some q →
      preceq q (voteDutyHeadAt c p a nr s rho x d) = true := by
  intro q hq
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hsch : ScheduleWellFormed s rho := by
    have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
    unfold ExecutionValid at hexec
    exact hexec.1.1.1
  have hnd : Statements.Consensus.Spec.Conditions.EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  have hgrade := fgStep_gradeCarrier_positive c p a nr s rho hwf hdom hsleep hhor hd hupper hx hw hev hem ht hpos
    hprevSg hprev hsame hroot hprior
  obtain ⟨Y, ⟨u, i2, t2, row2, hu, hev2, hem2, hwin, rfl⟩, hqY⟩ :=
    Proofs.Consensus.RootWitness.grade2CandidateAt_preceq_honestWindowCarrier_of_emits c p a nr s rho hδ hsch hnd hw hem
      hgrade hq
  obtain ⟨i', hev', -, hround⟩ := Proofs.Consensus.RootWitness.emits_confirmed_sgBlockAt c p a nr s rho hem
  have hil : i' < rho.events.length := (List.getElem?_eq_some_iff.mp hev').1
  have hii : i' = i := (List.Nodup.getElem?_inj hil
    (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd)).mp (hev'.trans hev.symm)
  subst hii
  have hlt : row2.round < row.round := by
    rw [hround]
    exact lt_of_mem_latestWindow hwin
  exact Proofs.Consensus.Blocks.preceq_trans hqY (hprevSg u i2 t2 row2 hu hev2 hem2 hlt)

/-- GST-zero の枝の round の帰納法の段の正の round。honest な `w` が時刻 `t < voteTime (d + 1)`(添字 `i` の tick)に行 `row` を出し、
務めの store の round が正で、前の round の行の tick の SG block と FG root・確認の証人、同じ round の行の tick の FG root、自分の FG root と
genuine な確認がどれも slot `d` の投票の務めの head `X` の祖先なら、自分の務めの SG block と grade 2 の候補も `X` の祖先。
手書き `WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut`(`DecoupledConsensusProofs/Protocol/Grades/WeakBootstrapAction.lean`)
の帰納の段のうち `hroots` の後で、`hformation` から grade の形成を取って SG block と確認の証人を押さえる枝に当たる(round 0 の枝は
`fgStep_round_zero`。周回 251)。G1 の root の active prefix は `fgStep_g1Prefix_positive`(周回 255)、grade 2 の候補は `fgStep_candidate_positive`(周回 254)から取り、
anchor は `frameAnchor_preceq_of_g1Prefix`(周回 253)、SG block は `sgBlockAt_preceq_of_candidate_anchor` で出す(周回 252)。 -/
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
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hg1 := fgStep_g1Prefix_positive c p a nr s rho hwf hdom hsleep hhor hd hupper hx hw hev hem ht hpos
    hprevSg hprev hsame hroot hprior
  have hq2 := fgStep_candidate_positive c p a nr s rho hwf hdom hsleep hhor hd hupper hx hw hev hem ht hpos
    hprevSg hprev hsame hroot hprior
  have hanchor := frameAnchor_preceq_of_g1Prefix (e := s.e) (hc := s.hc) hroot hg1
  exact ⟨sgBlockAt_preceq_of_candidate_anchor c p a nr s rho hδ hem hroot hprior hq2 hanchor, hq2⟩

/-- GST-zero の枝の round の帰納法の段(`fgStep_preceq_laterVoteHead_positive` と同じ前提から、round の正を除いたもの)。
務めの store の round で分け、0 なら `fgStep_round_zero`、正なら `fgStep_preceq_laterVoteHead_positive`(周回 251。周回 252 から穴ではない)。 -/
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
その tick の務めの SG block と務めの確認の証人 `T` は、`1 ≤ d ≤ last + 1`(`last` の確認の時刻は `horizon` 以下)の honest なノード `x` の
slot `d` の投票の務めの head の祖先。手書き `actionSources_preceq_voteDutyHead_of_gstZero` の第 1・3 の結論(`actionSGBlockAt ⪯ voteDutyHead`
と `fgConfirmationWitness S (actionStoreAt S rho w r) = some T → T ⪯ voteDutyHead S rho x d`。
`DecoupledConsensusProofs/Execution/WeakGenesisGSTZeroActionSources.lean`)に当たり、手書きの round の境 `S.a r < vote_time (d + 1)` を
行の時刻の境に置き換えた(周回 247。周回 256 に確認の証人だけの `fgWitness_preceq_laterVoteHead` から SG block も返す形に広げた)。
手書きと同じ運び: round の同時帰納(`RootWitness.dutyStoreAt_jointRoundInduction_of_prior`。手書き
`WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut`)を `base = cut = 0`、`limit = voteTime (d + 1)`、
行ごとの性質を SG block ⪯ X(手書きの第 1 連言)に置いて掛ける。`cut = 0` なので bootstrap と古い根の前提は空。段の genuine な確認
(手書きの `hprior`)は、行を出した tick が確認評価の tick(`emits_confTick`)で slot が `d` 未満(`emits_slot_lt_of_lt_nextVote`)
なので前提 `hpriorD`(slot `d` 未満の genuine な確認は `X` の祖先。手書きの `hpriorD`)から、SG block と grade 2 の候補は `fgStep_preceq_laterVoteHead`(round 0 は証明済み、正の round は G1 の root の active prefix と grade 2 の候補の担い手が `fgStep_gradeCarrier_positive` で、その共通の構成が `relativeGradeCarrierAt_of_commonUpper` で、配送の `acceptedBlock_handled_held` は周回 266 に閉じた。周回 252〜266)から(周回 250)。
周回 270 に、段の genuine な確認を前提 `hpriorD` で受け取る形にした(slot の帰納法 `protectedVoteSlots_gstZero` の段で、帰納法の仮定から渡すため)。 -/
theorem laterVoteHead_rowSources_of_prior (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hpriorD : ∀ (w : ValidatorId) (i : Nat) (t : Int) (C : Block), rho.honest.contains w = true →
      Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t →
      Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d →
      Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
      preceq C (voteDutyHeadAt c p a nr s rho x d) = true)
    {u : ValidatorId} (hu : rho.honest.contains u = true)
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} {i2 : Nat} {t2 : Int}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2)
    (hev : rho.events[i2]? = some (NamedEvent.Tick u t2))
    (ht2 : t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) :
    preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i2 t2) (voteDutyHeadAt c p a nr s rho x d) = true ∧
      ∀ T, Proofs.Consensus.RootWitness.fgConfirmationWitnessAt c p a nr s rho u i2 t2 = some T →
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
  refine (fun h => ⟨h.1, (h.2 (Nat.zero_le _)).2⟩)
    (Proofs.Consensus.RootWitness.dutyStoreAt_jointRoundInduction_of_prior c p a nr s rho hfacts.1 (by omega) hs hnd
    hqh hcar hcf (base := 0) (cut := 0) (limit := Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))
    (X := voteDutyHeadAt c p a nr s rho x d)
    (fun w i t _ => preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho w i t)
      (voteDutyHeadAt c p a nr s rho x d) = true) le_rfl
    (fun _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)) ?_
    u i2 t2 row hum hev hem ht2 (Nat.zero_le _))
  intro w i t row' hw hi hem' hlim _ hprevQ hprev hsame hroot
  have hprior : ∀ C, Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
      preceq C (voteDutyHeadAt c p a nr s rho x d) = true := fun C hC =>
    hpriorD w i t C ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hw)
      (emits_confTick c p a nr s rho hfacts.1 hem' hi) (emits_slot_lt_of_lt_nextVote c p a nr s rho hfacts.1 hem' hlim) hC
  obtain ⟨hq, hg⟩ := fgStep_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hd hupper hx hw hi hem' hlim
    (fun w2 i2 t2 row2 hw2 hi2 hem2 hlt => hprevQ w2 i2 t2 row2 hw2 hi2 hem2 (Nat.zero_le _) hlt)
    (fun w2 i2 t2 row2 hw2 hi2 hem2 hlt => hprev w2 i2 t2 row2 hw2 hi2 hem2 (Nat.zero_le _) hlt)
    hsame hroot hprior
  exact ⟨hq, hprior, hg⟩

/-- slot `d` の投票の cone(手書き `NamedHonestVotesCone S rho d (fun X => Block.Preceq B X)`。
`DecoupledConsensusInternal/Definitions/NamedLifecycle.lean`): slot `d` の委員会の honest な元はどれも、`B` の子孫である run のブロック
`X` の root に、投票時刻 `voteTime e d` に投票する(周回 270)。 -/
def HonestVotesCone (d : Nat) (B : Block) : Prop :=
  ∀ x, rho.honest.contains x = true → (c d).contains x = true →
    ∃ X : Model.Consensus.Objects.NamedBlocks.NamedBlock,
      preceq B (Model.Consensus.Objects.NamedBlocks.eraseBlock X) = true ∧
      Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho X ∧
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho x
        (Model.Consensus.Execution.Objects.NamedObject.GfVote
          ⟨x, d, root (Model.Consensus.Objects.NamedBlocks.eraseBlock X)⟩)
        (Model.Consensus.Protocol.Schedule.voteTime s.e d)

/-- **slot `d` で `B` が保護される**(手書き `ProtectedVoteSlot`。`DecoupledConsensusProofs/Protocol/Grades/SafetySlotInduction.lean`):
すべての honest なノードの slot `d` の投票の務めの head が `B` の子孫で(`heads`)、slot `d` の投票の cone が `B` の上にある(`cone`)。
周回 270。 -/
structure ProtectedVoteSlot (d : Nat) (B : Block) : Prop where
  heads : ∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x d) = true
  cone : HonestVotesCone c p a nr s rho d B

/-- 保護は祖先に降りる(手書き `ProtectedVoteSlot.of_ancestor`。周回 270)。 -/
theorem ProtectedVoteSlot.of_ancestor {d : Nat} {B P : Block} (hP : ProtectedVoteSlot c p a nr s rho d P)
    (hBP : preceq B P = true) : ProtectedVoteSlot c p a nr s rho d B := by
  refine ⟨fun x hx => Proofs.Consensus.Blocks.preceq_trans hBP (hP.heads x hx), ?_⟩
  intro x hx hxc
  obtain ⟨X, hPX, hX, hem⟩ := hP.cone x hx hxc
  exact ⟨X, Proofs.Consensus.Blocks.preceq_trans hBP hPX, hX, hem⟩

/-- slot `d` 未満の確認評価の tick の genuine な確認は、どれも honest なノードの slot `d` の投票の務めの head の祖先(手書きの帰納の段の
`hpriorD`。`laterVoteHead_rowSources_of_prior` の前提を honest なノードすべてについて束ねたもの。周回 270)。 -/
def PriorConfsBelow (d : Nat) : Prop :=
  ∀ x, rho.honest.contains x = true → ∀ (w : ValidatorId) (i : Nat) (t : Int) (C : Block),
    rho.honest.contains w = true → Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t →
    Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d →
    Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
    preceq C (voteDutyHeadAt c p a nr s rho x d) = true

/-- 投票の務めの head は tree のブロック: fork choice の `ghost` は出発点の anchor(grade の読み。tree の元か `j` / `f`。
`Trees.getSgRootWith_cases`)を返すか、歩く tree(voter view の処理済みの tree を絞ったもの。どれも tree の部分集合)の元を返す
(`Trees.ghost_cases`)。`j` / `f` は `TreeInv` で tree にある(手書き `voterHeadAt` が読みの tree にあることに当たる。周回 272)。 -/
theorem voteHeadBlock_mem_tree (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    {st : Model.Consensus.Protocol.Store.Store} (h : Proofs.Consensus.Trees.TreeInv st) :
    Proofs.Consensus.Voting.voteHeadBlock cache e hc st ∈ st.tree.elems := by
  unfold Proofs.Consensus.Voting.voteHeadBlock Model.Consensus.Protocol.Handlers.getHeadInTreeWith
    Model.Consensus.Protocol.ForkChoice.Head.getHeadInTreeWithLayer
    Model.Consensus.Protocol.ForkChoice.Goldfish.goldfishForkChoice
  dsimp only
  rcases Proofs.Consensus.Trees.ghost_cases _ _ _ _ with heq | hmem
  · rw [heq]
    rcases Proofs.Consensus.Trees.getSgRootWith_cases cache e hc (Model.Consensus.Protocol.Store.storeToHealing st)
      _ with h1 | h1 | h1
    · exact h1
    · rw [h1]; exact h.j
    · rw [h1]; exact h.f
  · unfold Model.Consensus.Protocol.Handlers.voterFilteredBlockTree at hmem
    have h2 := Proofs.Consensus.Trees.getFilteredBlockTreeFrom_sub hmem
    unfold Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree at h2
    exact ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp h2).1

/-- **投票時刻の読みの bodies のブロックの slot は `d` 以下**(手書き `block_slot_lt_of_mem_storeAt` の投票時刻の形): genesis でなければ
投票時刻より前の event で入ったので、提案時刻はその event の時刻以下(`NoFutureRead.bodies_entry_slot`)で投票時刻 `voteTime e d`
より前(`JustificationCertificate.time_lt_of_lt_idxLt`)、したがって slot は `d` 以下(周回 294)。 -/
theorem voteTimeBodies_slot_le (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (hδ : 0 < s.e.delta) (x : ValidatorId) (d : Nat) {X : Model.Consensus.Objects.NamedBlocks.NamedBlock}
    (hX : X ∈ (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e d)) x).st.bodies.elems) :
    slot (Model.Consensus.Objects.NamedBlocks.eraseBlock X) ≤ d := by
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs] at hX
  rcases Proofs.Consensus.NoFutureRead.bodies_entry_slot c p a nr s rho hs hnn hδ _ x X hX with
    rfl | ⟨j, ev, hj, hev, -, hle⟩
  · exact Nat.zero_le _
  · have hlt := Proofs.Consensus.JustificationCertificate.time_lt_of_lt_idxLt rho hs hj hev
    have h := Proofs.Consensus.Window.le_slotOf_of_le s.e hδ (hle.trans hlt.le)
    rwa [Proofs.Consensus.Voting.slotOf_voteTime s.e hδ] at h

/-- **cone は `heads` から出る**。正の slot `d`(`d ≤ last + 1`、`last` の確認の時刻は `horizon` 以下)で、すべての honest なノードの
slot `d` の投票の務めの head が `B` の子孫なら、slot `d` の委員会の honest な元は投票時刻に、`B` の子孫で slot が `d` 以下の run の
ブロックの root に投票する。手書き `WeakGoldfish.goldfishCone_succ_of_runFrontierWitnesses` の結論の cone の側に当たる。周回 272 に
`voteCone_genesis` として証明した運びを、周回 273 に `heads` を前提にして一般の `B` に広げた: 投票時刻は `last` の確認の時刻以下なので
horizon 以下で、honest な委員は投票を出し(`Voting.honest_emits_gfVote_head`)、その head は tick の前の store の tree のブロックの root
(`voteHeadBlock_mem_tree`)、tree のブロックは bodies の名前付きブロックの消去(`Carrier.StoreInv.named`)で run のブロック
(`RootWitness.blockInRun_of_stateBefore`)。tick の前の状態は投票時刻の読み(`RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime`)
なので、投票の head は `voteDutyHeadAt x d` そのもので、`B ⪯ X` は `heads` から出る。周回 294 に slot の上限
(`voteTimeBodies_slot_le`。手書き `coneSupport_of_named_votes` の前提 `hvote` の `X.slot ≤ s`)を、周回 296 に `X` の消去が
投票の務めの head であること(`voteConeStamped_of_heads` に渡す)を足した。 -/
theorem voteConeSlot_of_heads (hwf : SetupWellFormed c p s)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {B : Block}
    (hheads : ∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x d) = true) :
    ∀ x, rho.honest.contains x = true → (c d).contains x = true →
      ∃ X : Model.Consensus.Objects.NamedBlocks.NamedBlock,
        preceq B (Model.Consensus.Objects.NamedBlocks.eraseBlock X) = true ∧
        Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho X ∧
        Statements.Consensus.Spec.Execution.Emits c p a nr s rho x
          (Model.Consensus.Execution.Objects.NamedObject.GfVote
            ⟨x, d, root (Model.Consensus.Objects.NamedBlocks.eraseBlock X)⟩)
          (Model.Consensus.Protocol.Schedule.voteTime s.e d) ∧
        slot (Model.Consensus.Objects.NamedBlocks.eraseBlock X) ≤ d ∧
        Model.Consensus.Objects.NamedBlocks.eraseBlock X = voteDutyHeadAt c p a nr s rho x d := by
  intro x hx hxc
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hnd : EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  obtain ⟨hs, -⟩ := Proofs.Consensus.Available.schedule_sorted_nodup s rho hsch
  have hvt : Model.Consensus.Protocol.Schedule.voteTime s.e d ≤ rho.horizon := by
    refine le_trans ?_ hhor
    have hd' : (d : Int) ≤ (last : Int) + 1 := by exact_mod_cast hupper
    unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    nlinarith
  obtain ⟨u, i, he, hval, hslot, hev, hhead⟩ :=
    Proofs.Consensus.Voting.honest_emits_gfVote_head c p a nr s rho hsch hδ hx (by omega) hxc hvt
  have hti := Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho i x
  have hmem := voteHeadBlock_mem_tree
    (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho i) x).st.core)
          (Model.Consensus.Protocol.Schedule.voteTime s.e d)
          (worldAt (stateBefore c p a nr s rho i) x).cache) s.e s.hc
    (st := (Proofs.Consensus.Voting.clocked s.e
      (worldAt (stateBefore c p a nr s rho i) x).st (Model.Consensus.Protocol.Schedule.voteTime s.e d)).core)
    (hti.congr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  obtain ⟨X, hX, hXe⟩ := (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho i x).named _ hmem
  have hduty : voteDutyHeadAt c p a nr s rho x d =
      Proofs.Consensus.Voting.voteHeadBlock
        (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho i) x).st.core)
          (Model.Consensus.Protocol.Schedule.voteTime s.e d)
          (worldAt (stateBefore c p a nr s rho i) x).cache) s.e s.hc
        (Proofs.Consensus.Voting.clocked s.e
          (worldAt (stateBefore c p a nr s rho i) x).st (Model.Consensus.Protocol.Schedule.voteTime s.e d)).core := by
    unfold voteDutyHeadAt; dsimp only
    rw [← Proofs.Consensus.RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime c p a nr s rho hs
      (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) hev]
    rfl
  refine ⟨X, ?_,
    Proofs.Consensus.RootWitness.blockInRun_of_stateBefore c p a nr s rho
      ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hx) i hX, ?_, ?_⟩
  · rw [hXe, ← hduty]
    exact hheads x hx
  · have hu : u = ⟨x, d, root (Model.Consensus.Objects.NamedBlocks.eraseBlock X)⟩ := by
      rw [hXe, ← Proofs.Consensus.Voting.voteHead_eq_root, ← hhead, ← hval, ← hslot]
    rw [← hu]
    exact he
  · rw [Proofs.Consensus.RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime c p a nr s rho hs
      (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) hev] at hX
    exact ⟨voteTimeBodies_slot_le c p a nr s rho hs
      (fun ev hev => (Proofs.Consensus.Window.eventTime_bounds hsch hev).1) hδ x d hX, hXe.trans hduty.symm⟩

/-- slot `d` の投票の cone は `heads` から出る(`voteConeSlot_of_heads` の slot の上限を落とした形。周回 273。周回 294 から射影)。 -/
theorem voteCone_of_heads (hwf : SetupWellFormed c p s)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {B : Block}
    (hheads : ∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x d) = true) :
    HonestVotesCone c p a nr s rho d B := by
  intro x hx hxc
  obtain ⟨X, hBX, hX, hem, -, -⟩ := voteConeSlot_of_heads c p a nr s rho hwf hsleep hhor hd hupper hheads x hx hxc
  exact ⟨X, hBX, hX, hem⟩

/-- 種の cone。正の slot `d` の委員会の honest な元は、投票時刻に run のブロックの root に投票する(genesis はどのブロックの祖先でも
あるので `heads` は自明)。手書き `protectedVoteSlot_genesis`(`DecoupledConsensusProofs/Protocol/Grades/WeakGenesis.lean`)の cone の段に
当たる。周回 270 に穴として置き、周回 272 に証明した。周回 273 から `voteCone_of_heads` の特別な場合。 -/
theorem voteCone_genesis (hwf : SetupWellFormed c p s)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) :
    HonestVotesCone c p a nr s rho d Block.Genesis :=
  voteCone_of_heads c p a nr s rho hwf hsleep hhor hd hupper (fun _ _ => Proofs.Consensus.Blocks.preceq_genesis _)

/-- `heads` があれば slot `d` で保護される(cone は `voteCone_of_heads`。周回 273)。 -/
theorem protectedVoteSlot_of_heads (hwf : SetupWellFormed c p s)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {B : Block}
    (hheads : ∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x d) = true) :
    ProtectedVoteSlot c p a nr s rho d B :=
  ⟨hheads, voteCone_of_heads c p a nr s rho hwf hsleep hhor hd hupper hheads⟩

/-- 投票の head は読みの FG root を延ばす: fork choice は anchor(`getSgRootWith`。FG root を延ばす
`ProposerRoot.getSgRootWith_extends_fgRoot`)から `ghost` で辿る(`Goldfish.ghost_preceq`)。手書き `get_head_in_tree_with_of_preceq_fgRoot`
の FG root ⪯ head の部分(周回 274)。 -/
theorem voteHeadBlock_extends_fgRoot (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (st : Model.Consensus.Protocol.Store.Store) :
    preceq (Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing st))
      (Proofs.Consensus.Voting.voteHeadBlock cache e hc st) = true := by
  unfold Proofs.Consensus.Voting.voteHeadBlock Model.Consensus.Protocol.Handlers.getHeadInTreeWith
    Model.Consensus.Protocol.ForkChoice.Head.getHeadInTreeWithLayer
    Model.Consensus.Protocol.ForkChoice.Goldfish.goldfishForkChoice
  dsimp only
  exact Proofs.Consensus.Blocks.preceq_trans
    (Proofs.Consensus.ProposerRoot.getSgRootWith_extends_fgRoot _ _ _ _ _)
    (Proofs.Consensus.Goldfish.ghost_preceq _ _ _ _)

/-- ノード `x` の slot `k` の投票の務めの読みの FG root(手書き `get_fg_root (voteDutyRead S rho w k).st.core.toHealing.toFG`)。
`voteDutyHeadAt` と同じ読み(周回 274)。 -/
def voteDutyFgRootAt (x : ValidatorId) (k : Nat) : Block :=
  let tv := Model.Consensus.Protocol.Schedule.voteTime s.e k
  let n := worldAt (stateBeforeTime c p a nr s rho tv) x
  Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot
    (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.Voting.clocked s.e n.st tv).core)

/-- 投票の務めの読みの FG root は投票の務めの head の祖先(周回 274)。 -/
theorem voteDutyFgRootAt_preceq_head (x : ValidatorId) (k : Nat) :
    preceq (voteDutyFgRootAt c p a nr s rho x k) (voteDutyHeadAt c p a nr s rho x k) = true :=
  voteHeadBlock_extends_fgRoot _ _ _ _

/-- **`heads` の FG root の枝**: `B` が読みの FG root の祖先なら head の祖先なので、`heads` は `B` が FG root の祖先でない
honest なノードについて示せばよい。手書き `WeakGoldfish.goldfishCone_step'` の `hbelowRoot` の枝(`C ⪯ get_fg_root …`。
`get_head_in_tree_with_of_preceq_fgRoot`)に当たる(周回 274)。 -/
theorem heads_of_notBelowFgRoot {k : Nat} {B : Block}
    (habove : ∀ x, rho.honest.contains x = true → ¬ preceq B (voteDutyFgRootAt c p a nr s rho x k) = true →
      preceq B (voteDutyHeadAt c p a nr s rho x k) = true) :
    ∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x k) = true := by
  intro x hx
  by_cases h : preceq B (voteDutyFgRootAt c p a nr s rho x k) = true
  · exact Proofs.Consensus.Blocks.preceq_trans h (voteDutyFgRootAt_preceq_head c p a nr s rho x k)
  · exact habove x hx h


/-- 確認の更新の前の段 `tickPreUpdateStore`(時計合わせ・提案・投票)の後の tree のブロックは、前の tree にあったか、受理の守りを
通った(`ParentSlot.Fresh`。`ParentSlot.tick_fresh` と同じ運びの 4 経路。周回 271)。 -/
theorem tickPreUpdateStore_fresh (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : Model.Consensus.Protocol.Handlers.NamedStore) (t : Int) :
    Proofs.Consensus.ParentSlot.Fresh st.core
      (Proofs.Consensus.AttestationSource.tickPreUpdateStore c p nr cache e hc cfg nd st t).core := by
  have h0 : Proofs.Consensus.ParentSlot.SStep
      { st with core := { st.core with t := t, s := Model.Consensus.Objects.Parameters.slotOf e t } }
      { st with core := { st.core with t := t, s := Model.Consensus.Objects.Parameters.slotOf e t } } :=
    Proofs.Consensus.ParentSlot.Step.refl _
  have hfin : Proofs.Consensus.ParentSlot.SStep
      { st with core := { st.core with t := t, s := Model.Consensus.Objects.Parameters.slotOf e t } }
      (Proofs.Consensus.AttestationSource.tickPreUpdateStore c p nr cache e hc cfg nd st t) := by
    unfold Proofs.Consensus.AttestationSource.tickPreUpdateStore
    dsimp only
    split_ifs
    all_goals first
      | exact Proofs.Consensus.ParentSlot.namedGoldfishVoteWith_step' c cache e hc nd
          (Proofs.Consensus.ParentSlot.proposeBlockWith_step' c p nr cache e hc cfg nd h0)
      | exact Proofs.Consensus.ParentSlot.namedGoldfishVoteWith_step' c cache e hc nd h0
      | exact Proofs.Consensus.ParentSlot.proposeBlockWith_step' c p nr cache e hc cfg nd h0
      | exact h0
  exact fun B hB => hfin.fresh B hB

/-- 確認の更新の前の段の store の tree の genesis でないブロックの親の slot はブロックの slot より小さい
(`ParentSlot.stateBefore_parentInv` を `tickPreUpdateStore_fresh` で運んだもの。周回 271)。 -/
theorem preUpdateTree_parentInv (w : ValidatorId) (i : Nat) (t : Int) :
    Proofs.Consensus.ParentSlot.ParentInv (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core :=
  (Proofs.Consensus.ParentSlot.stateBefore_parentInv c p a nr s rho i w).of_fresh
    (tickPreUpdateStore_fresh c p nr _ s.e s.hc s.cfg _ _ t)

/-- slot 0 の genuine な確認は genesis。確認評価の tick の slot `q = slotOf e t - 1` が 0 なら、その genuine な確認は genesis。
手書き `actionLiveConfirmed_eq_genesis_zero`(`DecoupledConsensusProofs/Protocol/Grades/WeakGenesis.lean`。手書きの帰納法の
`hconfBoot` の `q = 0` の枝)に当たる。周回 270 に穴として置き、周回 271 に手書きの `confEligible_zero_child_false` と同じ運びで
証明した: eligible なら支持者がいて(得点は支持者の数 `Majority.score_eq_supporters`)、その slot 0 の投票が指す tree のブロック `X` は
slot 0 なので genesis(genesis でない tree のブロックの slot は親の slot より大きい `preUpdateTree_parentInv`)、`C ⪯ X` から
`C` も genesis。手書きと違い anchor が genesis であることは要らない。 -/
theorem genuineConf_slot_zero (hwf : SetupWellFormed c p s) {w : ValidatorId} {i : Nat} {t : Int}
    (hq : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 = 0) {C : Block}
    (hC : Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C) :
    C = Block.Genesis := by
  have hδ : (0 : Int) ≤ s.e.delta := (Proofs.Consensus.Liveness.wf_facts hwf).1.le
  have hel := hC.2
  rw [hq] at hel
  set st := (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core with hst
  have hpos : 0 < (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters st.tree
      (Proofs.Consensus.Goldfish.supportVotes s.e st 0) (Proofs.Consensus.Goldfish.supportVotes s.e st 0) 0 C).size := by
    have h := of_decide_eq_true hel
    rw [Proofs.Consensus.Majority.score_eq_supporters s.e st 0 C hδ] at h
    omega
  obtain ⟨-, u, -, -, -, hus, htu⟩ := Proofs.Consensus.Goldfish.exists_supporter_of_pos hpos
  unfold Model.Consensus.Protocol.ForkChoice.Goldfish.targetsUnder at htu
  split at htu
  · rename_i X hX
    obtain ⟨hXs, hCX⟩ := Bool.and_eq_true_iff.mp htu
    have hXs' : slot X = 0 := by rw [hus] at hXs; exact Nat.le_zero.mp (of_decide_eq_true hXs)
    have hXg : X = Block.Genesis := by
      by_contra hne
      have := preUpdateTree_parentInv c p a nr s rho w i t X
        (Proofs.Consensus.BlockStamps.findRoot?_mem hX).1 hne
      omega
    subst hXg
    simpa [preceq] using hCX
  · exact absurd htu Bool.false_ne_true

/-- `voteDutyFgRootAt` は投票時刻の読みの FG root(時計合わせは FG root を変えない。周回 275)。 -/
theorem voteDutyFgRootAt_eq_read (x : ValidatorId) (k : Nat) :
    voteDutyFgRootAt c p a nr s rho x k =
      Model.Consensus.Protocol.ForkChoice.Goldfish.getFgRoot (Model.Consensus.Protocol.Store.storeToHealing
        (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e k)) x).st.core) :=
  rfl

/-- 段の FG root は前の slot の head の祖先: `1 ≤ d ≤ last` で `PriorConfsBelow d` なら、honest なノード `x` の slot `d + 1` の
投票の務めの読みの FG root は、honest なノード `y` の slot `d` の投票の務めの head の祖先。`confFgRoot_preceq_laterVoteHead` と同じ運び:
FG root の確認の証人(`RootWitness.stateBeforeTime_fgRoot_confirmationWitness`)で genesis か、時刻 `< voteTime (d + 1)` に honest な
署名者が行を出した tick の務めの確認の証人に分け、後者は `laterVoteHead_rowSources_of_prior` に帰納法の仮定 `hprior y` を渡す
(手書き `goldfishCone_succ_of_runFrontierWitnesses` の `hroots` の上界の側。周回 275)。 -/
theorem voteDutyFgRoot_preceq_prevHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) (hprior : PriorConfsBelow c p a nr s rho d)
    {x y : ValidatorId} (hx : rho.honest.contains x = true) (hy : rho.honest.contains y = true) :
    preceq (voteDutyFgRootAt c p a nr s rho x (d + 1)) (voteDutyHeadAt c p a nr s rho y d) = true := by
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
  obtain ⟨⟨⟨⟨⟨⟨hhor0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hsch
  have hlag : (0 : Int) ≤ Model.Consensus.Spec.Constants.participationLag s :=
    (Proofs.Consensus.Constants.period_pos s hfacts.1 hfacts.2.2).le
  have hqh := Proofs.Consensus.JustificationCertificate.quorumHonest_of_sleepyRegime
    (Proofs.Consensus.JustificationCertificate.sorted_validators hwf) hsleep hlag le_rfl (by rw [sub_self]; exact hhor0)
  have hxm : x ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hx
  rw [voteDutyFgRootAt_eq_read]
  rcases Proofs.Consensus.RootWitness.stateBeforeTime_fgRoot_confirmationWitness c p a nr s rho hs hqh hcar hcf hxm
      (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) with
    hg | ⟨-, row, -, t2, i2, -, -, hH, -, ht2, hem, hev, hT⟩
  · rw [hg]
    exact Proofs.Consensus.Blocks.preceq_genesis _
  · exact (laterVoteHead_rowSources_of_prior c p a nr s rho hwf hdom hsleep hhor hd (by omega) hy (hprior y hy)
      ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hH) hem hev ht2).2 _ hT

/-- **保存の段の FG root の互換**: slot `d` で保護された `B` と、honest なノード `x` の slot `d + 1` の読みの FG root は、どちらも
`x` の slot `d` の head の祖先なので互換(`Blocks.preceq_linear`)。`B` が FG root の祖先でなければ FG root ⪯ `B`(手書き
`goldfishCone_step'` の `hrootBelow` の枝に入る前提。周回 275)。 -/
theorem fgRoot_preceq_of_notBelow (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) (hprior : PriorConfsBelow c p a nr s rho d) {B : Block}
    (hB : ProtectedVoteSlot c p a nr s rho d B) {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hroot : ¬ preceq B (voteDutyFgRootAt c p a nr s rho x (d + 1)) = true) :
    preceq (voteDutyFgRootAt c p a nr s rho x (d + 1)) B = true :=
  (Proofs.Consensus.Blocks.preceq_linear (hB.heads x hx)
    (voteDutyFgRoot_preceq_prevHead c p a nr s rho hwf hdom hsleep hhor hd hdlast hprior hx hx)).resolve_left hroot

/-- ノード `x` の slot `k` の投票の務めの読みの anchor(fork choice が `ghost` を始める SG root。手書き `voterAnchorAt`)。
`voteDutyHeadAt` と同じ読み(周回 276)。 -/
def voteDutyAnchorAt (x : ValidatorId) (k : Nat) : Block :=
  let tv := Model.Consensus.Protocol.Schedule.voteTime s.e k
  let n := worldAt (stateBeforeTime c p a nr s rho tv) x
  let hs := Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.Voting.clocked s.e n.st tv).core
  Model.Consensus.Protocol.ForkChoice.Head.getSgRootWith (preparedCache s n tv) s.e s.hc hs
    (Model.Consensus.Protocol.Grades.roundOf s.hc hs.s)

/-- 投票の務めの読みの anchor は投票の務めの head の祖先(`Goldfish.ghost_preceq`。周回 276)。 -/
theorem voteDutyAnchorAt_preceq_head (x : ValidatorId) (k : Nat) :
    preceq (voteDutyAnchorAt c p a nr s rho x k) (voteDutyHeadAt c p a nr s rho x k) = true := by
  unfold voteDutyAnchorAt voteDutyHeadAt Proofs.Consensus.Voting.voteHeadBlock
    Model.Consensus.Protocol.Handlers.getHeadInTreeWith
    Model.Consensus.Protocol.ForkChoice.Head.getHeadInTreeWithLayer
    Model.Consensus.Protocol.ForkChoice.Goldfish.goldfishForkChoice
  dsimp only
  exact Proofs.Consensus.Goldfish.ghost_preceq _ _ _ _

/-- 投票の務めの読みの FG root は anchor の祖先(`ProposerRoot.getSgRootWith_extends_fgRoot`。周回 276)。 -/
theorem fgRoot_preceq_voteDutyAnchorAt (x : ValidatorId) (k : Nat) :
    preceq (voteDutyFgRootAt c p a nr s rho x k) (voteDutyAnchorAt c p a nr s rho x k) = true :=
  Proofs.Consensus.ProposerRoot.getSgRootWith_extends_fgRoot _ _ _ _ _

/-- **段の anchor は前の slot の head の祖先**: `1 ≤ d ≤ last` で `PriorConfsBelow d` なら、honest なノード `x` の slot `d + 1` の
投票の務めの読みの anchor は、honest なノード `y` の slot `d` の投票の務めの head `D` の祖先。手書き
`goldfishCone_succ_of_runFrontierWitnesses` の `hanchors`(`WeakBootstrapSlot.lean` の `getSgRoot_compatible_of_windowHistory_at_read`)を、
互換でなく `D` の祖先の形で出したもの。運びは `fgStep_g1Prefix_positive` と同じ: anchor は G1 の root の active prefix か FG root
(`frameAnchor_preceq_of_g1Prefix`。FG root は `voteDutyFgRoot_preceq_prevHead`)、G1 の root は round `r = roundOf (d + 1)` の G1 の
domain 時刻の読みで凍結した `g0` の祖先(`preparedCache` の `onPhaseTick` の結果か、tick の前の cache の `stateBefore_phase_origin`。
round 0 は凍結が空)、`g0` は grade の担い手(`relativeGradeCarrierAt_of_commonUpper` を `D` で掛ける)の下で窓の round の honest な
行の SG block の祖先。窓の round の行の時刻(action 時刻)と domain 時刻は `R ≥ 3` で投票時刻 `voteTime (d + 1)` より前なので、
行の源は `laterVoteHead_rowSources_of_prior` に帰納法の仮定 `hprior y` を渡して `D` の祖先(周回 276)。 -/
theorem voteDutyAnchor_preceq_prevHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) (hprior : PriorConfsBelow c p a nr s rho d)
    {x y : ValidatorId} (hx : rho.honest.contains x = true) (hy : rho.honest.contains y = true) :
    preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) (voteDutyHeadAt c p a nr s rho y d) = true := by
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hδ := hfacts.1
  have hR := hfacts.2.2
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnd : EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  have hnd' := Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd
  have hxm : x ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hx
  -- 時刻 `< voteTime (d + 1)` の honest な行の源は slot `d` の head の祖先
  have hrows : ∀ (u : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation),
      u ∈ rho.honest.elems → rho.events[i2]? = some (NamedEvent.Tick u t2) →
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) →
      preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i2 t2) (voteDutyHeadAt c p a nr s rho y d) = true ∧
        ∀ T, Proofs.Consensus.RootWitness.fgConfirmationWitnessAt c p a nr s rho u i2 t2 = some T →
          preceq T (voteDutyHeadAt c p a nr s rho y d) = true :=
    fun u i2 t2 row2 hu hev2 hem2 ht2 =>
      laterVoteHead_rowSources_of_prior c p a nr s rho hwf hdom hsleep hhor hd (by omega) hy (hprior y hy)
        ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu) hem2 hev2 ht2
  set r := Model.Consensus.Protocol.Grades.roundOf s.hc (d + 1) with hrdef
  have hrR : r * s.hc.r ≤ d + 1 := Nat.div_mul_le_self (d + 1) s.hc.r
  -- round `r` の G1 の domain 時刻は投票時刻以下
  have hdomle : Model.Consensus.Protocol.Grades.domainTime s.e s.hc r Model.Consensus.Protocol.Grades.GradePhase.G1 ≤
      Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) := by
    have h1 : ((r * s.hc.r : Nat) : Int) ≤ ((d + 1 : Nat) : Int) := by exact_mod_cast hrR
    unfold Model.Consensus.Protocol.Grades.domainTime Model.Consensus.Protocol.Grades.openingTime
      Model.Consensus.Protocol.Schedule.proposalTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
      Model.Consensus.Protocol.Grades.openingSlot
    simp only [Model.Consensus.Protocol.Grades.domainOffset, Int.ofNat_eq_natCast]
    nlinarith
  have hvhor : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon := by
    refine le_trans ?_ hhor
    have hd' : (d : Int) ≤ (last : Int) := by exact_mod_cast hdlast
    unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  -- 窓の round の行の時刻は投票時刻より前
  have hwinTime : ∀ {u : ValidatorId} {row2 : Model.Consensus.Objects.NamedBlocks.NamedAttestation} {t2 : Int},
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
        (Model.Consensus.Execution.Objects.NamedObject.Attest row2) t2 →
      row2.round ∈ Model.Consensus.Protocol.ForkChoice.Goldfish.latestWindow s.hc.etaSG r →
      t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) := by
    intro u row2 t2 hem2 hwin
    have hk := lt_of_mem_latestWindow hwin
    have hkR : (row2.round + 1) * s.hc.r ≤ d + 1 :=
      le_trans (Nat.mul_le_mul_right _ hk) hrR
    have hkR' : row2.round * s.hc.r + 3 ≤ d + 1 := by nlinarith
    have hkI : ((row2.round * s.hc.r : Nat) : Int) + 3 ≤ ((d + 1 : Nat) : Int) := by exact_mod_cast hkR'
    rw [Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem2]
    unfold Model.Consensus.Protocol.Grades.actionTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
      Model.Consensus.Protocol.Grades.openingSlot
    simp only [Int.ofNat_eq_natCast] at hkI ⊢
    nlinarith
  -- round `r` の G1 の読みの grade の担い手
  have hcarrier : Proofs.Consensus.RootWitness.RelativeGradeCarrierAt c p a nr s rho r
      Model.Consensus.Protocol.Grades.GradePhase.G1 := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · intro w _ B hB
      rw [hr0, Proofs.Consensus.FrameCapture.gradeBool_zero] at hB
      exact absurd hB Bool.false_ne_true
    refine relativeGradeCarrierAt_of_commonUpper c p a nr s rho hwf hdom hsleep hrpos _ (le_trans hdomle hvhor)
      (D := voteDutyHeadAt c p a nr s rho y d) ?_ ?_
    · rintro Y ⟨u, i2, t2, row2, hu, hev2, hem2, hwin, rfl⟩
      exact (hrows u i2 t2 row2 hu hev2 hem2 (hwinTime hem2 hwin)).1
    · intro v hv
      refine stateBeforeTime_f_preceq_of_witnesses c p a nr s rho hwf hsleep hv _ ?_
      intro u i2 t2 row2 hu hev2 hem2 ht2 T hT
      exact (hrows u i2 t2 row2 hu hev2 hem2 (lt_of_lt_of_le ht2 hdomle)).2 T hT
  unfold voteDutyAnchorAt Model.Consensus.Protocol.ForkChoice.Head.getSgRootWith
  dsimp only
  refine frameAnchor_preceq_of_g1Prefix ?_ ?_
  · exact voteDutyFgRoot_preceq_prevHead c p a nr s rho hwf hdom hsleep hhor hd hdlast hprior hx hy
  intro g b hg hb
  have hslot : (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.Voting.clocked s.e
      (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x).st
      (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))).core).s = d + 1 :=
    Proofs.Consensus.Voting.slotOf_voteTime s.e hδ (d + 1)
  have hg' : Model.Consensus.Protocol.Grades.phaseResult
      (Model.Consensus.Protocol.Grades.readFrame
        (preparedCache s (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x)
          (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)))
        (Model.Consensus.Protocol.Store.storeToHealing (Proofs.Consensus.Voting.clocked s.e
          (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x).st
          (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))).core) r)
      Model.Consensus.Protocol.Grades.GradePhase.G1 = some (some g) := by
    rw [hslot] at hg
    exact hg
  rw [Proofs.Consensus.FrameCapture.phaseResult_readFrame] at hg'
  obtain ⟨old, hold, hgold⟩ := Proofs.Consensus.Grade2Capture.clipResult_some hg' (Proofs.Consensus.Blocks.preceq_self g)
  obtain ⟨i0, hi0⟩ := Proofs.Consensus.FinalizedAccountable.readAt_eq_stateBefore c p a nr s rho hs
    (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) - 1)
  have hst : stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) =
      stateBefore c p a nr s rho i0 := by
    rw [← hi0, readAt_eq_stateBeforeTime_succ, sub_add_cancel]
  unfold Model.Consensus.Execution.Run.preparedCache at hold
  rw [hst] at hold
  -- G1 の結果は round `r` の G1 の domain 時刻の読みで凍結された `g0` の祖先
  obtain ⟨g0, hgr, hold0⟩ : ∃ g0, Model.Consensus.Protocol.Grades.gradeBool s.e
        (Model.Consensus.Protocol.Grades.gradeView
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho
            (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r Model.Consensus.Protocol.Grades.GradePhase.G1)) x).st.core))
        (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBeforeTime c p a nr s rho
          (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r Model.Consensus.Protocol.Grades.GradePhase.G1)) x).st.core).f
        s.hc.etaSG r
        (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc r Model.Consensus.Protocol.Grades.GradePhase.G1)
        (Model.Consensus.Protocol.Grades.lateTime s.e s.hc r Model.Consensus.Protocol.Grades.GradePhase.G1) g0 = true ∧
      preceq old g0 = true := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · exfalso
      rw [hr0] at hold
      rcases Proofs.Consensus.FrameCapture.onPhaseTick_phase_some hold with ⟨x0, hx0, hxe⟩ | ⟨-, hxe⟩
      · rw [Proofs.Consensus.FrameCapture.stateBefore_phase_zero c p a nr s rho i0 x _ hx0] at hxe
        simp at hxe
      · rw [Proofs.Consensus.FrameCapture.freezeRoot_zero] at hxe
        simp at hxe
    rcases Proofs.Consensus.FrameCapture.onPhaseTick_phase_some hold with ⟨x0, hx0, hxe⟩ | ⟨ht, hxe⟩
    · obtain ⟨old0, rfl, hclip⟩ := Option.map_eq_some_iff.mp hxe.symm
      obtain ⟨j, -, hevj, hx0e⟩ := Proofs.Consensus.FrameCapture.stateBefore_phase_origin c p a nr s rho i0 x hrpos
        Model.Consensus.Protocol.Grades.GradePhase.G1 hx0
      obtain ⟨g0, hfz, hclip0⟩ := Option.map_eq_some_iff.mp hx0e.symm
      have hgr := (Proofs.Consensus.Grade2Capture.freezeRoot_mem hfz).2
      rw [Proofs.Consensus.RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime c p a nr s rho hs hnd' hevj] at hgr
      refine ⟨g0, hgr, ?_⟩
      rw [← hclip, ← hclip0]
      exact Proofs.Consensus.Blocks.preceq_trans (Proofs.Consensus.Grade2Capture.clipGrade_preceq _ _)
        (Proofs.Consensus.Grade2Capture.clipGrade_preceq _ _)
    · obtain ⟨g0, hfz, hclip⟩ := Option.map_eq_some_iff.mp hxe.symm
      have hgr := (Proofs.Consensus.Grade2Capture.freezeRoot_mem hfz).2
      rw [← hst, ht] at hgr
      refine ⟨g0, hgr, ?_⟩
      rw [← hclip]
      exact Proofs.Consensus.Grade2Capture.clipGrade_preceq _ _
  obtain ⟨Y, ⟨u, i2, t2, row2, hu, hev2, hem2, hwin, rfl⟩, hg0Y⟩ := hcarrier x hxm g0 hgr
  exact Proofs.Consensus.Blocks.preceq_trans (Proofs.Consensus.Grade2Capture.activePrefix_preceq hb)
    (Proofs.Consensus.Blocks.preceq_trans hgold (Proofs.Consensus.Blocks.preceq_trans hold0
      (Proofs.Consensus.Blocks.preceq_trans hg0Y (hrows u i2 t2 row2 hu hev2 hem2 (hwinTime hem2 hwin)).1)))

/-- **保存の段の anchor の互換**: slot `d` で保護された `B` と、honest なノード `x` の slot `d + 1` の読みの anchor は、どちらも
`x` の slot `d` の head の祖先なので互換(`Blocks.preceq_linear`)。`B` が anchor の祖先でなければ anchor ⪯ `B`(周回 276)。 -/
theorem anchor_preceq_of_notBelow (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) (hprior : PriorConfsBelow c p a nr s rho d) {B : Block}
    (hB : ProtectedVoteSlot c p a nr s rho d B) {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hanc : ¬ preceq B (voteDutyAnchorAt c p a nr s rho x (d + 1)) = true) :
    preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) B = true :=
  (Proofs.Consensus.Blocks.preceq_linear (hB.heads x hx)
    (voteDutyAnchor_preceq_prevHead c p a nr s rho hwf hdom hsleep hhor hd hdlast hprior hx hx)).resolve_left hanc

/-- **`heads` の anchor の枝**: `B` が読みの anchor の祖先なら head の祖先(`voteDutyAnchorAt_preceq_head`)なので、`heads` は `B` が
anchor の祖先でない honest なノードについて示せばよい(anchor は FG root を延ばすので `heads_of_notBelowFgRoot` より強い。周回 276)。 -/
theorem heads_of_notBelowAnchor {k : Nat} {B : Block}
    (habove : ∀ x, rho.honest.contains x = true → ¬ preceq B (voteDutyAnchorAt c p a nr s rho x k) = true →
      preceq B (voteDutyHeadAt c p a nr s rho x k) = true) :
    ∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x k) = true := by
  intro x hx
  by_cases h : preceq B (voteDutyAnchorAt c p a nr s rho x k) = true
  · exact Proofs.Consensus.Blocks.preceq_trans h (voteDutyAnchorAt_preceq_head c p a nr s rho x k)
  · exact habove x hx h

/-- ノード `x` の slot `k` の投票の務めの読みの store(`voteDutyHeadAt` / `voteDutyAnchorAt` と同じ読み。周回 278)。 -/
def voteDutyStoreAt (x : ValidatorId) (k : Nat) : Model.Consensus.Protocol.Store.Store :=
  (Proofs.Consensus.Voting.clocked s.e
    (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e k)) x).st
    (Model.Consensus.Protocol.Schedule.voteTime s.e k)).core

/-- **投票の務めの head は過半の支持を通る**: `x` の slot `k` の読みの voter view(投票 `voterView`・支持の投票 `voterSupportView`、
slot `st.s - 1`)で `B` の支持者が参加者の過半、支持の投票が投票の部分集合、歩みの tree `voterFilteredBlockTree` に重複が無く、
anchor から `B` までの途中がその tree にあり、anchor ⪯ `B` なら、`B` は投票の務めの head の祖先
(`Majority.goldfishForkChoice_passes_supporter_majority`。手書き `goldfish_fork_choice_passes_supporter_majority`)。段の 2 つの穴は
これを読みの view の数え上げに渡す形で閉じる見込み(周回 278)。 -/
theorem voteDutyHead_passes_supporter_majority (x : ValidatorId) (k : Nat) {B : Block}
    (hnd : (Model.Consensus.Protocol.Handlers.voterFilteredBlockTree s.e (voteDutyStoreAt c p a nr s rho x k)
      (voteDutyStoreAt c p a nr s rho x k).s).elems.Nodup)
    (hsub : ∀ u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
          (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
        (voteDutyStoreAt c p a nr s rho x k).s).elems,
      u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
          (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
        (voteDutyStoreAt c p a nr s rho x k).s).elems)
    (hmaj : Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) B).size)
    (hAB : preceq (voteDutyAnchorAt c p a nr s rho x k) B = true)
    (hpath : ∀ C, preceq (voteDutyAnchorAt c p a nr s rho x k) C = true → C ≠ voteDutyAnchorAt c p a nr s rho x k →
      preceq C B = true →
      C ∈ (Model.Consensus.Protocol.Handlers.voterFilteredBlockTree s.e (voteDutyStoreAt c p a nr s rho x k)
        (voteDutyStoreAt c p a nr s rho x k).s).elems) :
    preceq B (voteDutyHeadAt c p a nr s rho x k) = true := by
  unfold voteDutyHeadAt Proofs.Consensus.Voting.voteHeadBlock
    Model.Consensus.Protocol.Handlers.getHeadInTreeWith
    Model.Consensus.Protocol.ForkChoice.Head.getHeadInTreeWithLayer
  dsimp only
  exact Proofs.Consensus.Majority.goldfishForkChoice_passes_supporter_majority s.e _ _ _ _ hnd hsub hmaj hAB hpath

/-- 投票の歩みの tree `voterFilteredBlockTree`(store の tree の 4 段の絞り込み: 処理済み・finalized の子孫・viable・FG root の下)は、
store の tree の要素に重複が無ければ重複が無い(`getFilteredBlockTree_nodup` と同じ運び。周回 279)。 -/
theorem voterFilteredBlockTree_nodup {e : Model.Consensus.Objects.Parameters.ProtocolEnv}
    {st : Model.Consensus.Protocol.Store.Store} (k : Nat) (hnd : st.tree.elems.Nodup) :
    (Model.Consensus.Protocol.Handlers.voterFilteredBlockTree e st k).elems.Nodup := by
  unfold Model.Consensus.Protocol.Handlers.voterFilteredBlockTree
    Model.Consensus.Protocol.ForkChoice.Goldfish.getFilteredBlockTreeFrom
    Model.Consensus.Protocol.ForkChoice.Goldfish.viableTree
    Model.Consensus.Protocol.ForkChoice.Goldfish.finalizedDescendants
    Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree NaruStd.Set.filter
  exact (((hnd.filter _).filter _).filter _).filter _

/-- 投票の務めの読みの歩みの tree に重複は無い(`voteDutyHead_passes_supporter_majority` の前提 `hnd`)。読みの store は
`stateBeforeTime` の `x` の store の時計を合わせただけなので、tree は `Trees.stateBeforeTime_treeInv` の欄 `nodup` を受け継ぐ
(周回 279)。 -/
theorem voteDutyStore_voterFilteredBlockTree_nodup (x : ValidatorId) (k : Nat) :
    (Model.Consensus.Protocol.Handlers.voterFilteredBlockTree s.e (voteDutyStoreAt c p a nr s rho x k)
      (voteDutyStoreAt c p a nr s rho x k).s).elems.Nodup := by
  apply voterFilteredBlockTree_nodup
  unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
  exact (Proofs.Consensus.Trees.stateBeforeTime_treeInv c p a nr s rho _ x).nodup

/-- voter view の pooled の部分: 解決の印 `tau` が freeze より前なら受信の印も freeze より前(`Majority.timestampVote_before_of_tau`)
なので、支持の pooled は投票の pooled に含まれる(周回 279)。 -/
theorem voterSupportView_pooled_sub (e : Model.Consensus.Objects.Parameters.ProtocolEnv)
    (st : Model.Consensus.Protocol.Store.Store) (k : Nat) (u : GoldfishVote)
    (hu : u ∈ (NaruStd.Set.filter (Model.Consensus.Protocol.StoreBase.pool
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st)) (k - 1))
      (fun vote => Model.Consensus.Objects.Time.occurrenceBefore
        (Model.Consensus.Protocol.StoreBase.tau
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st)) vote)
        (Model.Consensus.Protocol.Schedule.viewFreeze e (k - 1)))).elems) :
    u ∈ (NaruStd.Set.filter (Model.Consensus.Protocol.StoreBase.pool
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st)) (k - 1))
      (fun vote => Model.Consensus.Objects.Time.occurrenceBefore
        (NaruStd.Table.get? (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
          (Model.Consensus.Protocol.Store.storeToHealing st)).timestampVote vote)
        (Model.Consensus.Protocol.Schedule.viewFreeze e (k - 1)))).elems := by
  obtain ⟨hpool, hτ⟩ := (Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hu
  rw [Proofs.Consensus.Trees.mem_filter_iff]
  exact ⟨hpool, Proofs.Consensus.Majority.timestampVote_before_of_tau (st := st) hτ le_rfl⟩

/-- **支持の voter view は投票の voter view に含まれる**(`voteDutyHead_passes_supporter_majority` の前提 `hsub` の形): pooled の部分は
`voterSupportView_pooled_sub`、carried の部分は store の tree のブロックの運ぶ支持の投票がそのブロックの運ぶ投票に含まれること
(`hcar`。受理の検査 `carriedSupportWellFormed` からの run の不変条件。周回 280 の `voteDutyStore_tree_carried`)から出る(周回 279)。 -/
theorem voterSupportView_sub_voterView (e : Model.Consensus.Objects.Parameters.ProtocolEnv)
    (st : Model.Consensus.Protocol.Store.Store) (k : Nat)
    (hcar : ∀ b ∈ st.tree.elems, ∀ u ∈ gfSupportVotes b, u ∈ gfVotes b) :
    ∀ u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView e
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st)) k).elems,
      u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterView e
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st)) k).elems := by
  intro u hu
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterSupportView at hu
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterView
  dsimp only at hu ⊢
  rw [Proofs.Consensus.Sets.mem_union_iff Proofs.Consensus.Orders.gv_compare_eq_iff] at hu ⊢
  rcases hu with hu | hu
  · exact Or.inl (voterSupportView_pooled_sub e st k u hu)
  · right
    rw [Proofs.Consensus.Sets.mem_flatMap_iff Proofs.Consensus.Orders.gv_compare_eq_iff] at hu ⊢
    obtain ⟨b, hb, hub⟩ := hu
    refine ⟨b, hb, ?_⟩
    rw [Proofs.Consensus.Sets.mem_toSet_iff Proofs.Consensus.Orders.gv_compare_eq_iff] at hub ⊢
    obtain ⟨hub, hcond⟩ := List.mem_filter.mp hub
    have hbt := ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hb).1
    simp only [Bool.and_eq_true] at hcond
    exact List.mem_filter.mpr ⟨hcar b hbt u hub, hcond.2⟩

/-- `voteDutyHead_passes_supporter_majority` の前提 `hnd` を `voteDutyStore_voterFilteredBlockTree_nodup` で、`hsub` を
`voterSupportView_sub_voterView` で外した形。残りの前提は、読みの store の tree の運ぶ支持の投票が運ぶ投票に含まれること(`hcar`)、
読みの voter view での `B` の支持者の過半(`hmaj`)、anchor ⪯ `B`(`hAB`)、anchor から `B` までの途中が歩みの tree にあること
(`hpath`)(周回 279)。 -/
theorem voteDutyHead_passes_supporter_majority_of_carried (x : ValidatorId) (k : Nat) {B : Block}
    (hcar : ∀ b ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems, ∀ u ∈ gfSupportVotes b, u ∈ gfVotes b)
    (hmaj : Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) B).size)
    (hAB : preceq (voteDutyAnchorAt c p a nr s rho x k) B = true)
    (hpath : ∀ C, preceq (voteDutyAnchorAt c p a nr s rho x k) C = true → C ≠ voteDutyAnchorAt c p a nr s rho x k →
      preceq C B = true →
      C ∈ (Model.Consensus.Protocol.Handlers.voterFilteredBlockTree s.e (voteDutyStoreAt c p a nr s rho x k)
        (voteDutyStoreAt c p a nr s rho x k).s).elems) :
    preceq B (voteDutyHeadAt c p a nr s rho x k) = true :=
  voteDutyHead_passes_supporter_majority c p a nr s rho x k
    (voteDutyStore_voterFilteredBlockTree_nodup c p a nr s rho x k)
    (voterSupportView_sub_voterView s.e _ _ hcar) hmaj hAB hpath

/-- 投票の務めの読みの store の tree のブロックの運ぶ支持の投票は運ぶ投票に含まれる(`voteDutyHead_passes_supporter_majority_of_carried`
の前提 `hcar`)。読みの store は `stateBeforeTime` の `x` の store の時計を合わせただけなので、`CarriedSupport.stateBeforeTime_tree_carried`
(run の前提 `DeliveryWellFormed` と提案の組み立てからの不変条件)を受け継ぐ(周回 280)。 -/
theorem voteDutyStore_tree_carried (hdw : DeliveryWellFormed c p a nr s rho) (x : ValidatorId) (k : Nat) :
    ∀ b ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems, ∀ u ∈ gfSupportVotes b, u ∈ gfVotes b := by
  unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
  exact Proofs.Consensus.CarriedSupport.stateBeforeTime_tree_carried c p a nr s rho hdw _ x

/-- `voteDutyHead_passes_supporter_majority_of_carried` の前提 `hcar` を `voteDutyStore_tree_carried`(run の前提
`DeliveryWellFormed`)で外した形。残りの前提は、読みの voter view での `B` の支持者の過半(`hmaj`)、anchor ⪯ `B`(`hAB`)、
anchor から `B` までの途中が歩みの tree にあること(`hpath`)(周回 280)。 -/
theorem voteDutyHead_passes_supporter_majority_of_delivery (hdw : DeliveryWellFormed c p a nr s rho)
    (x : ValidatorId) (k : Nat) {B : Block}
    (hmaj : Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) B).size)
    (hAB : preceq (voteDutyAnchorAt c p a nr s rho x k) B = true)
    (hpath : ∀ C, preceq (voteDutyAnchorAt c p a nr s rho x k) C = true → C ≠ voteDutyAnchorAt c p a nr s rho x k →
      preceq C B = true →
      C ∈ (Model.Consensus.Protocol.Handlers.voterFilteredBlockTree s.e (voteDutyStoreAt c p a nr s rho x k)
        (voteDutyStoreAt c p a nr s rho x k).s).elems) :
    preceq B (voteDutyHeadAt c p a nr s rho x k) = true :=
  voteDutyHead_passes_supporter_majority_of_carried c p a nr s rho x k
    (voteDutyStore_tree_carried c p a nr s rho hdw x k) hmaj hAB hpath

/-- **読みの voter view での cone の支持は過半の支持を与える**(段の 2 つの穴の橋に残る前提 `hmaj` の形): `x` の slot `k` の読みの
voter view の参加者が slot `st.s - 1` の committee に収まり(手書き `corePreparedVoteViewValid`)、honest な委員がその view で equivocate
せず(手書き `coreVoterViewNoHonestEquivocation`)、支持の voter view に `B` 以下を指す slot `st.s - 1` の投票を持てば(手書き
`coneSupport_of_named_votes` の `vote` の欄)、`B` の支持者は参加者の過半。committee の整列は `SetupWellFormed`、honest 過半は
`HonestCommittees` の slot `st.s - 1` の不等式。`Majority.supporterMajority_of_cone`(手書き `supporterMajority_of_cone`)を読みの
view に掛けた形(周回 290)。 -/
theorem voteDutyStore_supporterMajority_of_cone (hwf : SetupWellFormed c p s) (hhc : HonestCommittees c rho.honest)
    (x : ValidatorId) (k : Nat) {B : Block}
    (hPC : ∀ v ∈ (Model.Consensus.Protocol.ForkChoice.Goldfish.rawParticipants
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)).elems,
      v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems)
    (hno : ∀ v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems, v ∈ rho.honest.elems →
      Model.Consensus.Protocol.Schedule.equivocates
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s) v = false)
    (hvote : ∀ v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems, v ∈ rho.honest.elems →
      ∃ u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s).elems,
        u.valIndex = v ∧ u.slot = (voteDutyStoreAt c p a nr s rho x k).s - 1 ∧
        Model.Consensus.Protocol.ForkChoice.Goldfish.targetsUnder
          (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree B u = true) :
    Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) B).size :=
  Proofs.Consensus.Majority.supporterMajority_of_cone s.e
    (Proofs.Consensus.Majority.committee_sorted hwf _) (Proofs.Consensus.Majority.honestCommittees_at hhc _)
    hPC hno hvote

/-- store の voter view(slot `k`)の参加者は slot `k - 1` の committee の要素: pooled の部分は pool の不変条件 `Votes.PoolInv`
(鍵 `k - 1` の pool の投票は slot が `k - 1` で投票者が committee の要素)、carried の部分は tree のブロックの運ぶ投票の投票者が committee
の要素であること(`CarriedCommittee.BlockCommittee`)と、view の絞り込み(投票の slot が `k - 1`)から。手書き
`voteSetValid_voter_view_of_carried` の committee の半分(周回 291)。 -/
theorem voterView_participants_committee (e : Model.Consensus.Objects.Parameters.ProtocolEnv)
    (st : Model.Consensus.Protocol.Store.Store) (k : Nat) (hp : Proofs.Consensus.Votes.PoolInv c st)
    (htree : ∀ b ∈ st.tree.elems, Proofs.Consensus.CarriedCommittee.BlockCommittee c b) :
    ∀ v ∈ (Model.Consensus.Protocol.ForkChoice.Goldfish.rawParticipants
        (Model.Consensus.Protocol.ForkChoice.Views.voterView e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st))
          k)).elems,
      v ∈ (c (k - 1)).elems := by
  intro v hv
  obtain ⟨hv, -⟩ := (Proofs.Consensus.Majority.mem_rawParticipants_iff _ _).mp hv
  obtain ⟨u, hu, rfl⟩ := (Proofs.Consensus.Goldfish.mem_voters_iff _ _).mp hv
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterView at hu
  dsimp only at hu
  rw [Proofs.Consensus.Sets.mem_union_iff Proofs.Consensus.Orders.gv_compare_eq_iff] at hu
  rcases hu with hu | hu
  · have hpool := ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hu).1
    exact (hp.mem (k := k - 1) hpool).2
  · rw [Proofs.Consensus.Sets.mem_flatMap_iff Proofs.Consensus.Orders.gv_compare_eq_iff] at hu
    obtain ⟨b, hb, hub⟩ := hu
    rw [Proofs.Consensus.Sets.mem_toSet_iff Proofs.Consensus.Orders.gv_compare_eq_iff] at hub
    obtain ⟨hub, hslot⟩ := List.mem_filter.mp hub
    have hbt := ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hb).1
    have hc := htree b hbt u hub
    rw [beq_iff_eq] at hslot
    rw [hslot] at hc
    exact (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hc

/-- **投票の務めの読みの voter view の参加者は slot `st.s - 1` の committee の要素**(`voteDutyStore_supporterMajority_of_cone` の前提
`hPC`。手書き `corePreparedVoteViewValid` の committee の半分)。読みの store は `stateBeforeTime` の `x` の store の時計を合わせただけで、
pool の不変条件は前提なし(`CarriedCommittee.stateBeforeTime_pool`)、tree のブロックの運ぶ投票の committee は run の前提
`DeliveryWellFormed` と提案の組み立てからの不変条件(`CarriedCommittee.stateBeforeTime_tree_committee`)(周回 291)。 -/
theorem voteDutyStore_participants_committee (hdw : DeliveryWellFormed c p a nr s rho) (x : ValidatorId) (k : Nat) :
    ∀ v ∈ (Model.Consensus.Protocol.ForkChoice.Goldfish.rawParticipants
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)).elems,
      v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems := by
  apply voterView_participants_committee c s.e
  · unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
    exact Proofs.Consensus.CarriedCommittee.stateBeforeTime_pool c p a nr s rho _ x
  · unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
    exact Proofs.Consensus.CarriedCommittee.stateBeforeTime_tree_committee c p a nr s rho hdw _ x

/-- `voteDutyStore_supporterMajority_of_cone` の前提 `hPC` を `voteDutyStore_participants_committee`(run の前提
`DeliveryWellFormed`)で外した形。`hmaj` の残りは、honest な委員が読みの voter view で equivocate しないこと(`hno`。手書き
`coreVoterViewNoHonestEquivocation`)と、honest な委員が支持の voter view に `B` 以下を指す投票を持つこと(`hvote`。手書き
`coneSupport_of_named_votes` の `vote`)(周回 291)。 -/
theorem voteDutyStore_supporterMajority_of_cone_delivery (hwf : SetupWellFormed c p s)
    (hhc : HonestCommittees c rho.honest) (hdw : DeliveryWellFormed c p a nr s rho)
    (x : ValidatorId) (k : Nat) {B : Block}
    (hno : ∀ v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems, v ∈ rho.honest.elems →
      Model.Consensus.Protocol.Schedule.equivocates
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s) v = false)
    (hvote : ∀ v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems, v ∈ rho.honest.elems →
      ∃ u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s).elems,
        u.valIndex = v ∧ u.slot = (voteDutyStoreAt c p a nr s rho x k).s - 1 ∧
        Model.Consensus.Protocol.ForkChoice.Goldfish.targetsUnder
          (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree B u = true) :
    Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) B).size :=
  voteDutyStore_supporterMajority_of_cone c p a nr s rho hwf hhc x k
    (voteDutyStore_participants_committee c p a nr s rho hdw x k) hno hvote

/-- store の voter view(slot `k`)の honest な投票者の投票は、slot が `k - 1` で、その投票者が実際に出した投票: pooled の部分は
pool の不変条件(slot)と前提 `hpool`(pool の honest な投票は出した投票)、carried の部分は view の絞り込み(slot)と前提 `htree`
(tree のブロックの運ぶ honest な投票は出した投票)から。手書き `coreEmitsOfVoteVisible` に当たる(周回 292)。 -/
theorem voterView_honest_emitted (e : Model.Consensus.Objects.Parameters.ProtocolEnv)
    (st : Model.Consensus.Protocol.Store.Store) (k : Nat) (hp : Proofs.Consensus.Votes.PoolInv c st)
    (hpool : ∀ u ∈ (Model.Consensus.Protocol.Store.storePool st (k - 1)).elems, rho.honest.contains u.valIndex = true →
      ∃ t, Statements.Consensus.Spec.Execution.Emits c p a nr s rho u.valIndex
        (Model.Consensus.Execution.Objects.NamedObject.GfVote u) t)
    (htree : ∀ b ∈ st.tree.elems, ∀ u ∈ gfVotes b, rho.honest.contains u.valIndex = true →
      ∃ t, Statements.Consensus.Spec.Execution.Emits c p a nr s rho u.valIndex
        (Model.Consensus.Execution.Objects.NamedObject.GfVote u) t)
    {u : GoldfishVote}
    (hu : u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterView e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st))
      k).elems)
    (hh : rho.honest.contains u.valIndex = true) :
    u.slot = k - 1 ∧ ∃ t, Statements.Consensus.Spec.Execution.Emits c p a nr s rho u.valIndex
      (Model.Consensus.Execution.Objects.NamedObject.GfVote u) t := by
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterView at hu
  dsimp only at hu
  rw [Proofs.Consensus.Sets.mem_union_iff Proofs.Consensus.Orders.gv_compare_eq_iff] at hu
  rcases hu with hu | hu
  · have hpool' := ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hu).1
    exact ⟨(hp.mem (k := k - 1) hpool').1, hpool u hpool' hh⟩
  · rw [Proofs.Consensus.Sets.mem_flatMap_iff Proofs.Consensus.Orders.gv_compare_eq_iff] at hu
    obtain ⟨b, hb, hub⟩ := hu
    rw [Proofs.Consensus.Sets.mem_toSet_iff Proofs.Consensus.Orders.gv_compare_eq_iff] at hub
    obtain ⟨hub, hslot⟩ := List.mem_filter.mp hub
    have hbt := ((Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hb).1
    rw [beq_iff_eq] at hslot
    exact ⟨hslot, htree b hbt u hub hh⟩

/-- **honest な投票者は store の voter view で equivocate しない**(`voterView_honest_emitted` の前提の下で): view の honest な `v` の
投票はどれも slot `k - 1` の `v` の出した投票なので、`ScheduleWellFormed` の下で等しい(`Voting.emits_gfVote_unique`)。view は整列
(pooled は pool の `toSet` の絞り込み、`union` は整列の `insert` の畳み込み)なので、`votesBy` の大きさは 1 以下(周回 292)。 -/
theorem voterView_no_honest_equivocation (hsch : ScheduleWellFormed s rho)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv)
    (st : Model.Consensus.Protocol.Store.Store) (k : Nat) (hp : Proofs.Consensus.Votes.PoolInv c st)
    (hpool : ∀ u ∈ (Model.Consensus.Protocol.Store.storePool st (k - 1)).elems, rho.honest.contains u.valIndex = true →
      ∃ t, Statements.Consensus.Spec.Execution.Emits c p a nr s rho u.valIndex
        (Model.Consensus.Execution.Objects.NamedObject.GfVote u) t)
    (htree : ∀ b ∈ st.tree.elems, ∀ u ∈ gfVotes b, rho.honest.contains u.valIndex = true →
      ∃ t, Statements.Consensus.Spec.Execution.Emits c p a nr s rho u.valIndex
        (Model.Consensus.Execution.Objects.NamedObject.GfVote u) t)
    {v : ValidatorId} (hv : rho.honest.contains v = true) :
    Model.Consensus.Protocol.Schedule.equivocates
      (Model.Consensus.Protocol.ForkChoice.Views.voterView e
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st))
        k) v = false := by
  have hsorted : Proofs.Consensus.Majority.SortedLt (Model.Consensus.Protocol.ForkChoice.Views.voterView e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st))
      k) := by
    unfold Model.Consensus.Protocol.ForkChoice.Views.voterView NaruStd.Set.union
    dsimp only
    apply Proofs.Consensus.Majority.SortedLt.foldl_insert Proofs.Consensus.Orders.gv_compare_eq_iff
      Proofs.Consensus.Majority.gv_lt_trans Proofs.Consensus.Majority.gv_gt_lt
    apply Proofs.Consensus.Majority.SortedLt.filter
    unfold Model.Consensus.Protocol.StoreBase.pool
    exact Proofs.Consensus.Majority.SortedLt.toSet Proofs.Consensus.Orders.gv_compare_eq_iff
      Proofs.Consensus.Majority.gv_lt_trans Proofs.Consensus.Majority.gv_gt_lt _
  unfold Model.Consensus.Protocol.Schedule.equivocates
  rw [decide_eq_false_iff_not]
  intro h2
  have hnd : (Model.Consensus.Protocol.Schedule.votesBy (Model.Consensus.Protocol.ForkChoice.Views.voterView e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st))
      k) v).elems.Nodup := by
    unfold Model.Consensus.Protocol.Schedule.votesBy
    exact Proofs.Consensus.Majority.SortedLt.nodup Proofs.Consensus.Majority.gv_irrefl
      (Proofs.Consensus.Majority.SortedLt.filter hsorted _)
  have hle : (Model.Consensus.Protocol.Schedule.votesBy (Model.Consensus.Protocol.ForkChoice.Views.voterView e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st))
      k) v).elems.length ≤ 1 := by
    apply Proofs.Consensus.Majority.length_le_one_of_nodup hnd
    intro x hx y hy
    rw [Proofs.Consensus.Goldfish.mem_votesBy_iff] at hx hy
    obtain ⟨hxs, t₁, he₁⟩ := voterView_honest_emitted c p a nr s rho e st k hp hpool htree hx.1 (by rw [hx.2]; exact hv)
    obtain ⟨hys, t₂, he₂⟩ := voterView_honest_emitted c p a nr s rho e st k hp hpool htree hy.1 (by rw [hy.2]; exact hv)
    rw [hx.2] at he₁
    rw [hy.2] at he₂
    exact Proofs.Consensus.Voting.emits_gfVote_unique c p a nr s rho hsch he₁ he₂ (hxs.trans hys.symm)
  unfold NaruStd.Set.size at h2
  omega

/-- **投票の務めの読みの voter view で honest な委員は equivocate しない**(`voteDutyStore_supporterMajority_of_cone_delivery` の前提
`hno`。手書き `coreVoterViewNoHonestEquivocation`): 読みの store は `stateBeforeTime` の `x` の store の時計を合わせただけで、
pool の honest な投票は出した投票(`PoolFrom.pool_genuine`)、tree のブロックは bodies の名前付きブロックの消去(`Carrier.StoreInv.named`)で、
bodies のブロックは genesis(運ぶ投票は空)か処理したブロック(`Attribution.bodies_processed`)なので、その運ぶ honest な投票は出した投票
(`UnforgeableSignatures` の carried の半分)。前提は `ScheduleWellFormed` と `UnforgeableSignatures`(周回 292)。 -/
theorem voteDutyStore_no_honest_equivocation (hsch : ScheduleWellFormed s rho)
    (hunf : UnforgeableSignatures c p a nr s rho) (x : ValidatorId) (k : Nat) :
    ∀ v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems, v ∈ rho.honest.elems →
      Model.Consensus.Protocol.Schedule.equivocates
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s) v = false := by
  intro v _ hv
  have hvc : rho.honest.contains v = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hv
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have heq := Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs
    (Model.Consensus.Protocol.Schedule.voteTime s.e k)
  have hinv : Proofs.Consensus.Carrier.StoreInv s.e s.cfg
      (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e k)) x).st := by
    unfold stateBeforeTime
    exact Proofs.Consensus.Carrier.foldl_worldStep_inv c p a nr s _ (Proofs.Consensus.Carrier.worldInit_inv s.e s.cfg) x
  apply voterView_no_honest_equivocation c p a nr s rho hsch s.e
  · unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
    exact Proofs.Consensus.CarriedCommittee.stateBeforeTime_pool c p a nr s rho _ x
  · intro u hu hh
    unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked at hu
    have hu' := (Proofs.Consensus.Votes.mem_storePool_iff _ _ _).mp hu
    rw [heq] at hu'
    exact Proofs.Consensus.PoolFrom.pool_genuine c p a nr s rho hunf hu' hh
  · intro b hb u hu hh
    unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked at hb
    obtain ⟨D, hD, rfl⟩ := hinv.named b hb
    rw [Proofs.Consensus.PoolFrom.gfVotes_eraseBlock] at hu
    rw [heq] at hD
    rcases Proofs.Consensus.Attribution.bodies_processed c p a nr s rho x _ D hD with rfl | ⟨t, hproc⟩
    · exact absurd hu (by simp [Model.Consensus.Objects.NamedBlocks.namedGfVotes])
    · obtain ⟨t2, -, hem⟩ := hunf.2 x _ t hproc _ (Proofs.Consensus.PoolFrom.carries_gfVote hu) u.valIndex ⟨hh, rfl⟩
      exact ⟨t2, hem⟩
  · exact hvc

/-- `voteDutyStore_supporterMajority_of_cone_delivery` の前提 `hno` を `voteDutyStore_no_honest_equivocation`(run の前提
`ScheduleWellFormed` / `UnforgeableSignatures`)で外した形。`hmaj` に残る前提は、honest な委員が支持の voter view に `B` 以下を指す
slot `st.s - 1` の投票を持つこと(`hvote`。手書き `coneSupport_of_named_votes` の `vote`)だけ(周回 292)。 -/
theorem voteDutyStore_supporterMajority_of_cone_run (hwf : SetupWellFormed c p s)
    (hhc : HonestCommittees c rho.honest) (hdw : DeliveryWellFormed c p a nr s rho)
    (hsch : ScheduleWellFormed s rho) (hunf : UnforgeableSignatures c p a nr s rho)
    (x : ValidatorId) (k : Nat) {B : Block}
    (hvote : ∀ v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems, v ∈ rho.honest.elems →
      ∃ u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s).elems,
        u.valIndex = v ∧ u.slot = (voteDutyStoreAt c p a nr s rho x k).s - 1 ∧
        Model.Consensus.Protocol.ForkChoice.Goldfish.targetsUnder
          (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree B u = true) :
    Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) B).size :=
  voteDutyStore_supporterMajority_of_cone_delivery c p a nr s rho hwf hhc hdw x k
    (voteDutyStore_no_honest_equivocation c p a nr s rho hsch hunf x k) hvote

/-- **pool の投票は支持の voter view にあり `B` 以下を指す**(store の形。手書き `mem_voter_support_view_of_pool` と
`stampedBefore_resolution_of`): slot `k - 1` のバケツの投票 `u` の head の root を引いたブロック `X`(slot が投票の slot 以下)の受信の印と、
投票の受信の印がどちらも凍結時刻 `viewFreeze e (k - 1)` より前なら、解決の印 `tau` も凍結より前(`BlockStamps.storeTau_before`)なので
`u` は支持の voter view の pooled の部分にあり、`B ⪯ X` なら `u` は `B` 以下を指す(`Goldfish.targetsUnder_iff`。周回 293)。 -/
theorem voterSupportView_pooled_targets (e : Model.Consensus.Objects.Parameters.ProtocolEnv)
    (st : Model.Consensus.Protocol.Store.Store) (k : Nat) {u : GoldfishVote} {X B : Block}
    (hpool : u ∈ (Model.Consensus.Protocol.StoreBase.pool
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st))
      (k - 1)).elems)
    (hr : findRoot? st.tree u.head = some X) (hsl : slot X ≤ u.slot)
    (hv : Model.Consensus.Objects.Time.occurrenceBefore (NaruStd.Table.get? st.timestampVote u)
      (Model.Consensus.Protocol.Schedule.viewFreeze e (k - 1)) = true)
    (hb : Model.Consensus.Objects.Time.occurrenceBefore (NaruStd.Table.get? st.timestampBlock X)
      (Model.Consensus.Protocol.Schedule.viewFreeze e (k - 1)) = true)
    (hBX : preceq B X = true) :
    u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView e
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish (Model.Consensus.Protocol.Store.storeToHealing st)) k).elems ∧
      Model.Consensus.Protocol.ForkChoice.Goldfish.targetsUnder
        (Model.Consensus.Protocol.Store.storeToHealing st).tree B u = true := by
  refine ⟨?_, (Proofs.Consensus.Goldfish.targetsUnder_iff _ _ _).mpr ⟨X, hr, hsl, hBX⟩⟩
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterSupportView
  dsimp only
  rw [Proofs.Consensus.Sets.mem_union_iff Proofs.Consensus.Orders.gv_compare_eq_iff]
  left
  rw [Proofs.Consensus.Trees.mem_filter_iff]
  exact ⟨hpool, Proofs.Consensus.BlockStamps.storeTau_before hr hsl hv hb⟩

/-- `voteDutyStore_supporterMajority_of_cone_run` の前提 `hvote`(支持の voter view の投票)を、読みの store の pool と tree と
2 つの受信の印で書いた形(手書き `coneSupport_of_named_votes` の `vote` の、`hcutoff` / `havailable` を受けた後の段)。
読みの tree は root が要素を決める(`tickTree_root_inj`。`stateBeforeTime` は `stateBefore` の添字 `idxLt` と一致:
`ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt`)ので、tree の `X` の root は `X` に解決し(`findRoot?_of_mem`)、
`voterSupportView_pooled_targets` に渡る。残る前提 `hpv` は、honest な委員ごとに、読みの pool の slot `st.s - 1` の投票 `u` と、
その head を root に持つ読みの tree のブロック `X`(slot が `st.s - 1` 以下で `B` の子孫)があり、投票と `X` の受信の印が
凍結時刻より前であること(周回 293)。 -/
theorem voteDutyStore_supportVote_of_pool (hsleep : SleepyRegime c p a nr s rho 0) (hsch : ScheduleWellFormed s rho)
    {x : ValidatorId} (hx : rho.honest.contains x = true) (k : Nat) {B : Block}
    (hpv : ∀ v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems, v ∈ rho.honest.elems →
      ∃ u X, u ∈ (Model.Consensus.Protocol.StoreBase.pool
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems ∧
        u.valIndex = v ∧ u.slot = (voteDutyStoreAt c p a nr s rho x k).s - 1 ∧
        X ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems ∧ root X = u.head ∧
        slot X ≤ (voteDutyStoreAt c p a nr s rho x k).s - 1 ∧
        Model.Consensus.Objects.Time.occurrenceBefore
          (NaruStd.Table.get? (voteDutyStoreAt c p a nr s rho x k).timestampVote u)
          (Model.Consensus.Protocol.Schedule.viewFreeze s.e ((voteDutyStoreAt c p a nr s rho x k).s - 1)) = true ∧
        Model.Consensus.Objects.Time.occurrenceBefore
          (NaruStd.Table.get? (voteDutyStoreAt c p a nr s rho x k).timestampBlock X)
          (Model.Consensus.Protocol.Schedule.viewFreeze s.e ((voteDutyStoreAt c p a nr s rho x k).s - 1)) = true ∧
        preceq B X = true) :
    ∀ v ∈ (c ((voteDutyStoreAt c p a nr s rho x k).s - 1)).elems, v ∈ rho.honest.elems →
      ∃ u ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s).elems,
        u.valIndex = v ∧ u.slot = (voteDutyStoreAt c p a nr s rho x k).s - 1 ∧
        Model.Consensus.Protocol.ForkChoice.Goldfish.targetsUnder
          (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree B u = true := by
  intro v hvc hvh
  obtain ⟨u, X, hpool, hval, hus, hX, hroot, hXs, hv, hb, hBX⟩ := hpv v hvc hvh
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have heq := Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs
    (Model.Consensus.Protocol.Schedule.voteTime s.e k)
  have hnd : (voteDutyStoreAt c p a nr s rho x k).tree.elems.Nodup := by
    unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
    exact (Proofs.Consensus.Trees.stateBeforeTime_treeInv c p a nr s rho _ x).nodup
  have hinj : ∀ y ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems,
      ∀ z ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems, root y = root z → y = z := by
    intro y hy z hz hr
    unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked at hy hz
    rw [heq] at hy hz
    exact tickTree_root_inj c p a nr s rho hsleep hx _ hy hz hr
  have hr := findRoot?_of_mem hnd hinj hX hroot
  obtain ⟨hmem, htg⟩ := voterSupportView_pooled_targets s.e (voteDutyStoreAt c p a nr s rho x k)
    (voteDutyStoreAt c p a nr s rho x k).s hpool hr (hus ▸ hXs) hv hb hBX
  exact ⟨u, hmem, hval, hus, htg⟩

/-- `voteDutyHead_passes_supporter_majority_of_delivery` の前提 `hpath`(anchor から `B` までの途中が歩みの tree にあること)を、
`B` の子孫で読みの処理済み tree にあり高さが band(`hMax - 1` 以上)のブロック `D` から出した形(手書き
`coreCandidatePathOfBandDescendant`。`ProcessedAncestor.voterFiltered_mem_of_band`: 処理済み tree は祖先について閉じ
(印の祖先の不変条件 `stateBeforeTime_ancestorStamped`)、FG root ⪯ anchor(`fgRoot_preceq_voteDutyAnchorAt`)。周回 281)。
残りの前提は、読みの voter view での `B` の支持者の過半(`hmaj`)、anchor ⪯ `B`(`hAB`)、band の子孫 `D`(`hBD`・`hD`・`hband`。
手書き `coreConeBandDescendant_of_runFrontier` が出すもの)。 -/
theorem voteDutyHead_passes_supporter_majority_of_band (hsch : ScheduleWellFormed s rho)
    (hdw : DeliveryWellFormed c p a nr s rho) (x : ValidatorId) (k : Nat) {B D : Block}
    (hmaj : Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
          (voteDutyStoreAt c p a nr s rho x k).s)
        ((voteDutyStoreAt c p a nr s rho x k).s - 1) B).size)
    (hAB : preceq (voteDutyAnchorAt c p a nr s rho x k) B = true)
    (hBD : preceq B D = true)
    (hD : D ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree s.e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x k)))
      (voteDutyStoreAt c p a nr s rho x k).s).elems)
    (hband : (voteDutyStoreAt c p a nr s rho x k).hMax - 1 ≤
      (Model.Consensus.Protocol.ForkChoice.Goldfish.chainStateOf (voteDutyStoreAt c p a nr s rho x k).sigma D).h) :
    preceq B (voteDutyHeadAt c p a nr s rho x k) = true := by
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev h =>
    (Proofs.Consensus.Window.eventTime_bounds hsch h).1
  have hanc : Proofs.Consensus.ProcessedAncestor.AncestorStamped (voteDutyStoreAt c p a nr s rho x k) := by
    unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
    exact Proofs.Consensus.ProcessedAncestor.stateBeforeTime_ancestorStamped c p a nr s rho hs hnn _ x
  have hcl : ∀ y, y ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems →
      parent y ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems := by
    unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
    exact Proofs.Consensus.ProcessedAncestor.stateBeforeTime_tree_closed c p a nr s rho _ x
  have hfj : Proofs.Consensus.ProposerFinality.FJ (voteDutyStoreAt c p a nr s rho x k) := by
    unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
    exact Proofs.Consensus.ProcessedAncestor.stateBeforeTime_fj c p a nr s rho hs _ x
  refine voteDutyHead_passes_supporter_majority_of_delivery c p a nr s rho hdw x k hmaj hAB ?_
  intro C hAC _ hCB
  exact Proofs.Consensus.ProcessedAncestor.voterFiltered_mem_of_band hanc hcl hfj
    (Proofs.Consensus.Blocks.preceq_trans hCB hBD) hD hband
    (Proofs.Consensus.Blocks.preceq_trans (fgRoot_preceq_voteDutyAnchorAt c p a nr s rho x k) hAC)

/-- **honest なノードの bodies のブロックは `T + Δ` より前の印で読み手の tree に入る**: GST-zero の枝で、honest な `u` の添字 `n` の
直前の bodies の名前付きブロック `Y`(`n` より前の event の時刻は `T` 以下、`0 ≤ T`)は、honest な読み手 `w` の時刻 `τ`
(`T + Δ ≤ τ ≤ horizon`)の読みの finalized が `Y` の消去と互換なら、その読みの tree にあり受信の印は `T + Δ` より前。
`honestActionRow_sgBlock_held` / `_entered` / `_delivered` の SG block を任意の bodies のブロックに広げた形(周回 282): `Y` は genesis
(初期の tree)か、`u` がある添字 `j0`(時刻 `t0 ≤ T`)で受理したブロック(`bodies_accepted_before`)。`w = u` なら受理の直後の bodies に
あり、`w ≠ u` なら `PartialSynchrony` の中継の連言(締切 `t0 + Δ ≤ T + Δ`)で、受理の直後に既に持つか締切より前に扱う
(`acceptedBlock_handled_held`)。印は `BlockStamps.tree_stamped`。手書き `coreHonestHeadsAvailable` の受理と中継の段に当たる。 -/
theorem bodiesBlock_stamped (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : u ∈ rho.honest.elems) {n : Nat} {T : Int}
    (hT0 : 0 ≤ T) (hT : ∀ j ev, j < n → rho.events[j]? = some ev → eventTime ev ≤ T)
    {Y : Model.Consensus.Objects.NamedBlocks.NamedBlock}
    (hY : Y ∈ (worldAt (stateBefore c p a nr s rho n) u).st.bodies.elems)
    {w : ValidatorId} (hw : w ∈ rho.honest.elems) {τ : Int} (hτ : T + s.e.delta ≤ τ) (hhor : τ ≤ rho.horizon)
    (hcompat : Model.Consensus.Objects.Blocks.compatible (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.f
      (Model.Consensus.Objects.NamedBlocks.eraseBlock Y) = true) :
    Model.Consensus.Objects.NamedBlocks.eraseBlock Y ∈
        (worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.tree.elems ∧
      Model.Consensus.Objects.Time.occurrenceBefore
        ((worldAt (stateBeforeTime c p a nr s rho τ) w).st.core.timestampBlock.get?
          (Model.Consensus.Objects.NamedBlocks.eraseBlock Y)) (T + s.e.delta) = true := by
  have hps : Statements.Consensus.Spec.Conditions.PartialSynchrony c p a nr s rho := hsleep.1.1.1.1.2
  have hgst : s.e.tGST ≤ 0 := hsleep.1.1.1.2
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  obtain ⟨hs, hnd⟩ := Proofs.Consensus.Available.schedule_sorted_nodup s rho hsch
  have hnd' := Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd
  have hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev := fun ev h =>
    (Proofs.Consensus.Window.eventTime_bounds hsch h).1
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hu' : rho.honest.contains u = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu
  have hw' : rho.honest.contains w = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hw
  -- 初期の tree にあるか、時刻が `T + Δ` より前のある event の後の tree にある
  have hentered : Model.Consensus.Objects.NamedBlocks.eraseBlock Y ∈
        (worldAt (stateBefore c p a nr s rho 0) w).st.core.tree.elems ∨
      ∃ (j : Nat) (ev : NamedEvent), rho.events[j]? = some ev ∧ eventTime ev < T + s.e.delta ∧
        Model.Consensus.Objects.NamedBlocks.eraseBlock Y ∈
          (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems := by
    rcases bodies_accepted_before c p a nr s rho u n Y hY with hg | ⟨j0, ev0, hj0n, hev0, hacc⟩
    · left
      subst hg
      have hb : Model.Consensus.Objects.NamedBlocks.NamedBlock.Genesis ∈
          (worldAt (stateBefore c p a nr s rho 0) w).st.bodies.elems := by
        show Model.Consensus.Objects.NamedBlocks.NamedBlock.Genesis ∈
          (NaruStd.Set.singleton Model.Consensus.Objects.NamedBlocks.NamedBlock.Genesis).elems
        exact (Proofs.Consensus.Sets.mem_singleton_iff _ _).mpr rfl
      exact (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho 0 w).tree _ hb
    · right
      have ht0 : eventTime ev0 ≤ T := hT j0 ev0 hj0n hev0
      have ht00 : 0 ≤ eventTime ev0 := hnn _ (List.mem_of_getElem? hev0)
      by_cases hwu : w = u
      · -- `u` 自身: 受理の直後の bodies にある
        subst hwu
        have hYw : Y ∈ (worldAt (stateBefore c p a nr s rho (j0 + 1)) w).st.bodies.elems :=
          (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mp hacc.2
        exact ⟨j0, ev0, hev0, by linarith, (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho (j0 + 1) w).tree Y hYw⟩
      · have hmax : max (eventTime ev0) s.e.tGST = eventTime ev0 := max_eq_left (le_trans hgst ht00)
        have hd : eventTime ev0 + s.e.delta ≤ rho.horizon := by linarith
        by_cases hpw : Model.Consensus.Execution.Node.processed (worldAt (stateBefore c p a nr s rho (j0 + 1)) w).st
            (Model.Consensus.Execution.Objects.NamedObject.Block Y) = true
        · -- `w` は受理の直後に既に bodies に持つ
          have hYw : Y ∈ (worldAt (stateBefore c p a nr s rho (j0 + 1)) w).st.bodies.elems :=
            (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mp hpw
          exact ⟨j0, ev0, hev0, by linarith, (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho (j0 + 1) w).tree Y hYw⟩
        · -- 締切の読みの finalized も `Y` と互換
          have hcd : Model.Consensus.Objects.Blocks.compatible
              (worldAt (stateBeforeTime c p a nr s rho (eventTime ev0 + s.e.delta)) w).st.core.f
              (Model.Consensus.Objects.NamedBlocks.eraseBlock Y) = true := by
            have hc := hcompat
            rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs] at hc ⊢
            have hmono := Proofs.Consensus.ReceiverFinality.stateBefore_f_mono c p a nr s rho
              (idxLt_mono rho (show eventTime ev0 + s.e.delta ≤ τ by linarith)) w
            rw [Proofs.Consensus.Blocks.compatible_comm] at hc ⊢
            exact Proofs.Consensus.FrameCapture.compatible_of_preceq_right hmono hc
          have h := hps.2 u j0 (Model.Consensus.Execution.Objects.NamedObject.Block Y) (eventTime ev0) ⟨hu', hacc⟩ w
          dsimp only at h
          rw [hmax] at h
          obtain ⟨t2, ⟨ht2, ht2d⟩, j, hh⟩ := h ⟨⟨⟨hw', hpw⟩, hd⟩, by
            simp [Model.Consensus.Execution.Node.excludes, hcd]⟩
          have hheld := acceptedBlock_handled_held c p a nr s rho hwf hdom hsleep hu hacc hw hwu ht2 hh
            (show t2 < τ by linarith) hhor hcompat
          obtain ⟨ev, ⟨⟨hevj, -⟩, hte⟩, -⟩ := hh
          exact ⟨j, ev, hevj, by rw [hte]; linarith, hheld⟩
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
  rcases hentered with h0 | ⟨j, ev, hj, hte, hB⟩
  · obtain ⟨hm, heq⟩ := Proofs.Consensus.BlockStamps.stateBefore_keep c p a nr s rho (Nat.zero_le _) w _ h0
    refine ⟨hm, ?_⟩
    rw [heq]
    exact (Proofs.Consensus.BlockStamps.stateBefore_stampInv c p a nr s rho hs hnn 0 w _ h0).before
      (show (0 : Int) < T + s.e.delta by linarith)
  · exact Proofs.Consensus.BlockStamps.tree_stamped c p a nr s rho hs hnn hj hte hB
      (Proofs.Consensus.ReceiverFinality.lt_idxLt_of_time_lt rho hs hnd' hj (lt_of_lt_of_le hte hτ))

/-- **honest なノードの slot `d` の投票の務めの head は、slot `d + 1` の読みの処理済み tree にある**(GST-zero の枝): honest な `u` の
slot `d` の投票の務めの head は、honest な `x` の slot `d + 1` の投票の務めの読み(時刻 `voteTime (d + 1)` ≤ horizon)の finalized が
それと互換なら、その読みの `voterProcessedBlockTree`(slot `d + 1`、freeze は `viewFreeze d`)にある。手書き
`coreHonestHeadProcessedAtNextDuty`(`DecoupledConsensusProofs/Protocol/Schedule/WeakGoldfishCone.lean` 2094 行)に当たり、手書き
`coreConeBandDescendant_of_processed` の band の枝の `D`(honest な委員の投票の head)を処理済み tree に入れる段(周回 282)。
head は `u` の時刻 `voteTime d` の読みの tree にある(`voteHeadBlock_mem_tree`)ので名前付きブロックの消去で、`bodiesBlock_stamped`
(`T = voteTime d`)で `x` の読みの tree にあり印は `voteTime d + Δ = supportCutoff d` より前、したがって `viewFreeze d` より前
(この tree と印の段は周回 296 から `voteDutyHead_stamped_next`)。 -/
theorem voteDutyHead_stamped_next (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : rho.honest.contains u = true) {d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hcompat : Model.Consensus.Objects.Blocks.compatible
      (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x).st.core.f
      (voteDutyHeadAt c p a nr s rho u d) = true) :
    voteDutyHeadAt c p a nr s rho u d ∈ (voteDutyStoreAt c p a nr s rho x (d + 1)).tree.elems ∧
      Model.Consensus.Objects.Time.occurrenceBefore
        (NaruStd.Table.get? (voteDutyStoreAt c p a nr s rho x (d + 1)).timestampBlock (voteDutyHeadAt c p a nr s rho u d))
        (Model.Consensus.Protocol.Schedule.viewFreeze s.e d) = true := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hu' : u ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hu
  have hx' : x ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hx
  have hT0 : 0 ≤ Model.Consensus.Protocol.Schedule.voteTime s.e d := by
    unfold Model.Consensus.Protocol.Schedule.voteTime Model.Consensus.Objects.Parameters.slotTime
      Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    positivity
  have hτ : Model.Consensus.Protocol.Schedule.voteTime s.e d + s.e.delta ≤
      Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) := by
    unfold Model.Consensus.Protocol.Schedule.voteTime Model.Consensus.Objects.Parameters.slotTime
      Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  -- head は `u` の時刻 `voteTime d` の読みの tree の要素で、名前付きブロックの消去
  have hmem : voteDutyHeadAt c p a nr s rho u d ∈
      (worldAt (stateBefore c p a nr s rho
        (Proofs.Consensus.ReceiverFinality.idxLt rho (Model.Consensus.Protocol.Schedule.voteTime s.e d))) u).st.core.tree.elems := by
    rw [← Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
    unfold voteDutyHeadAt
    exact voteHeadBlock_mem_tree _ s.e s.hc
      ((Proofs.Consensus.Trees.stateBeforeTime_treeInv c p a nr s rho _ u).congr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  obtain ⟨Y, hY, hYe⟩ := (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho _ u).named _ hmem
  have hcompat' := hcompat
  rw [← hYe] at hcompat'
  obtain ⟨htree, hstamp⟩ := bodiesBlock_stamped c p a nr s rho hwf hdom hsleep hu' hT0
    (fun j ev hj hev => le_of_lt (Proofs.Consensus.JustificationCertificate.time_lt_of_lt_idxLt rho hs hj hev))
    hY hx' hτ hhor hcompat'
  rw [hYe] at htree hstamp
  refine ⟨htree, Proofs.Consensus.GradeSupporter.occurrenceBefore_mono hstamp ?_⟩
  unfold Model.Consensus.Protocol.Schedule.voteTime Model.Consensus.Protocol.Schedule.viewFreeze
  linarith

/-- honest なノードの slot `d` の投票の務めの head は、slot `d + 1` の読みの処理済み tree にある(tree と印は
`voteDutyHead_stamped_next`。周回 282。周回 296 から射影)。 -/
theorem voteDutyHead_processed_next (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : rho.honest.contains u = true) {d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hcompat : Model.Consensus.Objects.Blocks.compatible
      (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x).st.core.f
      (voteDutyHeadAt c p a nr s rho u d) = true) :
    voteDutyHeadAt c p a nr s rho u d ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree s.e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
      (voteDutyStoreAt c p a nr s rho x (d + 1)).s).elems := by
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  obtain ⟨htree, hstamp⟩ := voteDutyHead_stamped_next c p a nr s rho hwf hdom hsleep hu hhor hx hcompat
  have hslot : (voteDutyStoreAt c p a nr s rho x (d + 1)).s = d + 1 :=
    Proofs.Consensus.Voting.slotOf_voteTime s.e hδ (d + 1)
  rw [hslot]
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree
  dsimp only
  rw [Proofs.Consensus.Trees.mem_filter_iff]
  refine ⟨htree, ?_⟩
  rw [Bool.or_eq_true]
  left
  rw [Nat.add_sub_cancel]
  exact hstamp

/-- **段の橋の band の枝**: honest な `u` の slot `d` の投票の務めの head を band の子孫 `D` に取る形。`B ⪯ head` で、honest な `x` の
slot `d + 1` の読みの `sigma` での head の高さが band(`hMax - 1` 以上)なら、`voteDutyHead_passes_supporter_majority_of_band` の前提
`hD` は `voteDutyHead_processed_next` から出る。その互換は、読みの finalized ⪯ FG root(`ReceiverFinality.store_fgRoot_extends`、
`FJ` は `stateBeforeTime_fj`)⪯ anchor ⪯ `B` ⪯ head から出す。手書き `coreConeBandDescendant_of_processed` の `hband` の枝
(`D = X.erase`)に当たる(周回 283)。残りの前提は `hmaj` と、head の高さの読み替え(手書き `coreStoredHeightAtVoteDuty`)。 -/
theorem voteDutyHead_passes_supporter_majority_of_bandHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) (hdw : DeliveryWellFormed c p a nr s rho)
    {u : ValidatorId} (hu : rho.honest.contains u = true) {d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon)
    {x : ValidatorId} (hx : rho.honest.contains x = true) {B : Block}
    (hmaj : Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) B).size)
    (hAB : preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) B = true)
    (hBD : preceq B (voteDutyHeadAt c p a nr s rho u d) = true)
    (hband : (voteDutyStoreAt c p a nr s rho x (d + 1)).hMax - 1 ≤
      (Model.Consensus.Protocol.ForkChoice.Goldfish.chainStateOf (voteDutyStoreAt c p a nr s rho x (d + 1)).sigma
        (voteDutyHeadAt c p a nr s rho u d)).h) :
    preceq B (voteDutyHeadAt c p a nr s rho x (d + 1)) = true := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hfj := Proofs.Consensus.ProcessedAncestor.stateBeforeTime_fj c p a nr s rho hs
    (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) x
  have hfroot : preceq
      (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x).st.core.f
      (voteDutyFgRootAt c p a nr s rho x (d + 1)) = true := by
    unfold voteDutyFgRootAt
    exact Proofs.Consensus.ReceiverFinality.store_fgRoot_extends
      (st := (Proofs.Consensus.Voting.clocked s.e _ (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))).core) hfj
  have hfh := Proofs.Consensus.Blocks.preceq_trans hfroot
    (Proofs.Consensus.Blocks.preceq_trans (fgRoot_preceq_voteDutyAnchorAt c p a nr s rho x (d + 1))
      (Proofs.Consensus.Blocks.preceq_trans hAB hBD))
  have hcompat := Proofs.Consensus.Blocks.compatible_of_preceq_common hfh (Proofs.Consensus.Blocks.preceq_self _)
  exact voteDutyHead_passes_supporter_majority_of_band c p a nr s rho hsch hdw x (d + 1) hmaj hAB hBD
    (voteDutyHead_processed_next c p a nr s rho hwf hdom hsleep hu hhor hx hcompat) hband

/-- **cone の投票の head のブロックは次の slot の読みの tree に凍結より前の印で入る**(`hpv` の tree の側): `1 ≤ d ≤ last` で、slot `d`
のすべての honest なノードの投票の務めの head が `B` の子孫、honest な `x` の slot `d + 1` の読みの anchor ⪯ `B` なら、slot `d` の
委員会の honest な元 `v` は、`B` の子孫で slot が `d` 以下の run のブロック `X` の root に投票し(`voteConeSlot_of_heads`)、`X` の消去は
`v` の slot `d` の head なので、`x` の読みの tree にあり受信の印は `viewFreeze d` より前(`voteDutyHead_stamped_next`。互換は
読みの finalized ⪯ FG root ⪯ anchor ⪯ `B` ⪯ head)。手書き `coneSupport_of_named_votes` の `havailable` の block の側に当たる。
`protectedVoteSlot_preserve` では `hB.heads` と `hbelow` がそのまま前提に当たる(周回 296)。 -/
theorem voteConeStamped_of_heads (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) {B : Block}
    (hheads : ∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x d) = true)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hbelow : preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) B = true) :
    ∀ v, rho.honest.contains v = true → (c d).contains v = true →
      ∃ X : Model.Consensus.Objects.NamedBlocks.NamedBlock,
        preceq B (Model.Consensus.Objects.NamedBlocks.eraseBlock X) = true ∧
        Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho X ∧
        Statements.Consensus.Spec.Execution.Emits c p a nr s rho v
          (Model.Consensus.Execution.Objects.NamedObject.GfVote
            ⟨v, d, root (Model.Consensus.Objects.NamedBlocks.eraseBlock X)⟩)
          (Model.Consensus.Protocol.Schedule.voteTime s.e d) ∧
        slot (Model.Consensus.Objects.NamedBlocks.eraseBlock X) ≤ d ∧
        Model.Consensus.Objects.NamedBlocks.eraseBlock X ∈ (voteDutyStoreAt c p a nr s rho x (d + 1)).tree.elems ∧
        Model.Consensus.Objects.Time.occurrenceBefore
          (NaruStd.Table.get? (voteDutyStoreAt c p a nr s rho x (d + 1)).timestampBlock
            (Model.Consensus.Objects.NamedBlocks.eraseBlock X))
          (Model.Consensus.Protocol.Schedule.viewFreeze s.e d) = true := by
  intro v hv hvc
  obtain ⟨X, hBX, hX, hem, hsl, hXe⟩ :=
    voteConeSlot_of_heads c p a nr s rho hwf hsleep hhor hd (by omega) hheads v hv hvc
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hvt : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon := by
    refine le_trans ?_ hhor
    have hd' : (d : Int) ≤ (last : Int) := by exact_mod_cast hdlast
    have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
    unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  have hfj := Proofs.Consensus.ProcessedAncestor.stateBeforeTime_fj c p a nr s rho hs
    (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) x
  have hfroot : preceq
      (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x).st.core.f
      (voteDutyFgRootAt c p a nr s rho x (d + 1)) = true := by
    unfold voteDutyFgRootAt
    exact Proofs.Consensus.ReceiverFinality.store_fgRoot_extends
      (st := (Proofs.Consensus.Voting.clocked s.e _ (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))).core) hfj
  have hfh := Proofs.Consensus.Blocks.preceq_trans hfroot
    (Proofs.Consensus.Blocks.preceq_trans (fgRoot_preceq_voteDutyAnchorAt c p a nr s rho x (d + 1))
      (Proofs.Consensus.Blocks.preceq_trans hbelow (hheads v hv)))
  have hcompat := Proofs.Consensus.Blocks.compatible_of_preceq_common hfh (Proofs.Consensus.Blocks.preceq_self _)
  obtain ⟨htree, hstamp⟩ := voteDutyHead_stamped_next c p a nr s rho hwf hdom hsleep hv hvt hx hcompat
  rw [← hXe] at htree hstamp
  exact ⟨X, hBX, hX, hem, hsl, htree, hstamp⟩

/-- **cone の投票は次の slot の読みの pool に凍結より前の印で入る**(`hpv` の全体): `voteConeStamped_of_heads` と同じ前提で、
honest な `x` の slot `d + 1` の読み(`st.s - 1 = d`)の、slot `d` の委員会の honest な元 `v` ごとに、投票
`⟨v, d, root (eraseBlock X)⟩` が読みの pool のバケツ `d` にあり受信の印が `viewFreeze d` より前(`v` は GST-zero の枝で投票の時刻
`voteTime d` に出すので、`Stamps.partialSynchrony_honest_gfVote_stamped` で `x` は `supportCutoff d = voteTime d + Δ` より前の
添字から pool に持ち、印は締切より前。読みの添字 `idxLt (voteTime (d + 1))` はその添字より後)。`X` の側は
`voteConeStamped_of_heads`。手書き `coneSupport_of_named_votes` の `havailable` の vote の側に当たる(周回 297)。 -/
theorem voteConePooled_of_heads (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) {B : Block}
    (hheads : ∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x d) = true)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hbelow : preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) B = true) :
    ∀ v ∈ (c ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1)).elems, v ∈ rho.honest.elems →
      ∃ u X, u ∈ (Model.Consensus.Protocol.StoreBase.pool
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1)).elems ∧
        u.valIndex = v ∧ u.slot = (voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1 ∧
        X ∈ (voteDutyStoreAt c p a nr s rho x (d + 1)).tree.elems ∧ root X = u.head ∧
        slot X ≤ (voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1 ∧
        Model.Consensus.Objects.Time.occurrenceBefore
          (NaruStd.Table.get? (voteDutyStoreAt c p a nr s rho x (d + 1)).timestampVote u)
          (Model.Consensus.Protocol.Schedule.viewFreeze s.e ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1)) = true ∧
        Model.Consensus.Objects.Time.occurrenceBefore
          (NaruStd.Table.get? (voteDutyStoreAt c p a nr s rho x (d + 1)).timestampBlock X)
          (Model.Consensus.Protocol.Schedule.viewFreeze s.e ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1)) = true ∧
        preceq B X = true := by
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hslot : (voteDutyStoreAt c p a nr s rho x (d + 1)).s = d + 1 :=
    Proofs.Consensus.Voting.slotOf_voteTime s.e hδ (d + 1)
  rw [hslot, Nat.add_sub_cancel]
  intro v hvc hvh
  have hv : rho.honest.contains v = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hvh
  have hvc' : (c d).contains v = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hvc
  obtain ⟨X, hBX, -, hem, hsl, htree, hstamp⟩ :=
    voteConeStamped_of_heads c p a nr s rho hwf hdom hsleep hhor hd hdlast hheads hx hbelow v hv hvc'
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, hunf⟩, -⟩ := hexec
  have hps : Statements.Consensus.Spec.Conditions.PartialSynchrony c p a nr s rho := hsleep.1.1.1.1.2
  have hgst : s.e.tGST ≤ 0 := hsleep.1.1.1.2
  obtain ⟨hs, hnd⟩ := Proofs.Consensus.Available.schedule_sorted_nodup s rho hsch
  have hnd' := Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd
  have hT0 : 0 ≤ Model.Consensus.Protocol.Schedule.voteTime s.e d := by
    unfold Model.Consensus.Protocol.Schedule.voteTime Model.Consensus.Objects.Parameters.slotTime
      Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    positivity
  have hcutv : Model.Consensus.Protocol.Schedule.supportCutoff s.e d ≤
      Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) := by
    unfold Model.Consensus.Protocol.Schedule.supportCutoff Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  have hvt : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon := by
    refine le_trans ?_ hhor
    have hd' : (d : Int) ≤ (last : Int) := by exact_mod_cast hdlast
    unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  obtain ⟨t2, j, ⟨-, ht2⟩, hh, hmem⟩ :=
    Proofs.Consensus.Stamps.partialSynchrony_honest_gfVote_stamped c p a nr s rho hps hsch hunf hδ hem hv
      (le_trans hgst hT0) hx (le_trans hcutv hvt)
  obtain ⟨ev, hevj, hte⟩ := Proofs.Consensus.Stamps.handlesAt_event c p a nr s rho hh
  have hji : j < Proofs.Consensus.ReceiverFinality.idxLt rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) :=
    Proofs.Consensus.ReceiverFinality.lt_idxLt_of_time_lt rho hs hnd' hevj
      (by rw [hte]; exact lt_of_lt_of_le ht2 hcutv)
  obtain ⟨hm, hob⟩ := hmem _ hji
  have heq := Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs
    (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))
  refine ⟨⟨v, d, root (Model.Consensus.Objects.NamedBlocks.eraseBlock X)⟩,
    Model.Consensus.Objects.NamedBlocks.eraseBlock X, ?_, rfl, rfl, htree, rfl, hsl, ?_, hstamp, hBX⟩
  · unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
    refine (Proofs.Consensus.Votes.mem_storePool_iff _ _ _).mpr ?_
    rw [heq]
    exact hm
  · unfold voteDutyStoreAt Proofs.Consensus.Voting.clocked
    rw [heq]
    refine Proofs.Consensus.GradeSupporter.occurrenceBefore_mono hob ?_
    show Model.Consensus.Protocol.Schedule.supportCutoff s.e d ≤ Model.Consensus.Protocol.Schedule.viewFreeze s.e d
    unfold Model.Consensus.Protocol.Schedule.supportCutoff Model.Consensus.Protocol.Schedule.viewFreeze
    linarith

/-- **段の橋の `hmaj` を cone の head から出す**: `voteConePooled_of_heads`(`hpv`)→ `voteDutyStore_supportVote_of_pool`(`hvote`)
→ `voteDutyStore_supporterMajority_of_cone_run` を組んだ形。slot `d` のすべての honest なノードの投票の務めの head が `B` の子孫で、
honest な `x` の slot `d + 1` の読みの anchor ⪯ `B` なら、その読みの voter view で `B` の支持者が参加者の過半(周回 297)。 -/
theorem voteDutyStore_supporterMajority_of_heads (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) (hhc : HonestCommittees c rho.honest)
    (hdw : DeliveryWellFormed c p a nr s rho) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) {B : Block}
    (hheads : ∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x d) = true)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hbelow : preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) B = true) :
    Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) B).size := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, hunf⟩, -⟩ := hexec
  exact voteDutyStore_supporterMajority_of_cone_run c p a nr s rho hwf hhc hdw hsch hunf x (d + 1)
    (voteDutyStore_supportVote_of_pool c p a nr s rho hsleep hsch hx (d + 1)
      (voteConePooled_of_heads c p a nr s rho hwf hdom hsleep hhor hd hdlast hheads hx hbelow))

/-- **投票の務めの読みの `sigma` の高さは名前付き導出の高さ**: `x` の slot `k` の読みの tree のブロック `B` は、読みの bodies の
名前付きブロック `Y` の消去で、`sigma` での `B` の chain 状態は `Y` の導出 `deriveNamed`(`Carrier.StoreInv` の `named` / `sigma`。
時計合わせ `clocked` は tree / `sigma` を変えない)。手書き `coreStoredHeightAtVoteDuty` の、根の衝突なしで `Y` を与えられた名前付き
ブロックと同一視する前の段に当たり、`voteDutyHead_passes_supporter_majority_of_bandHead` の `hband` を導出の高さで読む(周回 283)。 -/
theorem voteDutyStore_sigma_named (x : ValidatorId) (k : Nat) {B : Block}
    (hB : B ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems) :
    ∃ Y, Y ∈ (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e k)) x).st.bodies.elems ∧
      Model.Consensus.Objects.NamedBlocks.eraseBlock Y = B ∧
      Model.Consensus.Protocol.ForkChoice.Goldfish.chainStateOf (voteDutyStoreAt c p a nr s rho x k).sigma B =
        Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg Y := by
  have hinv := Proofs.Consensus.JustifiedCarrier.stateBeforeTime_inv c p a nr s rho
    (Model.Consensus.Protocol.Schedule.voteTime s.e k) x
  obtain ⟨Y, hY, hYe⟩ := hinv.named B hB
  refine ⟨Y, hY, hYe, ?_⟩
  rw [← hYe]
  exact hinv.sigma Y hY

/-- **投票の務めの読みの最大の高さの carrier**: `x` の slot `k` の読みには、bodies の名前付きブロック `W` で、消去が読みの tree にあり、
`sigma` のその鍵の値が `W` の導出で、その高さが読みの `hMax` に等しいものがある(`MaxCarrier.stateBeforeTime_maxCarrier`。
時計合わせは tree / sigma / `hMax` を変えない)。手書き `coreFrontierQuorumWitness` の最初の段
(`maximum_carrier_stateBeforeTime`)に当たり、band に届かない枝の frontier の証人の出発点(周回 285)。 -/
theorem voteDutyStore_maxCarrier (x : ValidatorId) (k : Nat) :
    ∃ W, W ∈ (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e k)) x).st.bodies.elems ∧
      Model.Consensus.Objects.NamedBlocks.eraseBlock W ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems ∧
      Model.Consensus.Protocol.ForkChoice.Goldfish.chainStateOf (voteDutyStoreAt c p a nr s rho x k).sigma
          (Model.Consensus.Objects.NamedBlocks.eraseBlock W) =
        Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg W ∧
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg W).h = (voteDutyStoreAt c p a nr s rho x k).hMax :=
  Proofs.Consensus.MaxCarrier.stateBeforeTime_maxCarrier c p a nr s rho
    (Model.Consensus.Protocol.Schedule.voteTime s.e k) x

/-- **投票の務めの読みの最大の高さの横断の honest な発行**: `x` の slot `k` の読みの `hMax` が 1 より大きければ、bodies の `W`
(導出の高さが `hMax`)と `eraseBlock W` の祖先 `X` があり、honest な署名者が slot `k` の投票の時刻より前に
`matchesEntry heightPair (hMax - 1) (root X)` の行を実際に出していて、その行は `x` が投票の時刻より前に処理した `W` の祖先 `Y` に
載っている(`MaxCrossing.stateBeforeTime_maxCrossing_honestEmission_lt`。前提 `QuorumHonest` / carried / `EventsSorted` は
sleepy regime から出す)。手書き `coreFrontierQuorumWitness`(高さの横断・定足数の honest な署名者・`honest_held_ancestor_row_emission`)
に当たり、band に届かない枝の frontier の証人の 2 段目(周回 286)。 -/
theorem voteDutyStore_maxCrossing_honestEmission (hwf : SetupWellFormed c p s) (hsleep : SleepyRegime c p a nr s rho 0)
    (x : ValidatorId) (k : Nat) (hlarge : 1 < (voteDutyStoreAt c p a nr s rho x k).hMax) :
    ∃ W X Y row t t2,
      W ∈ (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e k)) x).st.bodies.elems ∧
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg W).h = (voteDutyStoreAt c p a nr s rho x k).hMax ∧
      preceq X (Model.Consensus.Objects.NamedBlocks.eraseBlock W) = true ∧
      Model.Consensus.Objects.NamedBlocks.namedPreceq Y W = true ∧
      row ∈ Model.Consensus.Objects.NamedBlocks.namedAttestations Y ∧ row.valIndex ∈ rho.honest.elems ∧
      Model.Consensus.Objects.NamedBlocks.matchesEntry row.heightPair ((voteDutyStoreAt c p a nr s rho x k).hMax - 1)
        (Model.Consensus.Objects.Blocks.root X) = true ∧
      Statements.Consensus.Spec.Execution.Processes c p a nr s rho x
        (Model.Consensus.Execution.Objects.NamedObject.Block Y) t ∧
      t < Model.Consensus.Protocol.Schedule.voteTime s.e k ∧ t2 ≤ t ∧
      t2 < Model.Consensus.Protocol.Schedule.voteTime s.e k ∧
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho row.valIndex
        (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2 := by
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
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
  exact Proofs.Consensus.MaxCrossing.stateBeforeTime_maxCrossing_honestEmission_lt c p a nr s rho hs hqh hcar x
    (Model.Consensus.Protocol.Schedule.voteTime s.e k) hlarge

/-- **投票の務めの読みの最大の高さの frontier の確認の証人**: `x` の slot `k` の読みの `hMax` が 1 より大きければ、honest な
署名者 `u` が slot `k` の投票の時刻より前の時刻 `t2` に高さ `hMax - 1` の行を出していて、その tick(添字 `i`)の務めの store
`dutyStoreAt u i t2` の bodies に、消去が務めの FG source の `D`(導出の高さ `hMax - 1`)と `D` の祖先 `K`(消去は `D` の導出の
`tH`、導出の高さ `hMax - 1`、導出の `tH` は `K` の消去)があり、務めの確認の証人は `K` の消去。`K` の根は横断の `X` の根で、
`X` は読みの bodies の `W`(導出の高さ `hMax`)の消去の祖先。`voteDutyStore_maxCrossing_honestEmission` の行に
`HeightRowWitness.emits_vote_confirmationWitness`(手書き `coreHonestHeightRowConfirmationWitness`)を掛けたもので、手書き
`coreFrontierConfirmationWitness` の `RunBlock K` を除く形に当たる(周回 287)。 -/
theorem voteDutyStore_frontierConfirmationWitness (hwf : SetupWellFormed c p s)
    (hsleep : SleepyRegime c p a nr s rho 0) (x : ValidatorId) (k : Nat)
    (hlarge : 1 < (voteDutyStoreAt c p a nr s rho x k).hMax) :
    ∃ W X row t2 i D K,
      W ∈ (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e k)) x).st.bodies.elems ∧
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg W).h = (voteDutyStoreAt c p a nr s rho x k).hMax ∧
      preceq X (Model.Consensus.Objects.NamedBlocks.eraseBlock W) = true ∧
      row.valIndex ∈ rho.honest.elems ∧
      Statements.Consensus.Spec.Execution.Emits c p a nr s rho row.valIndex
        (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2 ∧
      t2 < Model.Consensus.Protocol.Schedule.voteTime s.e k ∧
      rho.events[i]? = some (Model.Consensus.Execution.Run.NamedEvent.Tick row.valIndex t2) ∧
      Proofs.Consensus.RootWitness.fgConfirmationWitnessAt c p a nr s rho row.valIndex i t2 =
        some (Model.Consensus.Objects.NamedBlocks.eraseBlock K) ∧
      D ∈ (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho row.valIndex i t2).bodies.elems ∧
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg D).h = (voteDutyStoreAt c p a nr s rho x k).hMax - 1 ∧
      K ∈ (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho row.valIndex i t2).bodies.elems ∧
      Model.Consensus.Objects.NamedBlocks.eraseBlock K = (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg D).tH ∧
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg K).h = (voteDutyStoreAt c p a nr s rho x k).hMax - 1 ∧
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg K).tH =
        Model.Consensus.Objects.NamedBlocks.eraseBlock K ∧
      Model.Consensus.Objects.NamedBlocks.namedPreceq K D = true ∧
      Model.Consensus.Objects.Blocks.root (Model.Consensus.Objects.NamedBlocks.eraseBlock K) =
        Model.Consensus.Objects.Blocks.root X ∧
      (worldAt (stateBefore c p a nr s rho (i + 1)) row.valIndex).st.bodies =
        (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho row.valIndex i t2).bodies := by
  obtain ⟨W, X, -, row, -, t2, hW, hWh, hX, -, -, hH, hmatch, -, -, -, ht2, hem⟩ :=
    voteDutyStore_maxCrossing_honestEmission c p a nr s rho hwf hsleep x k hlarge
  obtain ⟨nu, hv⟩ := Proofs.Consensus.RootEntry.matchesEntry_vote hmatch
  obtain ⟨i, D, K, hev, hfg, hD, -, hDh, hK, hKe, hKh, hKt, hKD, hKr, hbod⟩ :=
    Proofs.Consensus.HeightRowWitness.emits_vote_confirmationWitness c p a nr s rho hem hv
  exact ⟨W, X, row, t2, i, D, K, hW, hWh, hX, hH, hem, ht2, hev, hfg, hD, hDh, hK, hKe, hKh, hKt, hKD, hKr, hbod⟩

/-- **行を出した tick の務めの store の bodies のブロックは、次の slot の読みの処理済み tree にある**(GST-zero の枝): honest な `u` が
時刻 `t2`(添字 `i` の tick)に行 `row` を出し、`stateBefore (i + 1)` の `u` の bodies が務めの store `dutyStoreAt u i t2` の bodies
(`HeightRowWitness.emits_vote_confirmationWitness` の最後の欄)で、`t2` が slot `d + 1` の投票時刻より前なら、務めの store の bodies の
`T` は、honest な `x` の slot `d + 1` の投票の務めの読み(時刻 `voteTime (d + 1)` ≤ horizon)の finalized がそれと互換なら、その読みの
`voterProcessedBlockTree`(freeze は `viewFreeze d`)にある。手書き `coreActionBlockProcessedAtNextDuty`
(`DecoupledConsensusProofs/Protocol/Schedule/WeakGoldfishCone.lean` 2237 行。手書き `coreConeBandDescendant_of_processed` の
`hblockProcessed`)に当たる。`t2` は行の round の action 時刻 = opening slot `q` の確認の時刻 `4Δq + 6Δ`
(`RootWitness.emits_attest_actionTime_round`)で、`voteTime (d + 1) = 4Δd + 5Δ` より前なので `q < d`、したがって
`t2 + Δ ≤ viewFreeze d = 4Δd + 3Δ`(手書き `coreActionLeSupportCutoff`)。あとは `voteDutyHead_processed_next` と同じく
`bodiesBlock_stamped`(`n = i + 1`、`T = t2`)で閉じる(周回 288)。 -/
theorem dutyBody_processed_next (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {u : ValidatorId} (hu : rho.honest.contains u = true)
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} {t2 : Int} {i : Nat}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2)
    (hev : rho.events[i]? = some (Model.Consensus.Execution.Run.NamedEvent.Tick u t2))
    (hbod : (worldAt (stateBefore c p a nr s rho (i + 1)) u).st.bodies =
      (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho u i t2).bodies)
    {T : Model.Consensus.Objects.NamedBlocks.NamedBlock}
    (hT : T ∈ (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho u i t2).bodies.elems) {d : Nat}
    (ht2 : t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))
    (hhor : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hcompat : Model.Consensus.Objects.Blocks.compatible
      (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x).st.core.f
      (Model.Consensus.Objects.NamedBlocks.eraseBlock T) = true) :
    Model.Consensus.Objects.NamedBlocks.eraseBlock T ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree s.e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
      (voteDutyStoreAt c p a nr s rho x (d + 1)).s).elems := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hu' : u ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hu
  have hx' : x ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hx
  have hT0 : 0 ≤ t2 :=
    (Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? hev)).1
  -- `t2` は opening slot `q` の確認の時刻で、`q < d` なので `t2 + Δ ≤ viewFreeze d`
  have hta : t2 = Model.Consensus.Protocol.Schedule.confirmationTime s.e
      (Model.Consensus.Protocol.Grades.openingSlot s.hc row.round) :=
    Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem
  have hfreeze : t2 + s.e.delta ≤ Model.Consensus.Protocol.Schedule.viewFreeze s.e d := by
    rw [hta] at ht2 ⊢
    generalize Model.Consensus.Protocol.Grades.openingSlot s.hc row.round = q at ht2 ⊢
    have hq : q < d := by
      by_contra hn
      have hdq : (d : Int) ≤ (q : Int) := by exact_mod_cast Nat.le_of_not_gt hn
      unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
        Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart at ht2
      simp only [Int.ofNat_eq_natCast] at ht2
      push_cast at ht2
      nlinarith
    have hqd : (q : Int) + 1 ≤ (d : Int) := by exact_mod_cast hq
    unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.viewFreeze
    unfold Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  have hτ : t2 + s.e.delta ≤ Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) := by
    refine le_trans hfreeze ?_
    unfold Model.Consensus.Protocol.Schedule.viewFreeze Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  -- `stateBefore (i + 1)` より前の event の時刻は `t2` 以下
  have hbefore : ∀ j ev, j < i + 1 → rho.events[j]? = some ev → eventTime ev ≤ t2 := by
    intro j ev hj hevj
    by_contra hn
    have hlt := Proofs.Consensus.Window.lt_of_time_lt hs hev hevj (lt_of_not_ge hn)
    omega
  have hTb : T ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) u).st.bodies.elems := by
    rw [hbod]; exact hT
  obtain ⟨htree, hstamp⟩ := bodiesBlock_stamped c p a nr s rho hwf hdom hsleep hu' hT0 hbefore hTb hx' hτ hhor hcompat
  have hslot : (voteDutyStoreAt c p a nr s rho x (d + 1)).s = d + 1 :=
    Proofs.Consensus.Voting.slotOf_voteTime s.e hδ (d + 1)
  rw [hslot]
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree
  dsimp only
  rw [Proofs.Consensus.Trees.mem_filter_iff]
  refine ⟨htree, ?_⟩
  rw [Bool.or_eq_true]
  left
  rw [Nat.add_sub_cancel]
  exact Proofs.Consensus.GradeSupporter.occurrenceBefore_mono hstamp hfreeze

/-- **frontier の確認の証人は低い保護されたブロックの子孫**(GST-zero の枝): honest な `u` が slot `d + 1` の投票時刻より前の時刻 `t2`
(添字 `i` の tick)に行を出し、その tick の務めの確認の証人が務めの store の bodies の `K` の消去で(`voteDutyStore_frontierConfirmationWitness`
の欄)、honest な `y` の slot `d` の投票の務めの head が `B` の子孫で、`B` の run の中の名前付きブロック `Bn` の導出の高さが `K` の導出の
高さより低いなら、`B` は `K` の消去の祖先。確認の証人は行の源として `y` の slot `d` の head の祖先(`laterVoteHead_rowSources_of_prior`)
なので `B` と比べられ、`K` の消去が `B` の祖先なら、その持ち上げは `Bn` の祖先で root の衝突なしで `K`(`K` は `u` の bodies にあり run の
中)になり、`deriveNamed_h_mono` で高さが矛盾する。手書き `coreConeBandDescendant_of_processed` の偽の枝の `hwitnesses`(呼び出し側
`protectedVoteSlots_of_historyCut_v2_w` の `hfrontierB`。recent な round は `hfgB`)と、互換から高さで逆向きを排除する段
(`coreNamedPreceq_of_runBlock_erase_preceq` と `derive_height_mono`)を合わせた形に当たる(周回 289)。 -/
theorem frontierWitness_above_of_upperHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {y : ValidatorId} (hy : rho.honest.contains y = true)
    (hpriorD : ∀ (w : ValidatorId) (i : Nat) (t : Int) (C : Block), rho.honest.contains w = true →
      Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t →
      Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d →
      Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
      preceq C (voteDutyHeadAt c p a nr s rho y d) = true)
    {B : Block} (hBy : preceq B (voteDutyHeadAt c p a nr s rho y d) = true)
    {Bn : Model.Consensus.Objects.NamedBlocks.NamedBlock}
    (hBnrun : Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho Bn)
    (hBne : Model.Consensus.Objects.NamedBlocks.eraseBlock Bn = B)
    {u : ValidatorId} (hu : rho.honest.contains u = true)
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} {t2 : Int} {i : Nat}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2)
    (hev : rho.events[i]? = some (Model.Consensus.Execution.Run.NamedEvent.Tick u t2))
    (ht2 : t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))
    {K : Model.Consensus.Objects.NamedBlocks.NamedBlock}
    (hfg : Proofs.Consensus.RootWitness.fgConfirmationWitnessAt c p a nr s rho u i t2 =
      some (Model.Consensus.Objects.NamedBlocks.eraseBlock K))
    (hK : K ∈ (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho u i t2).bodies.elems)
    (hbod : (worldAt (stateBefore c p a nr s rho (i + 1)) u).st.bodies =
      (Proofs.Consensus.RootWitness.dutyStoreAt c p a nr s rho u i t2).bodies)
    (hh : (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg Bn).h <
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg K).h) :
    preceq B (Model.Consensus.Objects.NamedBlocks.eraseBlock K) = true := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho hexec).2
  -- 確認の証人は `y` の slot `d` の head の祖先なので `B` と比べられる
  have hKy := (laterVoteHead_rowSources_of_prior c p a nr s rho hwf hdom hsleep hhor hd hupper hy hpriorD hu hem hev ht2).2
    _ hfg
  rcases Proofs.Consensus.Blocks.preceq_linear hBy hKy with hBK | hKB
  · exact hBK
  · -- `K` の消去が `B` の祖先なら、持ち上げは root の衝突なしで `K` で、高さが矛盾する
    exfalso
    rw [← hBne] at hKB
    obtain ⟨Kn, hKn, hKne⟩ := Proofs.Consensus.NamedBlocks.erased_ancestor_lift hKB
    have hKb : K ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) u).st.bodies.elems := by
      rw [hbod]; exact hK
    have hKdir : Statements.Consensus.Spec.Execution.DirectBlockInRun c p a nr s rho K :=
      Or.inr ⟨u, hu, _, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hKb⟩
    have heq : K = Kn := hcf K Bn ⟨⟨K, hKdir, Proofs.Consensus.NamedBlocks.namedPreceq_self K⟩, hBnrun⟩ K Kn
      ⟨⟨Or.inl (Proofs.Consensus.NamedBlocks.namedPreceq_self _), Or.inr hKn⟩,
        by rw [← Proofs.Consensus.NamedBlocks.root_eraseBlock, ← Proofs.Consensus.NamedBlocks.root_eraseBlock, hKne]⟩
    rw [← heq] at hKn
    exact absurd (Proofs.Consensus.EntryHeight.deriveNamed_h_mono s.e s.cfg hKn) (Nat.not_le_of_lt hh)

/-- **段の橋の band に届かない枝**: `voteDutyHead_passes_supporter_majority_of_bandNamed` の偽の枝。`B` の名前付きブロック `Bn` の導出の
高さが `x` の slot `d + 1` の読みの `hMax - 1` より低ければ、読みの `hMax` は 1 より大きく、frontier の確認の証人 `K`
(`voteDutyStore_frontierConfirmationWitness`。導出の高さ `hMax - 1`)は `B` の子孫(`frontierWitness_above_of_upperHead`。上界は
honest な `y` の slot `d` の head)。読みの finalized ⪯ FG root ⪯ anchor ⪯ `B` ⪯ `K` の消去なので `K` の消去は読みの処理済み tree にあり
(`dutyBody_processed_next`)、その `sigma` の高さは、読みの bodies の名前付きブロックの導出(`voteDutyStore_sigma_named`)が root の
衝突なしで `K` なので `hMax - 1`。`D = K` の消去で `voteDutyHead_passes_supporter_majority_of_band` を掛ける。手書き
`coreConeBandDescendant_of_processed` の `by_cases hband` の偽の枝(`D = K.erase`)と `coreCandidatePathOfBandDescendant` に当たる
(周回 289)。残りの前提は `hmaj`。 -/
theorem voteDutyHead_passes_supporter_majority_of_belowBand (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) (hdw : DeliveryWellFormed c p a nr s rho) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) {y : ValidatorId} (hy : rho.honest.contains y = true)
    (hpriorD : ∀ (w : ValidatorId) (i : Nat) (t : Int) (C : Block), rho.honest.contains w = true →
      Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t →
      Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d →
      Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
      preceq C (voteDutyHeadAt c p a nr s rho y d) = true)
    {x : ValidatorId} (hx : rho.honest.contains x = true) {B : Block}
    (hmaj : Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) B).size)
    (hAB : preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) B = true)
    (hBy : preceq B (voteDutyHeadAt c p a nr s rho y d) = true)
    {Bn : Model.Consensus.Objects.NamedBlocks.NamedBlock}
    (hBnrun : Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho Bn)
    (hBne : Model.Consensus.Objects.NamedBlocks.eraseBlock Bn = B)
    (hhigh : (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg Bn).h <
      (voteDutyStoreAt c p a nr s rho x (d + 1)).hMax - 1) :
    preceq B (voteDutyHeadAt c p a nr s rho x (d + 1)) = true := by
  have hfacts := Proofs.Consensus.Liveness.wf_facts hwf
  have hδ := hfacts.1
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho hexec).2
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hvhor : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon := by
    refine le_trans ?_ hhor
    have hd' : (d : Int) ≤ (last : Int) := by exact_mod_cast hdlast
    unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  have hlarge : 1 < (voteDutyStoreAt c p a nr s rho x (d + 1)).hMax := by omega
  obtain ⟨-, -, row, t2, i, -, K, -, -, -, hrowH, hem, ht2, hev, hfg, -, -, hK, -, hKh, -, -, -, hbod⟩ :=
    voteDutyStore_frontierConfirmationWitness c p a nr s rho hwf hsleep x (d + 1) hlarge
  have hu : rho.honest.contains row.valIndex = true :=
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hrowH
  -- frontier の確認の証人は `B` の子孫
  have hBK := frontierWitness_above_of_upperHead c p a nr s rho hwf hdom hsleep hhor hd (by omega) hy hpriorD hBy
    hBnrun hBne hu hem hev ht2 hfg hK hbod (by rw [hKh]; exact hhigh)
  -- `K` の消去は読みの処理済み tree にある
  have hfj := Proofs.Consensus.ProcessedAncestor.stateBeforeTime_fj c p a nr s rho hs
    (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) x
  have hfroot : preceq
      (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x).st.core.f
      (voteDutyFgRootAt c p a nr s rho x (d + 1)) = true := by
    unfold voteDutyFgRootAt
    exact Proofs.Consensus.ReceiverFinality.store_fgRoot_extends
      (st := (Proofs.Consensus.Voting.clocked s.e _ (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))).core) hfj
  have hfK := Proofs.Consensus.Blocks.preceq_trans hfroot
    (Proofs.Consensus.Blocks.preceq_trans (fgRoot_preceq_voteDutyAnchorAt c p a nr s rho x (d + 1))
      (Proofs.Consensus.Blocks.preceq_trans hAB hBK))
  have hcompat := Proofs.Consensus.Blocks.compatible_of_preceq_common hfK (Proofs.Consensus.Blocks.preceq_self _)
  have hproc := dutyBody_processed_next c p a nr s rho hwf hdom hsleep hu hem hev hbod hK ht2 hvhor hx hcompat
  refine voteDutyHead_passes_supporter_majority_of_band c p a nr s rho hsch hdw x (d + 1) hmaj hAB hBK hproc ?_
  -- `sigma` での `K` の消去の高さは `K` の導出の高さ `hMax - 1`
  have htree := hproc
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree at htree
  dsimp only at htree
  rw [Proofs.Consensus.Trees.mem_filter_iff] at htree
  obtain ⟨Y, hY, hYe, hσ⟩ := voteDutyStore_sigma_named c p a nr s rho x (d + 1) htree.1
  rw [hσ]
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs] at hY
  have hYdir : Statements.Consensus.Spec.Execution.DirectBlockInRun c p a nr s rho Y :=
    Or.inr ⟨x, hx, _, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hY⟩
  have hKb : K ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) row.valIndex).st.bodies.elems := by
    rw [hbod]; exact hK
  have hKdir : Statements.Consensus.Spec.Execution.DirectBlockInRun c p a nr s rho K :=
    Or.inr ⟨row.valIndex, hu, _, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hKb⟩
  have heq : Y = K := hcf Y K ⟨⟨Y, hYdir, Proofs.Consensus.NamedBlocks.namedPreceq_self Y⟩,
      ⟨K, hKdir, Proofs.Consensus.NamedBlocks.namedPreceq_self K⟩⟩ Y K
    ⟨⟨Or.inl (Proofs.Consensus.NamedBlocks.namedPreceq_self _), Or.inr (Proofs.Consensus.NamedBlocks.namedPreceq_self _)⟩,
      by rw [← Proofs.Consensus.NamedBlocks.root_eraseBlock, ← Proofs.Consensus.NamedBlocks.root_eraseBlock, hYe]⟩
  rw [heq, hKh]

/-- **投票の務めの読みの `sigma` の高さは祖先で単調**: `x`(honest)の slot `k` の読みの tree の 2 つのブロック `A ⪯ B` について、
`sigma` での `A` の高さは `B` の高さ以下。どちらも読みの bodies の名前付きブロックの導出の高さ(`voteDutyStore_sigma_named`)で、
`B` の名前付きブロックの祖先に `A` の持ち上げがあり(`NamedBlocks.erased_ancestor_lift`)、root の衝突なしで `A` の名前付きブロックと
同じなので、`EntryHeight.deriveNamed_h_mono`(手書き `derive_height_mono`)に帰着する。手書き `coreStoredHeightAtVoteDuty` と
`derive_height_mono` を合わせた形(周回 284)。 -/
theorem voteDutyStore_sigma_h_mono (hsleep : SleepyRegime c p a nr s rho 0) {x : ValidatorId}
    (hx : rho.honest.contains x = true) (k : Nat) {A B : Block}
    (hA : A ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems)
    (hB : B ∈ (voteDutyStoreAt c p a nr s rho x k).tree.elems) (hAB : preceq A B = true) :
    (Model.Consensus.Protocol.ForkChoice.Goldfish.chainStateOf (voteDutyStoreAt c p a nr s rho x k).sigma A).h ≤
      (Model.Consensus.Protocol.ForkChoice.Goldfish.chainStateOf (voteDutyStoreAt c p a nr s rho x k).sigma B).h := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho hexec).2
  unfold ExecutionValid at hexec
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hexec.1.1.1
  obtain ⟨YA, hYA, hYAe, hσA⟩ := voteDutyStore_sigma_named c p a nr s rho x k hA
  obtain ⟨YB, hYB, hYBe, hσB⟩ := voteDutyStore_sigma_named c p a nr s rho x k hB
  rw [hσA, hσB]
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs] at hYA hYB
  have hin : ∀ D, D ∈ (worldAt (stateBefore c p a nr s rho
      (Proofs.Consensus.ReceiverFinality.idxLt rho (Model.Consensus.Protocol.Schedule.voteTime s.e k))) x).st.bodies.elems →
      Statements.Consensus.Spec.Execution.DirectBlockInRun c p a nr s rho D := fun D hD =>
    Or.inr ⟨x, hx, _, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hD⟩
  rw [← hYBe] at hAB
  obtain ⟨An, hAn, hAne⟩ := Proofs.Consensus.NamedBlocks.erased_ancestor_lift hAB
  have heq : YA = An := hcf YA An
    ⟨⟨YA, hin YA hYA, Proofs.Consensus.NamedBlocks.namedPreceq_self YA⟩, ⟨YB, hin YB hYB, hAn⟩⟩ YA An
    ⟨⟨Or.inl (Proofs.Consensus.NamedBlocks.namedPreceq_self _), Or.inr (Proofs.Consensus.NamedBlocks.namedPreceq_self _)⟩,
      by rw [← Proofs.Consensus.NamedBlocks.root_eraseBlock, ← Proofs.Consensus.NamedBlocks.root_eraseBlock, hYAe, hAne]⟩
  rw [heq]
  exact Proofs.Consensus.EntryHeight.deriveNamed_h_mono s.e s.cfg hAn

/-- **段の橋の band の枝(名前付きの高さの形)**: `voteDutyHead_passes_supporter_majority_of_bandHead` の `hband` を、`B` の
名前付きブロック `Bn`(run の中、消去が `B`)の導出の高さで与える形。head は `x` の読みの処理済み tree にあり
(`voteDutyHead_processed_next`)、その `sigma` の高さは名前付き導出 `Y` の高さ(`voteDutyStore_sigma_named`)で、`B` の持ち上げは
`Y` の祖先かつ root の衝突なしで `Bn` なので、`deriveNamed_h_mono` で `Bn` の高さ ≤ head の高さ。手書き
`coreConeBandDescendant_of_processed` の `by_cases hband`(`Cn` の導出の高さ)の真の枝に当たる(周回 284)。 -/
theorem voteDutyHead_passes_supporter_majority_of_bandNamed (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) (hdw : DeliveryWellFormed c p a nr s rho)
    {u : ValidatorId} (hu : rho.honest.contains u = true) {d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon)
    {x : ValidatorId} (hx : rho.honest.contains x = true) {B : Block}
    (hmaj : Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) B).size)
    (hAB : preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) B = true)
    (hBD : preceq B (voteDutyHeadAt c p a nr s rho u d) = true)
    {Bn : Model.Consensus.Objects.NamedBlocks.NamedBlock}
    (hBnrun : Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho Bn)
    (hBne : Model.Consensus.Objects.NamedBlocks.eraseBlock Bn = B)
    (hband : (voteDutyStoreAt c p a nr s rho x (d + 1)).hMax - 1 ≤
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg Bn).h) :
    preceq B (voteDutyHeadAt c p a nr s rho x (d + 1)) = true := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho hexec).2
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hfj := Proofs.Consensus.ProcessedAncestor.stateBeforeTime_fj c p a nr s rho hs
    (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) x
  have hfroot : preceq
      (worldAt (stateBeforeTime c p a nr s rho (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))) x).st.core.f
      (voteDutyFgRootAt c p a nr s rho x (d + 1)) = true := by
    unfold voteDutyFgRootAt
    exact Proofs.Consensus.ReceiverFinality.store_fgRoot_extends
      (st := (Proofs.Consensus.Voting.clocked s.e _ (Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1))).core) hfj
  have hfh := Proofs.Consensus.Blocks.preceq_trans hfroot
    (Proofs.Consensus.Blocks.preceq_trans (fgRoot_preceq_voteDutyAnchorAt c p a nr s rho x (d + 1))
      (Proofs.Consensus.Blocks.preceq_trans hAB hBD))
  have hcompat := Proofs.Consensus.Blocks.compatible_of_preceq_common hfh (Proofs.Consensus.Blocks.preceq_self _)
  -- head は `x` の読みの tree にあり、その `sigma` の高さは名前付き導出の高さ
  have hproc := voteDutyHead_processed_next c p a nr s rho hwf hdom hsleep hu hhor hx hcompat
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree at hproc
  dsimp only at hproc
  rw [Proofs.Consensus.Trees.mem_filter_iff] at hproc
  obtain ⟨Y, hY, hYe, hσ⟩ := voteDutyStore_sigma_named c p a nr s rho x (d + 1) hproc.1
  refine voteDutyHead_passes_supporter_majority_of_bandHead c p a nr s rho hwf hdom hsleep hdw hu hhor hx hmaj hAB hBD ?_
  rw [hσ]
  -- `B` の名前付きの持ち上げは `Y` の祖先で、root の衝突なしで `Bn`
  rw [← hYe] at hBD
  obtain ⟨An, hAn, hAne⟩ := Proofs.Consensus.NamedBlocks.erased_ancestor_lift hBD
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs] at hY
  have hYdir : Statements.Consensus.Spec.Execution.DirectBlockInRun c p a nr s rho Y :=
    Or.inr ⟨x, hx, _, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hY⟩
  have heq : Bn = An := hcf Bn An ⟨hBnrun, ⟨Y, hYdir, hAn⟩⟩ Bn An
    ⟨⟨Or.inl (Proofs.Consensus.NamedBlocks.namedPreceq_self _), Or.inr (Proofs.Consensus.NamedBlocks.namedPreceq_self _)⟩,
      by rw [← Proofs.Consensus.NamedBlocks.root_eraseBlock, ← Proofs.Consensus.NamedBlocks.root_eraseBlock, hBne, hAne]⟩
  rw [heq] at hband
  exact le_trans hband (Proofs.Consensus.EntryHeight.deriveNamed_h_mono s.e s.cfg hAn)

/-- **確認の締切は投票時刻ではない**(Δ > 0): `4Δ · k + 2Δ = 4Δ · k' + Δ` なら `1 = 4 · (k' - k)` で、整数では成り立たない
(`supportCutoff_ne_proposalTime` と同じ運び。周回 277)。 -/
theorem supportCutoff_ne_voteTime {e : Model.Consensus.Objects.Parameters.ProtocolEnv} (hδ : 0 < e.delta) (k k' : Nat) :
    Model.Consensus.Protocol.Schedule.supportCutoff e k ≠ Model.Consensus.Protocol.Schedule.voteTime e k' := by
  unfold Model.Consensus.Protocol.Schedule.supportCutoff Model.Consensus.Protocol.Schedule.voteTime
    Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
  simp only [Int.ofNat_eq_natCast]
  intro h
  have h0 : e.delta * (4 * (k' : Int) - 4 * (k : Int) - 1) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hδ.ne' h1
  · omega

/-- **確認評価の tick の確認の更新の前の段は時計を合わせただけ**(Δ > 0): tick の時刻は確認の締切で、提案時刻でも投票時刻でもない
(`supportCutoff_ne_proposalTime` / `supportCutoff_ne_voteTime`)ので、`tickPreUpdateStore` は提案も投票もしない(周回 277)。 -/
theorem confPreUpdate_eq (hδ : 0 < s.e.delta) {w : ValidatorId} {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t) :
    Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t =
      { (worldAt (stateBefore c p a nr s rho i) w).st with
        core := { (worldAt (stateBefore c p a nr s rho i) w).st.core with
          t := t, s := Model.Consensus.Objects.Parameters.slotOf s.e t } } := by
  have hnp : ¬ ((decide (0 < Model.Consensus.Objects.Parameters.slotOf s.e t) &&
      (t == Model.Consensus.Protocol.Schedule.proposalTime s.e (Model.Consensus.Objects.Parameters.slotOf s.e t))) &&
      (p (Model.Consensus.Objects.Parameters.slotOf s.e t) == (Model.Consensus.Execution.Setup.setupNode w).valIndex)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    rintro ⟨⟨-, hp⟩, -⟩
    exact supportCutoff_ne_proposalTime hδ _ _ (ht.2.2.symm.trans hp)
  have hnv : ¬ (decide (0 < Model.Consensus.Objects.Parameters.slotOf s.e t) &&
      (t == Model.Consensus.Protocol.Schedule.voteTime s.e (Model.Consensus.Objects.Parameters.slotOf s.e t))) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    rintro ⟨-, hv⟩
    exact supportCutoff_ne_voteTime hδ _ _ (ht.2.2.symm.trans hv)
  unfold Proofs.Consensus.RootWitness.preUpdateStoreAt Proofs.Consensus.AttestationSource.tickPreUpdateStore
  dsimp only
  split_ifs
  rfl

/-- 支持の投票 `u` と同じ投票者の遅い投票は `u` そのもの(`noSecondVoteIn lateVotes` の絞り込み。`Majority.supportVotes_unique` の
片方を遅い投票に広げた形)。 -/
theorem supportVotes_eq_of_late {e : Model.Consensus.Objects.Parameters.ProtocolEnv}
    {st : Model.Consensus.Protocol.Store.Store} {k : Nat} {u u' : Model.Consensus.Objects.Blocks.GoldfishVote}
    (hu : u ∈ (Proofs.Consensus.Goldfish.supportVotes e st k).elems)
    (hu' : u' ∈ (Proofs.Consensus.Goldfish.lateVotes e st k).elems) (hv : u'.valIndex = u.valIndex) : u' = u := by
  unfold Proofs.Consensus.Goldfish.supportVotes at hu
  obtain ⟨-, hno⟩ := (Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hu
  unfold Model.Consensus.Protocol.ForkChoice.Goldfish.noSecondVoteIn NaruStd.Set.all at hno
  rw [List.all_eq_true] at hno
  have h := hno u' hu'
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h
  rcases h with h | h
  · exact h
  · exact absurd hv h

/-- honest な 2 つのノードの読みの tree の要素は root が等しければ同じブロック(`tickTree_root_inj` の 2 ノード版。周回 277)。 -/
theorem runTree_root_inj (hsleep : SleepyRegime c p a nr s rho 0) {w₁ w₂ : ValidatorId}
    (hw₁ : rho.honest.contains w₁ = true) (hw₂ : rho.honest.contains w₂ = true) (j₁ j₂ : Nat)
    {x y : Block} (hx : x ∈ (worldAt (stateBefore c p a nr s rho j₁) w₁).st.core.tree.elems)
    (hy : y ∈ (worldAt (stateBefore c p a nr s rho j₂) w₂).st.core.tree.elems)
    (hr : root x = root y) : x = y := by
  have hcf : Statements.Consensus.Spec.Execution.NamedRootCollisionFree c p a nr s rho :=
    (runWellFormed_of_executionValid c p a nr s rho (Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep)).2
  have hin : ∀ (w : ValidatorId) (j : Nat), rho.honest.contains w = true →
      ∀ D, D ∈ (worldAt (stateBefore c p a nr s rho j) w).st.bodies.elems →
      Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho D := fun w j hw D hD =>
    ⟨D, Or.inr ⟨w, hw, j, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hD⟩,
      Proofs.Consensus.NamedBlocks.namedPreceq_self D⟩
  obtain ⟨X, hX, rfl⟩ := (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho j₁ w₁).named x hx
  obtain ⟨Y, hY, rfl⟩ := (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho j₂ w₂).named y hy
  exact Proofs.Consensus.FinalizedAccountable.rootInjective_of_collisionFree c p a nr s rho hcf
    (hin w₁ j₁ hw₁ X hX) (hin w₂ j₂ hw₂ Y hY)
    _ _ ⟨⟨Or.inl (Proofs.Consensus.Blocks.preceq_self _), Or.inr (Proofs.Consensus.Blocks.preceq_self _)⟩, hr⟩

/-- **genuine な確認には honest な委員の支持者がいる**(GST-zero、`1 ≤ d`): 確認評価の tick(slot `d = slotOf e t - 1`)の genuine な確認 `C`
について、slot `d` の委員会の honest な元 `y` があり、`C` は `y` の slot `d` の投票の務めの head の祖先。手書き
`WeakGoldfish.genuineConfirmation_exists_honestVoteSupporter_after_gst`(`Protocol/ForkChoice/Views/WeakConfirmationSupport.lean`)に当たる。
運び: 確認の更新の前の段は時計を合わせただけ(`confPreUpdate_eq`)なので pool・印・tree は tick の前の store のもの。slot `d` の委員会の
honest な元はみな投票時刻に投票を出し(`Voting.honest_emits_gfVote_head`)、GST 以後なので支持の締切より前の受信の印で `w` の pool に入る
(`Stamps.partialSynchrony_honest_gfVote_stamped`。扱いの添字は時刻が締切より前なので tick の添字より前)ので、遅い投票の参加者。
`C` は eligible なので honest な支持者 `v` がいて(`Majority.exists_honest_supporter_of_eligible`)、その支持の投票は `v` の遅い投票と
同じ(`supportVotes_eq_of_late`)なので head は `v` の投票の務めの head の root。`C` の上の解決先と務めの head はどちらも honest な
ノードの読みの tree の要素で root が等しいので同じブロック(`runTree_root_inj`。周回 277)。 -/
theorem genuineConf_honestVoteSupporter (hwf : SetupWellFormed c p s) (hsleep : SleepyRegime c p a nr s rho 0)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t) {d : Nat}
    (hq : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 = d) (hd : 1 ≤ d) {C : Block}
    (hC : Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C) :
    ∃ y, rho.honest.contains y = true ∧ (c d).contains y = true ∧
      preceq C (voteDutyHeadAt c p a nr s rho y d) = true := by
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hreg := hsleep
  unfold SleepyRegime at hreg
  obtain ⟨⟨⟨⟨⟨hexec, hps⟩, hgst⟩, hhc⟩, -⟩, -⟩ := hreg
  unfold ExecutionValid at hexec
  obtain ⟨⟨⟨hsch, -⟩, hunf⟩, -⟩ := hexec
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnd : EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  have htime : t = Model.Consensus.Protocol.Schedule.confirmationTime s.e d := by
    rw [← hq]; exact Proofs.Consensus.ConfirmedOrigin.confTick_time s rho ht
  have hconfHor : Model.Consensus.Protocol.Schedule.confirmationTime s.e d ≤ rho.horizon := by
    rw [← hq]; exact Proofs.Consensus.ConfirmedOrigin.confTick_horizon s rho hsch ht
  have hcutConf : Model.Consensus.Protocol.Schedule.supportCutoff s.e d ≤
      Model.Consensus.Protocol.Schedule.confirmationTime s.e d :=
    Proofs.Consensus.Majority.supportCutoff_le_confirmationTime s.e d hδ.le
  have hvoteCut : Model.Consensus.Protocol.Schedule.voteTime s.e d ≤
      Model.Consensus.Protocol.Schedule.supportCutoff s.e d := by
    unfold Model.Consensus.Protocol.Schedule.voteTime Model.Consensus.Protocol.Schedule.supportCutoff
    linarith
  have hvoteNonneg : 0 ≤ Model.Consensus.Protocol.Schedule.voteTime s.e d := by
    unfold Model.Consensus.Protocol.Schedule.voteTime Model.Consensus.Objects.Parameters.slotTime
      Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    positivity
  set st := (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core with hst
  have hpre := confPreUpdate_eq c p a nr s rho hδ ht
  have hpool : ∀ k, Proofs.Consensus.Votes.poolList st k =
      Proofs.Consensus.Votes.poolList (worldAt (stateBefore c p a nr s rho i) w).st.core k := by
    intro k; rw [hst, hpre]; rfl
  have htv : st.timestampVote = (worldAt (stateBefore c p a nr s rho i) w).st.core.timestampVote := by
    rw [hst, hpre]
  have htree : st.tree = (worldAt (stateBefore c p a nr s rho i) w).st.core.tree := by
    rw [hst, hpre]
  have hinv : Proofs.Consensus.Votes.PoolInv c st := fun k u hu =>
    Proofs.Consensus.Votes.stateBefore_pool c p a nr s rho i w k u (by rw [← hpool]; exact hu)
  -- slot `d` の委員会の honest な元の投票は `st` の遅い投票
  have hvote : ∀ v, (c d).contains v = true → rho.honest.contains v = true →
      ∃ u iv, u ∈ (Proofs.Consensus.Goldfish.lateVotes s.e st d).elems ∧ u.valIndex = v ∧
        rho.events[iv]? = some (NamedEvent.Tick v (Model.Consensus.Protocol.Schedule.voteTime s.e d)) ∧
        u.head = Proofs.Consensus.Voting.voteHead
          (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho iv) v).st.core)
            (Model.Consensus.Protocol.Schedule.voteTime s.e d) (worldAt (stateBefore c p a nr s rho iv) v).cache)
          s.e s.hc (Proofs.Consensus.Voting.clocked s.e (worldAt (stateBefore c p a nr s rho iv) v).st
            (Model.Consensus.Protocol.Schedule.voteTime s.e d)).core := by
    intro v hvc hv
    obtain ⟨u, iv, hem, hval, hslot, hevv, hhead⟩ :=
      Proofs.Consensus.Voting.honest_emits_gfVote_head c p a nr s rho hsch hδ hv (by omega) hvc
        (le_trans (le_trans hvoteCut hcutConf) hconfHor)
    have hcut : Model.Consensus.Protocol.Schedule.supportCutoff s.e u.slot ≤ rho.horizon := by
      rw [hslot]; exact le_trans hcutConf hconfHor
    obtain ⟨t2, j, ⟨-, ht2⟩, hh, hmem⟩ :=
      Proofs.Consensus.Stamps.partialSynchrony_honest_gfVote_stamped c p a nr s rho hps hsch hunf hδ hem hv
        (le_trans hgst hvoteNonneg) hw hcut
    obtain ⟨ev, hevj, hte⟩ := Proofs.Consensus.Stamps.handlesAt_event c p a nr s rho hh
    have hji : j < i := by
      refine Proofs.Consensus.Window.lt_of_time_lt hs hevj ht.1 ?_
      show eventTime ev < t
      rw [hte, htime]
      rw [hslot] at ht2
      exact lt_of_lt_of_le ht2 hcutConf
    obtain ⟨hm, hob⟩ := hmem i hji
    refine ⟨u, iv, ?_, hval, hevv, hhead⟩
    unfold Proofs.Consensus.Goldfish.lateVotes
    rw [Proofs.Consensus.Trees.mem_filter_iff]
    refine ⟨(Proofs.Consensus.Votes.mem_storePool_iff st d u).mpr (by rw [hpool, ← hslot]; exact hm), ?_⟩
    rw [htv]
    rw [hslot] at hob
    exact Proofs.Consensus.GradeSupporter.occurrenceBefore_mono hob hcutConf
  have hall : ∀ v ∈ (c d).elems, v ∈ rho.honest.elems →
      v ∈ (Model.Consensus.Protocol.ForkChoice.Goldfish.rawParticipants
        (Proofs.Consensus.Goldfish.lateVotes s.e st d)).elems := by
    intro v hvc hvh
    obtain ⟨u, -, hlate, hval, -⟩ := hvote v
      ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hvc)
      ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hvh)
    exact Proofs.Consensus.Majority.mem_rawParticipants_of_voters
      ((Proofs.Consensus.Goldfish.mem_voters_iff _ _).mpr ⟨u, hlate, hval⟩)
  have hel : Proofs.Consensus.Goldfish.eligible s.e st d C = true := by
    have h := hC.2
    rw [hq] at h
    exact h
  obtain ⟨v, u, hvH, hu, hvi, -, htu⟩ :=
    Proofs.Consensus.Majority.exists_honest_supporter_of_eligible s.e d C rho.honest hδ.le hinv
      (Proofs.Consensus.Majority.committee_sorted hwf d) (Proofs.Consensus.Majority.honestCommittees_at hhc d) hall hel
  have hv : rho.honest.contains v = true := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hvH
  have hvc : (c d).contains v = true := by
    rw [← hvi]
    exact (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr
      (Proofs.Consensus.Majority.supportVotes_committee hinv hδ.le hu)
  obtain ⟨u', iv, hlate', hval', hevv, hhead⟩ := hvote v hvc hv
  have huu : u' = u := supportVotes_eq_of_late hu hlate' (hval'.trans hvi.symm)
  subst huu
  -- 務めの head は tick の前の `v` の store の tree の要素
  have hti := Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho iv v
  have hmemV := voteHeadBlock_mem_tree
    (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho iv) v).st.core)
          (Model.Consensus.Protocol.Schedule.voteTime s.e d)
          (worldAt (stateBefore c p a nr s rho iv) v).cache) s.e s.hc
    (st := (Proofs.Consensus.Voting.clocked s.e
      (worldAt (stateBefore c p a nr s rho iv) v).st (Model.Consensus.Protocol.Schedule.voteTime s.e d)).core)
    (hti.congr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  have hduty : voteDutyHeadAt c p a nr s rho v d =
      Proofs.Consensus.Voting.voteHeadBlock
        (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (Model.Consensus.Protocol.Store.storeToHealing (worldAt (stateBefore c p a nr s rho iv) v).st.core)
          (Model.Consensus.Protocol.Schedule.voteTime s.e d)
          (worldAt (stateBefore c p a nr s rho iv) v).cache) s.e s.hc
        (Proofs.Consensus.Voting.clocked s.e
          (worldAt (stateBefore c p a nr s rho iv) v).st (Model.Consensus.Protocol.Schedule.voteTime s.e d)).core := by
    unfold voteDutyHeadAt; dsimp only
    rw [← Proofs.Consensus.RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime c p a nr s rho hs
      (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) hevv]
    rfl
  refine ⟨v, hv, hvc, ?_⟩
  unfold Model.Consensus.Protocol.ForkChoice.Goldfish.targetsUnder at htu
  split at htu
  · rename_i X hX
    obtain ⟨-, hCX⟩ := Bool.and_eq_true_iff.mp htu
    have hXmem : X ∈ (worldAt (stateBefore c p a nr s rho i) w).st.core.tree.elems := by
      rw [← htree]; exact (Proofs.Consensus.BlockStamps.findRoot?_mem hX).1
    have hXr : root X = u'.head := (Proofs.Consensus.BlockStamps.findRoot?_mem hX).2
    have hXV : X = voteDutyHeadAt c p a nr s rho v d := by
      rw [hduty]
      refine runTree_root_inj c p a nr s rho hsleep hw hv i iv hXmem hmemV ?_
      rw [hXr, hhead, Proofs.Consensus.Voting.voteHead_eq_root]
    rw [← hXV]
    exact hCX
  · exact absurd htu Bool.false_ne_true

/-- **新しい確認の段の anchor の互換**: slot `d` の genuine な確認 `C` には、slot `d` の head が `C` を延ばす honest な委員 `y` がいる
(`genuineConf_honestVoteSupporter`)。honest なノード `x` の slot `d + 1` の読みの anchor も `y` の slot `d` の head の祖先
(`voteDutyAnchor_preceq_prevHead`)なので互換で、`C` が anchor の祖先でなければ anchor ⪯ `C`(`anchor_preceq_of_notBelow` と同じ形。
周回 277)。 -/
theorem anchor_preceq_of_genuineConf (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) (hprior : PriorConfsBelow c p a nr s rho d)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hq : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 = d) {C : Block}
    (hC : Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hanc : ¬ preceq C (voteDutyAnchorAt c p a nr s rho x (d + 1)) = true) :
    preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) C = true := by
  obtain ⟨y, hy, -, hCy⟩ := genuineConf_honestVoteSupporter c p a nr s rho hwf hsleep hw ht hq hd hC
  exact (Proofs.Consensus.Blocks.preceq_linear hCy
    (voteDutyAnchor_preceq_prevHead c p a nr s rho hwf hdom hsleep hhor hd hdlast hprior hx hy)).resolve_left hanc

/-- **保護の保存の段の `heads`**(周回 270 に穴として置き、周回 297 に閉じた)。`1 ≤ d ≤ last` で、slot `d` 未満の genuine な確認が slot `d` の投票の head の祖先なら(`PriorConfsBelow d`)、
slot `d` で保護された `B` は、すべての honest なノードの slot `d + 1` の投票の務めの head の祖先(cone は `voteCone_of_heads` で出るので
`protectedVoteSlot_of_heads` で slot `d + 1` の保護になる)。手書き `protectedVoteSlots_of_historyCut_v2_w` の段の `hpreserve`
(`DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/WeakBootstrapSlot.lean`。`P = genesis` なので `P ⪯ B` は自明)に当たる。
閉じるのに要るもの: 委員会の honest な元 `x` の slot `d` の head `D` を上界に `laterVoteHead_rowSources_of_prior` で行の源を押さえ、
読みの FG root と anchor が `B` と互換であることを示す(手書き `WeakGoldfish.goldfishCone_succ_of_runFrontierWitnesses` の heads の側)
(周回 270。周回 273 に結論を cone から切り離して `heads` だけにした)。周回 274 から 1 つの honest なノード `x` についての主張で、
`B` が `x` の読みの FG root の祖先である枝は `heads_of_notBelowFgRoot` が閉じるので、`B` が FG root の祖先でない(手書き
`goldfishCone_step'` の `hrootBelow` の枝)ときだけを示せばよい。周回 275 から、互換でない場合は `fgRoot_preceq_of_notBelow` が
排除し、穴は FG root が `B` の真の祖先である枝だけになった。周回 276 から同じことを anchor(`voteDutyAnchorAt`。FG root を延ばす)で
行い、`B` が anchor の祖先の枝は `heads_of_notBelowAnchor`、互換でない場合は `anchor_preceq_of_notBelow` が閉じるので、穴は anchor が
`B` の真の祖先である(`hbelow` ∧ `hanc`。FG root ⪯ anchor ⪯ `B` も従う)枝だけ。残りは手書き `goldfishCone_step'` の `hrootBelow` の枝
(`coreConeBandDescendant_of_runFrontier` → `coreGoldfishConePathEligible` → `goldfish_fork_choice_captures_supporter_majority`)。
周回 278 から歩みの組合せの層は `voteDutyHead_passes_supporter_majority`(証明済み)にあり、残りはその前提: 読みの voter view での
`B` の支持者の過半、`voterSupportView ⊆ voterView`、歩みの tree の重複なし、anchor から `B` までの途中が歩みの tree にあること。
周回 279 から重複なしと包含の pooled の部分は証明済みで、`voteDutyHead_passes_supporter_majority_of_carried` の残りの前提は
carried の包含 `hcar`・過半 `hmaj`・`hAB`(= `hbelow`)・`hpath`。周回 280 から `hcar` も証明済み(`voteDutyStore_tree_carried`。
`hdw` は `hsleep` の `ExecutionValid` から)で、`voteDutyHead_passes_supporter_majority_of_delivery` の残りの前提は `hmaj`・`hAB`・`hpath`。
周回 281 から `hpath` も、対象の子孫で読みの処理済み tree にあり高さが band のブロック `D` から出る
(`voteDutyHead_passes_supporter_majority_of_band`。`hsch` は `hexec.1.1.1`)ので、残りは `hmaj` と band の子孫 `D`
(手書き `coreConeBandDescendant_of_runFrontier`)。周回 282 から、band の枝の `D` の候補(honest な委員の slot `d` の投票の務めの head)が
`x` の slot `d + 1` の読みの処理済み tree にあることは `voteDutyHead_processed_next`(証明済み。読みの finalized との互換が前提)が出す。
周回 283 から、band の枝(`D` = honest な `u` の slot `d` の head で、`x` の読みの `sigma` での高さが `hMax - 1` 以上)は
`voteDutyHead_passes_supporter_majority_of_bandHead`(証明済み。互換も中で出す)で閉じ、前提は `hmaj`・`hAB`・`B ⪯ head`・`hband`。
`hband` の高さは `voteDutyStore_sigma_named` で読みの bodies の名前付きブロックの導出 `deriveNamed` の高さに読み替えられる。
周回 284 から、band の判定を `B` の名前付きブロック `Bn`(run の中)の導出の高さで与える形
`voteDutyHead_passes_supporter_majority_of_bandNamed`(証明済み。手書き `by_cases hband` の真の枝)があり、読みの tree の上の
`sigma` の高さの単調性は `voteDutyStore_sigma_h_mono`。
周回 285 から、frontier の証人の出発点(読みの `hMax` を導出の高さで担う bodies のブロック `W`。手書き
`maximum_carrier_stateBeforeTime`)は `voteDutyStore_maxCarrier`(証明済み)。
周回 289 から、band に届かない枝(`Bn` の導出の高さ < `hMax - 1`)は `voteDutyHead_passes_supporter_majority_of_belowBand`
(証明済み。frontier の確認の証人 `K` を band の子孫に取る)で閉じ、前提は `hmaj`・`hAB`・honest な `y` の slot `d` の head が `B` の
子孫・`hprior y`。band の枝と合わせ、`B` の名前付きブロックで場合分けすれば、残りは `hmaj`(読みの voter view での `B` の支持者の過半)だけ。
周回 290 から `hmaj` は `voteDutyStore_supporterMajority_of_cone`(証明済み。`HonestCommittees` と committee の整列は regime から)で、
読みの voter view の参加者が committee に収まること・honest な委員が equivocate しないこと・honest な委員が支持の voter view に `B` 以下を
指す投票を持つこと(手書き `corePreparedVoteViewValid` / `coreVoterViewNoHonestEquivocation` / `coneSupport_of_named_votes` の `vote`)に分かれる。
周回 291 から参加者の committee は `voteDutyStore_participants_committee`(証明済み。`DeliveryWellFormed`)で外れ、
`voteDutyStore_supporterMajority_of_cone_delivery` の残りの前提は `hno` と `hvote`。
周回 292 から `hno` も `voteDutyStore_no_honest_equivocation`(証明済み。`ScheduleWellFormed` / `UnforgeableSignatures`)で外れ、
`voteDutyStore_supporterMajority_of_cone_run` の残りの前提は `hvote` だけ。
周回 293 から `hvote` は `voteDutyStore_supportVote_of_pool` で、読みの pool の投票・head を root に持つ読みの tree のブロック・2 つの
受信の印の形 `hpv` に移った。周回 294 から、`hpv` の honest な委員の投票と、その head のブロックが `B` の子孫で slot が `st.s - 1` 以下で
あることは、slot `st.s - 1` の honest なノードの head が `B` の子孫なら cone の形(`voteConeSlot_of_heads`)で出る。周回 296 から tree の側
(head のブロックが読みの tree に `viewFreeze (st.s - 1)` より前の印で入ること)は `voteConeStamped_of_heads`(前提は slot `st.s - 1` の
`heads` と anchor ⪯ `B`)で出る。周回 297 に pool の側(その投票が読みの pool のバケツ `st.s - 1` に凍結より前の印で入ること)を
`voteConePooled_of_heads`(`Stamps.partialSynchrony_honest_gfVote_stamped`)で出し、`hmaj` を `voteDutyStore_supporterMajority_of_heads`
で組んで閉じた: `B` は `x` の slot `d` の head(読みの bodies の名前付きブロックの消去)の祖先なので名前付きの持ち上げ `Bn` があり、
その導出の高さが band に届けば `voteDutyHead_passes_supporter_majority_of_bandNamed`、届かなければ `_of_belowBand`(`hprior x`)。 -/
theorem protectedVoteSlot_preserve (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) (hprior : PriorConfsBelow c p a nr s rho d) {B : Block}
    (hB : ProtectedVoteSlot c p a nr s rho d B) {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hanc : ¬ preceq B (voteDutyAnchorAt c p a nr s rho x (d + 1)) = true)
    (hbelow : preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) B = true) :
    preceq B (voteDutyHeadAt c p a nr s rho x (d + 1)) = true := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hdw : DeliveryWellFormed c p a nr s rho := hexec.1.1.2
  have hhc : HonestCommittees c rho.honest := hsleep.1.1.2
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hmaj := voteDutyStore_supporterMajority_of_heads c p a nr s rho hwf hdom hsleep hhc hdw hhor hd hdlast
    hB.heads hx hbelow
  -- `B` の名前付きの持ち上げ: `x` の slot `d` の head は読みの bodies の名前付きブロック `Y` の消去で、`B` はその祖先
  have hmem : voteDutyHeadAt c p a nr s rho x d ∈
      (worldAt (stateBefore c p a nr s rho
        (Proofs.Consensus.ReceiverFinality.idxLt rho (Model.Consensus.Protocol.Schedule.voteTime s.e d))) x).st.core.tree.elems := by
    rw [← Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
    unfold voteDutyHeadAt
    exact voteHeadBlock_mem_tree _ s.e s.hc
      ((Proofs.Consensus.Trees.stateBeforeTime_treeInv c p a nr s rho _ x).congr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  obtain ⟨Y, hY, hYe⟩ := (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho _ x).named _ hmem
  have hBY := hB.heads x hx
  rw [← hYe] at hBY
  obtain ⟨Bn, hBn, hBne⟩ := Proofs.Consensus.NamedBlocks.erased_ancestor_lift hBY
  have hBnrun : Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho Bn :=
    ⟨Y, Or.inr ⟨x, hx, _, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hY⟩,
      hBn⟩
  have hvhor : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon := by
    refine le_trans ?_ hhor
    have hd' : (d : Int) ≤ (last : Int) := by exact_mod_cast hdlast
    have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
    unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  by_cases hband : (voteDutyStoreAt c p a nr s rho x (d + 1)).hMax - 1 ≤
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg Bn).h
  · exact voteDutyHead_passes_supporter_majority_of_bandNamed c p a nr s rho hwf hdom hsleep hdw hx hvhor hx hmaj
      hbelow (hB.heads x hx) hBnrun hBne hband
  · exact voteDutyHead_passes_supporter_majority_of_belowBand c p a nr s rho hwf hdom hsleep hdw hhor hd hdlast hx
      (hprior x hx) hx hmaj hbelow (hB.heads x hx) hBnrun hBne (Nat.lt_of_not_le hband)

/-- 穴: 新しい確認の段の移送の境界。`1 ≤ d ≤ last` で、slot `q = d` の確認評価の tick の genuine な確認 `C` が honest なノード `x` の
slot `d + 1` の読みの FG root の子孫なら、確認の更新の前の段の store の slot `d` の確認(分子 `supportVotes`、分母 `lateVotes`)から
`x` の slot `d + 1` の読みの voter view(投票 `voterView`、支持の投票 `voterSupportView`、tree は読みの tree)への
`Majority.AdoptionTransport` がある。手書き `adoptionTransport_B_after_gst`
(`DecoupledConsensusProofs/Protocol/Schedule/WeakConfirmationTransport.lean`)に当たる。周回 299 に `genuineConf_supporterMajority` の
数え上げ(`AdoptionTransport.supporterMajority_of_eligible`)を外して切り出した。閉じるのに要るもの: `forward` は、`C` 以下を指す分子の
投票が GST 以後なので読みの pool に凍結より前の印で入り(honest な投票は `Stamps.partialSynchrony_honest_gfVote_stamped`、byzantine の
投票は読み手が受けた配送の中継)、その head の解決先が読みの tree にあること(`voteDutyHead_stamped_next` の運び)。`backward` は、読みの
voter view の投票が確認の遅い投票にあるか、遅い投票で equivocation が検出済みであること(凍結より前に読み手が受けた投票は中継で
確認の評価者にも `confirmationTime` までに届く)。 -/
theorem genuineConf_adoptionTransport (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hq : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 = d) {C : Block}
    (hC : Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hroot : preceq (voteDutyFgRootAt c p a nr s rho x (d + 1)) C = true) :
    Proofs.Consensus.Majority.AdoptionTransport s.e (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core d
      (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))).tree
      (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
          (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
        (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
      (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
        (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
          (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
        (voteDutyStoreAt c p a nr s rho x (d + 1)).s) C := by
  sorry

/-- **新しい確認の段の過半の移送**(周回 298 に穴として置き、周回 299 に閉じた)。`1 ≤ d ≤ last` で、slot `q = d` の確認評価の tick の
genuine な確認 `C` が honest なノード `x` の slot `d + 1` の読みの FG root の子孫なら、その読みの voter view で `C` の支持者は過半
(`votersCount < 2 · rawSupporters`)。手書き `confirmation_adoption`(`Protocol/ForkChoice/Goldfish/Adoption.lean`)を
`adoptionTransport_B_after_gst`(`Protocol/Schedule/WeakConfirmationTransport.lean`)の境界に掛けた形。`C` は確認の更新の前の段の
store の slot `d` で eligible(`GenuineConfirmationAt` の第 2 欄)なので、移送の境界(穴 `genuineConf_adoptionTransport`)と
`Majority.AdoptionTransport.supporterMajority_of_eligible` で出る。読みの slot は `d + 1`(`Voting.slotOf_voteTime`)、読みの投票の重複なしは
`voterView` が整列した集合の和(`SortedLt.foldl_insert`)であることから。 -/
theorem genuineConf_supporterMajority (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hq : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 = d) {C : Block}
    (hC : Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hroot : preceq (voteDutyFgRootAt c p a nr s rho x (d + 1)) C = true) :
    Model.Consensus.Protocol.ForkChoice.Goldfish.votersCount s.e
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) <
      2 * (Model.Consensus.Protocol.ForkChoice.Goldfish.rawSupporters
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))).tree
        (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        (Model.Consensus.Protocol.ForkChoice.Views.voterSupportView s.e
          (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
            (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
          (voteDutyStoreAt c p a nr s rho x (d + 1)).s)
        ((voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1) C).size := by
  have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
  have hT := genuineConf_adoptionTransport c p a nr s rho hwf hdom hsleep hhor hd hdlast hw ht hq hC hx hroot
  have helig := hC.2
  rw [hq] at helig
  have hsd : (voteDutyStoreAt c p a nr s rho x (d + 1)).s - 1 = d := by
    rw [show (voteDutyStoreAt c p a nr s rho x (d + 1)).s = d + 1 from Proofs.Consensus.Voting.slotOf_voteTime s.e hδ (d + 1)]
    omega
  have hnd : (Model.Consensus.Protocol.ForkChoice.Views.voterView s.e
      (Model.Consensus.Protocol.ForkChoice.Goldfish.fgToGoldfish
        (Model.Consensus.Protocol.Store.storeToHealing (voteDutyStoreAt c p a nr s rho x (d + 1))))
      (voteDutyStoreAt c p a nr s rho x (d + 1)).s).elems.Nodup := by
    unfold Model.Consensus.Protocol.ForkChoice.Views.voterView NaruStd.Set.union
    dsimp only
    refine Proofs.Consensus.Majority.SortedLt.nodup Proofs.Consensus.Majority.gv_irrefl ?_
    exact Proofs.Consensus.Majority.SortedLt.foldl_insert Proofs.Consensus.Orders.gv_compare_eq_iff
      Proofs.Consensus.Majority.gv_lt_trans Proofs.Consensus.Majority.gv_gt_lt _
      (Proofs.Consensus.Majority.SortedLt.filter (Proofs.Consensus.Majority.SortedLt.toSet
        Proofs.Consensus.Orders.gv_compare_eq_iff Proofs.Consensus.Majority.gv_lt_trans
        Proofs.Consensus.Majority.gv_gt_lt _) _)
  rw [hsd]
  exact hT.supporterMajority_of_eligible (le_of_lt hδ) hnd helig _

/-- **新しい確認の段の `heads`**(周回 270 に穴として置き、周回 298 に閉じた)。`1 ≤ d ≤ last` で `PriorConfsBelow d` なら、slot `q = d` の確認評価の tick の genuine な確認 `C` は
すべての honest なノードの slot `d + 1` の投票の務めの head の祖先(`protectedVoteSlot_of_heads` で slot `d + 1` の保護になる)。
手書き `protectedVoteSlots_of_historyCut_v2_w` の段の `q = d` の枝(`P ⪯ B` の向き。`P = genesis` なので
常にこの向き)で、`WeakGoldfish.protectedVoteSlot_succ_of_genuineConfirmationWith`
(`DecoupledConsensusProofs/Protocol/ForkChoice/Views/WeakConfirmationHead.lean`)に当たる(周回 270。周回 273 に結論を `heads` だけにした)。周回 274 から
1 つの honest なノード `x` についての主張。周回 277 から `protectedVoteSlot_preserve` と同じ anchor の形: `C` が anchor の祖先の枝は
`heads_of_notBelowAnchor`、互換は `C` の honest な支持者(`genuineConf_honestVoteSupporter`。手書き
`genuineConfirmation_exists_honestVoteSupporter_after_gst`)を介して `anchor_preceq_of_genuineConf` が出すので、穴は anchor が `C` の
真の祖先である(`hbelow` ∧ `hanc`)枝だけ。閉じるのに要るもの: anchor から `C` までの `ghost` の歩みが `C` を通ること(`C` は slot `d`
で eligible なので、経路の各ブロックの得点は過半。手書き `protectedVoteSlot_succ_of_genuineConfirmationWith` の head の段と
`goldfish_fork_choice_captures_supporter_majority`)。周回 278 から歩みの組合せの層は `voteDutyHead_passes_supporter_majority`
(証明済み)にあり、残りはその前提(読みの voter view での `C` の支持者の過半、`voterSupportView ⊆ voterView`、歩みの tree の重複なし、
anchor から `C` までの途中が歩みの tree にあること)。周回 279 から重複なしと包含の pooled の部分は証明済みで、
`voteDutyHead_passes_supporter_majority_of_carried` の残りの前提は carried の包含 `hcar`・過半 `hmaj`・`hAB`(= `hbelow`)・`hpath`。周回 280 から `hcar` も証明済み(`voteDutyStore_tree_carried`。
`hdw` は `hsleep` の `ExecutionValid` から)で、`voteDutyHead_passes_supporter_majority_of_delivery` の残りの前提は `hmaj`・`hAB`・`hpath`。
周回 281 から `hpath` も、対象の子孫で読みの処理済み tree にあり高さが band のブロック `D` から出る
(`voteDutyHead_passes_supporter_majority_of_band`。`hsch` は `hexec.1.1.1`)ので、残りは `hmaj` と band の子孫 `D`
(手書き `coreConeBandDescendant_of_runFrontier`)。周回 282 から、band の枝の `D` の候補(honest な委員の slot `d` の投票の務めの head)が
`x` の slot `d + 1` の読みの処理済み tree にあることは `voteDutyHead_processed_next`(証明済み。読みの finalized との互換が前提)が出す。
周回 283 から、band の枝(`D` = honest な `u` の slot `d` の head で、`x` の読みの `sigma` での高さが `hMax - 1` 以上)は
`voteDutyHead_passes_supporter_majority_of_bandHead`(証明済み。互換も中で出す)で閉じ、前提は `hmaj`・`hAB`・`B ⪯ head`・`hband`。
`hband` の高さは `voteDutyStore_sigma_named` で読みの bodies の名前付きブロックの導出 `deriveNamed` の高さに読み替えられる。
周回 284 から、band の判定を `B` の名前付きブロック `Bn`(run の中)の導出の高さで与える形
`voteDutyHead_passes_supporter_majority_of_bandNamed`(証明済み。手書き `by_cases hband` の真の枝)があり、読みの tree の上の
`sigma` の高さの単調性は `voteDutyStore_sigma_h_mono`。
周回 285 から、frontier の証人の出発点(読みの `hMax` を導出の高さで担う bodies のブロック `W`。手書き
`maximum_carrier_stateBeforeTime`)は `voteDutyStore_maxCarrier`(証明済み)。
周回 289 から、band に届かない枝(`Bn` の導出の高さ < `hMax - 1`)は `voteDutyHead_passes_supporter_majority_of_belowBand`
(証明済み。frontier の確認の証人 `K` を band の子孫に取る)で閉じ、前提は `hmaj`・`hAB`・honest な `y` の slot `d` の head が `B` の
子孫・`hprior y`。band の枝と合わせ、`B` の名前付きブロックで場合分けすれば、残りは `hmaj`(読みの voter view での `B` の支持者の過半)だけ。
周回 290 から `hmaj` は `voteDutyStore_supporterMajority_of_cone`(証明済み。`HonestCommittees` と committee の整列は regime から)で、
読みの voter view の参加者が committee に収まること・honest な委員が equivocate しないこと・honest な委員が支持の voter view に `B` 以下を
指す投票を持つこと(手書き `corePreparedVoteViewValid` / `coreVoterViewNoHonestEquivocation` / `coneSupport_of_named_votes` の `vote`)に分かれる。
周回 291 から参加者の committee は `voteDutyStore_participants_committee`(証明済み。`DeliveryWellFormed`)で外れ、
`voteDutyStore_supporterMajority_of_cone_delivery` の残りの前提は `hno` と `hvote`。
周回 292 から `hno` も `voteDutyStore_no_honest_equivocation`(証明済み。`ScheduleWellFormed` / `UnforgeableSignatures`)で外れ、
`voteDutyStore_supporterMajority_of_cone_run` の残りの前提は `hvote` だけ。
周回 293 から `hvote` は `voteDutyStore_supportVote_of_pool` で、読みの pool の投票・head を root に持つ読みの tree のブロック・2 つの
受信の印の形 `hpv` に移った。周回 294 から、`hpv` の honest な委員の投票と、その head のブロックが `B` の子孫で slot が `st.s - 1` 以下で
あることは、slot `st.s - 1` の honest なノードの head が `B` の子孫なら cone の形(`voteConeSlot_of_heads`)で出る。周回 296 から tree の側
(head のブロックが読みの tree に `viewFreeze (st.s - 1)` より前の印で入ること)は `voteConeStamped_of_heads`(前提は slot `st.s - 1` の
`heads` と anchor ⪯ `B`)で出る。周回 297 から pool の側も `voteConePooled_of_heads` で出て、slot `d` の honest なノードの head が
すべて対象の子孫なら `hmaj` は `voteDutyStore_supporterMajority_of_heads` が出す(`protectedVoteSlot_preserve` はこれで閉じた)。
この段では slot `d` の head が `C` の子孫とは限らないので、周回 298 に `hmaj` を `genuineConf_supporterMajority`(周回 299 に閉じた。手書き
`adoptionTransport_B_after_gst` と `AdoptionTransport.supporters_subset` / `participants_subset` の数え上げ)に切り出して閉じた:
`C` の honest な支持者 `y`(`genuineConf_honestVoteSupporter`。slot `d` の head が `C` の子孫)を上界にとり、`C` を `y` の slot `d` の head
(読みの bodies の名前付きブロックの消去)の祖先として名前付きに持ち上げた `Cn` の導出の高さが band に届けば
`voteDutyHead_passes_supporter_majority_of_bandNamed`、届かなければ `_of_belowBand`(`hprior y`)。 -/
theorem protectedVoteSlot_succ_of_genuineConf (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hdlast : d ≤ last) (hprior : PriorConfsBelow c p a nr s rho d)
    {w : ValidatorId} (hw : rho.honest.contains w = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hq : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 = d) {C : Block}
    (hC : Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C)
    {x : ValidatorId} (hx : rho.honest.contains x = true)
    (hanc : ¬ preceq C (voteDutyAnchorAt c p a nr s rho x (d + 1)) = true)
    (hbelow : preceq (voteDutyAnchorAt c p a nr s rho x (d + 1)) C = true) :
    preceq C (voteDutyHeadAt c p a nr s rho x (d + 1)) = true := by
  have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
  unfold ExecutionValid at hexec
  have hsch : ScheduleWellFormed s rho := hexec.1.1.1
  have hdw : DeliveryWellFormed c p a nr s rho := hexec.1.1.2
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hmaj := genuineConf_supporterMajority c p a nr s rho hwf hdom hsleep hhor hd hdlast hw ht hq hC hx
    (Proofs.Consensus.Blocks.preceq_trans (fgRoot_preceq_voteDutyAnchorAt c p a nr s rho x (d + 1)) hbelow)
  -- `C` の honest な支持者 `y`: slot `d` の head が `C` の子孫
  obtain ⟨y, hy, -, hCy⟩ := genuineConf_honestVoteSupporter c p a nr s rho hwf hsleep hw ht hq hd hC
  -- `C` の名前付きの持ち上げ: `y` の slot `d` の head は読みの bodies の名前付きブロック `Y` の消去で、`C` はその祖先
  have hmem : voteDutyHeadAt c p a nr s rho y d ∈
      (worldAt (stateBefore c p a nr s rho
        (Proofs.Consensus.ReceiverFinality.idxLt rho (Model.Consensus.Protocol.Schedule.voteTime s.e d))) y).st.core.tree.elems := by
    rw [← Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
    unfold voteDutyHeadAt
    exact voteHeadBlock_mem_tree _ s.e s.hc
      ((Proofs.Consensus.Trees.stateBeforeTime_treeInv c p a nr s rho _ y).congr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  obtain ⟨Y, hY, hYe⟩ := (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho _ y).named _ hmem
  have hCY := hCy
  rw [← hYe] at hCY
  obtain ⟨Cn, hCn, hCne⟩ := Proofs.Consensus.NamedBlocks.erased_ancestor_lift hCY
  have hCnrun : Statements.Consensus.Spec.Execution.BlockInRun c p a nr s rho Cn :=
    ⟨Y, Or.inr ⟨y, hy, _, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hY⟩,
      hCn⟩
  have hvhor : Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) ≤ rho.horizon := by
    refine le_trans ?_ hhor
    have hd' : (d : Int) ≤ (last : Int) := by exact_mod_cast hdlast
    have hδ := (Proofs.Consensus.Liveness.wf_facts hwf).1
    unfold Model.Consensus.Protocol.Schedule.confirmationTime Model.Consensus.Protocol.Schedule.voteTime
      Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    simp only [Int.ofNat_eq_natCast]
    push_cast
    nlinarith
  by_cases hband : (voteDutyStoreAt c p a nr s rho x (d + 1)).hMax - 1 ≤
      (Model.Consensus.Protocol.ChainState.deriveNamed s.e s.cfg Cn).h
  · exact voteDutyHead_passes_supporter_majority_of_bandNamed c p a nr s rho hwf hdom hsleep hdw hy hvhor hx hmaj
      hbelow hCy hCnrun hCne hband
  · exact voteDutyHead_passes_supporter_majority_of_belowBand c p a nr s rho hwf hdom hsleep hdw hhor hd hdlast hy
      (hprior y hy) hx hmaj hbelow hCy hCnrun hCne (Nat.lt_of_not_le hband)

/-- **GST-zero の枝の保護された投票の slot**: `1 ≤ d ≤ last + 1`(`last` の確認の時刻は `horizon` 以下)なら、genesis は slot `d` で
保護され、slot `d` 未満の確認評価の tick の genuine な確認もどれも slot `d` で保護される。手書き `protectedVoteSlots_of_gstZero_v2`
(`DecoupledConsensusProofs/Execution/WeakGenesisGSTZeroActionSources.lean`。`base = cut = 0`、`start = 1`、`P = genesis` で
`WeakJoint.protectedVoteSlots_of_historyCut_v2_after_gst` を掛けたもの)と同じ運びの slot の帰納法: 種は `voteCone_genesis`、
slot 0 の確認は `genuineConf_slot_zero` で genesis、段は古い確認を `protectedVoteSlot_preserve`、slot `d` の確認を
`protectedVoteSlot_succ_of_genuineConf` で進める(周回 270)。段の穴は `heads` だけを返し、cone は `protectedVoteSlot_of_heads` が足す
(周回 273)。段の穴はノードごとで、FG root の祖先の枝は `heads_of_notBelowFgRoot` が閉じる(周回 274)。保存の段の FG root と `B` の
互換は `fgRoot_preceq_of_notBelow` が出し(周回 275)、周回 276 からは anchor との互換 `anchor_preceq_of_notBelow` を使う。新しい確認の段も
周回 277 から anchor の枝(`heads_of_notBelowAnchor`)と互換(`anchor_preceq_of_genuineConf`)で穴に渡す。 -/
theorem protectedVoteSlots_gstZero (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon) :
    ∀ d, 1 ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot c p a nr s rho d Block.Genesis ∧
      ∀ (w : ValidatorId) (i : Nat) (t : Int) (C : Block), rho.honest.contains w = true →
        Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t →
        Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d →
        Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C →
        ProtectedVoteSlot c p a nr s rho d C := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
    intro hupper
    have hseed : ProtectedVoteSlot c p a nr s rho 1 Block.Genesis :=
      ⟨fun x _ => Proofs.Consensus.Blocks.preceq_genesis _,
        voteCone_genesis c p a nr s rho hwf hsleep hhor le_rfl hupper⟩
    refine ⟨hseed, ?_⟩
    intro w i t C _ _ hq hC
    rw [genuineConf_slot_zero c p a nr s rho hwf (by omega) hC]
    exact hseed
  | succ d hd ih =>
    intro hupper
    have hdlast : d ≤ last := by omega
    have hprev := ih (by omega)
    have hprior : PriorConfsBelow c p a nr s rho d := fun x hx w i t C hw ht hq hC =>
      (hprev.2 w i t C hw ht hq hC).heads x hx
    have hsucc : ∀ {B : Block},
        (∀ x, rho.honest.contains x = true → preceq B (voteDutyHeadAt c p a nr s rho x (d + 1)) = true) →
        ProtectedVoteSlot c p a nr s rho (d + 1) B :=
      fun h => protectedVoteSlot_of_heads c p a nr s rho hwf hsleep hhor (by omega) hupper h
    have hpres : ∀ {B : Block}, ProtectedVoteSlot c p a nr s rho d B → ProtectedVoteSlot c p a nr s rho (d + 1) B :=
      fun hB => hsucc (heads_of_notBelowAnchor c p a nr s rho fun x hx hr =>
        protectedVoteSlot_preserve c p a nr s rho hwf hdom hsleep hhor hd hdlast hprior hB hx hr
          (anchor_preceq_of_notBelow c p a nr s rho hwf hdom hsleep hhor hd hdlast hprior hB hx hr))
    refine ⟨hpres hprev.1, ?_⟩
    intro w i t C hw ht hq hC
    by_cases hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d
    · exact hpres (hprev.2 w i t C hw ht hqd hC)
    · have hqd' : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 = d := by omega
      exact hsucc (heads_of_notBelowAnchor c p a nr s rho fun x hx hr =>
        protectedVoteSlot_succ_of_genuineConf c p a nr s rho hwf hdom hsleep hhor hd hdlast hprior hw ht
          hqd' hC hx hr
          (anchor_preceq_of_genuineConf c p a nr s rho hwf hdom hsleep hhor hd hdlast hprior hw ht hqd' hC hx hr))

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick(添字 `i`・時刻 `t`、slot `q = slotOf e t - 1`)の genuine な確認
(確認の更新の前の段の head で、その slot で eligible。`RootWitness.GenuineConfirmationAt`)は、`q < d ≤ last + 1`(`last` の
確認の時刻は `horizon` 以下)の honest なノード `x` の slot `d` の投票の務めの head の祖先。手書き `protectedVoteSlots_of_gstZero_v2`
の第 2 連言(`GenuineConfirmationWith … (confStore S rho w q) q B → ProtectedVoteSlot S rho d B`)の `heads`
(`DecoupledConsensusProofs/Execution/WeakGenesisGSTZeroActionSources.lean`)に当たる。周回 250 に穴として置き、周回 270 に
slot の帰納法 `protectedVoteSlots_gstZero` の第 2 連言の `heads` で証明した(`q < d` なので `1 ≤ d`)。 -/
theorem genuineConf_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1) {C : Block}
    (hC : Proofs.Consensus.RootWitness.GenuineConfirmationAt c p a nr s rho w i t C) :
    preceq C (voteDutyHeadAt c p a nr s rho x d) = true :=
  ((protectedVoteSlots_gstZero c p a nr s rho hwf hdom hsleep hhor d (by omega) hupper).2 w i t C hw ht hqd hC).heads x hx

/-- `laterVoteHead_rowSources_of_prior` の前提 `hpriorD` を `genuineConf_preceq_laterVoteHead` で満たしたもの(周回 270)。 -/
theorem laterVoteHead_rowSources (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {x : ValidatorId} (hx : rho.honest.contains x = true)
    {u : ValidatorId} (hu : rho.honest.contains u = true)
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} {i2 : Nat} {t2 : Int}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2)
    (hev : rho.events[i2]? = some (NamedEvent.Tick u t2))
    (ht2 : t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) :
    preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i2 t2) (voteDutyHeadAt c p a nr s rho x d) = true ∧
      ∀ T, Proofs.Consensus.RootWitness.fgConfirmationWitnessAt c p a nr s rho u i2 t2 = some T →
        preceq T (voteDutyHeadAt c p a nr s rho x d) = true :=
  laterVoteHead_rowSources_of_prior c p a nr s rho hwf hdom hsleep hhor hd hupper hx
    (fun _ _ _ _ hw ht hq hC => genuineConf_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hw hx ht hq hupper hC)
    hu hem hev ht2

/-- `laterVoteHead_rowSources` の確認の証人の連言(手書き `actionSources_preceq_voteDutyHead_of_gstZero` の 3 つ目の結論。周回 247)。 -/
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
    preceq T (voteDutyHeadAt c p a nr s rho x d) = true :=
  (laterVoteHead_rowSources c p a nr s rho hwf hdom hsleep hhor hd hupper hx hu hem hev ht2).2 T hT

/-- `laterVoteHead_rowSources` の SG block の連言(手書き `actionSources_preceq_voteDutyHead_of_gstZero` の第 1 の結論。周回 256)。 -/
theorem sgBlock_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {x : ValidatorId} (hx : rho.honest.contains x = true)
    {u : ValidatorId} (hu : rho.honest.contains u = true)
    {row : Model.Consensus.Objects.NamedBlocks.NamedAttestation} {i2 : Nat} {t2 : Int}
    (hem : Statements.Consensus.Spec.Execution.Emits c p a nr s rho u
      (Model.Consensus.Execution.Objects.NamedObject.Attest row) t2)
    (hev : rho.events[i2]? = some (NamedEvent.Tick u t2))
    (ht2 : t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1)) :
    preceq (Proofs.Consensus.RootWitness.sgBlockAt c p a nr s rho u i2 t2) (voteDutyHeadAt c p a nr s rho x d) = true :=
  (laterVoteHead_rowSources c p a nr s rho hwf hdom hsleep hhor hd hupper hx hu hem hev ht2).1

/-- GST-zero の枝で、honest なノード `w` の確認評価の tick(添字 `i`・時刻 `t`、slot `q = slotOf e t - 1`)の確認の更新の前の段の
store の FG root は、`q < d ≤ last + 1`(`last` の確認の時刻は `horizon` 以下)の honest なノードの slot `d` の投票の務めの head の祖先。
手書き `preparedFGRoot_preceq_voteDutyHead_of_gstZero`(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。
手書きと同じ運び: FG root を tick の時刻の読みの FG root に移し(`confPreUpdate_fgRoot`)、その確認の証人
(`RootWitness.stateBeforeTime_fgRoot_confirmationWitness`。手書き `WeakFG.fgRoot_confirmationWitness_at_read`)で genesis か、
時刻 `< t` に honest な署名者が行を出した tick の務めの確認の証人に分け、後者は `t` が slot `d + 1` の投票時刻より前
(`confTick_lt_nextVote`)なので `fgWitness_preceq_laterVoteHead` から(周回 247)。 -/
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

/-- `confFgRoot_preceq_laterVoteHead` と同じ前提で、確認の更新の前の段の store の round `R` の窓の round の honest な行の SG block
(`RootWitness.HonestWindowCarrierAt R`)は、slot `d` の投票の務めの head の祖先。窓の round は `R` より小さい
(`lt_of_mem_latestWindow`)ので、その行の時刻(opening slot の確認の時刻)は slot `d + 1` の投票時刻より前
(`confirmationTime_lt_nextVote`。slot は `slotOf e t ≤ d`)で、`sgBlock_preceq_laterVoteHead`(手書き
`actionSources_preceq_voteDutyHead_of_gstZero`)で閉じる(周回 256 の `confG1Raw_preceq_laterVoteHead_positive` の後半を周回 257 に切り出した)。 -/
theorem confWindowCarrier_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1) {Y : Block}
    (hY : Proofs.Consensus.RootWitness.HonestWindowCarrierAt c p a nr s rho
      (Model.Consensus.Protocol.Grades.roundOf s.hc
        (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) Y) :
    preceq Y (voteDutyHeadAt c p a nr s rho x d) = true := by
  obtain ⟨hδ, -, hr⟩ := Proofs.Consensus.Liveness.wf_facts hwf
  obtain ⟨u, i2, t2, row2, hu, hev2, hem2, hwin, rfl⟩ := hY
  have hlt := lt_of_mem_latestWindow hwin
  have hS : (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s =
      Model.Consensus.Objects.Parameters.slotOf s.e t :=
    (tickPreUpdateStore_clockIs c p nr _ s.e s.hc s.cfg _ _ t).2
  rw [hS] at hlt
  have hS0 : 0 < Model.Consensus.Objects.Parameters.slotOf s.e t := ht.2.1
  -- 行の round の opening slot は `slotOf e t` より小さい
  have hopen : Model.Consensus.Protocol.Grades.openingSlot s.hc row2.round + 1 ≤ d := by
    have h1 : (row2.round + 1) * s.hc.r ≤ Model.Consensus.Objects.Parameters.slotOf s.e t :=
      (Nat.le_div_iff_mul_le (by omega)).mp hlt
    have h2 : Model.Consensus.Protocol.Grades.openingSlot s.hc row2.round = row2.round * s.hc.r := rfl
    rw [h2]
    rw [Nat.add_mul] at h1
    omega
  have ht2 : t2 < Model.Consensus.Protocol.Schedule.voteTime s.e (d + 1) := by
    rw [Proofs.Consensus.RootWitness.emits_attest_actionTime_round c p a nr s rho hem2, actionTime_eq_confirmationTime]
    have h := confirmationTime_lt_nextVote s hδ (first := Model.Consensus.Protocol.Grades.openingSlot s.hc row2.round)
      (last := d - 1) (by omega)
    have hd' : d - 1 + 1 + 1 = d + 1 := by omega
    rwa [hd'] at h
  have hu' : rho.honest.contains u = true := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu
  exact sgBlock_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor (by omega) hupper hx hu' hem2 hev2 ht2

/-- `confFgRoot_preceq_laterVoteHead` と同じ前提で、確認の更新の前の段の store の round `R` が正なら、round `R` の phase G1 の
読みの grade に担い手(窓の round の honest な行の SG block。`RootWitness.RelativeGradeCarrierAt`)がある。手書き
`preparedG1Raw_preceq_voteDutyHead_of_gstZero`(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)の正の round の枝が
raw の grade に当てる `relativeGradeCarrierAt_of_awakeWindowMajority` に当たる。共通の構成 `relativeGradeCarrierAt_of_commonUpper` を
`D = X` で掛ける。G1 の domain 時刻 `T1`(round `R` の opening slot の開始)は確認評価の tick の時刻 `t` より前で(`t` は slot
`slotOf e t ≥ R * r` の提案時刻の `2Δ` 後)、`t` は horizon 以内。窓の担い手は `confWindowCarrier_preceq_laterVoteHead`、
読み手の finalized は `stateBeforeTime_f_preceq_of_witnesses` で `T1` より前の行の確認の証人に下ろし、`t` は slot `d + 1` の
投票時刻より前(`confTick_lt_nextVote`)なので `fgWitness_preceq_laterVoteHead` で閉じる(周回 256 に穴として置き、周回 257 に閉じた)。 -/
theorem confG1Carrier_positive (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (_hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1)
    (hpos : 0 < Model.Consensus.Protocol.Grades.roundOf s.hc
      (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s) :
    Proofs.Consensus.RootWitness.RelativeGradeCarrierAt c p a nr s rho
      (Model.Consensus.Protocol.Grades.roundOf s.hc
        (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)
      Model.Consensus.Protocol.Grades.GradePhase.G1 := by
  obtain ⟨hδ, -, -⟩ := Proofs.Consensus.Liveness.wf_facts hwf
  have hsch : ScheduleWellFormed s rho := by
    have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
    unfold ExecutionValid at hexec
    exact hexec.1.1.1
  have hS : (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s =
      Model.Consensus.Objects.Parameters.slotOf s.e t :=
    (tickPreUpdateStore_clockIs c p nr _ s.e s.hc s.cfg _ _ t).2
  -- G1 の domain 時刻は確認評価の tick の時刻より前
  have hT1t : Model.Consensus.Protocol.Grades.domainTime s.e s.hc
      (Model.Consensus.Protocol.Grades.roundOf s.hc
        (Proofs.Consensus.RootWitness.preUpdateStoreAt c p a nr s rho w i t).core.s)
      Model.Consensus.Protocol.Grades.GradePhase.G1 < t := by
    rw [hS]
    have hRS : Model.Consensus.Protocol.Grades.roundOf s.hc (Model.Consensus.Objects.Parameters.slotOf s.e t) * s.hc.r ≤
        Model.Consensus.Objects.Parameters.slotOf s.e t := Nat.div_mul_le_self _ _
    have h1 := Proofs.Consensus.Clocks.proposalTime_mono s.e hδ hRS
    have h2 : t = Model.Consensus.Protocol.Schedule.proposalTime s.e (Model.Consensus.Objects.Parameters.slotOf s.e t) +
        2 * s.e.delta := ht.2.2
    have h3 : Model.Consensus.Protocol.Grades.domainTime s.e s.hc
        (Model.Consensus.Protocol.Grades.roundOf s.hc (Model.Consensus.Objects.Parameters.slotOf s.e t))
        Model.Consensus.Protocol.Grades.GradePhase.G1 =
        Model.Consensus.Protocol.Schedule.proposalTime s.e
          (Model.Consensus.Protocol.Grades.roundOf s.hc (Model.Consensus.Objects.Parameters.slotOf s.e t) * s.hc.r) := by
      unfold Model.Consensus.Protocol.Grades.domainTime Model.Consensus.Protocol.Grades.openingTime
      simp [Model.Consensus.Protocol.Grades.domainOffset, Model.Consensus.Protocol.Grades.openingSlot]
    rw [h3]
    linarith
  have hth : t ≤ rho.horizon := (Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? ht.1)).2
  have htv := confTick_lt_nextVote s rho hδ ht hqd
  refine relativeGradeCarrierAt_of_commonUpper c p a nr s rho hwf hdom hsleep hpos
    Model.Consensus.Protocol.Grades.GradePhase.G1 (by linarith) (D := voteDutyHeadAt c p a nr s rho x d) ?_ ?_
  · intro Y hY
    exact confWindowCarrier_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hx ht hqd hupper hY
  · intro v hv
    refine stateBeforeTime_f_preceq_of_witnesses c p a nr s rho hwf hsleep hv _ ?_
    intro u i2 t2 row2 hu hev2 hem2 ht2 T hT
    exact fgWitness_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor (by omega) hupper hx
      ((Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu) hem2 hev2 (by linarith) hT

/-- `confFgRoot_preceq_laterVoteHead` と同じ前提で、確認の更新の前の段の store の round `R` が正なら、その round の g1 の frame の
raw ブロックは slot `d` の投票の務めの head の祖先。手書き `preparedG1Raw_preceq_voteDutyHead_of_gstZero` の正の round の枝
(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たり、同じ運び: raw は G1 の domain 時刻の tick で凍結した
`g0` の祖先(`confCache_phase_origin`)で、`g0` はその読みで grade を通る(`Grade2Capture.freezeRoot_mem`。手書き
`WeakSG.phaseGrade_of_preparedFrame_g1`)ので、担い手(`confG1Carrier_positive`)の下で窓の round の honest な行の SG block の祖先で、
それは `confWindowCarrier_preceq_laterVoteHead` で閉じる(周回 246 に穴として置き、周回 256 に担い手を除いて閉じた)。 -/
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
  have hsch : ScheduleWellFormed s rho := by
    have hexec := Proofs.Consensus.Liveness.executionValid_of_sleepy c p a nr s rho hsleep
    unfold ExecutionValid at hexec
    exact hexec.1.1.1
  have hs := Proofs.Consensus.Window.eventsSorted_of_schedule hsch
  have hnd : Statements.Consensus.Spec.Conditions.EventsNodup rho := by
    have h := hsch
    unfold ScheduleWellFormed at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hnd⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact hnd
  have hnd' := Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd
  have hwm : w ∈ rho.honest.elems := (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mp hw
  obtain ⟨j, g0, -, hevj, hfz, hrawg0⟩ := confCache_phase_origin c p a nr s rho ht.1 _ hpos
    Model.Consensus.Protocol.Grades.GradePhase.G1 hraw (Proofs.Consensus.Blocks.preceq_self raw)
  obtain ⟨-, hgrade⟩ := Proofs.Consensus.Grade2Capture.freezeRoot_mem hfz
  rw [Proofs.Consensus.RootWitness.worldAt_stateBefore_tick_eq_stateBeforeTime c p a nr s rho hs hnd' hevj] at hgrade
  obtain ⟨Y, hY, hg0Y⟩ :=
    confG1Carrier_positive c p a nr s rho hwf hdom hsleep hhor hw hx ht hqd hupper hpos w hwm g0 hgrade
  exact Proofs.Consensus.Blocks.preceq_trans (Proofs.Consensus.Blocks.preceq_trans hrawg0 hg0Y)
    (confWindowCarrier_preceq_laterVoteHead c p a nr s rho hwf hdom hsleep hhor hx ht hqd hupper hY)

/-- `confFgRoot_preceq_laterVoteHead` と同じ前提で、確認の更新の前の段の store の round の g1 の frame の raw ブロックは、
slot `d` の投票の務めの head の祖先。手書き `preparedG1Raw_preceq_voteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。round 0 は g1 の frame に root が無いので矛盾
(`confCache_g1_round_zero`)、正の round は `confG1Raw_preceq_laterVoteHead_positive`(担い手は `confG1Carrier_positive`。周回 256・257)から(周回 246)。 -/
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
anchor は g1 の frame の raw の active prefix(`Grade2Capture.activePrefix_preceq` で raw の祖先)か FG root なので、
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
walk は anchor のままか(`Goldfish.head_cases`)、filtered tree の適格な要素なので、`confAnchor_preceq_laterVoteHead` と
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
手書きと同じく、g2 の root `raw` の active prefix `g` は filtered tree にあり `g ⪯ raw` なので、`confFrameG2_g1Root_positive` で
g1 の root `root1` を取り(`g ⪯ root1`)、filtered tree の重複なし(`preUpdateTree_nodup`)から `activePrefix_exists` で
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
正の round は `confFrameRoot_preceq_confWalk_positive` から(周回 228)。 -/
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

/-- `recordAt_preceq_laterVoteHead` の finalized の版。手書き `finalizedAt_preceq_laterVoteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)に当たる。
手書きと同じ運び: 時刻 `t` の読みを時刻 `< t + 1` の読みに移し(`readAt_eq_stateBeforeTime_succ`)、finalized ⪯ FG root
(`ReceiverFinality.store_fgRoot_extends`。読みの `f ⪯ j` は `ProposerFinality.readAt_fj`)とし、FG root を証明済みの
`RootWitness.stateBeforeTime_fgRoot_confirmationWitness` で genesis(`first = 0`)か honest な行の務めの確認の証人に分ける。
後者は行の時刻が行の round の action 時刻(`RootWitness.emits_attest_actionTime_round`)で、それは opening slot の確認の時刻
(`actionTime_eq_confirmationTime`)なので `first` を opening slot にとり(行の tick は run の event なので `horizon` 以下)、
`first ≤ last` なら行の時刻は slot `last + 2` の投票時刻より前(`confirmationTime_lt_nextVote`)なので
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

/-- 確認の記録の一致: GST-zero の枝は共通の上界(`commonUpper_genesis`)から、回復の枝は穴 `recordAgree_recovered` から。
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

/-- GST-zero の枝(`t0 = 0`)の確認の出力の一致: 共通の上界(`commonUpper_genesis`)から `agreeFrom_confirmed_of_commonUpper`。
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
