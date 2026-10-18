import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Available
import Proofs.Consensus.ShortHorizon
import Proofs.Consensus.Voting
import Proofs.Consensus.ConfirmedOrigin
import Proofs.Consensus.ProposerRoot
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
   ある slot 以後の投票の務めの head `voteDutyHeadAt` の祖先であることを言う `recordAt_preceq_laterVoteHead` / 穴 `finalizedAt_preceq_laterVoteHead`
   から、4 つの slot の最大で上界を揃えて証明する(周回 222)。`recordAt_preceq_laterVoteHead` は確認の記録の由来(証明済みの
   `ConfirmedOrigin.storeAt_confirmed_origin`: genesis か、確認評価の tick の確認の walk か grade の stable root)で分け、穴
   `confWalk_preceq_laterVoteHead`(walk ⪯ 後の投票の head)と `confStableRoot_preceq_confWalk`(stable root ⪯ walk。穴ではない)から証明する(周回 224)。
   `confStableRoot_preceq_confWalk` は stable root が FG root に戻る枝を FG root ⪯ SG root ⪯ head で閉じ、g2 の frame の root がある枝を
   `confFrameRoot_preceq_confWalk`(穴ではない)に渡す(周回 226)。`confFrameRoot_preceq_confWalk` は確認の更新の前の段の store の round で分け、
   round 0 は g2 の frame に root が無いので矛盾(`confCache_g2_round_zero`。G2 の round 0 の domain 時刻は `-Δ` で、run の event の時刻は 0 以上)、
   正の round は `confFrameRoot_preceq_confWalk_positive`(穴ではない)に渡す(周回 228)。これは g1 の frame の anchor が fork choice の SG root で
   walk がそこから歩くので、`confFrameRoot_preceq_anchor_positive`(g2 の frame の root の active prefix ⪯ g1 の anchor。穴ではない)から証明する(周回 230)。
   これは穴 `confFrameG2_g1Root_positive`(g2 の root の祖先で filtered tree にあるものは g1 の root の祖先)で g1 の root を取り、
   `activePrefix_exists`(tree の重複なし `preUpdateTree_nodup` を使う。周回 233 に閉じた)と `activePrefix_dominates` で anchor に移す(周回 232)。
   回復の枝の記録の一致と交差の互換は穴 `recordAgree_recovered` / `crossAgree_recovered`。
3. 穴(7 件): `confWalk_preceq_laterVoteHead`(手書き `preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero`、
   `DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)/ `confFrameG2_g1Root_positive`(手書き
   `q10_g1_slot_of_g2_slot`、`DecoupledConsensusProofs/Protocol/Grades/Q10Frame.lean`)/
   `finalizedAt_preceq_laterVoteHead`(手書き
   `finalizedAt_preceq_laterVoteDutyHead_of_gstZero`、`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)/
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

/-- 穴: GST-zero の枝で、honest なノード `w` の確認評価の tick(添字 `i`・時刻 `t`、slot `q = slotOf e t - 1`)の確認の walk
(`ConfirmedOrigin.confWalkAt`: 確認の更新の前の段の fork choice の head)は、`q < d ≤ last + 1`(`last` の確認の時刻は `horizon` 以下)の
honest などのノードの slot `d` の投票の務めの head の祖先。手書き `preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/Grades/GSTZeroPreparedWalk.lean`)に当たる。
閉じるのに要るもの: walk が anchor から動かなければ prepared anchor の上界(手書き `preparedConfirmationAnchor_preceq_voteDutyHead_of_gstZero`。
FG root の枝と G1 の raw の枝)、動けば genuine な確認で、保護された投票の slot(手書き `protectedVoteSlots_of_gstZero_v2`)の `heads`。 -/
theorem confWalk_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0) {last d : Nat}
    (hhor : Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon)
    {w x : ValidatorId} (hw : rho.honest.contains w = true) (hx : rho.honest.contains x = true) {i : Nat} {t : Int}
    (ht : Proofs.Consensus.ConfirmedOrigin.ConfTick s rho w i t)
    (hqd : Model.Consensus.Objects.Parameters.slotOf s.e t - 1 < d) (hupper : d ≤ last + 1) :
    preceq (Proofs.Consensus.ConfirmedOrigin.confWalkAt c p a nr s rho w i t) (voteDutyHeadAt c p a nr s rho x d) = true := by
  sorry

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

/-- 穴: GST-zero の枝で、honest なノード `w` の確認評価の tick の、確認の更新の前の段の store の round が正なら、その round の
frame の g2 の root `raw` の祖先 `P` で filtered tree にあるものは、同じ frame の g1 の root `root1` の祖先でもある。
手書き `NamedOutageClosure.q10_g1_slot_of_g2_slot`(`Protocol/Grades/Q10Frame.lean`)に当たる(周回 232)。
閉じるのに要るもの: 読みの時刻が round の G1 の domain 時刻より後で次の round の opening 以下であること(確認評価の tick の時刻)、
G2 と G1 がそれぞれ domain 時刻の tick で凍結されること(`Grade2Capture.stateBefore_g2_origin`、形は `freezeRoot_mem`。手書き
`FrameCompleted.frame_phase_completed_in_round`)、G2 の root が G1 の grade の条件 `gradeBool` を満たして G1 の最深の root の祖先になること。 -/
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
  sorry

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
(slot `q`)の walk か stable root なら `first = q` とし、穴 `confWalk_preceq_laterVoteHead`(と stable root は
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

/-- 穴: `recordAt_preceq_laterVoteHead` の finalized の版。手書き `finalizedAt_preceq_laterVoteDutyHead_of_gstZero`
(`DecoupledConsensusProofs/Protocol/ChainState/GSTZeroSixFieldBypassNamed.lean`)に当たる。
閉じるのに要るもの: finalized が FG root の祖先であること、FG root の確認の証人(手書き `WeakFG.fgRoot_confirmationWitness_at_read`)、
務めの出どころが後の投票の head の祖先であること(手書き `actionSources_preceq_voteDutyHead_of_gstZero`)を生成 Model の store で示すこと。
genesis の枝は `SlashableBound` を与えないので `finalizedSafe` の本体は使えない。 -/
theorem finalizedAt_preceq_laterVoteHead (hwf : SetupWellFormed c p s) (hdom : RunDomain s rho)
    (hsleep : SleepyRegime c p a nr s rho 0)
    (hzero : Model.Consensus.Protocol.Schedule.confirmationTime s.e 0 ≤ rho.horizon)
    {v : ValidatorId} (hv : rho.honest.contains v = true) (t : Int) :
    ∃ first : Nat, Model.Consensus.Protocol.Schedule.confirmationTime s.e first ≤ rho.horizon ∧
      ∀ last, first ≤ last → Model.Consensus.Protocol.Schedule.confirmationTime s.e last ≤ rho.horizon →
        ∀ x, rho.honest.contains x = true →
          preceq (storeAt c p a nr s rho v t).core.f (voteDutyHeadAt c p a nr s rho x (last + 1)) = true := by
  sorry

/-- GST-zero の枝(`t0 = 0`)で最初の確認の時刻 `confirmationTime e 0` が `horizon` 以下の run の、honest な 2 ノードの時刻 0 以後の
2 つの読みの finalized と確認の記録 `latestConfirmed` の共通の上界(`CommonUpperFrom`): 穴 `finalizedAt_preceq_laterVoteHead` /
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
