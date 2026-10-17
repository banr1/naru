import Proofs.Consensus.RootEntry
import Proofs.Consensus.FinalizedAccountable
import Proofs.Consensus.Grade2Capture
import Mathlib.Tactic

/-!
# FG root の名前付きブロックは、honest な署名者の同じ高さの入口(C71 の補題)

`RootEntry.stateBeforeTime_fgRoot_honestEntry` は、時刻 `< time` の読みの FG root が genesis でなければ、読みの bodies の `D`
(導出の `j` が FG root)と、honest な署名者 `w` の bodies の入口の checkpoint `K`(導出の `h` が `D` の導出の `hJ`、
`tH` が `K` の消去、根が FG root の根)を返す。ここでは次の段を足す。

1. 読みの主 `v` の bodies に、消去が FG root の名前付きブロック `J` がある(`D` の導出の `j` は `D` の消去の祖先なので、
   `erased_ancestor_lift` で `D` の名前付きの祖先 `J` に持ち上げ、bodies は祖先について閉じる。`stateBeforeTime_fgRoot_named`)。
2. `NamedRootCollisionFree` の下で `v` が honest なら `J = K`(`J` も `K` も honest なノードの `stateBefore` の bodies にあるので
   run の中のブロックで、`namedRoot` が等しい)。したがって FG root の名前付きブロック `J` は署名者 `w` の bodies にもあり、
   `J` の導出の `h` は `D` の導出の `hJ`、`tH` は `J` の消去、`J` は `w` の務めの FG source の名前付きブロック `D'` の祖先
   (`stateBeforeTime_fgRoot_entryWitness`)。
3. `D'` / `J` を `StoreInv.sigma` で `w` の tick の中の store `st3` の chain 状態に移す: 務めの FG source `q` と FG root `R` の
   `(h, tH)` は `(hJ, R)` で、`R` は `st3` の tree にあり `R ⪯ q`(`stateBeforeTime_fgRoot_storeWitness`。周回 167 / 168)。
4. `st3` は run の関数 `dutyStoreAt w i t2`(`AttestationSource.tickDutyStore`)で、その務めの確認の証人
   `fgConfirmationWitnessAt w i t2`(FG source の chain 状態の `tH`)は `some R`(`stateBeforeTime_fgRoot_confirmationWitness`。周回 171)。
5. 時刻の境 `cutTime` で証人の tick を最近(`cutTime ≤ t2`)と古い(`t2 < cutTime`)に分け、最近の務めの証人がどれも `B` と互換で、
   古い証人が `R` なら `B` と `R` が互換、という 2 つの前提から `compatible R B`
   (`stateBeforeTime_fgRoot_compatible_of_bootstrap_and_recent`。周回 172)。
6. 提案しない tick では、務めの store `dutyStoreAt w i t` の FG root は `stateBefore i` の `w` の store の FG root
   (`dutyStoreAt_fgRoot_of_not_proposing`。時計合わせ・投票・確認の更新は FG root の 4 欄を変えない。周回 173)。
   手書きの右辺は読みの時刻の store `storeBeforeTime` で、`stateBefore i` から読みの時刻への橋渡しは 8。
7. 行を出した tick は提案しない: action 時刻 `4Δ · (r · R) + 6Δ` は提案時刻 `4Δ · k` と重ならない(Δ > 0)ので、6 の前提は
   発行から出る(`dutyStoreAt_fgRoot_of_emits`。周回 174)。
8. 添字 `i` の event が `Tick w t` なら、`stateBefore i` の `w` の状態は時刻 `< t` の読み `stateBeforeTime t` の `w` の状態
   (`idxLt t` から `i` までの event は `w` のものでない。`EventsSorted` と重複なし)。7 と合わせて、行を出した tick の務めの store の
   FG root は読みの FG root(`dutyStoreAt_fgRoot_eq_stateBeforeTime`。手書き `actionStoreAt_fgRoot_eq_storeBeforeTime`。周回 175)。
9. 8 に 4 を掛けて、行を出した tick の務めの store の FG root は genesis か、時刻 `< t` に発行された行の tick の務めの確認の証人
   (`dutyStoreAt_fgRoot_confirmationWitness`。手書き `fgRoot_confirmationWitness_at_action`。周回 176)。
10. 9 の証人の時刻を時刻の境 `cutTime` で分け、最近の務めの証人がどれも `X` の祖先で、古い証人が `R` なら `R ⪯ X`、という
   2 つの前提から、行を出した tick の務めの FG root は `X` の祖先(`dutyStoreAt_fgRoot_preceq_of_recent_and_legacy`。
   手書き `actionSources_preceq_of_priorConfirmations_and_historyCut` の帰納の段 `hroots`。周回 177)。
11. 発行した行の時刻は行の round の action 時刻(`emits_attest_actionTime_round`)で、action 時刻は round について狭義単調
   (Δ > 0、`0 < R`。`actionTime_lt_actionTime_iff`)なので、時刻の境を round `cut` の action 時刻に置くと `t2 < cutTime` は
   手書きの round の境 `a.round < cut` と同じ行を選ぶ(`emits_attest_time_lt_actionTime_iff`。周回 178)。
12. 10 と 11 を round の強い帰納で組み、round `cut` 以上の行の tick の務めの FG root と確認の証人が `X` の祖先であることを、
   古い証人の前提と「前の round の仮定の下で、FG root が `X` の祖先なら確認の証人も」という段の前提から出す
   (`dutyStoreAt_preceq_of_roundInduction`。手書き `actionSources_preceq_of_priorConfirmations_and_historyCut` の帰納の
   骨組みの第 2 連言。周回 179)。
13. 12 を行ごとの性質 `Q`(手書きの第 1 連言の SG block ⪯ X に当たる)との同時帰納に広げる。round `base` 以上 `cut` 未満の
   行は `Q` を前提 `hbootstrap` から受け、段の前提 `hstep` は前の round の `Q` と FG root・確認の証人の両方を仮定に受ける
   (`dutyStoreAt_jointRoundInduction`。手書きの段 `hsg` が `hstep` の中に届く。12 はその `Q := True` の系。周回 180)。
   `hstep` は、同じ round の行を出した honest な tick の FG root がどれも `X` の祖先であることも仮定に受ける
   (手書きの `hformation` が要る同じ round の FG root ⪯ D に当たる(行を出した tick に限る)。周回 181)。
14. 務めの確認の証人 `T` は務めの FG source `q` の chain 状態の `tH` で、`q` は務めの store の `liveConfirmed` の祖先か、
   務めの grade 2 の候補そのもの(`fgConfirmationWitnessAt_source`。`deepestClear` の場合分け。手書きの段で確認の証人を
   `hlive` と窓の SG block に分ける前の段。周回 182)。
15. 14 の `q` は務めの store の tree にあり、`T ⪯ q`(chain 状態の `tH` は自分の祖先。store の版は
   `AttestationSource.chainState_tH_preceq`、手書き `derive_named_T_h_preceq`)。したがって `T` は務めの store の
   `liveConfirmed` の祖先か、grade 2 の候補 `q` の祖先(`fgConfirmationWitnessAt_preceq_source`。周回 183)。
16. 務めの store の `liveConfirmed` は、`stateBefore i` の `w` の store の `liveConfirmed` のままか、務めの store の FG root か、
   確認の更新の前の段 `preUpdateStoreAt` の eligible な head(提案・投票はこの欄を変えず、確認の更新は `Goldfish.live` を書く。
   `dutyStoreAt_live_cases`)。15 の `liveConfirmed` の枝をこれで割り、確認の証人を 4 つの枝に分け
   (`fgConfirmationWitnessAt_preceq_cases`)、FG root ⪯ X の下で FG root の枝を閉じる(`fgConfirmationWitnessAt_preceq_of_fgRoot`。
   手書きの `hlive` の出どころの場合分け。手書きの対応先は `actionStoreAt_liveConfirmed_genuine_or_fgRoot` で、枝は
   GenuineConfirmation と FG root の 2 つ。周回 184)。
17. 行を出した tick の時刻は action 時刻 `4Δ · (r · R) + 6Δ` で、その slot `r · R + 1` の supportCutoff `4Δ · (r · R + 1) + 2Δ`
   と一致する(Δ > 0。`AttestationSource.slotOf_actionTime` / `supportCutoff_actionTime`)。したがって務めの store は必ず
   確認の更新を通り(その slot `slotOf t - 1` は行の round の opening slot。`emits_attest_slotOf_pred`)、16 の第 1 の枝は起きない
   (`dutyStoreAt_live_cases_of_emits`。手書きの 2 枝に当たる)。確認の証人は 3 つの枝になり
   (`fgConfirmationWitnessAt_preceq_cases_of_emits`)、FG root ⪯ X の下で残るのは eligible な head と grade 2 の候補の 2 枝
   (`fgConfirmationWitnessAt_preceq_of_emits_fgRoot`。周回 185)。手書きの FG root の枝は確認の更新の前の store の FG root で、
   ここは更新の後の務めの store の FG root だが、確認の更新は FG root の 4 欄を変えないので値は同じ。`_of_emits` の定理の文は
   slot を `slotOf s.e t - 1` のまま書くので、opening slot に揃えるには `emits_attest_slotOf_pred` で `rw` する。
18. 手書きの `GenuineConfirmationWith` に当たる `GenuineConfirmationAt`(確認の更新の前の段の head で、その slot で eligible)を置き、
   17 の 2 枝を手書きと同じ形に書く(`dutyStoreAt_live_genuine_or_fgRoot_of_emits`)。FG root ⪯ X とこの tick の genuine な確認 ⪯ X
   から `liveConfirmed ⪯ X`(`dutyStoreAt_live_preceq_of_prior`。手書きの本体の `hlive`)、確認の証人は `X` の祖先か grade 2 の
   候補の祖先(`fgConfirmationWitnessAt_preceq_of_emits_prior`。手書きの `hform.witness` の第 1 の枝に `hlive` を掛ける段)。
   残る grade 2 の枝は窓の SG block に繋ぐ(周回 186)。
19. 務めの grade 2 の候補を `grade2CandidateAt` と名付け、genuine な確認 ⪯ X と grade 2 の候補 ⪯ X から確認の証人 ⪯ X
   (`fgConfirmationWitnessAt_preceq_of_prior_grade2`)。round の同時帰納の `hstep` の確認の証人の連言を、この 2 つ
   (手書きの `hprior` と、`nodeQ2_preceq_honestWindowCarrier` に `hsg` を掛ける側)の供給に置き換えた版
   `dutyStoreAt_jointRoundInduction_of_prior`(周回 187)。
20. 務めの grade 2 の候補 `q` は、`stateBefore i` の `w` の cache の務めの round の G2 の結果 `b0` の祖先か、この tick で
   凍結した `freezeRoot` の結果の祖先(`grade2CandidateAt_cases`。cache の 1 段は `Grade2Capture`)。行を出した tick の時刻は
   G2 の domain 時刻ではない(`actionTime_ne_domainTime_G2`)ので、行を出した tick では前者だけ
   (`grade2CandidateAt_of_emits`。手書き `q2_capture_at_action_read` の前半。周回 188)。`b0` を凍結した tick への run の
   帰納は手書きの `NamedCacheProvenance.completed_phase_origin` に当たる(`Grade2Capture.stateBefore_g2_origin`)。
21. 20 に run の帰納を掛け、行を出した tick の務めの grade 2 の候補は、添字 `j < i` の `w` の tick(時刻は務めの round の G2 の
   domain 時刻)で `stateBefore j` の store の `freezeRoot` が凍結した root の祖先(`grade2CandidateAt_origin_of_emits`。
   手書き `q2_capture_at_action_read` の全体に当たる。手書きは任意の round を取り、ここは `hem` と Δ > 0 で務めの round に限る。
   周回 189)。
22. 21 の凍結した root `b0` は `stateBefore j` の `w` の grade view の tree にあり、その `gradeBool` が真
   (`grade2CandidateAt_frozen_of_emits`。`Grade2Capture.freezeRoot_mem` を掛ける。手書き
   `nodeQ2_preceq_honestWindowCarrier` の局所の `hgrade'` に当たる。周回 190)。
23. 22 の `stateBefore j` を、8 で時刻 `< domainTime k G2` の読みに移す(`grade2CandidateAt_graded_of_emits`。手書きの局所の
   `hrawGrade`)。その `gradeBool` の通った block に性質 `P` の担い手があれば、務めの grade 2 の候補にもある
   (`grade2CandidateAt_preceq_carrier_of_emits`。手書き `nodeQ2_preceq_honestWindowCarrier` の全体で、担い手「窓の round の
   honest な action の SG block」を `P` に抽象した。周回 191)。ただし手書きの `hgrade` の horizon の守り
   (`domain … ≤ horizon →`)は外して、`hcarrier` を守りなしの全称にしている。
24. 23 の読みの時刻 `domainTime k G2` は、`ScheduleWellFormed` の下で 0 以上 horizon 以下(凍結した tick が run の event なので
   `Window.eventTime_bounds`。`grade2CandidateAt_domainTime_bounds_of_emits`。手書きの `hdomainHor`)。これで担い手の前提に
   手書きの `hgrade` の horizon の守り(と `0 ≤`)と tree への所属を足した版を置く
   (`grade2CandidateAt_preceq_carrier_horizon_of_emits`。`ScheduleWellFormed` と重複なし `EventsNodup` の下。周回 193)。
25. 務めの SG block `sgBlockAt`(務めの grade 2 の候補を渡した `getSgVoteWith`。手書き `actionSGBlockAt`)を置き、発行した行の
   `confirmed` はその根(`emits_confirmed_sgBlockAt`)。窓の round の honest な行の SG block を `HonestWindowCarrierAt`、
   手書きと同じ形の担い手の性質を `RelativeGradeCarrierAt` と名付け、24 の `P` をそれに置いて手書き
   `nodeQ2_preceq_honestWindowCarrier` と同じ前提の形にした(`grade2CandidateAt_preceq_honestWindowCarrier_of_emits`。周回 194)。
26. 担い手の行の `confirmed` は担い手の根(`EventsNodup` の下で `honestWindowCarrierAt_confirmed`)。25 の結論を、窓の round の
   honest な行 `row2` で `row2.confirmed = some (root Y)` かつ `q ⪯ Y` の形に開いた
   (`grade2CandidateAt_preceq_windowConfirmed_of_emits`。周回 195)。

`RelativeGradeCarrierAt` を awake の窓の多数派と `hsg` から作る(手書き
`relativeGradeCarrierAt_of_awakeWindowHistory_gstZero`)のは次の段。その数え上げの核(grade の通った block には honest な
支持者がいる。手書き `q20_graded_has_honest_supporter`)は `GradeSupporter.lean` にある(周回 196)。

手書きでは `HealingSurface.processedJustification_confirmationWitness`(`Protocol/ChainState/FGRootWitness.lean`)の、
根の単射で入口の checkpoint と FG root の名前付きブロックを同一視するところに当たる。
-/

namespace Proofs.Consensus.RootWitness

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.JustificationCertificate Proofs.Consensus.Carrier Proofs.Consensus.NamedBlocks

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 読みの bodies の `D` の導出の `j` は、`D` の名前付きの祖先 `J`(やはり bodies にある)の消去(前提なし)。 -/
theorem bodies_j_named {st : NamedStore} (h : StoreInv s.e s.cfg st) {D : NamedBlock} (hD : D ∈ st.bodies.elems) :
    ∃ J : NamedBlock, J ∈ st.bodies.elems ∧ namedPreceq J D = true ∧ eraseBlock J = (deriveNamed s.e s.cfg D).j := by
  obtain ⟨J, hJD, hJe⟩ := erased_ancestor_lift (Proofs.Consensus.Derivation.deriveNamed_inv s.e s.cfg D).j_preceq
  exact ⟨J, Proofs.Consensus.Attribution.ancestor_mem_bodies h.closed hD hJD, hJD, hJe⟩

/-- 時刻 `< time` の読みの主の bodies に、消去が FG root の名前付きブロック `J` がある(前提なし)。
`J` は bodies のある `D`(導出の `j` が FG root)の名前付きの祖先。 -/
theorem stateBeforeTime_fgRoot_named (v : ValidatorId) (time : Int) :
    ∃ D J : NamedBlock, D ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems ∧
      (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∧
      J ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems ∧ namedPreceq J D = true ∧
      eraseBlock J = getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) := by
  obtain ⟨D, hD, hDj⟩ := Proofs.Consensus.FinalizedSource.stateBeforeTime_fgRoot_justified c p a nr s rho v time
  obtain ⟨J, hJ, hJD, hJe⟩ := bodies_j_named s (Proofs.Consensus.JustifiedCarrier.stateBeforeTime_inv c p a nr s rho time v) hD
  exact ⟨D, J, hD, hDj, hJ, hJD, hJe.trans hDj⟩

/-- honest なノードの `stateBefore i` の bodies にある名前付きブロックは run の中のブロック。 -/
theorem blockInRun_of_stateBefore {u : ValidatorId} (hu : u ∈ rho.honest.elems) (i : Nat) {B : NamedBlock}
    (hB : B ∈ (worldAt (stateBefore c p a nr s rho i) u).st.bodies.elems) : BlockInRun c p a nr s rho B := by
  unfold BlockInRun DirectBlockInRun
  exact ⟨B, Or.inr ⟨u, (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Sets.vid_eq _ _).mpr hu, i,
    (Proofs.Consensus.Sets.contains_iff_mem Proofs.Consensus.Orders.nb_compare_eq_iff _ _).mpr hB⟩, namedPreceq_self B⟩

/-- **FG root の名前付きブロックは honest な署名者の入口の checkpoint**: 前提 `EventsSorted` / `QuorumHonest` / `hcar` と
`NamedRootCollisionFree` の下で、honest な `v` の時刻 `< time` の読みの FG root は genesis か、次の形。
読みの bodies の `D`(導出の `j` が FG root)と、その名前付きの祖先 `J`(消去が FG root、`v` の bodies にある)があり、
honest な署名者 `w`(= `row.valIndex`)が時刻 `t2 < time` に行 `row`(height pair `Vote hJ (root FG root) nu`、`hJ` は `D` の
導出の `hJ`)を出し、その発行は添字 `i` の event `Tick w t2`。`J` は `stateBefore (i + 1)` の `w` の bodies にあり、`w` の務めの
FG source `q` の名前付きブロック `D'`(`eraseBlock D' = q`、やはり `w` の bodies にある)の祖先で、`J` の導出の `h` は
`hJ`、`tH` は `J` の消去。`D'` の導出の `(h, tH)` は `(hJ, FG root)`(署名者の務めの FG source の入口は FG root そのもの)。 -/
theorem stateBeforeTime_fgRoot_entryWitness (hs : EventsSorted rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hcf : NamedRootCollisionFree c p a nr s rho) {v : ValidatorId} (hv : v ∈ rho.honest.elems) (time : Int) :
    getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) = Block.Genesis ∨
      ∃ (D J : NamedBlock) (row : NamedAttestation) (nu : Bool) (t2 : Int) (i : Nat) (q : Block) (D' : NamedBlock),
        D ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems ∧
        (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∧
        J ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems ∧ namedPreceq J D = true ∧
        eraseBlock J = getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∧
        row.valIndex ∈ rho.honest.elems ∧
        row.heightPair = NamedHeightPair.Vote (deriveNamed s.e s.cfg D).hJ
          (root (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core))) nu ∧
        t2 < time ∧ Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 ∧
        rho.events[i]? = some (NamedEvent.Tick row.valIndex t2) ∧
        D' ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) row.valIndex).st.bodies.elems ∧ eraseBlock D' = q ∧
        (∃ (cache : Model.Consensus.Protocol.Grades.Cache) (st3 : NamedStore),
          cache = Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (storeToHealing (worldAt (stateBefore c p a nr s rho i) row.valIndex).st.core) t2
            (worldAt (stateBefore c p a nr s rho i) row.valIndex).cache ∧
          st3 = Proofs.Consensus.AttestationSource.tickDutyStore c p nr cache s.e s.hc s.cfg
            (Model.Consensus.Execution.Setup.setupNode row.valIndex) (worldAt (stateBefore c p a nr s rho i) row.valIndex).st t2 ∧
          StoreInv s.e s.cfg st3 ∧
          (worldAt (stateBefore c p a nr s rho (i + 1)) row.valIndex).st.bodies = st3.bodies ∧
          Model.Consensus.Protocol.Duties.Inputs.fgSourceWith cache s.e s.hc (storeToHealing st3.core)
              (Model.Consensus.Protocol.Grades.roundOf s.hc st3.core.s)
              (Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith cache s.e s.hc (storeToHealing st3.core)
                (Model.Consensus.Protocol.Grades.roundOf s.hc st3.core.s)) = some q ∧
          q ∈ st3.core.tree.elems) ∧
        J ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) row.valIndex).st.bodies.elems ∧
        namedPreceq J D' = true ∧
        (deriveNamed s.e s.cfg J).h = (deriveNamed s.e s.cfg D).hJ ∧
        (deriveNamed s.e s.cfg J).tH = eraseBlock J ∧
        (deriveNamed s.e s.cfg D').h = (deriveNamed s.e s.cfg D).hJ ∧
        (deriveNamed s.e s.cfg D').tH =
          getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) := by
  rcases Proofs.Consensus.RootEntry.stateBeforeTime_fgRoot_honestEntry c p a nr s rho hs hqh hcar v time with hg |
    ⟨D, row, nu, t2, i, cache, st3, q, D', K, hD, hDj, hH, hrow, ht2, hem, hev, hcache, hd, hinv, hbod, hq, hqt,
      hD', hD'q, hD'h, -, hK, hKD', hKe, hKh, hKt, hKr⟩
  · exact Or.inl hg
  · right
    obtain ⟨J, hJ, hJD, hJe⟩ := bodies_j_named s (Proofs.Consensus.JustifiedCarrier.stateBeforeTime_inv c p a nr s rho time v) hD
    have hJe' := hJe.trans hDj
    have hJrun : BlockInRun c p a nr s rho J := by
      have hJ' := hJ
      rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs time] at hJ'
      exact blockInRun_of_stateBefore c p a nr s rho hv _ hJ'
    have hKrun : BlockInRun c p a nr s rho K := blockInRun_of_stateBefore c p a nr s rho hH (i + 1) hK
    have hroot : namedRoot J = namedRoot K := by
      rw [← root_eraseBlock, ← root_eraseBlock, hJe', hKr]
    have hJK : J = K := hcf J K ⟨hJrun, hKrun⟩ J K ⟨⟨Or.inl (namedPreceq_self J), Or.inr (namedPreceq_self K)⟩, hroot⟩
    subst hJK
    exact ⟨D, J, row, nu, t2, i, q, D', hD, hDj, hJ, hJD, hJe', hH, hrow, ht2, hem, hev, hD', hD'q,
      ⟨cache, st3, hcache, hd, hinv, hbod, hq, hqt⟩, hK, hKD', hKh, hKt, hD'h, hKe.symm.trans hJe'⟩

/-- **store の言葉の版**: `stateBeforeTime_fgRoot_entryWitness` の `D'` / `J` を `StoreInv.sigma` で署名者の tick の中の store
`st3` の chain 状態に移す。読みの FG root `R` が genesis でなければ、honest な署名者の行(height pair `Vote hJ (root R) nu`)の
務めの FG source `q` について `(chainStateOf st3.core.sigma q).(h, tH) = (hJ, R)` で、`R` 自身も `st3` の tree にあって
`(chainStateOf st3.core.sigma R).(h, tH) = (hJ, R)`、さらに `preceq R q = true`(`namedPreceq J D'` を `eraseBlock_preceq` で
消去に落とす。周回 168)。手書きでは `fgRoot_confirmationWitness_at_read` / `_at_action` の
`(n.st.core.σ Cfg).T_h = some R` に当たる(務めの store は tick の中の `st3`)。 -/
theorem stateBeforeTime_fgRoot_storeWitness (hs : EventsSorted rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hcf : NamedRootCollisionFree c p a nr s rho) {v : ValidatorId} (hv : v ∈ rho.honest.elems) (time : Int) :
    getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) = Block.Genesis ∨
      ∃ (D : NamedBlock) (row : NamedAttestation) (nu : Bool) (t2 : Int) (i : Nat) (q : Block)
        (cache : Model.Consensus.Protocol.Grades.Cache) (st3 : NamedStore),
        D ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems ∧
        (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∧
        row.valIndex ∈ rho.honest.elems ∧
        row.heightPair = NamedHeightPair.Vote (deriveNamed s.e s.cfg D).hJ
          (root (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core))) nu ∧
        t2 < time ∧ Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 ∧
        rho.events[i]? = some (NamedEvent.Tick row.valIndex t2) ∧
        cache = Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (storeToHealing (worldAt (stateBefore c p a nr s rho i) row.valIndex).st.core) t2
          (worldAt (stateBefore c p a nr s rho i) row.valIndex).cache ∧
        st3 = Proofs.Consensus.AttestationSource.tickDutyStore c p nr cache s.e s.hc s.cfg
          (Model.Consensus.Execution.Setup.setupNode row.valIndex) (worldAt (stateBefore c p a nr s rho i) row.valIndex).st t2 ∧
        StoreInv s.e s.cfg st3 ∧
        (worldAt (stateBefore c p a nr s rho (i + 1)) row.valIndex).st.bodies = st3.bodies ∧
        Model.Consensus.Protocol.Duties.Inputs.fgSourceWith cache s.e s.hc (storeToHealing st3.core)
            (Model.Consensus.Protocol.Grades.roundOf s.hc st3.core.s)
            (Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith cache s.e s.hc (storeToHealing st3.core)
              (Model.Consensus.Protocol.Grades.roundOf s.hc st3.core.s)) = some q ∧
        q ∈ st3.core.tree.elems ∧
        (chainStateOf st3.core.sigma q).h = (deriveNamed s.e s.cfg D).hJ ∧
        (chainStateOf st3.core.sigma q).tH =
          getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∧
        getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∈ st3.core.tree.elems ∧
        (chainStateOf st3.core.sigma
          (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core))).h =
          (deriveNamed s.e s.cfg D).hJ ∧
        (chainStateOf st3.core.sigma
          (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core))).tH =
          getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∧
        preceq (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core)) q = true := by
  rcases stateBeforeTime_fgRoot_entryWitness c p a nr s rho hs hqh hcar hcf hv time with hg |
    ⟨D, J, row, nu, t2, i, q, D', hD, hDj, -, -, hJe, hH, hrow, ht2, hem, hev, hD', hD'q,
      ⟨cache, st3, hcache, hd, hinv, hbod, hq, hqt⟩, hJ, hJD', hJh, hJt, hD'h, hD't⟩
  · exact Or.inl hg
  · right
    rw [hbod] at hD' hJ
    have hsq := hinv.sigma D' hD'
    have hsJ := hinv.sigma J hJ
    have hpre := eraseBlock_preceq hJD'
    rw [hD'q] at hsq hpre
    rw [hJe] at hsJ hpre
    refine ⟨D, row, nu, t2, i, q, cache, st3, hD, hDj, hH, hrow, ht2, hem, hev, hcache, hd, hinv, hbod, hq, hqt,
      ?_, ?_, ?_, ?_, ?_, hpre⟩
    · rw [hsq]; exact hD'h
    · rw [hsq]; exact hD't
    · rw [← hJe]; exact hinv.tree J hJ
    · rw [hsJ]; exact hJh
    · rw [hsJ, hJt, hJe]

/-- run の添字 `i` の event `Tick w t` の中で attestation の務めが読む store(`AttestationSource.tickDutyStore` に tick の前の
`w` の store と tick の `onPhaseTick` の cache を渡したもの)。手書きの `actionStoreAt` に当たる(周回 171)。
手書きは round の添字で確認の更新を無条件に掛けるが、ここは event の添字と時刻で、確認の更新は supportCutoff の時刻だけ。
`rho.events[i]? = some (Tick w t)` でなくても定義されるので、単独で使うときはその前提を持ち回る(周回 172)。 -/
def dutyStoreAt (w : ValidatorId) (i : Nat) (t : Int) : NamedStore :=
  Proofs.Consensus.AttestationSource.tickDutyStore c p nr
    (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
      (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t (worldAt (stateBefore c p a nr s rho i) w).cache)
    s.e s.hc s.cfg (Model.Consensus.Execution.Setup.setupNode w) (worldAt (stateBefore c p a nr s rho i) w).st t

/-- 務めの FG source の chain 状態の `tH`(source が無ければ `none`)。手書き `fgConfirmationWitness`
(`DecoupledConsensusInternal/Legacy/Definitions/ActionSources.lean:48`)の `(actionFGSource S n).map (fun Cfg => (n.st.core.σ Cfg).T_h)` に当たる(周回 171)。 -/
def fgConfirmationWitnessAt (w : ValidatorId) (i : Nat) (t : Int) : Option Block :=
  (Model.Consensus.Protocol.Duties.Inputs.fgSourceWith
      (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
        (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t (worldAt (stateBefore c p a nr s rho i) w).cache)
      s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
      (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
      (Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
        (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
          (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t (worldAt (stateBefore c p a nr s rho i) w).cache)
        s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s))).map
    (fun q => (chainStateOf (dutyStoreAt c p a nr s rho w i t).core.sigma q).tH)

/-- **務めの確認の証人の source の 2 つの場合**(前提なし): 務めの確認の証人が `T` なら、`T` は務めの FG source `q` の
chain 状態の `tH` で、`q` は務めの store の `liveConfirmed` の祖先か、務めの grade 2 の候補そのもの
(`AttestationSource.fgSourceWith_cases`)。手書きの段で `hform.witness` を `hlive` と窓の SG block に分ける前の、
`fg_source_with` の `deepest_clear` の場合分けに当たる(周回 182)。 -/
theorem fgConfirmationWitnessAt_source {w : ValidatorId} {i : Nat} {t : Int} {T : Block}
    (h : fgConfirmationWitnessAt c p a nr s rho w i t = some T) :
    ∃ q : Block, T = (chainStateOf (dutyStoreAt c p a nr s rho w i t).core.sigma q).tH ∧
      (preceq q (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed = true ∨
        Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
          (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
            (worldAt (stateBefore c p a nr s rho i) w).cache)
          s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) = some q) := by
  unfold fgConfirmationWitnessAt at h
  obtain ⟨q, hq, hT⟩ := Option.map_eq_some_iff.mp h
  exact ⟨q, hT.symm, Proofs.Consensus.AttestationSource.fgSourceWith_cases hq⟩

/-- **確認の証人は source の祖先**(前提なし): 務めの確認の証人が `T` なら、14 の source `q` は務めの store の tree にあり、
`T ⪯ q`(務めの store は `stateBefore` の `StoreInv` / `TreeInv` を受け継ぎ、`AttestationSource.chainState_tH_preceq`)。
したがって `T` は務めの store の `liveConfirmed` の祖先か、務めの grade 2 の候補 `q` の祖先。手書きの段で `hform.witness` の
`T ⪯ live_confirmed` の枝(`derive_named_T_h_preceq` と `deepest_clear_preceq` の推移)と、grade 2 の枝の `T ⪯ q` に当たる
(周回 183)。 -/
theorem fgConfirmationWitnessAt_preceq_source {w : ValidatorId} {i : Nat} {t : Int} {T : Block}
    (h : fgConfirmationWitnessAt c p a nr s rho w i t = some T) :
    ∃ q : Block, T = (chainStateOf (dutyStoreAt c p a nr s rho w i t).core.sigma q).tH ∧
      q ∈ (dutyStoreAt c p a nr s rho w i t).core.tree.elems ∧ preceq T q = true ∧
      (preceq T (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed = true ∨
        Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
          (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
            (worldAt (stateBefore c p a nr s rho i) w).cache)
          s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) = some q) := by
  have hi : StoreInv s.e s.cfg (dutyStoreAt c p a nr s rho w i t) :=
    Proofs.Consensus.AttestationSource.tickDutyStore_inv c p nr _ s.hc _ t (stateBefore_inv c p a nr s rho i w)
  have ht : Proofs.Consensus.Trees.TreeInv (dutyStoreAt c p a nr s rho w i t).core :=
    Proofs.Consensus.AttestationSource.tickDutyStore_treeInv c p nr _ s.hc _ t (stateBefore_inv c p a nr s rho i w)
      (Proofs.Consensus.Trees.stateBefore_treeInv c p a nr s rho i w)
  have h' := h
  unfold fgConfirmationWitnessAt at h'
  obtain ⟨q, hq, hT⟩ := Option.map_eq_some_iff.mp h'
  have hqm : q ∈ (dutyStoreAt c p a nr s rho w i t).core.tree.elems :=
    Proofs.Consensus.AttestationSource.fgSource_mem_tree hi ht hq
  have hTq : preceq T q = true := by
    rw [← hT]
    exact Proofs.Consensus.AttestationSource.chainState_tH_preceq hi hqm
  refine ⟨q, hT.symm, hqm, hTq, ?_⟩
  rcases Proofs.Consensus.AttestationSource.fgSourceWith_cases hq with hl | hg
  · exact Or.inl (Proofs.Consensus.Blocks.preceq_trans hTq hl)
  · exact Or.inr hg

/-- 務めの store の確認の更新の前の段(`AttestationSource.tickPreUpdateStore`。時計合わせ・提案・投票の後)。 -/
def preUpdateStoreAt (w : ValidatorId) (i : Nat) (t : Int) : NamedStore :=
  Proofs.Consensus.AttestationSource.tickPreUpdateStore c p nr
    (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
      (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t (worldAt (stateBefore c p a nr s rho i) w).cache)
    s.e s.hc s.cfg (Model.Consensus.Execution.Setup.setupNode w) (worldAt (stateBefore c p a nr s rho i) w).st t

/-- **務めの store の `liveConfirmed` の出どころ**(前提なし): `stateBefore i` の `w` の store の `liveConfirmed` のままか、
務めの store の FG root か、確認の更新の前の段 `preUpdateStoreAt` の eligible な head
(`AttestationSource.tickDutyStore_live_cases`。周回 184)。 -/
theorem dutyStoreAt_live_cases (w : ValidatorId) (i : Nat) (t : Int) :
    (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed =
        (worldAt (stateBefore c p a nr s rho i) w).st.core.liveConfirmed ∨
      (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed =
        getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) ∨
      (Proofs.Consensus.Goldfish.eligible s.e (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)
          (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true ∧
        (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed =
          Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) :=
  Proofs.Consensus.AttestationSource.tickDutyStore_live_cases c p nr _ s.e s.hc s.cfg _ _ t

/-- **確認の証人の 4 つの枝**(前提なし): 務めの確認の証人 `T` は、`stateBefore i` の `w` の store の `liveConfirmed` の祖先か、
務めの store の FG root の祖先か、確認の更新の前の段の eligible な head の祖先か、務めの grade 2 の候補 `q` の祖先
(15 の `liveConfirmed` の枝を `dutyStoreAt_live_cases` で割る。周回 184)。手書きの段で `T ⪯ live_confirmed` に `hlive` を
掛けるところを、`live_confirmed` の出どころごとに分けたもの(手書きの出どころの場合分けは
`actionStoreAt_liveConfirmed_genuine_or_fgRoot` の 2 枝。行を出した tick の 3 枝の版は
`fgConfirmationWitnessAt_preceq_cases_of_emits`)。 -/
theorem fgConfirmationWitnessAt_preceq_cases {w : ValidatorId} {i : Nat} {t : Int} {T : Block}
    (h : fgConfirmationWitnessAt c p a nr s rho w i t = some T) :
    preceq T (worldAt (stateBefore c p a nr s rho i) w).st.core.liveConfirmed = true ∨
      preceq T (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) = true ∨
      (Proofs.Consensus.Goldfish.eligible s.e (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)
          (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true ∧
        preceq T (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true) ∨
      ∃ q : Block, Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
          (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
            (worldAt (stateBefore c p a nr s rho i) w).cache)
          s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) = some q ∧
        preceq T q = true := by
  obtain ⟨q, -, -, hTq, hl | hg⟩ := fgConfirmationWitnessAt_preceq_source c p a nr s rho h
  · rcases dutyStoreAt_live_cases c p a nr s rho w i t with he | he | ⟨hel, he⟩
    · exact Or.inl (he ▸ hl)
    · exact Or.inr (Or.inl (he ▸ hl))
    · exact Or.inr (Or.inr (Or.inl ⟨hel, he ▸ hl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨q, hg, hTq⟩))

/-- **FG root が `X` の祖先なら**(前提なし): 務めの確認の証人 `T` は `X` の祖先か、残る 3 つの枝(前の `liveConfirmed`、
eligible な head、grade 2 の候補)のどれか。`hstep` の中で、段の仮定の FG root ⪯ X から確認の証人の FG root の枝を閉じる形
(周回 184)。 -/
theorem fgConfirmationWitnessAt_preceq_of_fgRoot {w : ValidatorId} {i : Nat} {t : Int} {T X : Block}
    (h : fgConfirmationWitnessAt c p a nr s rho w i t = some T)
    (hroot : preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true) :
    preceq T X = true ∨
      preceq T (worldAt (stateBefore c p a nr s rho i) w).st.core.liveConfirmed = true ∨
      (Proofs.Consensus.Goldfish.eligible s.e (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)
          (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true ∧
        preceq T (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true) ∨
      ∃ q : Block, Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
          (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
            (worldAt (stateBefore c p a nr s rho i) w).cache)
          s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) = some q ∧
        preceq T q = true := by
  rcases fgConfirmationWitnessAt_preceq_cases c p a nr s rho h with hl | hr | hh | hg
  · exact Or.inr (Or.inl hl)
  · exact Or.inl (Proofs.Consensus.Blocks.preceq_trans hr hroot)
  · exact Or.inr (Or.inr (Or.inl hh))
  · exact Or.inr (Or.inr (Or.inr hg))

/-- **務めの確認の証人の版**: 前提 `EventsSorted` / `QuorumHonest` / `hcar` と `NamedRootCollisionFree` の下で、honest な `v` の
時刻 `< time` の読みの FG root `R` は genesis か、読みの bodies の `D`(導出の `j` が `R`)と honest な署名者の行(height pair
`Vote hJ (root R) nu`、発行は時刻 `t2 < time` の添字 `i` の `Tick`)があって、その tick の務めの確認の証人が `R`
(`fgConfirmationWitnessAt … i t2 = some R`)。手書き `fgRoot_confirmationWitness_at_read` の
`fgConfirmationWitness S (actionStoreAt …) = some R` に当たる(周回 171)。 -/
theorem stateBeforeTime_fgRoot_confirmationWitness (hs : EventsSorted rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hcf : NamedRootCollisionFree c p a nr s rho) {v : ValidatorId} (hv : v ∈ rho.honest.elems) (time : Int) :
    getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) = Block.Genesis ∨
      ∃ (D : NamedBlock) (row : NamedAttestation) (nu : Bool) (t2 : Int) (i : Nat),
        D ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems ∧
        (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) ∧
        row.valIndex ∈ rho.honest.elems ∧
        row.heightPair = NamedHeightPair.Vote (deriveNamed s.e s.cfg D).hJ
          (root (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core))) nu ∧
        t2 < time ∧ Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 ∧
        rho.events[i]? = some (NamedEvent.Tick row.valIndex t2) ∧
        fgConfirmationWitnessAt c p a nr s rho row.valIndex i t2 =
          some (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core)) := by
  rcases stateBeforeTime_fgRoot_storeWitness c p a nr s rho hs hqh hcar hcf hv time with hg |
    ⟨D, row, nu, t2, i, q, cache, st3, hD, hDj, hH, hrow, ht2, hem, hev, hcache, hd, -, -, hq, -, -, hqt, -, -, -, -⟩
  · exact Or.inl hg
  · right
    refine ⟨D, row, nu, t2, i, hD, hDj, hH, hrow, ht2, hem, hev, ?_⟩
    subst hcache
    have hd' : st3 = dutyStoreAt c p a nr s rho row.valIndex i t2 := hd
    subst hd'
    unfold fgConfirmationWitnessAt
    rw [hq, Option.map_some, hqt]

/-- **最近の務めの証人と古い証人から FG root の互換を出す**: 前提 `EventsSorted` / `QuorumHonest` / `hcar` と
`NamedRootCollisionFree` の下で、honest な `v` の時刻 `< time` の読みの FG root `R` と任意のブロック `B` について、
`hrecent`(時刻 `cutTime ≤ t < time` に honest な `w` が行を出した tick の務めの確認の証人 `T` はどれも `B` と互換。
手書きと同じく行を出した務めの tick だけを量化する)と
`hbootstrap`(時刻 `< cutTime` の、`R` を説明する古い行の証人が `R` なら `B` と `R` は互換)から `compatible R B`。
`R` が genesis なら `preceq_genesis` で前提なしに成り立つ。手書き `fgRoot_compatible_of_bootstrap_and_recentActions_at_read`
(`Protocol/ChainState/FGRootWitness.lean`)に当たり、手書きの round の境 `a.round < cut` を時刻の境 `t2 < cutTime` に置き換えた
(周回 172)。 -/
theorem stateBeforeTime_fgRoot_compatible_of_bootstrap_and_recent (hs : EventsSorted rho)
    (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hcf : NamedRootCollisionFree c p a nr s rho) {v : ValidatorId} (hv : v ∈ rho.honest.elems) {time cutTime : Int}
    {B : Block}
    (hrecent : ∀ (w : ValidatorId) (i : Nat) (t : Int), cutTime ≤ t → t < time → w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) →
      ∀ row : NamedAttestation, row.valIndex = w → Emits c p a nr s rho w (NamedObject.Attest row) t →
      ∀ T, fgConfirmationWitnessAt c p a nr s rho w i t = some T → compatible B T = true)
    (hbootstrap : ∀ (D : NamedBlock) (row : NamedAttestation) (nu : Bool) (t2 : Int) (i : Nat),
      D ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems →
      (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) →
      row.valIndex ∈ rho.honest.elems →
      row.heightPair = NamedHeightPair.Vote (deriveNamed s.e s.cfg D).hJ
        (root (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core))) nu →
      t2 < time → t2 < cutTime → Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 →
      rho.events[i]? = some (NamedEvent.Tick row.valIndex t2) →
      fgConfirmationWitnessAt c p a nr s rho row.valIndex i t2 =
        some (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core)) →
      compatible B (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core)) = true) :
    compatible (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core)) B = true := by
  rcases stateBeforeTime_fgRoot_confirmationWitness c p a nr s rho hs hqh hcar hcf hv time with hg |
    ⟨D, row, nu, t2, i, hD, hDj, hH, hrow, ht2, hem, hev, hT⟩
  · rw [hg]
    unfold compatible
    rw [Proofs.Consensus.Blocks.preceq_genesis, Bool.true_or]
  · rw [Proofs.Consensus.Blocks.compatible_comm]
    by_cases hcut : t2 < cutTime
    · exact hbootstrap D row nu t2 i hD hDj hH hrow ht2 hcut hem hev hT
    · exact hrecent row.valIndex i t2 (le_of_not_gt hcut) ht2 hH hev row rfl hem _ hT

end Run

/-! ## 提案しない tick の務めの store の FG root(周回 173)

`getFgRoot` は store の `hMax` / `hJ` / `j` / `f` だけを読む。tick の中で務めの store `tickDutyStore` を作る段のうち、時計合わせ・
投票 `namedGoldfishVoteWith`・確認の更新 `namedUpdateConfirmationWith` はこの 4 欄を変えず、変えうるのは提案
`proposeBlockWith`(自分のブロックの受理)だけ。したがって提案しない tick では、務めの store の FG root は tick の前の store の
FG root に等しい。手書き `fgRoot_confirmationWitness_at_action` が使う `actionStoreAt_fgRoot_eq_storeBeforeTime`(務めの store の
FG root は読みの FG root)の前段に当たる。 -/

/-- 投票 `namedGoldfishVoteWith` は FG root を変えない(`timestampVote` / `gfVotes` だけを更新する)。 -/
theorem namedGoldfishVoteWith_fgRoot (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) :
    getFgRoot (storeToHealing (Model.Consensus.Protocol.Duties.Proposals.namedGoldfishVoteWith c cache e hc nd st).1.core) =
      getFgRoot (storeToHealing st.core) := by
  unfold Model.Consensus.Protocol.Duties.Proposals.namedGoldfishVoteWith
  split
  rename_i core out h
  show getFgRoot (storeToHealing core) = getFgRoot (storeToHealing st.core)
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [h]
  subst h1
  unfold goldfishVoteWith
  dsimp only
  split_ifs
  · unfold onGoldfishVoteChecked
    split_ifs
    · rfl
    · unfold onGoldfishVote
      split_ifs <;> rfl
  · rfl

/-- 確認の更新 `namedUpdateConfirmationWith` は FG root を変えない(`liveConfirmed` / `latestConfirmed` / `latestStable` だけを
更新する)。 -/
theorem namedUpdateConfirmationWith_fgRoot (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : NamedStore) (k : Nat) :
    getFgRoot (storeToHealing
        (Model.Consensus.Protocol.Duties.Proposals.namedUpdateConfirmationWith cache e hc st k).core) =
      getFgRoot (storeToHealing st.core) := rfl

/-- **提案しない tick の務めの store の FG root**: tick の提案の条件(`0 < s`・`t` が slot `s` の提案時刻・`s` の proposer が
自分)が成り立たなければ、`tickDutyStore` の FG root は tick の前の store の FG root。 -/
theorem tickDutyStore_fgRoot_of_not_proposing (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) (t : Int)
    (hnp : ¬ ((decide (0 < slotOf e t) && (t == Model.Consensus.Protocol.Schedule.proposalTime e (slotOf e t))) &&
      (p (slotOf e t) == nd.valIndex)) = true) :
    getFgRoot (storeToHealing (Proofs.Consensus.AttestationSource.tickDutyStore c p nr cache e hc cfg nd st t).core) =
      getFgRoot (storeToHealing st.core) := by
  unfold Proofs.Consensus.AttestationSource.tickDutyStore
  dsimp only
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  split_ifs
  all_goals simp only [namedUpdateConfirmationWith_fgRoot, namedGoldfishVoteWith_fgRoot]
  all_goals rfl

/-- tick の出力に行があれば、tick の時刻はある round の action 時刻(生成 `tick` の attestation の条件の左半分)。 -/
theorem tick_attest_actionTime {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (Model.Consensus.Protocol.Tick.tick c p a nr cache e hc cfg nd st rec t).2.2) :
    ∃ r : Nat, t = Model.Consensus.Protocol.Grades.actionTime hc e.delta r := by
  revert hrow
  unfold Model.Consensus.Protocol.Tick.tick
  dsimp only
  split_ifs
  all_goals intro hrow
  all_goals simp only [List.mem_append, List.mem_singleton] at hrow
  -- attestation を出さない経路: 出力に行は無い
  all_goals (try (exfalso; rcases hrow with h | h <;> (try split at h) <;> simp at h; done))
  -- attestation を出す経路: 最後の `if` の条件から時刻を取り出す
  all_goals
    rename_i hact
    simp only [Bool.and_eq_true, beq_iff_eq] at hact
    exact ⟨_, hact.1⟩

/-- tick の出力に行があれば、tick の時刻は務めの store `tickDutyStore` の slot の round の action 時刻(生成 `tick` の
attestation の条件の左半分を、round を務めの store から読む形で取り出す。周回 178)。 -/
theorem tick_attest_actionTime_dutyStore {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (Model.Consensus.Protocol.Tick.tick c p a nr cache e hc cfg nd st rec t).2.2) :
    t = Model.Consensus.Protocol.Grades.actionTime hc e.delta
      (Model.Consensus.Protocol.Grades.roundOf hc
        (Proofs.Consensus.AttestationSource.tickDutyStore c p nr cache e hc cfg nd st t).core.s) := by
  revert hrow
  unfold Model.Consensus.Protocol.Tick.tick Proofs.Consensus.AttestationSource.tickDutyStore
  dsimp only
  split_ifs
  all_goals intro hrow
  all_goals simp only [List.mem_append, List.mem_singleton] at hrow
  -- attestation を出さない経路: 出力に行は無い
  all_goals (try (exfalso; rcases hrow with h | h <;> (try split at h) <;> simp at h; done))
  -- attestation を出す経路: 最後の `if` の条件から時刻を取り出す
  all_goals
    rename_i hact
    simp only [Bool.and_eq_true, beq_iff_eq] at hact
    exact hact.1

/-- **行の round の action 時刻**: tick の出力に行 `row` があれば、tick の時刻は `row.round` の action 時刻。行は務めの store
`tickDutyStore` での `attestWith` の行(`tick_attest_dutyStore`)で、その round は務めの store の slot の round
(`attestationInput` の `round` を `namedCreate` がそのまま写す)。手書きでは行が round `a.round` の action 時刻にだけ出ることに
当たる(周回 178)。 -/
theorem tick_attest_actionTime_round {e : ProtocolEnv} {cfg : HeightConfig} (c : Nat → NaruStd.Set ValidatorId)
    (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId)
    (cache : Model.Consensus.Protocol.Grades.Cache) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (Model.Consensus.Protocol.Tick.tick c p a nr cache e hc cfg nd st rec t).2.2) :
    t = Model.Consensus.Protocol.Grades.actionTime hc e.delta row.round := by
  have ht := tick_attest_actionTime_dutyStore c p a nr cache hc nd st rec t hrow
  obtain ⟨-, -, hr⟩ := Proofs.Consensus.AttestationSource.tick_attest_dutyStore c p a nr cache hc nd st rec t hrow
  rw [hr]
  exact ht

/-- **action 時刻は round について狭義単調**(Δ > 0、`0 < R`): `actionTime r1 < actionTime r2 ↔ r1 < r2`
(`4Δ · (r · R) + 6Δ` の `r` の係数 `4Δ · R` が正)。時刻の境と round の境を行き来するのに使う(周回 178)。 -/
theorem actionTime_lt_actionTime_iff {delta : Int} (hδ : 0 < delta) {hc : Model.Consensus.Protocol.Grades.HealConfig}
    (hr : 0 < hc.r) (r1 r2 : Nat) :
    Model.Consensus.Protocol.Grades.actionTime hc delta r1 < Model.Consensus.Protocol.Grades.actionTime hc delta r2 ↔
      r1 < r2 := by
  unfold Model.Consensus.Protocol.Grades.actionTime Model.Consensus.Objects.Time.slotStart
    Model.Consensus.Protocol.Grades.openingSlot
  simp only [Int.ofNat_eq_natCast, Nat.cast_mul]
  have hr' : (0 : Int) < (hc.r : Int) := by exact_mod_cast hr
  have hpos : 0 < delta * (hc.r : Int) := mul_pos hδ hr'
  constructor
  · intro h
    by_contra hge
    have hle : (r2 : Int) ≤ (r1 : Int) := by exact_mod_cast not_lt.mp hge
    nlinarith
  · intro h
    have hlt : (r1 : Int) < (r2 : Int) := by exact_mod_cast h
    nlinarith

/-- **action 時刻は提案時刻ではない**(Δ > 0): `4Δ · (r · R) + 6Δ = 4Δ · k` なら `6 = 4 · (k - r · R)` で、整数では成り立たない。 -/
theorem actionTime_ne_proposalTime {e : ProtocolEnv} (hδ : 0 < e.delta) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (r k : Nat) :
    Model.Consensus.Protocol.Grades.actionTime hc e.delta r ≠ Model.Consensus.Protocol.Schedule.proposalTime e k := by
  unfold Model.Consensus.Protocol.Grades.actionTime Model.Consensus.Protocol.Schedule.proposalTime
    Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    Model.Consensus.Protocol.Grades.openingSlot
  simp only [Int.ofNat_eq_natCast]
  intro h
  have h0 : e.delta * (4 * (k : Int) - 4 * ((r * hc.r : Nat) : Int) - 6) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hδ.ne' h1
  · omega

/-- action 時刻の tick は提案しない(Δ > 0): `tick` の `proposing` の Bool 式は真でない。 -/
theorem not_proposing_of_actionTime {e : ProtocolEnv} (hδ : 0 < e.delta) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (p : Nat → ValidatorId) (nd : Model.Consensus.Protocol.Schedule.Node) {t : Int} {r : Nat}
    (ht : t = Model.Consensus.Protocol.Grades.actionTime hc e.delta r) :
    ¬ ((decide (0 < slotOf e t) && (t == Model.Consensus.Protocol.Schedule.proposalTime e (slotOf e t))) &&
      (p (slotOf e t) == nd.valIndex)) = true := by
  simp only [Bool.and_eq_true, beq_iff_eq]
  rintro ⟨⟨-, hp⟩, -⟩
  exact actionTime_ne_proposalTime hδ hc r _ (ht ▸ hp)

/-- **行を出した tick の務めの store の FG root**(Δ > 0): tick の出力に行があれば、その tick は提案しないので、
`tickDutyStore` の FG root は tick の前の store の FG root。 -/
theorem tickDutyStore_fgRoot_of_attest {e : ProtocolEnv} {cfg : HeightConfig} (hδ : 0 < e.delta)
    (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (Model.Consensus.Protocol.Tick.tick c p a nr cache e hc cfg nd st rec t).2.2) :
    getFgRoot (storeToHealing (Proofs.Consensus.AttestationSource.tickDutyStore c p nr cache e hc cfg nd st t).core) =
      getFgRoot (storeToHealing st.core) := by
  obtain ⟨r, ht⟩ := tick_attest_actionTime c p a nr cache hc nd st rec t hrow
  exact tickDutyStore_fgRoot_of_not_proposing c p nr cache e hc cfg nd st t (not_proposing_of_actionTime hδ hc p nd ht)

section RunAtAction

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **run の版**: `w` が時刻 `t` の slot の proposer でない(または `t` が提案時刻でない)なら、添字 `i` の tick の務めの store
`dutyStoreAt w i t` の FG root は、`stateBefore i` の `w` の store の FG root。 -/
theorem dutyStoreAt_fgRoot_of_not_proposing (w : ValidatorId) (i : Nat) (t : Int)
    (hnp : ¬ ((decide (0 < slotOf s.e t) && (t == Model.Consensus.Protocol.Schedule.proposalTime s.e (slotOf s.e t))) &&
      (p (slotOf s.e t) == (Model.Consensus.Execution.Setup.setupNode w).valIndex)) = true) :
    getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) =
      getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) :=
  tickDutyStore_fgRoot_of_not_proposing c p nr _ s.e s.hc s.cfg _ _ t hnp

/-- **行を出した時刻の務めの store の FG root**(Δ > 0): `w` が時刻 `t` に行 `row` を出したなら、`t` は action 時刻で提案の
時刻ではないので、任意の添字 `i` の務めの store `dutyStoreAt w i t` の FG root は `stateBefore i` の `w` の store の FG root
(`dutyStoreAt_fgRoot_of_not_proposing` の前提 `hnp` を発行から供給する。周回 174)。 -/
theorem dutyStoreAt_fgRoot_of_emits (hδ : 0 < s.e.delta) {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) (i : Nat) :
    getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) =
      getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) := by
  obtain ⟨j, -, hrow⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho w _ t).mp hem
  rw [Proofs.Consensus.Signing.nodeTick_out] at hrow
  obtain ⟨r, ht⟩ := tick_attest_actionTime c p a nr _ s.hc _ _ _ t hrow
  exact dutyStoreAt_fgRoot_of_not_proposing c p a nr s rho w i t (not_proposing_of_actionTime hδ s.hc p _ ht)

/-- `idxLt t` から tick `Tick w t`(添字 `i`)までの event は `w` のものではない(`EventsSorted` と重複なし): その時刻は `t` 以上で
key は `(t, 0)` 以下なので、`w` の配送(phase 1)は並ばず、`w` の時刻 `t` の tick は添字 `i` の event と同じで重複になる。 -/
theorem eventNode_ne_of_idxLt_le_of_lt_tick (hs : EventsSorted rho) (hnd : rho.events.Nodup) {w : ValidatorId}
    {i j : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick w t))
    (hj : Proofs.Consensus.ReceiverFinality.idxLt rho t ≤ j) (hji : j < i) {ev : NamedEvent}
    (hev : rho.events[j]? = some ev) : eventNode ev ≠ w := by
  have hge : t ≤ eventTime ev := by
    by_contra hlt
    have := Proofs.Consensus.ReceiverFinality.lt_idxLt_of_time_lt rho hs hnd hev (not_le.mp hlt)
    omega
  have hkey : compare (eventKey ev) (eventKey (NamedEvent.Tick w t)) ≠ .gt := by
    have h := hs j i hji
    rw [hev, hi] at h
    exact h
  intro hn
  cases ev with
  | Tick u t' =>
    simp only [eventNode] at hn
    subst hn
    have hle : t' ≤ t := Proofs.Consensus.Runs.time_le_of_key_ne_gt hkey
    simp only [eventTime] at hge hle
    have ht' : t' = t := le_antisymm hle hge
    subst ht'
    have hjl : j < rho.events.length := (List.getElem?_eq_some_iff.mp hev).1
    have : j = i := (List.Nodup.getElem?_inj hjl hnd).mp (hev.trans hi.symm)
    omega
  | Deliver u o t' =>
    apply hkey
    simp only [eventTime] at hge
    show (compare t' t).then (compare (1 : Nat) 0) = .gt
    rcases lt_or_eq_of_le hge with hlt | heq
    · rw [Int.compare_eq_gt.mpr hlt]
      rfl
    · rw [heq, Int.compare_eq_eq.mpr rfl]
      rfl

/-- **tick の前の状態は時刻 `< t` の読み**(`EventsSorted` と重複なし): 添字 `i` の event が `Tick w t` なら、`stateBefore i` の
`w` の状態は `stateBeforeTime t` の `w` の状態。`idxLt t ≤ i` で、その間の event はどれも `w` のものでない
(`eventNode_ne_of_idxLt_le_of_lt_tick`)ので `RecordGrowth.node_succ_other` で `w` の状態は変わらない(周回 175)。 -/
theorem worldAt_stateBefore_tick_eq_stateBeforeTime (hs : EventsSorted rho) (hnd : rho.events.Nodup)
    {w : ValidatorId} {i : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick w t)) :
    worldAt (stateBefore c p a nr s rho i) w = worldAt (stateBeforeTime c p a nr s rho t) w := by
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs]
  have hle : Proofs.Consensus.ReceiverFinality.idxLt rho t ≤ i := by
    by_contra hlt
    have := Proofs.Consensus.JustificationCertificate.time_lt_of_lt_idxLt rho hs (not_le.mp hlt) hi
    simp only [eventTime] at this
    exact lt_irrefl _ this
  have hil : i < rho.events.length := (List.getElem?_eq_some_iff.mp hi).1
  have key : ∀ n, Proofs.Consensus.ReceiverFinality.idxLt rho t ≤ n → n ≤ i →
      worldAt (stateBefore c p a nr s rho n) w =
        worldAt (stateBefore c p a nr s rho (Proofs.Consensus.ReceiverFinality.idxLt rho t)) w := by
    intro n
    induction n with
    | zero => intro h0 _; rw [Nat.le_zero.mp h0]
    | succ n ih =>
      intro hm hni
      by_cases hmn : Proofs.Consensus.ReceiverFinality.idxLt rho t ≤ n
      · have hnl : n < rho.events.length := by omega
        have hev : rho.events[n]? = some rho.events[n] := List.getElem?_eq_getElem hnl
        rw [Proofs.Consensus.RecordGrowth.node_succ_other c p a nr s rho hev w
          (eventNode_ne_of_idxLt_le_of_lt_tick rho hs hnd hi hmn (by omega) hev)]
        exact ih hmn (by omega)
      · have : Proofs.Consensus.ReceiverFinality.idxLt rho t = n + 1 := by omega
        rw [this]
  exact key i hle le_rfl

/-- **行を出した tick の務めの store の FG root は時刻 `< t` の読みの FG root**(Δ > 0、`EventsSorted` と重複なし): `w` が時刻 `t` に
行 `row` を出し、添字 `i` の event が `Tick w t` なら、務めの store `dutyStoreAt w i t` の FG root は `stateBeforeTime t` の `w` の
store の FG root。`dutyStoreAt_fgRoot_of_emits` と `worldAt_stateBefore_tick_eq_stateBeforeTime` を合わせたもの。手書き
`actionStoreAt_fgRoot_eq_storeBeforeTime` に当たる(手書きの務めの store は定義上読みの時刻の store から作るので `rfl` だが、
生成 `tick` は tick の前の状態 `stateBefore i` から作るので橋渡しが要る。周回 175)。 -/
theorem dutyStoreAt_fgRoot_eq_stateBeforeTime (hδ : 0 < s.e.delta) (hs : EventsSorted rho) (hnd : EventsNodup rho)
    {w : ValidatorId} {row : NamedAttestation} {t : Int} (hem : Emits c p a nr s rho w (NamedObject.Attest row) t)
    {i : Nat} (hi : rho.events[i]? = some (NamedEvent.Tick w t)) :
    getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) =
      getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho t) w).st.core) := by
  rw [dutyStoreAt_fgRoot_of_emits c p a nr s rho hδ hem i,
    worldAt_stateBefore_tick_eq_stateBeforeTime c p a nr s rho hs
      (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) hi]

/-- **行を出した tick の務めの store の FG root の確認の証人**(Δ > 0、`EventsSorted` と重複なし、`QuorumHonest` / `hcar` /
`NamedRootCollisionFree`): honest な `w` が時刻 `t` に行 `row` を出し、添字 `i` の event が `Tick w t` なら、務めの store
`dutyStoreAt w i t` の FG root `R` は genesis か、読みの bodies の `D`(導出の `j` が `R`)と honest な署名者の行(height pair
`Vote hJ (root R) nu`、発行は時刻 `t2 < t` の添字 `i2` の `Tick`)があって、その tick の務めの確認の証人が `R`。
`dutyStoreAt_fgRoot_eq_stateBeforeTime` で `R` を `w` の時刻 `< t` の読みの FG root に移し、
`stateBeforeTime_fgRoot_confirmationWitness` を掛けたもの。手書き `fgRoot_confirmationWitness_at_action`
(`Protocol/ChainState/FGRootWitness.lean`)に当たる(周回 176)。 -/
theorem dutyStoreAt_fgRoot_confirmationWitness (hδ : 0 < s.e.delta) (hs : EventsSorted rho) (hnd : EventsNodup rho)
    (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hcf : NamedRootCollisionFree c p a nr s rho) {w : ValidatorId} (hw : w ∈ rho.honest.elems)
    {row : NamedAttestation} {t : Int} (hem : Emits c p a nr s rho w (NamedObject.Attest row) t)
    {i : Nat} (hi : rho.events[i]? = some (NamedEvent.Tick w t)) :
    getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) = Block.Genesis ∨
      ∃ (D : NamedBlock) (row2 : NamedAttestation) (nu : Bool) (t2 : Int) (i2 : Nat),
        D ∈ (worldAt (stateBeforeTime c p a nr s rho t) w).st.bodies.elems ∧
        (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) ∧
        row2.valIndex ∈ rho.honest.elems ∧
        row2.heightPair = NamedHeightPair.Vote (deriveNamed s.e s.cfg D).hJ
          (root (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core))) nu ∧
        t2 < t ∧ Emits c p a nr s rho row2.valIndex (NamedObject.Attest row2) t2 ∧
        rho.events[i2]? = some (NamedEvent.Tick row2.valIndex t2) ∧
        fgConfirmationWitnessAt c p a nr s rho row2.valIndex i2 t2 =
          some (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) := by
  rw [dutyStoreAt_fgRoot_eq_stateBeforeTime c p a nr s rho hδ hs hnd hem hi]
  exact stateBeforeTime_fgRoot_confirmationWitness c p a nr s rho hs hqh hcar hcf hw t

/-- **行を出した tick の務めの FG root は `X` の祖先 — 最近の証人と古い根から**(Δ > 0、`EventsSorted` と重複なし、
`QuorumHonest` / `hcar` / `NamedRootCollisionFree`): honest な `w` が時刻 `t` に行 `row` を出し、添字 `i` の event が `Tick w t` で、
`hrecent`(時刻 `cutTime ≤ t2 < t` に honest な署名者が行を出した tick の務めの確認の証人 `T` はどれも `T ⪯ X`)と
`hlegacy`(時刻 `t2 < cutTime` の、務めの FG root `R` を説明する古い行の証人が `R` なら `R ⪯ X`)があれば、務めの store
`dutyStoreAt w i t` の FG root は `X` の祖先。`R` が genesis なら `preceq_genesis` で前提なしに成り立つ。手書き
`actionSources_preceq_of_priorConfirmations_and_historyCut`(`Protocol/Grades/WeakBootstrapAction.lean`)の帰納の中の段 `hroots`
に当たり、手書きの round の境 `a.round < cut` を時刻の境 `t2 < cutTime` に置き換えた(周回 177)。 -/
theorem dutyStoreAt_fgRoot_preceq_of_recent_and_legacy (hδ : 0 < s.e.delta) (hs : EventsSorted rho)
    (hnd : EventsNodup rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hcf : NamedRootCollisionFree c p a nr s rho) {w : ValidatorId} (hw : w ∈ rho.honest.elems)
    {row : NamedAttestation} {t : Int} (hem : Emits c p a nr s rho w (NamedObject.Attest row) t)
    {i : Nat} (hi : rho.events[i]? = some (NamedEvent.Tick w t)) {cutTime : Int} {X : Block}
    (hrecent : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int), cutTime ≤ t2 → t2 < t → w2 ∈ rho.honest.elems →
      rho.events[i2]? = some (NamedEvent.Tick w2 t2) →
      ∀ row2 : NamedAttestation, row2.valIndex = w2 → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
      ∀ T, fgConfirmationWitnessAt c p a nr s rho w2 i2 t2 = some T → preceq T X = true)
    (hlegacy : ∀ (D : NamedBlock) (row2 : NamedAttestation) (nu : Bool) (t2 : Int) (i2 : Nat),
      D ∈ (worldAt (stateBeforeTime c p a nr s rho t) w).st.bodies.elems →
      (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) →
      row2.valIndex ∈ rho.honest.elems →
      row2.heightPair = NamedHeightPair.Vote (deriveNamed s.e s.cfg D).hJ
        (root (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core))) nu →
      t2 < t → t2 < cutTime → Emits c p a nr s rho row2.valIndex (NamedObject.Attest row2) t2 →
      rho.events[i2]? = some (NamedEvent.Tick row2.valIndex t2) →
      fgConfirmationWitnessAt c p a nr s rho row2.valIndex i2 t2 =
        some (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) →
      preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true) :
    preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true := by
  rcases dutyStoreAt_fgRoot_confirmationWitness c p a nr s rho hδ hs hnd hqh hcar hcf hw hem hi with hg |
    ⟨D, row2, nu, t2, i2, hD, hDj, hH, hrow, ht2, hem2, hev, hT⟩
  · rw [hg]
    exact Proofs.Consensus.Blocks.preceq_genesis X
  · by_cases hcut : t2 < cutTime
    · exact hlegacy D row2 nu t2 i2 hD hDj hH hrow ht2 hcut hem2 hev hT
    · exact hrecent row2.valIndex i2 t2 (le_of_not_gt hcut) ht2 hH hev row2 rfl hem2 _ hT

/-- **発行した行の時刻は行の round の action 時刻**: `w` が時刻 `t` に行 `row` を出したなら `t = actionTime row.round`
(`tick_attest_actionTime_round` を `Emits` の tick に掛けたもの。周回 178)。 -/
theorem emits_attest_actionTime_round {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) :
    t = Model.Consensus.Protocol.Grades.actionTime s.hc s.e.delta row.round := by
  obtain ⟨j, -, hrow⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho w _ t).mp hem
  rw [Proofs.Consensus.Signing.nodeTick_out] at hrow
  exact tick_attest_actionTime_round c p a nr _ s.hc _ _ _ t hrow

/-- **時刻の境と round の境の対応**(Δ > 0、`0 < R`): `w` が時刻 `t` に行 `row` を出したなら、
`t < actionTime cut ↔ row.round < cut`。round `cut` の action 時刻を時刻の境 `cutTime` に置くと、周回 172 / 177 の時刻の境
`t2 < cutTime` は手書きの round の境 `a.round < cut` と同じ行を選ぶ(周回 178)。 -/
theorem emits_attest_time_lt_actionTime_iff (hδ : 0 < s.e.delta) (hr : 0 < s.hc.r) {w : ValidatorId}
    {row : NamedAttestation} {t : Int} (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) (cut : Nat) :
    t < Model.Consensus.Protocol.Grades.actionTime s.hc s.e.delta cut ↔ row.round < cut := by
  rw [emits_attest_actionTime_round c p a nr s rho hem]
  exact actionTime_lt_actionTime_iff hδ hr row.round cut

/-- **行を出した tick の確認の更新の slot は行の round の opening slot**(Δ > 0): `w` が時刻 `t` に行 `row` を出したなら、
`slotOf t - 1 = openingSlot row.round`(`t` は action 時刻で、その slot は opening slot の次。`AttestationSource.slotOf_actionTime`)。
手書きの確認の更新が opening slot の store `confStore … (opening_slot r)` で読むことに当たる(周回 185)。 -/
theorem emits_attest_slotOf_pred (hδ : 0 < s.e.delta) {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) :
    slotOf s.e t - 1 = Model.Consensus.Protocol.Grades.openingSlot s.hc row.round := by
  rw [emits_attest_actionTime_round c p a nr s rho hem,
    Proofs.Consensus.AttestationSource.slotOf_actionTime hδ s.hc row.round, Nat.add_sub_cancel]

/-- **行を出した tick の務めの store の `liveConfirmed` の 2 つの枝**(Δ > 0): `w` が時刻 `t` に行 `row` を出したなら、`t` は
action 時刻(`emits_attest_actionTime_round`)で supportCutoff の時刻でもあるので、務めの store は必ず確認の更新を通る
(`AttestationSource.tickDutyStore_live_cases_of_actionTime`)。したがって任意の添字 `i` の務めの store `dutyStoreAt w i t` の
`liveConfirmed` は、務めの store の FG root か、確認の更新の前の段 `preUpdateStoreAt` の eligible な head で、
`dutyStoreAt_live_cases` の第 1 の枝(`stateBefore i` の値のまま)は起きない。手書き
`actionStoreAt_liveConfirmed_genuine_or_fgRoot`(`Execution/RecoveryActionLiveSourceSplit.lean`。GenuineConfirmation と FG root の
2 枝)に当たる。手書きの FG root の枝は確認の更新の前の store(`confStore`)の FG root で、こちらは更新の後の務めの store の
FG root だが、確認の更新は FG root の 4 欄を変えないので値は同じ。確認の更新の slot `slotOf t - 1` は行の round の opening slot
(`emits_attest_slotOf_pred`。周回 185)。 -/
theorem dutyStoreAt_live_cases_of_emits (hδ : 0 < s.e.delta) {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) (i : Nat) :
    (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed =
        getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) ∨
      (Proofs.Consensus.Goldfish.eligible s.e (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)
          (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true ∧
        (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed =
          Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) :=
  Proofs.Consensus.AttestationSource.tickDutyStore_live_cases_of_actionTime c p nr _ s.e s.hc s.cfg _ _ hδ
    (emits_attest_actionTime_round c p a nr s rho hem)

/-- **行を出した tick の確認の証人の 3 つの枝**(Δ > 0): `w` が時刻 `t` に行 `row` を出したなら、務めの確認の証人 `T` は、
務めの store の FG root の祖先か、確認の更新の前の段の eligible な head の祖先か、務めの grade 2 の候補 `q` の祖先
(`fgConfirmationWitnessAt_preceq_source` の `liveConfirmed` の枝を `dutyStoreAt_live_cases_of_emits` で割る。
`fgConfirmationWitnessAt_preceq_cases` の第 1 の枝(前の `liveConfirmed`)は起きない。周回 185)。 -/
theorem fgConfirmationWitnessAt_preceq_cases_of_emits (hδ : 0 < s.e.delta) {w : ValidatorId}
    {row : NamedAttestation} {t : Int} (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat} {T : Block}
    (h : fgConfirmationWitnessAt c p a nr s rho w i t = some T) :
    preceq T (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) = true ∨
      (Proofs.Consensus.Goldfish.eligible s.e (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)
          (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true ∧
        preceq T (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true) ∨
      ∃ q : Block, Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
          (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
            (worldAt (stateBefore c p a nr s rho i) w).cache)
          s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) = some q ∧
        preceq T q = true := by
  obtain ⟨q, -, -, hTq, hl | hg⟩ := fgConfirmationWitnessAt_preceq_source c p a nr s rho h
  · rcases dutyStoreAt_live_cases_of_emits c p a nr s rho hδ hem i with he | ⟨hel, he⟩
    · exact Or.inl (he ▸ hl)
    · exact Or.inr (Or.inl ⟨hel, he ▸ hl⟩)
  · exact Or.inr (Or.inr ⟨q, hg, hTq⟩)

/-- **行を出した tick で FG root が `X` の祖先なら**(Δ > 0): 務めの確認の証人 `T` は `X` の祖先か、eligible な head の枝か、
grade 2 の候補の枝(`fgConfirmationWitnessAt_preceq_of_fgRoot` から前の `liveConfirmed` の枝を除いた形。`hstep` の中で、段の
仮定の FG root ⪯ X の下で残るのは、手書きの `hprior`(GenuineConfirmation ⪯ D)を掛ける枝と窓の SG block に繋ぐ枝の 2 つ。
周回 185。`hprior` を掛けた版は `fgConfirmationWitnessAt_preceq_of_emits_prior`)。 -/
theorem fgConfirmationWitnessAt_preceq_of_emits_fgRoot (hδ : 0 < s.e.delta) {w : ValidatorId}
    {row : NamedAttestation} {t : Int} (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat}
    {T X : Block} (h : fgConfirmationWitnessAt c p a nr s rho w i t = some T)
    (hroot : preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true) :
    preceq T X = true ∨
      (Proofs.Consensus.Goldfish.eligible s.e (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)
          (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true ∧
        preceq T (Proofs.Consensus.Goldfish.head
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1)) = true) ∨
      ∃ q : Block, Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
          (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
            (worldAt (stateBefore c p a nr s rho i) w).cache)
          s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) = some q ∧
        preceq T q = true := by
  rcases fgConfirmationWitnessAt_preceq_cases_of_emits c p a nr s rho hδ hem h with hr | hh | hg
  · exact Or.inl (Proofs.Consensus.Blocks.preceq_trans hr hroot)
  · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr hg)

/-- **務めの tick の genuine な確認**: `C` は確認の更新の前の段 `preUpdateStoreAt` の head(確認の更新の slot `slotOf t - 1` の
`Goldfish.head`)で、その slot で eligible。手書き `GenuineConfirmationWith`(`Protocol/Grades/ProposalLifecycleCore.lean`。
欄 `selected`(更新の後の `live_confirmed` が `C`)と `genuine`(walk の結果が eligible)。両方が揃えば `C` は eligible な
walk の結果)に当たる。手書きは opening slot の `confStore` で読み、
ここは添字 `i` の tick の確認の更新の前の段で読む(行を出した tick ではその slot は行の round の opening slot。
`emits_attest_slotOf_pred`。周回 186)。 -/
def GenuineConfirmationAt (w : ValidatorId) (i : Nat) (t : Int) (C : Block) : Prop :=
  C = Proofs.Consensus.Goldfish.head
      (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
        (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
        (worldAt (stateBefore c p a nr s rho i) w).cache)
      s.e s.hc (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1) ∧
    Proofs.Consensus.Goldfish.eligible s.e (preUpdateStoreAt c p a nr s rho w i t).core (slotOf s.e t - 1) C = true

/-- **行を出した tick の `liveConfirmed` は genuine な確認か FG root**(Δ > 0): `dutyStoreAt_live_cases_of_emits` の 2 枝を
`GenuineConfirmationAt` で書いた形。手書き `actionStoreAt_liveConfirmed_genuine_or_fgRoot` と同じ内容の 2 枝
(第 1 の枝が GenuineConfirmation、第 2 の枝が FG root。第 2 枝の存在量化を外した形)。手書きの FG root は確認の更新の前の store(`confStore`)の FG root で、
こちらは更新の後の務めの store の FG root だが、確認の更新は FG root の 4 欄を変えないので値は同じ
(`namedUpdateConfirmationWith_fgRoot`。周回 186)。 -/
theorem dutyStoreAt_live_genuine_or_fgRoot_of_emits (hδ : 0 < s.e.delta) {w : ValidatorId} {row : NamedAttestation}
    {t : Int} (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) (i : Nat) :
    (∃ C : Block, GenuineConfirmationAt c p a nr s rho w i t C ∧
        C = (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed) ∨
      (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed =
        getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) := by
  rcases dutyStoreAt_live_cases_of_emits c p a nr s rho hδ hem i with he | ⟨hel, he⟩
  · exact Or.inr he
  · exact Or.inl ⟨_, ⟨rfl, hel⟩, he.symm⟩

/-- **行を出した tick の `liveConfirmed` は `X` の祖先**(Δ > 0): 務めの store の FG root が `X` の祖先で(`hroot`)、
その tick の genuine な確認がどれも `X` の祖先なら(`hprior`)、務めの store の `liveConfirmed` も `X` の祖先。
手書き `actionSources_preceq_of_priorConfirmations_and_historyCut` の本体の `hlive`(`hprior` を opening slot で呼ぶ枝と
`hroots` の枝)に当たる。手書きの `hprior` は `cut` の opening slot 以上 `s` 未満の全 slot と全 honest を量化するが、ここはこの tick の
確認だけを受ける(周回 186)。 -/
theorem dutyStoreAt_live_preceq_of_prior (hδ : 0 < s.e.delta) {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat} {X : Block}
    (hroot : preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true)
    (hprior : ∀ C, GenuineConfirmationAt c p a nr s rho w i t C → preceq C X = true) :
    preceq (dutyStoreAt c p a nr s rho w i t).core.liveConfirmed X = true := by
  rcases dutyStoreAt_live_genuine_or_fgRoot_of_emits c p a nr s rho hδ hem i with ⟨C, hC, he⟩ | he
  · rw [← he]
    exact hprior C hC
  · rw [he]
    exact hroot

/-- **行を出した tick の確認の証人は `X` の祖先か grade 2 の枝**(Δ > 0): FG root ⪯ X(`hroot`)とこの tick の genuine な確認
⪯ X(`hprior`)の下で、務めの確認の証人 `T` は `X` の祖先か、務めの grade 2 の候補 `q` の祖先
(`fgConfirmationWitnessAt_preceq_source` の `liveConfirmed` の枝に `dutyStoreAt_live_preceq_of_prior` を掛ける)。手書きの本体で
`hform.witness` の第 1 の枝に `hlive` を掛けるところに当たり、残る枝は窓の SG block に繋ぐ grade 2 の枝(周回 186)。 -/
theorem fgConfirmationWitnessAt_preceq_of_emits_prior (hδ : 0 < s.e.delta) {w : ValidatorId}
    {row : NamedAttestation} {t : Int} (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat}
    {T X : Block} (h : fgConfirmationWitnessAt c p a nr s rho w i t = some T)
    (hroot : preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true)
    (hprior : ∀ C, GenuineConfirmationAt c p a nr s rho w i t C → preceq C X = true) :
    preceq T X = true ∨
      ∃ q : Block, Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
          (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
            (worldAt (stateBefore c p a nr s rho i) w).cache)
          s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) = some q ∧
        preceq T q = true := by
  obtain ⟨q, -, -, hTq, hl | hg⟩ := fgConfirmationWitnessAt_preceq_source c p a nr s rho h
  · exact Or.inl (Proofs.Consensus.Blocks.preceq_trans hl
      (dutyStoreAt_live_preceq_of_prior c p a nr s rho hδ hem hroot hprior))
  · exact Or.inr ⟨q, hg, hTq⟩

/-- **round の同時帰納で行ごとの性質 `Q` と FG root・確認の証人を運ぶ**(Δ > 0、`0 < R`、`EventsSorted` と重複なし、
`QuorumHonest` / `hcar` / `NamedRootCollisionFree`、`base ≤ cut`): round `base` 以上の行を時刻 `< limit` に出した honest な
tick について、
- `hbootstrap`: round `base` 以上 `cut` 未満の行の tick は `Q` を満たす。
- `hlegacy`: round `cut` 以上の行の tick で、round `< cut` の古い行の証人が務めの FG root `R` なら `R ⪯ X`。
- `hstep`: round `cut` 以上の行 `row` の tick で、前の round の仮定(round `base` 以上 `row.round` 未満の行の tick はどれも
  `Q` を満たし、round `cut` 以上 `row.round` 未満の行の tick の FG root と確認の証人はどれも `X` の祖先)の下で、自分の務めの
  FG root も `X` の祖先なら、自分も `Q` を満たし確認の証人も `X` の祖先。`hstep` は、同じ round `row.round` の行を出した
  honest な tick の務めの FG root がどれも `X` の祖先であることも仮定に受ける(本体が自分の FG root と同じ導出で出す)。

これらから、その tick は `Q` を満たし、round が `cut` 以上なら務めの FG root と確認の証人はどれも `X` の祖先。
手書き `actionSources_preceq_of_priorConfirmations_and_historyCut`(`Protocol/Grades/WeakBootstrapAction.lean`)の
round の強い帰納の骨組みの 2 つの連言に当たる。`Q` を手書きの第 1 連言(行の tick の SG block ⪯ X)に置くと、手書きの段
`hsg`(round `base` 以上 `r` 未満の行の SG block)は `hstep` の第 1 の仮定として届く。段 `hroots` は
`dutyStoreAt_fgRoot_preceq_of_recent_and_legacy` に `cutTime := actionTime cut` を置き、時刻の境を
`emits_attest_time_lt_actionTime_iff` で round の境に移して帰納法の仮定から供給する。`hstep` の中身(SG block と確認の証人を
grade と clear から押さえる段)は含まない(周回 180)。手書きの `hformation`・`hprior`、round 0 の場合、窓の `hspan`
も `hstep` を書く側が供給し、`hlive` は書く側が `hprior` と FG root から導く(手書きでも前提ではなく本体で導く)。同じ round の FG root の仮定は行を出した tick だけを量化し、行を出さない honest の FG root は
含まない(周回 181)。 -/
theorem dutyStoreAt_jointRoundInduction (hδ : 0 < s.e.delta) (hr : 0 < s.hc.r) (hs : EventsSorted rho)
    (hnd : EventsNodup rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hcf : NamedRootCollisionFree c p a nr s rho) {base cut : Nat} {limit : Int} {X : Block}
    (Q : ValidatorId → Nat → Int → NamedAttestation → Prop) (hbc : base ≤ cut)
    (hbootstrap : ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → base ≤ row.round → row.round < cut → Q w i t row)
    (hlegacy : ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → cut ≤ row.round →
      ∀ (D : NamedBlock) (row2 : NamedAttestation) (nu : Bool) (t2 : Int) (i2 : Nat),
      D ∈ (worldAt (stateBeforeTime c p a nr s rho t) w).st.bodies.elems →
      (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) →
      row2.valIndex ∈ rho.honest.elems →
      row2.heightPair = NamedHeightPair.Vote (deriveNamed s.e s.cfg D).hJ
        (root (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core))) nu →
      t2 < t → row2.round < cut → Emits c p a nr s rho row2.valIndex (NamedObject.Attest row2) t2 →
      rho.events[i2]? = some (NamedEvent.Tick row2.valIndex t2) →
      fgConfirmationWitnessAt c p a nr s rho row2.valIndex i2 t2 =
        some (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) →
      preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true)
    (hstep : ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → cut ≤ row.round →
      (∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        base ≤ row2.round → row2.round < row.round → Q w2 i2 t2 row2) →
      (∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        cut ≤ row2.round → row2.round < row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w2 i2 t2).core)) X = true ∧
          ∀ T, fgConfirmationWitnessAt c p a nr s rho w2 i2 t2 = some T → preceq T X = true) →
      (∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        row2.round = row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w2 i2 t2).core)) X = true) →
      preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true →
      Q w i t row ∧ ∀ T, fgConfirmationWitnessAt c p a nr s rho w i t = some T → preceq T X = true) :
    ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → base ≤ row.round →
      Q w i t row ∧ (cut ≤ row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true ∧
          ∀ T, fgConfirmationWitnessAt c p a nr s rho w i t = some T → preceq T X = true) := by
  suffices h : ∀ r : Nat, ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), row.round = r →
      w ∈ rho.honest.elems → rho.events[i]? = some (NamedEvent.Tick w t) →
      Emits c p a nr s rho w (NamedObject.Attest row) t → t < limit → base ≤ row.round →
      Q w i t row ∧ (cut ≤ row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true ∧
          ∀ T, fgConfirmationWitnessAt c p a nr s rho w i t = some T → preceq T X = true) by
    intro w i t row
    exact h row.round w i t row rfl
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro w i t row hrr hw hi hem hlim hbase
    by_cases hboot : row.round < cut
    · exact ⟨hbootstrap w i t row hw hi hem hlim hbase hboot, fun h => absurd h (not_le_of_gt hboot)⟩
    have hcut : cut ≤ row.round := le_of_not_gt hboot
    -- 前の round の行は時刻 `t` より前(action 時刻の狭義単調性)なので `limit` 未満で、帰納法の仮定が使える。
    have hearlier : ∀ {w2 : ValidatorId} {t2 : Int} {row2 : NamedAttestation},
        Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 → row2.round < row.round → t2 < t := by
      intro w2 t2 row2 hem2 hlt
      rw [emits_attest_actionTime_round c p a nr s rho hem2, emits_attest_actionTime_round c p a nr s rho hem]
      exact (actionTime_lt_actionTime_iff hδ hr row2.round row.round).mpr hlt
    have hprevQ : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        base ≤ row2.round → row2.round < row.round → Q w2 i2 t2 row2 := by
      intro w2 i2 t2 row2 hw2 hi2 hem2 hb2 hlt
      exact (ih row2.round (hrr ▸ hlt) w2 i2 t2 row2 rfl hw2 hi2 hem2 ((hearlier hem2 hlt).trans hlim) hb2).1
    have hprev : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        cut ≤ row2.round → row2.round < row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w2 i2 t2).core)) X = true ∧
          ∀ T, fgConfirmationWitnessAt c p a nr s rho w2 i2 t2 = some T → preceq T X = true := by
      intro w2 i2 t2 row2 hw2 hi2 hem2 hcut2 hlt
      exact (ih row2.round (hrr ▸ hlt) w2 i2 t2 row2 rfl hw2 hi2 hem2 ((hearlier hem2 hlt).trans hlim)
        (hbc.trans hcut2)).2 hcut2
    -- 同じ round の行を出した honest な tick の FG root は、どれも `X` の祖先(段 `hroots`)。同じ round の行の時刻は
    -- `t` と同じ action 時刻なので `limit` 未満で、前の round の仮定と `hlegacy` がその tick にも届く。
    have hsame : ∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        row2.round = row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w2 i2 t2).core)) X = true := by
      intro w2 i2 t2 row2 hw2 hi2 hem2 hsr
      have ht2t : t2 = t := by
        rw [emits_attest_actionTime_round c p a nr s rho hem2, emits_attest_actionTime_round c p a nr s rho hem, hsr]
      have hcut2 : cut ≤ row2.round := hsr ▸ hcut
      refine dutyStoreAt_fgRoot_preceq_of_recent_and_legacy c p a nr s rho hδ hs hnd hqh hcar hcf hw2 hem2 hi2
        (cutTime := Model.Consensus.Protocol.Grades.actionTime s.hc s.e.delta cut) ?_ ?_
      · intro w3 i3 t3 hct3 ht3 hw3 hi3 row3 hrow3 hem3 T hT
        subst hrow3
        have hcut3 : cut ≤ row3.round :=
          le_of_not_gt fun h => absurd ((emits_attest_time_lt_actionTime_iff c p a nr s rho hδ hr hem3 cut).mpr h)
            (not_lt_of_ge hct3)
        have hlt : row3.round < row.round := by
          rw [emits_attest_actionTime_round c p a nr s rho hem3, emits_attest_actionTime_round c p a nr s rho hem2]
            at ht3
          exact hsr ▸ (actionTime_lt_actionTime_iff hδ hr row3.round row2.round).mp ht3
        exact (hprev row3.valIndex i3 t3 row3 hw3 hi3 hem3 hcut3 hlt).2 T hT
      · intro D row3 nu t3 i3 hD hDj hH hrow ht3 hct3 hem3 hev hT
        exact hlegacy w2 i2 t2 row2 hw2 hi2 hem2 (ht2t ▸ hlim) hcut2 D row3 nu t3 i3 hD hDj hH hrow ht3
          ((emits_attest_time_lt_actionTime_iff c p a nr s rho hδ hr hem3 cut).mp hct3) hem3 hev hT
    have hroot := hsame w i t row hw hi hem rfl
    obtain ⟨hq, hwit⟩ := hstep w i t row hw hi hem hlim hcut hprevQ hprev hsame hroot
    exact ⟨hq, fun _ => ⟨hroot, hwit⟩⟩

/-- **round の帰納で FG root と確認の証人を運ぶ**(Δ > 0、`0 < R`、`EventsSorted` と重複なし、`QuorumHonest` / `hcar` /
`NamedRootCollisionFree`): round `cut` 以上の行を時刻 `< limit` に出した honest な tick について、
`hlegacy`(round `< cut` の古い行の証人が務めの FG root `R` なら `R ⪯ X`)と
`hstep`(round `cut ≤ row.round` の行の tick で、前の round の仮定(round `cut` 以上 `row.round` 未満の行の tick の FG root と
確認の証人がどれも `X` の祖先)の下で、自分の務めの FG root も `X` の祖先なら、自分の確認の証人も `X` の祖先)から、務めの
FG root と確認の証人はどれも `X` の祖先。手書き `actionSources_preceq_of_priorConfirmations_and_historyCut` の帰納の骨組みの
第 2 連言だけを運ぶ版で、`hstep` の帰納法の仮定には SG block の連言が無い(周回 179)。手書きの段 `hsg` を `hstep` の中で
使うには、同時帰納の `dutyStoreAt_jointRoundInduction` を使う。この定理はその `Q := True`、`base := cut` の系(周回 180)。 -/
theorem dutyStoreAt_preceq_of_roundInduction (hδ : 0 < s.e.delta) (hr : 0 < s.hc.r) (hs : EventsSorted rho)
    (hnd : EventsNodup rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hcf : NamedRootCollisionFree c p a nr s rho) {cut : Nat} {limit : Int} {X : Block}
    (hlegacy : ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → cut ≤ row.round →
      ∀ (D : NamedBlock) (row2 : NamedAttestation) (nu : Bool) (t2 : Int) (i2 : Nat),
      D ∈ (worldAt (stateBeforeTime c p a nr s rho t) w).st.bodies.elems →
      (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) →
      row2.valIndex ∈ rho.honest.elems →
      row2.heightPair = NamedHeightPair.Vote (deriveNamed s.e s.cfg D).hJ
        (root (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core))) nu →
      t2 < t → row2.round < cut → Emits c p a nr s rho row2.valIndex (NamedObject.Attest row2) t2 →
      rho.events[i2]? = some (NamedEvent.Tick row2.valIndex t2) →
      fgConfirmationWitnessAt c p a nr s rho row2.valIndex i2 t2 =
        some (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) →
      preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true)
    (hstep : ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → cut ≤ row.round →
      (∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        cut ≤ row2.round → row2.round < row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w2 i2 t2).core)) X = true ∧
          ∀ T, fgConfirmationWitnessAt c p a nr s rho w2 i2 t2 = some T → preceq T X = true) →
      preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true →
      ∀ T, fgConfirmationWitnessAt c p a nr s rho w i t = some T → preceq T X = true) :
    ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → cut ≤ row.round →
      preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true ∧
        ∀ T, fgConfirmationWitnessAt c p a nr s rho w i t = some T → preceq T X = true := by
  intro w i t row hw hi hem hlim hcut
  refine (dutyStoreAt_jointRoundInduction c p a nr s rho hδ hr hs hnd hqh hcar hcf (base := cut)
    (fun _ _ _ _ => True) le_rfl (fun _ _ _ _ _ _ _ _ _ _ => trivial) hlegacy ?_ w i t row hw hi hem hlim hcut).2 hcut
  intro w i t row hw hi hem hlim hcut _ hprev _ hroot
  exact ⟨trivial, hstep w i t row hw hi hem hlim hcut hprev hroot⟩

/-- **務めの grade 2 の候補**: 添字 `i` の tick の務めの store で、務めの store の slot の round(`roundOf … .core.s`)の
grade 2 の候補(`grade2BlockWith`)。行の round に繋ぐには `tick_attest_actionTime_round` 系の補題が要る(手書きは `actionStoreAt_round`)。
`fgConfirmationWitnessAt_preceq_source` などの第 2 の枝の `q` はこの値(周回 187)。 -/
def grade2CandidateAt (w : ValidatorId) (i : Nat) (t : Int) : Option Block :=
  Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
    (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
      (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
      (worldAt (stateBefore c p a nr s rho i) w).cache)
    s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
    (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)

/-- **行を出した tick の確認の証人は `X` の祖先**(Δ > 0): FG root ⪯ X(`hroot`)、この tick の genuine な確認 ⪯ X
(`hprior`)、務めの grade 2 の候補 ⪯ X(`hgrade2`)から、務めの確認の証人 ⪯ X。`fgConfirmationWitnessAt_preceq_of_emits_prior`
の grade 2 の枝を `T ⪯ q ⪯ X` で閉じる。手書きの本体で `hform.witness` の第 2 の枝を `nodeQ2_preceq_honestWindowCarrier`
(`WeakBootstrapAction.lean`)と窓の SG block ⪯ X で閉じるところに当たり、`hgrade2` はその 2 段をまとめた前提(周回 187)。 -/
theorem fgConfirmationWitnessAt_preceq_of_prior_grade2 (hδ : 0 < s.e.delta) {w : ValidatorId}
    {row : NamedAttestation} {t : Int} (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat}
    {T X : Block} (h : fgConfirmationWitnessAt c p a nr s rho w i t = some T)
    (hroot : preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true)
    (hprior : ∀ C, GenuineConfirmationAt c p a nr s rho w i t C → preceq C X = true)
    (hgrade2 : ∀ q, grade2CandidateAt c p a nr s rho w i t = some q → preceq q X = true) :
    preceq T X = true := by
  rcases fgConfirmationWitnessAt_preceq_of_emits_prior c p a nr s rho hδ hem h hroot hprior with hX | ⟨q, hq, hTq⟩
  · exact hX
  · exact Proofs.Consensus.Blocks.preceq_trans hTq (hgrade2 q hq)

/-- **round の同時帰納の `hstep` を genuine な確認と grade 2 の候補で書いた版**(Δ > 0、`0 < R`、`EventsSorted` と重複なし、
`QuorumHonest` / `hcar` / `NamedRootCollisionFree`、`base ≤ cut`): `dutyStoreAt_jointRoundInduction` の `hstep` の結論のうち
確認の証人の連言を、その tick の genuine な確認 ⪯ X と務めの grade 2 の候補 ⪯ X の 2 つに置き換えた。証人の連言は
`fgConfirmationWitnessAt_preceq_of_prior_grade2` で `hstep'` の FG root の仮定と合わせて出す。手書き
`actionSources_preceq_of_priorConfirmations_and_historyCut` では、`hprior` は定理の前提で opening slot で呼ばれ、grade 2 の
候補は窓の SG block を経て閉じる。ここではどちらも `hstep'` を書く側が帰納法の仮定の下で供給する(周回 187)。 -/
theorem dutyStoreAt_jointRoundInduction_of_prior (hδ : 0 < s.e.delta) (hr : 0 < s.hc.r) (hs : EventsSorted rho)
    (hnd : EventsNodup rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hcf : NamedRootCollisionFree c p a nr s rho) {base cut : Nat} {limit : Int} {X : Block}
    (Q : ValidatorId → Nat → Int → NamedAttestation → Prop) (hbc : base ≤ cut)
    (hbootstrap : ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → base ≤ row.round → row.round < cut → Q w i t row)
    (hlegacy : ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → cut ≤ row.round →
      ∀ (D : NamedBlock) (row2 : NamedAttestation) (nu : Bool) (t2 : Int) (i2 : Nat),
      D ∈ (worldAt (stateBeforeTime c p a nr s rho t) w).st.bodies.elems →
      (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core) →
      row2.valIndex ∈ rho.honest.elems →
      row2.heightPair = NamedHeightPair.Vote (deriveNamed s.e s.cfg D).hJ
        (root (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core))) nu →
      t2 < t → row2.round < cut → Emits c p a nr s rho row2.valIndex (NamedObject.Attest row2) t2 →
      rho.events[i2]? = some (NamedEvent.Tick row2.valIndex t2) →
      fgConfirmationWitnessAt c p a nr s rho row2.valIndex i2 t2 =
        some (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) →
      preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true)
    (hstep' : ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → cut ≤ row.round →
      (∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        base ≤ row2.round → row2.round < row.round → Q w2 i2 t2 row2) →
      (∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        cut ≤ row2.round → row2.round < row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w2 i2 t2).core)) X = true ∧
          ∀ T, fgConfirmationWitnessAt c p a nr s rho w2 i2 t2 = some T → preceq T X = true) →
      (∀ (w2 : ValidatorId) (i2 : Nat) (t2 : Int) (row2 : NamedAttestation), w2 ∈ rho.honest.elems →
        rho.events[i2]? = some (NamedEvent.Tick w2 t2) → Emits c p a nr s rho w2 (NamedObject.Attest row2) t2 →
        row2.round = row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w2 i2 t2).core)) X = true) →
      preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true →
      Q w i t row ∧ (∀ C, GenuineConfirmationAt c p a nr s rho w i t C → preceq C X = true) ∧
        ∀ q, grade2CandidateAt c p a nr s rho w i t = some q → preceq q X = true) :
    ∀ (w : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), w ∈ rho.honest.elems →
      rho.events[i]? = some (NamedEvent.Tick w t) → Emits c p a nr s rho w (NamedObject.Attest row) t →
      t < limit → base ≤ row.round →
      Q w i t row ∧ (cut ≤ row.round →
        preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true ∧
          ∀ T, fgConfirmationWitnessAt c p a nr s rho w i t = some T → preceq T X = true) := by
  refine dutyStoreAt_jointRoundInduction c p a nr s rho hδ hr hs hnd hqh hcar hcf Q hbc hbootstrap hlegacy ?_
  intro w i t row hw hi hem hlim hcut hprevQ hprev hsame hroot
  obtain ⟨hq, hprior, hgrade2⟩ := hstep' w i t row hw hi hem hlim hcut hprevQ hprev hsame hroot
  exact ⟨hq, fun T hT =>
    fgConfirmationWitnessAt_preceq_of_prior_grade2 c p a nr s rho hδ hem hT hroot hprior hgrade2⟩

/-- **action 時刻は G2 の domain 時刻ではない**(Δ > 0): `4Δ · (r · R) + 6Δ = 4Δ · (k · R) - Δ` なら
`7 = 4 · (k · R - r · R)` で、整数では成り立たない。手書きの `action_after_g2` は同じ round で `domain < a` を示す。
ここは round を問わない(周回 188)。 -/
theorem actionTime_ne_domainTime_G2 {e : ProtocolEnv} (hδ : 0 < e.delta) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (r k : Nat) :
    Model.Consensus.Protocol.Grades.actionTime hc e.delta r ≠
      Model.Consensus.Protocol.Grades.domainTime e hc k Model.Consensus.Protocol.Grades.GradePhase.G2 := by
  unfold Model.Consensus.Protocol.Grades.actionTime Model.Consensus.Protocol.Grades.domainTime
    Model.Consensus.Protocol.Grades.openingTime Model.Consensus.Protocol.Schedule.proposalTime
    Model.Consensus.Objects.Parameters.slotTime Model.Consensus.Objects.Time.slotStart
    Model.Consensus.Protocol.Grades.openingSlot
  simp only [Model.Consensus.Protocol.Grades.domainOffset, Int.ofNat_eq_natCast]
  intro h
  have h0 : e.delta * (4 * ((k * hc.r : Nat) : Int) - 4 * ((r * hc.r : Nat) : Int) - 7) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hδ.ne' h1
  · omega

/-- **務めの grade 2 の候補の出どころ**(前提なし): 務めの grade 2 の候補が `q` なら、`q ⪯ b0` の `b0` があり、
`stateBefore i` の `w` の cache の、務めの store の slot の round `k` の G2 の結果が `some (some b0)` か、tick の時刻 `t` が
round `k` の G2 の domain 時刻で、tick の前の store で `freezeRoot` が `b0` を凍結した
(`Grade2Capture.grade2BlockWith_onPhaseTick_cases`。手書き `q2_capture_at_action_read` の本体の前半。周回 188)。 -/
theorem grade2CandidateAt_cases {w : ValidatorId} {i : Nat} {t : Int} {q : Block}
    (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    ∃ b0, preceq q b0 = true ∧
      ((Model.Consensus.Protocol.Grades.cacheAtRound (worldAt (stateBefore c p a nr s rho i) w).cache
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)).g2 = some (some b0) ∨
        (t = Model.Consensus.Protocol.Grades.domainTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2 ∧
          Model.Consensus.Protocol.Grades.freezeRoot s.e
              (Model.Consensus.Protocol.Grades.gradeView
                (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core))
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core).f s.hc.etaSG
              (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
              (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc
                (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
                Model.Consensus.Protocol.Grades.GradePhase.G2)
              (Model.Consensus.Protocol.Grades.lateTime s.e s.hc
                (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
                Model.Consensus.Protocol.Grades.GradePhase.G2) = some b0)) :=
  Proofs.Consensus.Grade2Capture.grade2BlockWith_onPhaseTick_cases h

/-- **行を出した tick の grade 2 の候補は、tick の前の cache の G2 の結果の祖先**(Δ > 0): 行を出した tick の時刻は
action 時刻で G2 の domain 時刻ではない(`actionTime_ne_domainTime_G2`)ので、`grade2CandidateAt_cases` の凍結の枝は起きない。
務めの grade 2 の候補 `q` について、`stateBefore i` の `w` の cache の務めの round の G2 の結果は `some (some b0)` で `q ⪯ b0`。
`hem` は `t` が action 時刻であることにだけ使い、添字 `i` を問わない(`i` が `Tick w t` の添字でなくても成り立つ)。
手書き `q2_capture_at_action_read` の、action の読みの cache から tick の前の cache へ戻す段(`prepared_g2_from_old`)に
当たる(周回 188)。`b0` を凍結した tick への run の帰納(手書き `completed_phase_origin`)を掛けた形は
`grade2CandidateAt_origin_of_emits`。 -/
theorem grade2CandidateAt_of_emits (hδ : 0 < s.e.delta) {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat} {q : Block}
    (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    ∃ b0, preceq q b0 = true ∧
      (Model.Consensus.Protocol.Grades.cacheAtRound (worldAt (stateBefore c p a nr s rho i) w).cache
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)).g2 =
        some (some b0) := by
  obtain ⟨b0, hqb, hold | ⟨ht, -⟩⟩ := grade2CandidateAt_cases c p a nr s rho h
  · exact ⟨b0, hqb, hold⟩
  · rw [emits_attest_actionTime_round c p a nr s rho hem] at ht
    exact absurd ht (actionTime_ne_domainTime_G2 hδ s.hc _ _)

/-- **行を出した tick の grade 2 の候補は、前の tick で凍結した G2 の root の祖先**(Δ > 0): 務めの grade 2 の候補 `q` について、
務めの round を `k` とすると、添字 `j < i` の event `Tick w t2`(`t2` は round `k` の G2 の domain 時刻)があり、`stateBefore j` の
`w` の store で `freezeRoot` が `b0` を凍結し、`q ⪯ b0`。`grade2CandidateAt_of_emits` に `Grade2Capture.stateBefore_g2_origin`
を掛ける。手書き `q2_capture_at_action_read` の全体に当たる(手書きは任意の round を取り、ここは `hem` と Δ > 0 で務めの
round に限る。周回 189)。 -/
theorem grade2CandidateAt_origin_of_emits (hδ : 0 < s.e.delta) {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat} {q : Block}
    (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    ∃ (j : Nat) (t2 : Int) (b0 : Block), j < i ∧ rho.events[j]? = some (NamedEvent.Tick w t2) ∧
      t2 = Model.Consensus.Protocol.Grades.domainTime s.e s.hc
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
        Model.Consensus.Protocol.Grades.GradePhase.G2 ∧
      Model.Consensus.Protocol.Grades.freezeRoot s.e
          (Model.Consensus.Protocol.Grades.gradeView
            (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core))
          (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core).f s.hc.etaSG
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
          (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2)
          (Model.Consensus.Protocol.Grades.lateTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2) = some b0 ∧
      preceq q b0 = true := by
  obtain ⟨b1, hqb1, hold⟩ := grade2CandidateAt_of_emits c p a nr s rho hδ hem h
  obtain ⟨j, t2, b0, hj, he, ht2, hfz, hb10⟩ :=
    Proofs.Consensus.Grade2Capture.stateBefore_g2_origin c p a nr s rho i w _ hold
  exact ⟨j, t2, b0, hj, he, ht2, hfz, Proofs.Consensus.Blocks.preceq_trans hqb1 hb10⟩

/-- **行を出した tick の grade 2 の候補は、grade の通った凍結した root の祖先**(Δ > 0): 務めの grade 2 の候補 `q` について、
務めの round を `k` とすると、添字 `j < i` の event `Tick w t2`(`t2` は round `k` の G2 の domain 時刻)と block `b0` があり、
`b0` は `stateBefore j` の `w` の grade view の tree にあり、その store での round `k` の G2 の `gradeBool` が真で、`q ⪯ b0`。
`grade2CandidateAt_origin_of_emits` に `Grade2Capture.freezeRoot_mem` を掛ける。手書き `nodeQ2_preceq_honestWindowCarrier` の
`hfreeze` から出す局所の `hgrade'` に当たる(周回 190)。その後の `stateBeforeTime` への書き換え(`hrawGrade`)は
`grade2CandidateAt_graded_of_emits`(周回 191)。 -/
theorem grade2CandidateAt_frozen_of_emits (hδ : 0 < s.e.delta) {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat} {q : Block}
    (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    ∃ (j : Nat) (t2 : Int) (b0 : Block), j < i ∧ rho.events[j]? = some (NamedEvent.Tick w t2) ∧
      t2 = Model.Consensus.Protocol.Grades.domainTime s.e s.hc
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
        Model.Consensus.Protocol.Grades.GradePhase.G2 ∧
      b0 ∈ (Model.Consensus.Protocol.Grades.gradeView
            (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core)).tree.elems ∧
      Model.Consensus.Protocol.Grades.gradeBool s.e
          (Model.Consensus.Protocol.Grades.gradeView
            (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core))
          (storeToHealing (worldAt (stateBefore c p a nr s rho j) w).st.core).f s.hc.etaSG
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
          (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2)
          (Model.Consensus.Protocol.Grades.lateTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2) b0 = true ∧
      preceq q b0 = true := by
  obtain ⟨j, t2, b0, hj, he, ht2, hfz, hqb0⟩ := grade2CandidateAt_origin_of_emits c p a nr s rho hδ hem h
  obtain ⟨hmem, hgrade⟩ := Proofs.Consensus.Grade2Capture.freezeRoot_mem hfz
  exact ⟨j, t2, b0, hj, he, ht2, hmem, hgrade, hqb0⟩

/-- **行を出した tick の grade 2 の候補は、G2 の domain 時刻の読みで grade の通った block の祖先**(Δ > 0、`EventsSorted` と
重複なし): 務めの grade 2 の候補 `q` について、務めの round を `k` とすると block `b0` があり、`b0` は時刻
`< domainTime k G2` の読み `stateBeforeTime` の `w` の grade view の tree にあり、その store での round `k` の G2 の `gradeBool`
が真で、`q ⪯ b0`。`grade2CandidateAt_frozen_of_emits` の `stateBefore j` を `worldAt_stateBefore_tick_eq_stateBeforeTime` で
読みの時刻に移す。手書き `nodeQ2_preceq_honestWindowCarrier` の局所の `hrawGrade`(`hgrade'` を `stateBeforeTime` に書き換える段)
に当たる(周回 191)。 -/
theorem grade2CandidateAt_graded_of_emits (hδ : 0 < s.e.delta) (hs : EventsSorted rho) (hnd : EventsNodup rho)
    {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat} {q : Block}
    (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    ∃ b0 : Block,
      b0 ∈ (Model.Consensus.Protocol.Grades.gradeView
            (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
              (Model.Consensus.Protocol.Grades.domainTime s.e s.hc
                (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
                Model.Consensus.Protocol.Grades.GradePhase.G2)) w).st.core)).tree.elems ∧
      Model.Consensus.Protocol.Grades.gradeBool s.e
          (Model.Consensus.Protocol.Grades.gradeView
            (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
              (Model.Consensus.Protocol.Grades.domainTime s.e s.hc
                (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
                Model.Consensus.Protocol.Grades.GradePhase.G2)) w).st.core))
          (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
            (Model.Consensus.Protocol.Grades.domainTime s.e s.hc
              (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
              Model.Consensus.Protocol.Grades.GradePhase.G2)) w).st.core).f s.hc.etaSG
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
          (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2)
          (Model.Consensus.Protocol.Grades.lateTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2) b0 = true ∧
      preceq q b0 = true := by
  obtain ⟨j, t2, b0, -, he, ht2, hmem, hgrade, hqb0⟩ := grade2CandidateAt_frozen_of_emits c p a nr s rho hδ hem h
  have hw := worldAt_stateBefore_tick_eq_stateBeforeTime c p a nr s rho hs
    (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd) he
  rw [hw, ht2] at hmem hgrade
  exact ⟨b0, hmem, hgrade, hqb0⟩

/-- **行を出した tick の grade 2 の候補は、grade の担い手の祖先**(Δ > 0、`EventsSorted` と重複なし): 務めの round を `k` として、
時刻 `< domainTime k G2` の読みの `w` の store で round `k` の G2 の `gradeBool` が真の block `B` には、性質 `P` を持つ `Y` があって
`B ⪯ Y`(`hcarrier`)なら、務めの grade 2 の候補 `q` にも `P` を持つ `Y` があって `q ⪯ Y`。`grade2CandidateAt_graded_of_emits`
に `hcarrier` を掛けて `preceq_trans` で繋ぐ。手書き `nodeQ2_preceq_honestWindowCarrier` の、horizon の守りを外した強い前提の
版で、手書きの `hgrade`(`RelativeGradeCarrierAt` の G2 の段)の担い手「窓の round の honest な action の SG block」を `P` に
抽象した(周回 191)。 -/
theorem grade2CandidateAt_preceq_carrier_of_emits (hδ : 0 < s.e.delta) (hs : EventsSorted rho)
    (hnd : EventsNodup rho) {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat} {P : Block → Prop}
    (hcarrier : ∀ B : Block,
      Model.Consensus.Protocol.Grades.gradeBool s.e
          (Model.Consensus.Protocol.Grades.gradeView
            (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
              (Model.Consensus.Protocol.Grades.domainTime s.e s.hc
                (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
                Model.Consensus.Protocol.Grades.GradePhase.G2)) w).st.core))
          (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
            (Model.Consensus.Protocol.Grades.domainTime s.e s.hc
              (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
              Model.Consensus.Protocol.Grades.GradePhase.G2)) w).st.core).f s.hc.etaSG
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
          (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2)
          (Model.Consensus.Protocol.Grades.lateTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2) B = true →
      ∃ Y, P Y ∧ preceq B Y = true)
    {q : Block} (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    ∃ Y, P Y ∧ preceq q Y = true := by
  obtain ⟨b0, -, hgrade, hqb0⟩ := grade2CandidateAt_graded_of_emits c p a nr s rho hδ hs hnd hem h
  obtain ⟨Y, hY, hb0Y⟩ := hcarrier b0 hgrade
  exact ⟨Y, hY, Proofs.Consensus.Blocks.preceq_trans hqb0 hb0Y⟩

/-- **grade 2 の候補があれば、読みの時刻は 0 以上 horizon 以下**(Δ > 0、`ScheduleWellFormed`): 務めの grade 2 の候補があれば、
務めの round を `k` として `0 ≤ domainTime k G2 ≤ horizon`。`grade2CandidateAt_frozen_of_emits` の凍結した tick
`Tick w (domainTime k G2)` は run の event なので `Window.eventTime_bounds`。手書き `nodeQ2_preceq_honestWindowCarrier` の
`hdomainHor` に当たる(周回 193)。 -/
theorem grade2CandidateAt_domainTime_bounds_of_emits (hδ : 0 < s.e.delta) (hsch : ScheduleWellFormed s rho)
    {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat} {q : Block}
    (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    0 ≤ Model.Consensus.Protocol.Grades.domainTime s.e s.hc
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
        Model.Consensus.Protocol.Grades.GradePhase.G2 ∧
      Model.Consensus.Protocol.Grades.domainTime s.e s.hc
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
        Model.Consensus.Protocol.Grades.GradePhase.G2 ≤ rho.horizon := by
  obtain ⟨j, t2, b0, -, he, ht2, -⟩ := grade2CandidateAt_frozen_of_emits c p a nr s rho hδ hem h
  have hb := Proofs.Consensus.Window.eventTime_bounds hsch (List.mem_of_getElem? he)
  simp only [eventTime] at hb
  rw [← ht2]
  exact hb

/-- **行を出した tick の grade 2 の候補は、horizon 以内の grade の担い手の祖先**(Δ > 0、`ScheduleWellFormed` と重複なし):
`grade2CandidateAt_preceq_carrier_of_emits` の `hcarrier` に、手書きの `hgrade` の horizon の守り `domainTime k G2 ≤ horizon`
(と `0 ≤ domainTime k G2`)と、`B` が読みの grade view の tree にあることを前件として足した版。守りは
`grade2CandidateAt_domainTime_bounds_of_emits`、tree への所属は `grade2CandidateAt_graded_of_emits` が供給する。
手書き `nodeQ2_preceq_honestWindowCarrier` の全体に当たる(担い手は `P` に抽象したまま。周回 193)。 -/
theorem grade2CandidateAt_preceq_carrier_horizon_of_emits (hδ : 0 < s.e.delta) (hsch : ScheduleWellFormed s rho)
    (hnd : EventsNodup rho) {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat} {P : Block → Prop}
    (hcarrier :
      0 ≤ Model.Consensus.Protocol.Grades.domainTime s.e s.hc
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
          Model.Consensus.Protocol.Grades.GradePhase.G2 →
      Model.Consensus.Protocol.Grades.domainTime s.e s.hc
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
          Model.Consensus.Protocol.Grades.GradePhase.G2 ≤ rho.horizon →
      ∀ B : Block,
      B ∈ (Model.Consensus.Protocol.Grades.gradeView
            (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
              (Model.Consensus.Protocol.Grades.domainTime s.e s.hc
                (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
                Model.Consensus.Protocol.Grades.GradePhase.G2)) w).st.core)).tree.elems →
      Model.Consensus.Protocol.Grades.gradeBool s.e
          (Model.Consensus.Protocol.Grades.gradeView
            (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
              (Model.Consensus.Protocol.Grades.domainTime s.e s.hc
                (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
                Model.Consensus.Protocol.Grades.GradePhase.G2)) w).st.core))
          (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
            (Model.Consensus.Protocol.Grades.domainTime s.e s.hc
              (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
              Model.Consensus.Protocol.Grades.GradePhase.G2)) w).st.core).f s.hc.etaSG
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
          (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2)
          (Model.Consensus.Protocol.Grades.lateTime s.e s.hc
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
            Model.Consensus.Protocol.Grades.GradePhase.G2) B = true →
      ∃ Y, P Y ∧ preceq B Y = true)
    {q : Block} (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    ∃ Y, P Y ∧ preceq q Y = true := by
  obtain ⟨h0, hhor⟩ := grade2CandidateAt_domainTime_bounds_of_emits c p a nr s rho hδ hsch hem h
  obtain ⟨b0, hmem, hgrade, hqb0⟩ := grade2CandidateAt_graded_of_emits c p a nr s rho hδ
    (Proofs.Consensus.Window.eventsSorted_of_schedule hsch) hnd hem h
  obtain ⟨Y, hY, hb0Y⟩ := hcarrier h0 hhor b0 hmem hgrade
  exact ⟨Y, hY, Proofs.Consensus.Blocks.preceq_trans hqb0 hb0Y⟩

/-- **務めの SG 投票のブロック**: 添字 `i` の tick の務めの store で、務めの round の grade 2 の候補 `grade2CandidateAt` を
`aG2` に渡した `getSgVoteWith`。行を出した tick では行の `confirmed` はこの根(`emits_confirmed_sgBlockAt`)。手書き
`actionSGBlockAt` に当たる(手書きは round の添字で読み、ここは event の添字と時刻で読む。周回 194)。 -/
def sgBlockAt (w : ValidatorId) (i : Nat) (t : Int) : Block :=
  Model.Consensus.Protocol.Duties.Inputs.getSgVoteWith
    (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
      (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
      (worldAt (stateBefore c p a nr s rho i) w).cache)
    s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
    (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
    (grade2CandidateAt c p a nr s rho w i t)

/-- **発行した行の `confirmed` は務めの SG block の根**(前提なし): `w` が時刻 `t` に行 `row` を出したなら、添字 `i` の event
`Tick w t` があり、`row.confirmed = some (root (sgBlockAt w i t))` で、`row.round` は務めの store の slot の round。
`tick_attest_dutyStore` と `AttestationSource.attestWith_confirmed_round`。手書きの `actionAttestationAt` の
`confirmed` の欄に当たる(周回 194)。 -/
theorem emits_confirmed_sgBlockAt {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) :
    ∃ i : Nat, rho.events[i]? = some (NamedEvent.Tick w t) ∧
      row.confirmed = some (root (sgBlockAt c p a nr s rho w i t)) ∧
      row.round = Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s := by
  obtain ⟨i, hev, hrow⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho w _ t).mp hem
  rw [Proofs.Consensus.Signing.nodeTick_out] at hrow
  obtain ⟨-, -, hr⟩ := Proofs.Consensus.AttestationSource.tick_attest_dutyStore c p a nr _ s.hc _ _ _ t hrow
  subst hr
  exact ⟨i, hev, Proofs.Consensus.AttestationSource.attestWith_confirmed_round _ _ _ _ _ _⟩

/-- **窓の round の honest な行の SG block**: `Y` は、honest な `u` が添字 `i` の event `Tick u t` で出した行 `row`
(round は `latestWindow etaSG r` の中)の tick の務めの SG block。手書き `RelativeGradeCarrierAt` の結論
`∃ k ∈ latest_window η_SG r, ∃ u ∈ honest, emits u (attest (actionAttestationAt u k)) (a k) ∧ B ⪯ actionSGBlockAt u k` の
担い手に当たる(手書きは round `k` の action の行を `actionAttestationAt` で名指しし、ここは発行した行と event の添字で
名指しする。周回 194)。 -/
def HonestWindowCarrierAt (r : Nat) (Y : Block) : Prop :=
  ∃ (u : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), u ∈ rho.honest.elems ∧
    rho.events[i]? = some (NamedEvent.Tick u t) ∧ Emits c p a nr s rho u (NamedObject.Attest row) t ∧
    row.round ∈ latestWindow s.hc.etaSG r ∧ Y = sgBlockAt c p a nr s rho u i t

/-- **grade の担い手の性質**: round `r` の phase `ph` の domain 時刻の読みで、honest な `w` の store の `gradeBool` が真の
block `B` には、窓の round の honest な行の SG block `Y`(`HonestWindowCarrierAt r`)があって `B ⪯ Y`。手書き
`RelativeGradeCarrierAt`(`Protocol/Grades/RelativeOneChain.lean`)に当たる(周回 194)。窓は手書きの
`RelativeGradeCarrierAt` と同じく読みの round `r` 自身の `latestWindow etaSG r`。手書きの `RelativeCarrierWindowAt` は、
引数 `r` の round の担い手を `r + 1` の phase の読みで述べる(周回 194 の reviewer の所見 B。周回 195 / 196)。 -/
def RelativeGradeCarrierAt (r : Nat) (ph : Model.Consensus.Protocol.Grades.GradePhase) : Prop :=
  ∀ w ∈ rho.honest.elems, ∀ B : Block,
    Model.Consensus.Protocol.Grades.gradeBool s.e
        (Model.Consensus.Protocol.Grades.gradeView
          (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
            (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) w).st.core))
        (storeToHealing (worldAt (stateBeforeTime c p a nr s rho
          (Model.Consensus.Protocol.Grades.domainTime s.e s.hc r ph)) w).st.core).f s.hc.etaSG r
        (Model.Consensus.Protocol.Grades.earlyTime s.e s.hc r ph)
        (Model.Consensus.Protocol.Grades.lateTime s.e s.hc r ph) B = true →
      ∃ Y, HonestWindowCarrierAt c p a nr s rho r Y ∧ preceq B Y = true

/-- **行を出した honest な tick の grade 2 の候補は、窓の round の honest な行の SG block の祖先**(Δ > 0、
`ScheduleWellFormed` と重複なし): 務めの round を `k` として、horizon 以内の phase で `RelativeGradeCarrierAt k` が成り立てば
(`hgrade`)、務めの grade 2 の候補 `q` には `HonestWindowCarrierAt k` の `Y` があって `q ⪯ Y`。
`grade2CandidateAt_preceq_carrier_horizon_of_emits` の担い手 `P` を窓の SG block に置いた版で、手書き
`nodeQ2_preceq_honestWindowCarrier`(`Protocol/Grades/WeakBootstrapAction.lean`)と同じ前提の形(`hgrade` は phase ごとの
horizon の守りつき)。手書きの前提 `0 < r` は使わない(周回 194)。 -/
theorem grade2CandidateAt_preceq_honestWindowCarrier_of_emits (hδ : 0 < s.e.delta) (hsch : ScheduleWellFormed s rho)
    (hnd : EventsNodup rho) {w : ValidatorId} (hw : w ∈ rho.honest.elems) {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat}
    (hgrade : ∀ ph, Model.Consensus.Protocol.Grades.domainTime s.e s.hc
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) ph ≤ rho.horizon →
      RelativeGradeCarrierAt c p a nr s rho
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) ph)
    {q : Block} (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    ∃ Y, HonestWindowCarrierAt c p a nr s rho
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) Y ∧
      preceq q Y = true :=
  grade2CandidateAt_preceq_carrier_horizon_of_emits c p a nr s rho hδ hsch hnd hem
    (P := HonestWindowCarrierAt c p a nr s rho
      (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s))
    (fun _ hhor B _ hB => hgrade _ hhor w hw B hB) h

/-- **担い手の行の `confirmed` は担い手の根**(重複なし): `HonestWindowCarrierAt r Y` の行 `row` は、honest な `u` が時刻 `t` に
出した round が窓の中の行で、`row.confirmed = some (root Y)`、`row.round` は添字 `i` の tick の務めの round。
`HonestWindowCarrierAt` は添字 `i` と行を `events[i]? = Tick u t` でしか結ばないので、`emits_confirmed_sgBlockAt` の返す添字が
`i` と同じであることを `EventsNodup` で示す(周回 194 の reviewer の所見 A。周回 195)。 -/
theorem honestWindowCarrierAt_confirmed (hnd : EventsNodup rho) {r : Nat} {Y : Block}
    (h : HonestWindowCarrierAt c p a nr s rho r Y) :
    ∃ (u : ValidatorId) (i : Nat) (t : Int) (row : NamedAttestation), u ∈ rho.honest.elems ∧
      rho.events[i]? = some (NamedEvent.Tick u t) ∧ Emits c p a nr s rho u (NamedObject.Attest row) t ∧
      row.round ∈ latestWindow s.hc.etaSG r ∧ Y = sgBlockAt c p a nr s rho u i t ∧
      row.confirmed = some (root Y) ∧
      row.round = Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho u i t).core.s := by
  obtain ⟨u, i, t, row, hu, hev, hem, hwin, rfl⟩ := h
  obtain ⟨i', hev', hconf, hround⟩ := emits_confirmed_sgBlockAt c p a nr s rho hem
  have hil : i' < rho.events.length := (List.getElem?_eq_some_iff.mp hev').1
  have : i' = i := (List.Nodup.getElem?_inj hil
    (Proofs.Consensus.RecordGrowth.nodup_of_eventsNodup rho hnd)).mp (hev'.trans hev.symm)
  subst this
  exact ⟨u, i', t, row, hu, hev, hem, hwin, rfl, hconf, hround⟩

/-- **行を出した honest な tick の grade 2 の候補は、窓の round の honest な行の `confirmed` の祖先**(Δ > 0、
`ScheduleWellFormed` と重複なし): `grade2CandidateAt_preceq_honestWindowCarrier_of_emits` の担い手 `Y` を
`honestWindowCarrierAt_confirmed` で開き、honest な `u` が出した窓の round の行 `row2` で `row2.confirmed = some (root Y)` かつ
`q ⪯ Y` の形にした。手書き `nodeQ2_preceq_honestWindowCarrier` の結論を発行した行の `confirmed` で読む形(周回 195)。 -/
theorem grade2CandidateAt_preceq_windowConfirmed_of_emits (hδ : 0 < s.e.delta) (hsch : ScheduleWellFormed s rho)
    (hnd : EventsNodup rho) {w : ValidatorId} (hw : w ∈ rho.honest.elems) {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {i : Nat}
    (hgrade : ∀ ph, Model.Consensus.Protocol.Grades.domainTime s.e s.hc
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) ph ≤ rho.horizon →
      RelativeGradeCarrierAt c p a nr s rho
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) ph)
    {q : Block} (h : grade2CandidateAt c p a nr s rho w i t = some q) :
    ∃ (Y : Block) (u : ValidatorId) (t2 : Int) (row2 : NamedAttestation), u ∈ rho.honest.elems ∧
      Emits c p a nr s rho u (NamedObject.Attest row2) t2 ∧
      row2.round ∈ latestWindow s.hc.etaSG
        (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s) ∧
      row2.confirmed = some (root Y) ∧ preceq q Y = true := by
  obtain ⟨Y, hY, hqY⟩ :=
    grade2CandidateAt_preceq_honestWindowCarrier_of_emits c p a nr s rho hδ hsch hnd hw hem hgrade h
  obtain ⟨u, -, t2, row2, hu, -, hem2, hwin, -, hconf, -⟩ := honestWindowCarrierAt_confirmed c p a nr s rho hnd hY
  exact ⟨Y, u, t2, row2, hu, hem2, hwin, hconf, hqY⟩

end RunAtAction

end Proofs.Consensus.RootWitness
