import Proofs.Consensus.RootEntry
import Proofs.Consensus.FinalizedAccountable
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

/-- **round の同時帰納で行ごとの性質 `Q` と FG root・確認の証人を運ぶ**(Δ > 0、`0 < R`、`EventsSorted` と重複なし、
`QuorumHonest` / `hcar` / `NamedRootCollisionFree`、`base ≤ cut`): round `base` 以上の行を時刻 `< limit` に出した honest な
tick について、
- `hbootstrap`: round `base` 以上 `cut` 未満の行の tick は `Q` を満たす。
- `hlegacy`: round `cut` 以上の行の tick で、round `< cut` の古い行の証人が務めの FG root `R` なら `R ⪯ X`。
- `hstep`: round `cut` 以上の行 `row` の tick で、前の round の仮定(round `base` 以上 `row.round` 未満の行の tick はどれも
  `Q` を満たし、round `cut` 以上 `row.round` 未満の行の tick の FG root と確認の証人はどれも `X` の祖先)の下で、自分の務めの
  FG root も `X` の祖先なら、自分も `Q` を満たし確認の証人も `X` の祖先。

これらから、その tick は `Q` を満たし、round が `cut` 以上なら務めの FG root と確認の証人はどれも `X` の祖先。
手書き `actionSources_preceq_of_priorConfirmations_and_historyCut`(`Protocol/Grades/WeakBootstrapAction.lean`)の
round の強い帰納の骨組みの 2 つの連言に当たる。`Q` を手書きの第 1 連言(行の tick の SG block ⪯ X)に置くと、手書きの段
`hsg`(round `base` 以上 `r` 未満の行の SG block)は `hstep` の第 1 の仮定として届く。段 `hroots` は
`dutyStoreAt_fgRoot_preceq_of_recent_and_legacy` に `cutTime := actionTime cut` を置き、時刻の境を
`emits_attest_time_lt_actionTime_iff` で round の境に移して帰納法の仮定から供給する。`hstep` の中身(SG block と確認の証人を
grade と clear から押さえる段)は含まない(周回 180)。 -/
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
    have hroot : preceq (getFgRoot (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)) X = true := by
      refine dutyStoreAt_fgRoot_preceq_of_recent_and_legacy c p a nr s rho hδ hs hnd hqh hcar hcf hw hem hi
        (cutTime := Model.Consensus.Protocol.Grades.actionTime s.hc s.e.delta cut) ?_ ?_
      · intro w2 i2 t2 hct2 ht2 hw2 hi2 row2 hrow2 hem2 T hT
        subst hrow2
        have hcut2 : cut ≤ row2.round :=
          le_of_not_gt fun h => absurd ((emits_attest_time_lt_actionTime_iff c p a nr s rho hδ hr hem2 cut).mpr h)
            (not_lt_of_ge hct2)
        have hlt : row2.round < row.round := by
          rw [emits_attest_actionTime_round c p a nr s rho hem2, emits_attest_actionTime_round c p a nr s rho hem]
            at ht2
          exact (actionTime_lt_actionTime_iff hδ hr row2.round row.round).mp ht2
        exact (hprev row2.valIndex i2 t2 row2 hw2 hi2 hem2 hcut2 hlt).2 T hT
      · intro D row2 nu t2 i2 hD hDj hH hrow ht2 hct2 hem2 hev hT
        exact hlegacy w i t row hw hi hem hlim hcut D row2 nu t2 i2 hD hDj hH hrow ht2
          ((emits_attest_time_lt_actionTime_iff c p a nr s rho hδ hr hem2 cut).mp hct2) hem2 hev hT
    obtain ⟨hq, hwit⟩ := hstep w i t row hw hi hem hlim hcut hprevQ hprev hroot
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
  intro w i t row hw hi hem hlim hcut _ hprev hroot
  exact ⟨trivial, hstep w i t row hw hi hem hlim hcut hprev hroot⟩

end RunAtAction

end Proofs.Consensus.RootWitness
