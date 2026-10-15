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
`w` の store と tick の `onPhaseTick` の cache を渡したもの)。手書きの `actionStoreAt` に当たる(周回 171)。 -/
def dutyStoreAt (w : ValidatorId) (i : Nat) (t : Int) : NamedStore :=
  Proofs.Consensus.AttestationSource.tickDutyStore c p nr
    (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
      (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t (worldAt (stateBefore c p a nr s rho i) w).cache)
    s.e s.hc s.cfg (Model.Consensus.Execution.Setup.setupNode w) (worldAt (stateBefore c p a nr s rho i) w).st t

/-- 務めの FG source の chain 状態の `tH`(source が無ければ `none`)。手書き `fgConfirmationWitness`
(`Internal/Definitions/ActionSources.lean`)の `(actionFGSource S n).map (fun Cfg => (n.st.core.σ Cfg).T_h)` に当たる(周回 171)。 -/
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

end Run

end Proofs.Consensus.RootWitness
