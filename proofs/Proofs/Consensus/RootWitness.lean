import Proofs.Consensus.RootEntry
import Proofs.Consensus.FinalizedAccountable
import Mathlib.Tactic

/-!
# FG root の名前付きブロックは、honest な署名者の同じ高さの入口(C71 の補題)

`RootEntry.stateBeforeTime_fgRoot_honestEntry` は、時刻 `< time` の読みの FG root が genesis でなければ、読みの bodies の `D`
(導出の `j` が FG root)と、honest な署名者 `w` の bodies の入口の checkpoint `K`(導出の `h` が `D` の導出の `hJ`、
`tH` が `K` の消去、根が FG root の根)を返す。ここでは次の 2 段を足す。

1. 読みの主 `v` の bodies に、消去が FG root の名前付きブロック `J` がある(`D` の導出の `j` は `D` の消去の祖先なので、
   `erased_ancestor_lift` で `D` の名前付きの祖先 `J` に持ち上げ、bodies は祖先について閉じる。`stateBeforeTime_fgRoot_named`)。
2. `NamedRootCollisionFree` の下で `v` が honest なら `J = K`(`J` も `K` も honest なノードの `stateBefore` の bodies にあるので
   run の中のブロックで、`namedRoot` が等しい)。したがって FG root の名前付きブロック `J` は署名者 `w` の bodies にもあり、
   `J` の導出の `h` は `D` の導出の `hJ`、`tH` は `J` の消去、`J` は `w` の務めの FG source の名前付きブロック `D'` の祖先
   (`stateBeforeTime_fgRoot_entryWitness`)。

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
    ⟨D, row, nu, t2, i, cache, st3, q, D', K, hD, hDj, hH, hrow, ht2, hem, hev, hcache, hinv, hbod, hq, hqt,
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
      ⟨cache, st3, hcache, hinv, hbod, hq, hqt⟩, hK, hKD', hKh, hKt, hD'h, hKe.symm.trans hJe'⟩

end Run

end Proofs.Consensus.RootWitness
