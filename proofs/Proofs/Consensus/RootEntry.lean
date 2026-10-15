import Proofs.Consensus.EntryHeight
import Proofs.Consensus.JustificationCertificate
import Proofs.Consensus.AttestationSource
import Mathlib.Tactic

/-!
# FG root の honest な行と、署名者の入口の checkpoint(C71 の補題)

`JustificationCertificate.stateBeforeTime_fgRoot_honestEmission_lt` は、時刻 `< time` の読みの FG root が genesis でなければ、
honest な署名者 `w` が時刻 `t2 < time` に出した行 `row` を返す。行は `matchesEntry heightPair hJ (root FG root)` なので
height pair は `Vote hJ (root FG root) nu`。`AttestationSource.emits_vote_source` をその発行に掛けると、`w` の tick の中の store の
FG source の chain 状態の `(h, root tH)` が `(hJ, root FG root)` で、tick の後の `w` の bodies に `eraseBlock D' = q`、
`(deriveNamed D').h = hJ`、`root (deriveNamed D').tH = root FG root` の `D'` がある。さらに `EntryHeight.entry_ancestor_same_height`
を `D'`(`w` の務めの FG source `q` の名前付きブロック。`eraseBlock D' = q`)に掛けると、`D'` の祖先 `K`(bodies は祖先について閉じるので、やはり `w` の bodies にある)があって、`K` の消去は
`D'` の導出の `tH` で、`K` の導出の `h` は `hJ`。したがって `K` の根は FG root の根(`stateBeforeTime_fgRoot_honestEntry`)。

手書きでは `HealingSurface.processedJustification_confirmationWitness`(`Protocol/ChainState/FGRootWitness.lean`)の、honest な
署名者の行を務めの FG source に結び、同じ高さの入口の checkpoint を取るところに当たる。
-/

namespace Proofs.Consensus.RootEntry

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.JustificationCertificate Proofs.Consensus.Carrier

/-- `matchesEntry p h r` なら `p = Vote h r nu`。 -/
theorem matchesEntry_vote {p : NamedHeightPair} {h : Nat} {r : BlockId} (hm : matchesEntry p h r = true) :
    ∃ nu, p = NamedHeightPair.Vote h r nu := by
  cases p with
  | Empty => simp [matchesEntry] at hm
  | Vote h' r' nu =>
    simp only [matchesEntry, Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨nu, rfl⟩

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **時刻 `< time` の読みの FG root は genesis か、次の形**: 読みの bodies の `D` の導出の `j` が FG root で、honest な署名者 `w` が
時刻 `t2 < time` に行 `row`(height pair `Vote hJ (root FG root) nu`、`hJ` は `D` の導出の `hJ`)を出しており、その発行は添字 `i` の
event `Tick w t2` で、その tick の中の store `st3`(`cache` は tick の `onPhaseTick` の cache)の務めの FG source `q` は `st3` の tree にあり、
`stateBefore (i + 1)` の `w` の bodies(= `st3` の bodies)に `eraseBlock D' = q` の `D'` がある。`D'` の導出の `(h, root tH)` は
`(hJ, root FG root)` で、`D'` の祖先 `K`(やはり `w` の bodies にある)の消去は `D'` の導出の `tH`、`K` の導出の `h` は `hJ`。
最後の 3 つの連言(`K` の導出の `h`、`K` の導出の `tH` が `K` の消去、`K` の根)は前の連言と `entry_eq_on_plateau` から出るが、
次の層で使う形として足しておく。前提は `stateBeforeTime_fgRoot_honestEmission_lt` と同じ。 -/
theorem stateBeforeTime_fgRoot_honestEntry (hs : EventsSorted rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (v : ValidatorId) (time : Int) :
    getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core) = Block.Genesis ∨
      ∃ (D : NamedBlock) (row : NamedAttestation) (nu : Bool) (t2 : Int) (i : Nat)
        (cache : Model.Consensus.Protocol.Grades.Cache) (st3 : NamedStore) (q : Block) (D' K : NamedBlock),
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
        D' ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) row.valIndex).st.bodies.elems ∧ eraseBlock D' = q ∧
        (deriveNamed s.e s.cfg D').h = (deriveNamed s.e s.cfg D).hJ ∧
        root (deriveNamed s.e s.cfg D').tH =
          root (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core)) ∧
        K ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) row.valIndex).st.bodies.elems ∧
        namedPreceq K D' = true ∧ eraseBlock K = (deriveNamed s.e s.cfg D').tH ∧
        (deriveNamed s.e s.cfg K).h = (deriveNamed s.e s.cfg D).hJ ∧
        (deriveNamed s.e s.cfg K).tH = eraseBlock K ∧
        root (eraseBlock K) =
          root (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho time) v).st.core)) := by
  rcases stateBeforeTime_fgRoot_honestEmission_lt c p a nr s rho hs hqh hcar v time with hg |
    ⟨D, X, row, t, t2, hD, hDj, -, -, hH, hm, -, -, -, ht2, hem⟩
  · exact Or.inl hg
  · right
    obtain ⟨nu, hv⟩ := matchesEntry_vote hm
    obtain ⟨i, cache, st3, q, hev, hcache, hd, hinv, -, hbod, -, hq, -, -, hqt, D', hD', hD'q, hD'h, hD'e⟩ :=
      Proofs.Consensus.AttestationSource.emits_vote_source c p a nr s rho hem hv
    obtain ⟨K, hKD, hKe, hKh⟩ := Proofs.Consensus.EntryHeight.entry_ancestor_same_height s.e s.cfg D'
    have hK : K ∈ (worldAt (stateBefore c p a nr s rho (i + 1)) row.valIndex).st.bodies.elems :=
      Proofs.Consensus.Attribution.ancestor_mem_bodies
        (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho (i + 1) row.valIndex).closed hD' hKD
    have hKt : (deriveNamed s.e s.cfg K).tH = eraseBlock K :=
      (Proofs.Consensus.EntryHeight.entry_eq_on_plateau s.e s.cfg hKD hKh).trans hKe.symm
    exact ⟨D, row, nu, t2, i, cache, st3, q, D', K, hD, hDj, hH, hv, ht2, hem, hev, hcache, hd, hinv, hbod, hq, hqt,
      hD', hD'q, hD'h, hD'e, hK, hKD, hKe, hKh.trans hD'h, hKt, by rw [hKe]; exact hD'e⟩

end Run

end Proofs.Consensus.RootEntry
