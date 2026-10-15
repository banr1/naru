import Proofs.Consensus.JustifiedCarrier
import Proofs.Consensus.Attribution
import Mathlib.Tactic

/-!
# finalized の分岐を justified な祖先の `j` に言い換える(C71 の補題)

`JustifiedCarrier.fgRoot_source` は FG root を bodies のどれかの導出の `j` か `f` として返す。ここでは `f` の分岐を言い換え、
FG root を常に bodies のどれかの導出の `j` にする。手書き `HealingSurface.fgRoot_justificationSource_at_read`
(`Protocol/ChainState/FGRootWitness.lean`)の形で、手書きの private な `derive_named_F_node_cases` /
`named_finalized_justificationAncestor` に当たる。

- **導出の 1 段**: `foldRows` は `j` / `hJ` / `f` / `hF` を変えない(`foldRows_fields`。`processAttestation` は署名者の集合だけを
  書く)。`processHeightEvents` が `f` / `hF` を書くのは finality の分岐の `f := j`、`hF := hJ` だけ(`processHeightEvents_f`)。
  したがって子の導出の `(f, hF)` は、親の導出の `(j, hJ)` か親の導出の `(f, hF)`(`deriveNamed_f_node`)。
- **justified な祖先**: `C` の構造帰納法で、どの `C` にも名前付きの祖先 `D` があって、`D` の導出の `(j, hJ)` は `C` の導出の
  `(f, hF)` に等しい(`finalized_justificationAncestor`。genesis は自分)。
- **FG root**: `StoreInv.closed`(bodies は親について閉じる)から祖先も bodies にある(`Attribution.ancestor_mem_bodies`)ので、
  store の FG root は bodies のどれかの `D` の導出の `j`(`fgRoot_justified`)。`D` の消去は tree にあり、FG root はその祖先
  (`fgRoot_justified_preceq`)。run のどの読み(`stateBefore` / `storeAt` / `stateBeforeTime`)でも前提なしに成り立つ。
-/

namespace Proofs.Consensus.FinalizedSource

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.NamedBlocks Proofs.Consensus.Carrier Proofs.Consensus.JustifiedCarrier

/-! ## 導出の 1 段 -/

/-- 行の畳み込みは `j` / `hJ` / `f` / `hF` を変えない。 -/
theorem foldAttest_fields : ∀ (rows : List NamedAttestation) (st : ChainState),
    (rows.foldl processAttestationWith st).j = st.j ∧ (rows.foldl processAttestationWith st).hJ = st.hJ ∧
    (rows.foldl processAttestationWith st).f = st.f ∧ (rows.foldl processAttestationWith st).hF = st.hF
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | row :: rows, st => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := foldAttest_fields rows (processAttestationWith st row)
    obtain ⟨-, -, hj, hhJ, hf, hhF⟩ := Proofs.Consensus.Derivation.pa_fields st (targetedView st row)
    exact ⟨h1.trans hj, h2.trans hhJ, h3.trans hf, h4.trans hhF⟩

/-- `foldRows` は `j` / `hJ` / `f` / `hF` を変えない。 -/
theorem foldRows_fields (st : ChainState) (geom : Block) (rows : List NamedAttestation) :
    (foldRows st geom rows).j = st.j ∧ (foldRows st geom rows).hJ = st.hJ ∧
    (foldRows st geom rows).f = st.f ∧ (foldRows st geom rows).hF = st.hF :=
  foldAttest_fields rows { st with s := slot geom }

/-- `processHeightEvents` の後の `(f, hF)` は、前の `(j, hJ)` か前の `(f, hF)`。 -/
theorem processHeightEvents_f (e : ProtocolEnv) (cfg : HeightConfig) (st : ChainState) :
    ((processHeightEvents e cfg st).f = st.j ∧ (processHeightEvents e cfg st).hF = st.hJ) ∨
    ((processHeightEvents e cfg st).f = st.f ∧ (processHeightEvents e cfg st).hF = st.hF) := by
  unfold processHeightEvents advanceHeight
  dsimp only
  split_ifs <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

/-- 子の導出の `(f, hF)` は、親の導出の `(j, hJ)` か親の導出の `(f, hF)`。手書き `derive_named_F_node_cases`。 -/
theorem deriveNamed_f_node (e : ProtocolEnv) (cfg : HeightConfig) (p : NamedBlock) (s : Nat) (r : BlockId)
    (v sup : List GoldfishVote) (rows : List NamedAttestation) (i : ValidatorId) :
    ((deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).f = (deriveNamed e cfg p).j ∧
      (deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).hF = (deriveNamed e cfg p).hJ) ∨
    ((deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).f = (deriveNamed e cfg p).f ∧
      (deriveNamed e cfg (NamedBlock.Node p s r v sup rows i)).hF = (deriveNamed e cfg p).hF) := by
  simp only [deriveNamed]
  unfold namedTransition transitionRows
  obtain ⟨hj, hhJ, hf, hhF⟩ := foldRows_fields (deriveNamed e cfg p)
    (eraseBlock (NamedBlock.Node p s r v sup rows i)) (namedAttestations (NamedBlock.Node p s r v sup rows i))
  rcases processHeightEvents_f e cfg (foldRows (deriveNamed e cfg p)
      (eraseBlock (NamedBlock.Node p s r v sup rows i)) (namedAttestations (NamedBlock.Node p s r v sup rows i))) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.trans hj, h2.trans hhJ⟩
  · exact Or.inr ⟨h1.trans hf, h2.trans hhF⟩

/-- どの `C` にも名前付きの祖先 `D` があって、`D` の導出の `(j, hJ)` は `C` の導出の `(f, hF)`。
手書き `named_finalized_justificationAncestor`(高さの等式は手書きに無い)。 -/
theorem finalized_justificationAncestor (e : ProtocolEnv) (cfg : HeightConfig) : ∀ C : NamedBlock,
    ∃ D : NamedBlock, namedPreceq D C = true ∧
      (deriveNamed e cfg D).j = (deriveNamed e cfg C).f ∧ (deriveNamed e cfg D).hJ = (deriveNamed e cfg C).hF
  | NamedBlock.Genesis => ⟨NamedBlock.Genesis, namedPreceq_self _, rfl, rfl⟩
  | NamedBlock.Node p s r v sup rows i => by
    rcases deriveNamed_f_node e cfg p s r v sup rows i with ⟨hf, hh⟩ | ⟨hf, hh⟩
    · exact ⟨p, namedPreceq_node (namedPreceq_self p) s r v sup rows i, hf.symm, hh.symm⟩
    · obtain ⟨D, hD, hDj, hDh⟩ := finalized_justificationAncestor e cfg p
      exact ⟨D, namedPreceq_node hD s r v sup rows i, hDj.trans hf.symm, hDh.trans hh.symm⟩

/-! ## FG root -/

/-- store の FG root は bodies のどれかの導出の `j`。手書き `fgRoot_justificationSource_at_read` の store の版。 -/
theorem fgRoot_justified {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : StoreInv e cfg st)
    (hj : JCarrier e cfg st) :
    ∃ D, D ∈ st.bodies.elems ∧ (deriveNamed e cfg D).j = getFgRoot (storeToHealing st.core) := by
  rcases fgRoot_eq st.core with hr | hr
  · obtain ⟨D, hD, hDj, -⟩ := hj
    exact ⟨D, hD, hDj.trans hr.symm⟩
  · obtain ⟨D, hD, hDf⟩ := h.carrier
    obtain ⟨D', hD', hD'j, -⟩ := finalized_justificationAncestor e cfg D
    exact ⟨D', Proofs.Consensus.Attribution.ancestor_mem_bodies h.closed hD hD',
      hD'j.trans (hDf.trans hr.symm)⟩

/-- store の FG root は、bodies のどれかの `D` の導出の `j` で、`D` の消去は tree にあり FG root はその祖先。 -/
theorem fgRoot_justified_preceq {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : StoreInv e cfg st)
    (hj : JCarrier e cfg st) :
    ∃ D, D ∈ st.bodies.elems ∧ eraseBlock D ∈ st.core.tree.elems ∧
      (deriveNamed e cfg D).j = getFgRoot (storeToHealing st.core) ∧
      preceq (getFgRoot (storeToHealing st.core)) (eraseBlock D) = true := by
  obtain ⟨D, hD, hDj⟩ := fgRoot_justified h hj
  refine ⟨D, hD, h.tree D hD, hDj, ?_⟩
  rw [← hDj]
  exact (Proofs.Consensus.Derivation.deriveNamed_inv e cfg D).j_preceq

section RunRoot

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字 `i` の直前のノード `v` の FG root は、その bodies のどれかの導出の `j`(前提なし)。 -/
theorem stateBefore_fgRoot_justified (i : Nat) (v : ValidatorId) :
    ∃ D, D ∈ (worldAt (stateBefore c p a nr s rho i) v).st.bodies.elems ∧
      (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core) :=
  fgRoot_justified (stateBefore_inv c p a nr s rho i v) (stateBefore_jcarrier c p a nr s rho i v)

/-- 時刻 `t` の読みの FG root は、その bodies のどれかの導出の `j`(前提なし)。 -/
theorem storeAt_fgRoot_justified (v : ValidatorId) (t : Int) :
    ∃ D, D ∈ (storeAt c p a nr s rho v t).bodies.elems ∧
      (deriveNamed s.e s.cfg D).j = getFgRoot (storeToHealing (storeAt c p a nr s rho v t).core) :=
  fgRoot_justified (readAt_inv c p a nr s rho t v) (readAt_jcarrier c p a nr s rho t v)

/-- 時刻 `< t` の読みの FG root は、その bodies のどれかの導出の `j`(前提なし)。
手書き `fgRoot_justificationSource_at_read` に当たる(手書きは `AdmissibleCore` を仮定する)。 -/
theorem stateBeforeTime_fgRoot_justified (v : ValidatorId) (t : Int) :
    ∃ D, D ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.bodies.elems ∧
      (deriveNamed s.e s.cfg D).j =
        getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho t) v).st.core) :=
  fgRoot_justified (stateBeforeTime_inv c p a nr s rho t v) (stateBeforeTime_jcarrier c p a nr s rho t v)

/-- 時刻 `< t` の読みの FG root は、その bodies のどれかの `D` の導出の `j` で、`D` の消去は tree にありその祖先(前提なし)。 -/
theorem stateBeforeTime_fgRoot_justified_preceq (v : ValidatorId) (t : Int) :
    ∃ D, D ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.bodies.elems ∧
      eraseBlock D ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.core.tree.elems ∧
      (deriveNamed s.e s.cfg D).j =
        getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho t) v).st.core) ∧
      preceq (getFgRoot (storeToHealing (worldAt (stateBeforeTime c p a nr s rho t) v).st.core))
        (eraseBlock D) = true :=
  fgRoot_justified_preceq (stateBeforeTime_inv c p a nr s rho t v) (stateBeforeTime_jcarrier c p a nr s rho t v)

end RunRoot

end Proofs.Consensus.FinalizedSource
