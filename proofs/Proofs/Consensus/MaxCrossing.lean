import Proofs.Consensus.MaxCarrier
import Proofs.Consensus.JustificationCertificate
import Mathlib.Tactic

/-!
# 最大の高さの横断の honest な行(C77 の補題)

`AvailableHoles` の段の 2 つの穴に残る「band に届かない枝」(手書き `coreFrontierConfirmationWitness`、
`DecoupledConsensusProofs/Protocol/Schedule/WeakGoldfishCone.lean`)の 2 段目。手書き `coreFrontierQuorumWitness` に当たる:
読みの `hMax` が 1 より大きければ、`hMax` を導出の高さで担う bodies のブロック `W`(`MaxCarrier`)の導出は高さ `hMax - 1` を
通過しているので、`Derivation.Inv.crossing`(手書き `NamedFinalityCertificates.height_crossing`)から、`eraseBlock W` の祖先 `X` と
重み `q` 以上の署名者集合で各署名者に `W` の chain 上の `matchesEntry heightPair (hMax - 1) (root X)` の行があるものが取れる。
その定足数の honest な署名者(`JustificationCertificate.QuorumHonest`。手書き `HonestWeightMajority.exists_honest_member_of_quorum`)の
行は、読みの主がある時刻に処理した `W` の祖先 `Y` が運んだもので、`UnforgeableSignatures` の carried の半分から、その署名者が
処理より前に実際に出した行になる(手書き `NamedOutageProvenance.honest_held_ancestor_row_emission`)。
`JustificationCertificate.fgRoot_honestRow` → `stateBefore_fgRoot_honestEmission_before` → `stateBeforeTime_fgRoot_honestEmission_lt`
と同じ積み上げ。
-/

namespace Proofs.Consensus.MaxCrossing

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Weights Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.NamedBlocks Proofs.Consensus.Sets Proofs.Consensus.Derivation
open Proofs.Consensus.Carrier Proofs.Consensus.JustificationCertificate Proofs.Consensus.MaxCarrier

/-- **導出の高さの横断の honest な行**: `1 ≤ h < (deriveNamed C).h` なら、`eraseBlock C` の祖先 `X` と、`C` の名前付き祖先 `Y` の
行で `H` の署名者の `matchesEntry heightPair h (root X)` のものがある。手書き `height_crossing` と
`exists_honest_member_of_quorum` を合わせた形。 -/
theorem crossing_honestRow (e : ProtocolEnv) (cfg : HeightConfig) {H : VSet} (hqh : QuorumHonest e H)
    (C : NamedBlock) {h : Nat} (h1 : 1 ≤ h) (h2 : h < (deriveNamed e cfg C).h) :
    ∃ X Y row, preceq X (eraseBlock C) = true ∧ namedPreceq Y C = true ∧ row ∈ namedAttestations Y ∧
      row.valIndex ∈ H.elems ∧ matchesEntry row.heightPair h (root X) = true := by
  obtain ⟨X, hX, Q, hQs, hQq, hrows⟩ := (deriveNamed_inv e cfg C).crossing h h1 h2
  obtain ⟨i, hiQ, hiH⟩ := hqh Q hQs hQq
  obtain ⟨row, ⟨Y, hY, hrow⟩, hvi, hm⟩ := hrows i hiQ
  exact ⟨X, Y, row, hX, hY, hrow, hvi ▸ hiH, hm⟩

/-- store の版: `1 < hMax` なら、bodies の `W`(導出の高さが `hMax`)と、`eraseBlock W` の祖先 `X`、bodies にある `W` の祖先 `Y`
の行で `H` の署名者の `matchesEntry heightPair (hMax - 1) (root X)` のものがある。 -/
theorem maxCrossing_honestRow {e : ProtocolEnv} {cfg : HeightConfig} {st : NamedStore} (h : StoreInv e cfg st)
    (hm : MCarrier e cfg st) {H : VSet} (hqh : QuorumHonest e H) (hlarge : 1 < st.core.hMax) :
    ∃ W X Y row, W ∈ st.bodies.elems ∧ (deriveNamed e cfg W).h = st.core.hMax ∧
      preceq X (eraseBlock W) = true ∧ Y ∈ st.bodies.elems ∧ namedPreceq Y W = true ∧
      row ∈ namedAttestations Y ∧ row.valIndex ∈ H.elems ∧
      matchesEntry row.heightPair (st.core.hMax - 1) (root X) = true := by
  obtain ⟨W, hW, hWh⟩ := hm
  obtain ⟨X, Y, row, hX, hY, hrow, hH, hmatch⟩ :=
    crossing_honestRow e cfg hqh W (h := st.core.hMax - 1) (by omega) (by omega)
  exact ⟨W, X, Y, row, hW, hWh, hX, Proofs.Consensus.Attribution.ancestor_mem_bodies h.closed hW hY, hY, hrow, hH, hmatch⟩

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 添字 `i` の直前のノード `v` の `hMax` が 1 より大きければ、bodies の `W`(導出の高さが `hMax`)と `eraseBlock W` の祖先 `X` が
あり、`v` が添字 `j < i` の event(時刻 `t`)で処理した `W` の祖先 `Y` が honest な署名者の行(`matchesEntry heightPair
(hMax - 1) (root X)`)を運び、その署名者は時刻 `t` 以前にその行を実際に出した。 -/
theorem stateBefore_maxCrossing_honestEmission_before (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (i : Nat) (v : ValidatorId) (hlarge : 1 < (worldAt (stateBefore c p a nr s rho i) v).st.core.hMax) :
    ∃ W X Y row j ev t t2, W ∈ (worldAt (stateBefore c p a nr s rho i) v).st.bodies.elems ∧
      (deriveNamed s.e s.cfg W).h = (worldAt (stateBefore c p a nr s rho i) v).st.core.hMax ∧
      preceq X (eraseBlock W) = true ∧ namedPreceq Y W = true ∧ row ∈ namedAttestations Y ∧
      row.valIndex ∈ rho.honest.elems ∧
      matchesEntry row.heightPair ((worldAt (stateBefore c p a nr s rho i) v).st.core.hMax - 1) (root X) = true ∧
      j < i ∧ rho.events[j]? = some ev ∧ eventTime ev = t ∧
      Processes c p a nr s rho v (NamedObject.Block Y) t ∧ t2 ≤ t ∧
      Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 := by
  obtain ⟨W, X, Y, row, hW, hWh, hX, hYb, hY, hrow, hH, hmatch⟩ :=
    maxCrossing_honestRow (stateBefore_inv c p a nr s rho i v) (stateBefore_mcarrier c p a nr s rho i v) hqh hlarge
  rcases bodies_processed_before c p a nr s rho v i Y hYb with rfl | ⟨j, ev, t, hj, hev, het, hproc⟩
  · simp [namedAttestations] at hrow
  · have hhon : rho.honest.contains row.valIndex = true := (contains_iff_mem vid_eq _ _).mpr hH
    obtain ⟨t2, ht2, hem⟩ := hcar v (NamedObject.Block Y) t hproc (NamedObject.Attest row)
      (Proofs.Consensus.Attribution.carries_attest hrow) row.valIndex ⟨hhon, rfl⟩
    exact ⟨W, X, Y, row, j, ev, t, t2, hW, hWh, hX, hY, hrow, hH, hmatch, hj, hev, het, hproc, ht2, hem⟩

/-- **時刻 `< time` の読みの最大の高さの横断の honest な発行**(手書き `coreFrontierQuorumWitness`): 読みの `hMax` が 1 より
大きければ、bodies の `W`(導出の高さが `hMax`)と `eraseBlock W` の祖先 `X` があり、honest な署名者が時刻 `< time` に
`matchesEntry heightPair (hMax - 1) (root X)` の行を実際に出していて、その行は `v` が時刻 `< time` に処理した `W` の祖先 `Y`
に載っている。 -/
theorem stateBeforeTime_maxCrossing_honestEmission_lt (hs : EventsSorted rho) (hqh : QuorumHonest s.e rho.honest)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (v : ValidatorId) (time : Int)
    (hlarge : 1 < (worldAt (stateBeforeTime c p a nr s rho time) v).st.core.hMax) :
    ∃ W X Y row t t2, W ∈ (worldAt (stateBeforeTime c p a nr s rho time) v).st.bodies.elems ∧
      (deriveNamed s.e s.cfg W).h = (worldAt (stateBeforeTime c p a nr s rho time) v).st.core.hMax ∧
      preceq X (eraseBlock W) = true ∧ namedPreceq Y W = true ∧ row ∈ namedAttestations Y ∧
      row.valIndex ∈ rho.honest.elems ∧
      matchesEntry row.heightPair ((worldAt (stateBeforeTime c p a nr s rho time) v).st.core.hMax - 1) (root X) = true ∧
      Processes c p a nr s rho v (NamedObject.Block Y) t ∧ t < time ∧ t2 ≤ t ∧ t2 < time ∧
      Emits c p a nr s rho row.valIndex (NamedObject.Attest row) t2 := by
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs time] at hlarge ⊢
  obtain ⟨W, X, Y, row, j, ev, t, t2, hW, hWh, hX, hY, hrow, hH, hmatch, hj, hev, het, hproc, ht2, hem⟩ :=
    stateBefore_maxCrossing_honestEmission_before c p a nr s rho hqh hcar _ v hlarge
  have htime : t < time := het ▸ time_lt_of_lt_idxLt rho hs hj hev
  exact ⟨W, X, Y, row, t, t2, hW, hWh, hX, hY, hrow, hH, hmatch, hproc, htime, ht2, lt_of_le_of_lt ht2 htime, hem⟩

end Run

end Proofs.Consensus.MaxCrossing
