import Proofs.Consensus.RootWitness
import Mathlib.Tactic

/-!
# 発行した高さの行の務めの確認の証人(C77 の補題)

`AvailableHoles` の段の 2 つの穴に残る「band に届かない枝」(手書き `coreFrontierConfirmationWitness`、
`DecoupledConsensusProofs/Protocol/Schedule/WeakGoldfishCone.lean`)の 3 段目。手書き `coreHonestHeightRowConfirmationWitness` に当たる:
`w` が時刻 `t` に height pair `Vote h entry nu` の行を出したなら、その tick(添字 `i`)の務めの store `dutyStoreAt w i t` の bodies に、
消去が務めの FG source の `D`(導出の高さ `h`)と、消去が `D` の導出の `tH` の `D` の祖先 `K`(導出の高さ `h`、`tH` は `K` の消去、
根は `entry`)があり、務めの確認の証人 `fgConfirmationWitnessAt w i t` は `K` の消去。

材料は `AttestationSource.emits_vote_source`(行の発行 → tick の中の store の FG source `q` の chain 状態の `(h, root tH)`)、
`AttestationSource.source_named`(`q` の名前付きブロック `D`)、`EntryHeight.entry_ancestor_same_height`(手書き
`coreActionNamedCheckpoint` の `K`)と `EntryHeight.entry_eq_on_plateau`。手書きは `K` を honest な務めの bodies の run の中のブロック
から取るが、ここは bodies が祖先について閉じること(`StoreInv.closed`)で足り、署名者が honest である前提は要らない。
-/

namespace Proofs.Consensus.HeightRowWitness

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution
open Proofs.Consensus.Carrier Proofs.Consensus.RootWitness

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **発行した高さの行の務めの確認の証人**(手書き `coreHonestHeightRowConfirmationWitness`): `w` が時刻 `t` に height pair
`Vote h entry nu` の行 `row` を出したなら、添字 `i` の event `Tick w t` の務めの store `dutyStoreAt w i t` の bodies に、
消去が務めの FG source の `D`(導出の高さ `h`)と、`D` の祖先 `K`(消去は `D` の導出の `tH`、導出の高さ `h`、導出の `tH` は
`K` の消去、根は `entry`)があり、務めの確認の証人は `K` の消去。`stateBefore (i + 1)` の `w` の bodies は務めの store の bodies
(`attestWith` は bodies を変えない。周回 288)。 -/
theorem emits_vote_confirmationWitness {w : ValidatorId} {row : NamedAttestation} {t : Int}
    (hem : Emits c p a nr s rho w (NamedObject.Attest row) t) {h : Nat} {entry : BlockId} {nu : Bool}
    (hv : row.heightPair = NamedHeightPair.Vote h entry nu) :
    ∃ (i : Nat) (D K : NamedBlock), rho.events[i]? = some (NamedEvent.Tick w t) ∧
      fgConfirmationWitnessAt c p a nr s rho w i t = some (eraseBlock K) ∧
      D ∈ (dutyStoreAt c p a nr s rho w i t).bodies.elems ∧
      Model.Consensus.Protocol.Duties.Inputs.fgSourceWith
          (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
            (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
            (worldAt (stateBefore c p a nr s rho i) w).cache)
          s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
          (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)
          (Model.Consensus.Protocol.Duties.Inputs.grade2BlockWith
            (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc
              (storeToHealing (worldAt (stateBefore c p a nr s rho i) w).st.core) t
              (worldAt (stateBefore c p a nr s rho i) w).cache)
            s.e s.hc (storeToHealing (dutyStoreAt c p a nr s rho w i t).core)
            (Model.Consensus.Protocol.Grades.roundOf s.hc (dutyStoreAt c p a nr s rho w i t).core.s)) =
        some (eraseBlock D) ∧
      (deriveNamed s.e s.cfg D).h = h ∧
      K ∈ (dutyStoreAt c p a nr s rho w i t).bodies.elems ∧
      eraseBlock K = (deriveNamed s.e s.cfg D).tH ∧ (deriveNamed s.e s.cfg K).h = h ∧
      (deriveNamed s.e s.cfg K).tH = eraseBlock K ∧ namedPreceq K D = true ∧ root (eraseBlock K) = entry ∧
      (worldAt (stateBefore c p a nr s rho (i + 1)) w).st.bodies = (dutyStoreAt c p a nr s rho w i t).bodies := by
  obtain ⟨i, cache, st3, q, hev, hcache, hst3, hinv, -, hsucc, -, hq, hh, he, hqt, -⟩ :=
    Proofs.Consensus.AttestationSource.emits_vote_source c p a nr s rho hem hv
  have hduty : st3 = dutyStoreAt c p a nr s rho w i t := by
    rw [hst3, hcache]; rfl
  subst hduty hcache
  obtain ⟨D, hD, hDq, hDh, hDe⟩ := Proofs.Consensus.AttestationSource.source_named hinv hqt hh he
  obtain ⟨K, hKD, hKe, hKh⟩ := Proofs.Consensus.EntryHeight.entry_ancestor_same_height s.e s.cfg D
  have hK : K ∈ (dutyStoreAt c p a nr s rho w i t).bodies.elems :=
    Proofs.Consensus.Attribution.ancestor_mem_bodies hinv.closed hD hKD
  have hKh' : (deriveNamed s.e s.cfg K).h = h := hKh.trans hDh
  have hKt : (deriveNamed s.e s.cfg K).tH = eraseBlock K :=
    (Proofs.Consensus.EntryHeight.entry_eq_on_plateau s.e s.cfg hKD hKh).trans hKe.symm
  have hfg : fgConfirmationWitnessAt c p a nr s rho w i t = some (eraseBlock K) := by
    unfold fgConfirmationWitnessAt
    rw [hq, Option.map_some, ← hDq, hinv.sigma D hD, hKe]
  refine ⟨i, D, K, hev, hfg, hD, hDq ▸ hq, hDh, hK, hKe, hKh', hKt, hKD, ?_, hsucc⟩
  rw [hKe]; exact hDe

end Run

end Proofs.Consensus.HeightRowWitness
