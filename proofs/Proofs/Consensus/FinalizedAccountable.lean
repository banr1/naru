import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Carrier
import Proofs.Consensus.CertificatesAccountable
import Mathlib.Tactic

/-!
# claim `finalizedAccountable` / `finalizedSafe`(C71 の補題)

run の中の honest なノード `u` / `v` の時刻 `t` / `t2` の finalized の読みについて:
- `finalizedAccountable`(前提 `SetupWellFormed ∧ RunDomain ∧ RunWellFormed`): 2 つの読みは互換(`compatible`)か、2 つの store の
  attestation の間に重み `2q − W` 以上の slashable な署名者集合がある(`SlashableStates`)— property `AccountablySafeFrom … Finalized 0`。
- `finalizedSafe`(前提に `AccountableRegime = RunWellFormed ∧ SlashableBound`): run の中のブロックの間に `Evidence` が無いので、
  2 つの読みは常に互換 — property `AgreeFrom … Finalized 0`。

筋(手書き `storeAccountableSafety_stateBefore` / `wholeRunAccountableFinalitySafety` / `wholeRunFinalitySafety`、
`DecoupledConsensusProofs/Protocol/ChainState/WholeRunFinalitySafety.lean`):
1. store の不変条件(`Carrier.lean`)から、各読みの finalized は bodies のどれかの名前付きブロック `D` の導出 `deriveNamed D` の `f`
   (finality carrier)で、`eraseBlock D ∈ tree`。
2. `EventsSorted` の下で `readAt t` はある `stateBefore i`(`filter (≤ t)` が接頭辞 `take i`)なので、`D` は run の中のブロック
   (`BlockInRun`: honest なノードの `stateBefore i` の bodies にある)。
3. `RunWellFormed` の `Idealization = NamedRootCollisionFree`(run の中の 2 ブロックの名前付き祖先の間で `namedRoot` が単射)を、
   消去した祖先を名前付き祖先に持ち上げて(`erased_ancestor_lift`)`RootInjectiveOnAncestors (eraseBlock D₁) (eraseBlock D₂)` にする。
4. `certificatesAccountable` の本体 `oriented`(高さの低い方から)を両向きに当て、互換か `Evidence s D₁ D₂`。
5. `Evidence`(2 本の chain の attestation の間の slashable な重み)を、`chainAttestations (eraseBlock D) ⊆ storeAttestations core`
   (`eraseBlock D ∈ tree`、`storeAttestations = flatMap tree chainAttestations`)で `SlashableStates` に持ち上げる
   (`finalizedAccountable`)か、`SlashableBound` で退ける(`finalizedSafe`)。
-/

namespace Proofs.Consensus.FinalizedAccountable

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Objects.Weights Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Evidence
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Accountability Statements.Consensus.Spec.Interface Statements.Consensus.Spec.Execution
open Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.NamedBlocks Proofs.Consensus.Runs
open Proofs.Consensus.Weights Proofs.Consensus.Carrier Proofs.Consensus.CertificatesAccountable
open Proofs.Consensus.Blocks

/-! ## 読みは run の接頭辞 -/

/-- 時刻が非減少な event の列では、`filter (≤ t)` はある接頭辞 `take i`。 -/
theorem filter_le_eq_take (t : Int) :
    ∀ (l : List NamedEvent), l.Pairwise (fun a b => eventTime a ≤ eventTime b) →
      ∃ i, l.filter (fun ev => decide (eventTime ev ≤ t)) = l.take i
  | [], _ => ⟨0, rfl⟩
  | x :: xs, hp => by
    rw [List.pairwise_cons] at hp
    obtain ⟨hx, hxs⟩ := hp
    by_cases hxt : eventTime x ≤ t
    · obtain ⟨i, hi⟩ := filter_le_eq_take t xs hxs
      exact ⟨i + 1, by simp [List.filter_cons, hxt, hi]⟩
    · refine ⟨0, ?_⟩
      rw [List.take_zero, List.filter_eq_nil_iff]
      intro y hy
      simp only [decide_eq_true_eq]
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hxt
      · exact fun hyt => hxt (le_trans (hx y hy') hyt)

/-- `EventsSorted` の下で `readAt t` はある `stateBefore i`。手書き `stateAt_eq_stateBefore_of_sorted`。 -/
theorem readAt_eq_stateBefore (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup)
    (rho : NamedRun) (hs : EventsSorted rho) (t : Int) :
    ∃ i, readAt c p a nr s rho t = stateBefore c p a nr s rho i := by
  obtain ⟨i, hi⟩ := filter_le_eq_take t rho.events (pairwise_of_eventsSorted rho hs)
  exact ⟨i, by unfold readAt stateBefore; rw [hi]⟩

/-- honest なノードの読みの bodies にある名前付きブロックは run の中のブロック(`BlockInRun`)。手書き `runBlock_of_stateBefore_mem`。 -/
theorem blockInRun_of_mem (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup)
    (rho : NamedRun) {u : ValidatorId} (hu : rho.honest.contains u = true) (hs : EventsSorted rho) (t : Int)
    (D : NamedBlock) (hD : D ∈ (worldAt (readAt c p a nr s rho t) u).st.bodies.elems) :
    BlockInRun c p a nr s rho D := by
  obtain ⟨i, hi⟩ := readAt_eq_stateBefore c p a nr s rho hs t
  rw [hi] at hD
  unfold BlockInRun DirectBlockInRun
  exact ⟨D, Or.inr ⟨u, hu, i, (contains_iff_mem nb_compare_eq_iff _ _).mpr hD⟩, namedPreceq_self D⟩

/-! ## root の衝突なし -/

/-- `NamedRootCollisionFree` から、run の中の 2 ブロックの消去について `RootInjectiveOnAncestors`。
手書き `namedRootInjectiveOnAncestors_of_collisionFree`。 -/
theorem rootInjective_of_collisionFree (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup)
    (rho : NamedRun) (hcf : NamedRootCollisionFree c p a nr s rho) {D₁ D₂ : NamedBlock}
    (h₁ : BlockInRun c p a nr s rho D₁) (h₂ : BlockInRun c p a nr s rho D₂) :
    RootInjectiveOnAncestors (eraseBlock D₁) (eraseBlock D₂) := by
  unfold RootInjectiveOnAncestors
  intro x y hxy
  obtain ⟨⟨hx, hy⟩, hr⟩ := hxy
  have lift : ∀ {z : Block}, preceq z (eraseBlock D₁) = true ∨ preceq z (eraseBlock D₂) = true →
      ∃ Z, (namedPreceq Z D₁ = true ∨ namedPreceq Z D₂ = true) ∧ eraseBlock Z = z := by
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨Z, hZ, hzz⟩ := erased_ancestor_lift hz
      exact ⟨Z, Or.inl hZ, hzz⟩
    · obtain ⟨Z, hZ, hzz⟩ := erased_ancestor_lift hz
      exact ⟨Z, Or.inr hZ, hzz⟩
  obtain ⟨X, hX, rfl⟩ := lift hx
  obtain ⟨Y, hY, rfl⟩ := lift hy
  rw [root_eraseBlock, root_eraseBlock] at hr
  rw [hcf D₁ D₂ ⟨h₁, h₂⟩ X Y ⟨⟨hX, hY⟩, hr⟩]

/-! ## chain の attestation は store の attestation -/

/-- tree にあるブロックの chain の attestation は store の attestation(`storeAttestations = flatMap tree chainAttestations`)。
手書き `chain_attestations_subset_store`。 -/
theorem chainAttestations_subset_store {st : Store} {b : Block} (hb : b ∈ st.tree.elems) (x : CombinedAttestation)
    (hx : (chainAttestations b).contains x = true) : (storeAttestations st).contains x = true := by
  rw [contains_iff_mem ca_compare_eq_iff] at hx ⊢
  unfold storeAttestations
  rw [mem_flatMap_iff ca_compare_eq_iff]
  exact ⟨b, hb, hx⟩

/-- `HasSlashableWeightBetween` は attestation の集合について単調(署名者集合はそのまま)。手書き `hasSlashableWeightBetween_mono`。 -/
theorem hasSlashableWeightBetween_mono {e : ProtocolEnv} {A1 A2 A1' A2' : NaruStd.Set CombinedAttestation}
    (h : HasSlashableWeightBetween e A1 A2) (h1 : ∀ x, A1.contains x = true → A1'.contains x = true)
    (h2 : ∀ x, A2.contains x = true → A2'.contains x = true) : HasSlashableWeightBetween e A1' A2' := by
  obtain ⟨members, hw, hs⟩ := h
  refine ⟨members, hw, fun i hi => ?_⟩
  obtain ⟨a, b, ⟨⟨⟨ha, hb⟩, hav⟩, hbv⟩, hsl⟩ := hs i hi
  exact ⟨a, b, ⟨⟨⟨h1 a ha, h2 b hb⟩, hav⟩, hbv⟩, hsl⟩

/-! ## 本体 -/

/-- 2 つの読みの finality carrier `D₁` / `D₂`(run の中のブロック)と、互換か `Evidence`。 -/
theorem core (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)
    (hwf : SetupWellFormed c p s) (hrun : RunWellFormed c p a nr s rho) {u v : ValidatorId}
    (hu : rho.honest.contains u = true) (hv : rho.honest.contains v = true) (t t2 : Int) :
    ∃ D₁ D₂ : NamedBlock, InRun c p a nr s rho D₁ ∧ InRun c p a nr s rho D₂ ∧
      (deriveNamed s.e s.cfg D₁).f = (storeAt c p a nr s rho u t).core.f ∧
      (deriveNamed s.e s.cfg D₂).f = (storeAt c p a nr s rho v t2).core.f ∧
      (∀ x, (chainAttestations (eraseBlock D₁)).contains x = true →
        (storeAttestations (storeAt c p a nr s rho u t).core).contains x = true) ∧
      (∀ x, (chainAttestations (eraseBlock D₂)).contains x = true →
        (storeAttestations (storeAt c p a nr s rho v t2).core).contains x = true) ∧
      (compatible (deriveNamed s.e s.cfg D₁).f (deriveNamed s.e s.cfg D₂).f = true ∨ Evidence s D₁ D₂) := by
  have hv' : Sorted (validators s.e.electorate) := by
    unfold SetupWellFormed at hwf
    obtain ⟨⟨⟨_, hnorm⟩, _⟩, _⟩ := hwf
    exact sorted_of_normalized hnorm
  unfold RunWellFormed at hrun
  obtain ⟨⟨_, hsorted⟩, hideal⟩ := hrun
  unfold Idealization at hideal
  obtain ⟨D₁, hD₁, hf₁⟩ := (readAt_inv c p a nr s rho t u).carrier
  obtain ⟨D₂, hD₂, hf₂⟩ := (readAt_inv c p a nr s rho t2 v).carrier
  have hin₁ : BlockInRun c p a nr s rho D₁ := blockInRun_of_mem c p a nr s rho hu hsorted t D₁ hD₁
  have hin₂ : BlockInRun c p a nr s rho D₂ := blockInRun_of_mem c p a nr s rho hv hsorted t2 D₂ hD₂
  have hroot := rootInjective_of_collisionFree c p a nr s rho hideal hin₁ hin₂
  refine ⟨D₁, D₂, hin₁, hin₂, hf₁, hf₂, ?_, ?_, ?_⟩
  · exact fun x hx => chainAttestations_subset_store ((readAt_inv c p a nr s rho t u).tree D₁ hD₁) x hx
  · exact fun x hx => chainAttestations_subset_store ((readAt_inv c p a nr s rho t2 v).tree D₂ hD₂) x hx
  · unfold Evidence
    rcases Nat.le_total (deriveNamed s.e s.cfg D₁).hF (deriveNamed s.e s.cfg D₂).hF with hle | hle
    · exact oriented s.e s.cfg hv' hroot hle
    · rcases oriented s.e s.cfg hv' (rootInjective_symm hroot) hle with hc | hs
      · exact Or.inl (by rw [compatible_comm]; exact hc)
      · exact Or.inr (hasSlashableWeightBetween_symm hs)

/-- claim `finalizedAccountable` の本体(義務の型そのまま)。 -/
theorem finalizedAccountable : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) (awake' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Bool)) (newRoot' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Model.Consensus.Objects.Identifiers.BlockId)) («s» : Model.Consensus.Execution.Setup.Setup) («rho» : Model.Consensus.Execution.Run.NamedRun), Statements.Consensus.Spec.Claims.finalizedAccountable committee' proposer' awake' newRoot' «s» «rho» := by
  intro committee' proposer' awake' newRoot' s rho
  unfold Statements.Consensus.Spec.Claims.finalizedAccountable
  intro h
  obtain ⟨⟨hwf, _⟩, hrun⟩ := h
  unfold Statements.Consensus.Spec.Properties.AccountablySafeFrom
    Statements.Consensus.Spec.Properties.AccountablyConsistentFrom
  intro u v t t2 hh
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, _⟩, _⟩, _⟩, _⟩ := hh
  obtain ⟨D₁, D₂, _, _, hf₁, hf₂, hs₁, hs₂, hc⟩ := core committee' proposer' awake' newRoot' s rho hwf hrun hu hv t t2
  rcases hc with hc | hev
  · left
    show compatible (storeAt committee' proposer' awake' newRoot' s rho u t).core.f
      (storeAt committee' proposer' awake' newRoot' s rho v t2).core.f = true
    rw [← hf₁, ← hf₂]
    exact hc
  · right
    unfold SlashableStates
    exact hasSlashableWeightBetween_mono hev hs₁ hs₂

/-- claim `finalizedSafe` の本体(義務の型そのまま)。 -/
theorem finalizedSafe : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) (awake' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Bool)) (newRoot' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Model.Consensus.Objects.Identifiers.BlockId)) («s» : Model.Consensus.Execution.Setup.Setup) («rho» : Model.Consensus.Execution.Run.NamedRun), Statements.Consensus.Spec.Claims.finalizedSafe committee' proposer' awake' newRoot' «s» «rho» := by
  intro committee' proposer' awake' newRoot' s rho
  unfold Statements.Consensus.Spec.Claims.finalizedSafe
  intro h
  obtain ⟨⟨hwf, _⟩, hreg⟩ := h
  unfold Statements.Consensus.Spec.Regimes.AccountableRegime at hreg
  obtain ⟨hrun, hsb⟩ := hreg
  unfold Statements.Consensus.Spec.Properties.AgreeFrom Statements.Consensus.Spec.Properties.ConsistentFrom
  intro u v t t2 hh
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, _⟩, _⟩, _⟩, _⟩ := hh
  obtain ⟨D₁, D₂, hin₁, hin₂, hf₁, hf₂, _, _, hc⟩ :=
    core committee' proposer' awake' newRoot' s rho hwf hrun hu hv t t2
  rcases hc with hc | hev
  · show compatible (storeAt committee' proposer' awake' newRoot' s rho u t).core.f
      (storeAt committee' proposer' awake' newRoot' s rho v t2).core.f = true
    rw [← hf₁, ← hf₂]
    exact hc
  · exact absurd hev (hsb D₁ D₂ ⟨hin₁, hin₂⟩)

end Proofs.Consensus.FinalizedAccountable
