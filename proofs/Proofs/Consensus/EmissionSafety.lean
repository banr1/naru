import Model.Consensus.Protocol.ChainState
import Proofs.Consensus.Signing
import Mathlib.Tactic

/-!
# honest な発行は slashable にならない(C71 の補題)

同じ validator `v` が run の中で実際に出した(`Emits`)2 つの attestation の消去は、互いに E1 / E2 の証拠にならない
(`slashable … = false`)。筋(手書き `honestNoDoubleTarget` / `no_timeout_against_finality` / `emissionVoteSafety`、
`DecoupledConsensusProofs/Protocol/ValidatorClient/{Bridge,SlashableBound}.lean` /
`Protocol/ChainState/ValidatorVoteSafety.lean`):
- 記録の性質(`Records.lean`)は run のどの添字でも成り立ち(`LockCompatible`)、一度成り立てば以後も成り立つ(target / lock / timeout の
  単調性、`FinalitySafeAt`)— `Signing.lean` の `legacy_init` / `legacy_pres`。
- 添字 `i` の tick が出した attestation の target は `i + 1` の記録に残る(height pair なら `target`、finality pair なら `lock`)ので、
  後の添字 `j` の tick が同じ高さに出す target はそれに等しい(`no_double_target`)。同じ tick が出す attestation は 1 つで、
  1 つの attestation の 2 つの pair は同じ高さなら同じ target を指す。
- finality pair を出した高さは `FinalitySafeAt`(timeout でない)で以後保たれ、timeout を出すと `timeout` が立って以後保たれるので、
  同じ高さの finality pair と timeout は両立しない(`no_timeout_against_finality`)。
- 以上から `e1Fields` / `e2Fields` が偽で `slashable` も偽(`emission_not_slashable`)。
-/

namespace Proofs.Consensus.EmissionSafety

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.ValidatorClient
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Records Proofs.Consensus.Signing

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun) (v : ValidatorId)

/-! ## run に沿った記録の性質 -/

theorem lockCompatible_at (i : Nat) : LockCompatible (worldAt (stateBefore c p a nr s rho i) v).signing.legacy :=
  legacy_init c p a nr s rho LockCompatible lockCompatible_initial
    (fun rec inp h => lockCompatible_create inp.valIndex inp.round inp.confirmed inp.fields inp.hJ inp.j inp.hF h) v i

theorem target_mono_at {i j : Nat} (hij : i ≤ j) {g : Nat} {T : BlockId}
    (h : recordTarget (worldAt (stateBefore c p a nr s rho i) v).signing.legacy g = some T) :
    recordTarget (worldAt (stateBefore c p a nr s rho j) v).signing.legacy g = some T :=
  legacy_pres c p a nr s rho (fun rec => recordTarget rec g = some T)
    (fun rec inp h => create_target_mono inp.valIndex inp.round inp.confirmed inp.fields inp.hJ inp.j inp.hF h) v h j hij

theorem lock_mono_at {i j : Nat} (hij : i ≤ j) {g : Nat} {T : BlockId}
    (h : recordLock (worldAt (stateBefore c p a nr s rho i) v).signing.legacy g = some T) :
    recordLock (worldAt (stateBefore c p a nr s rho j) v).signing.legacy g = some T :=
  legacy_pres c p a nr s rho (fun rec => recordLock rec g = some T)
    (fun rec inp h => create_lock_mono inp.valIndex inp.round inp.confirmed inp.fields inp.hJ inp.j inp.hF h) v h j hij

theorem timeout_mono_at {i j : Nat} (hij : i ≤ j) {g : Nat}
    (h : recordTimeout (worldAt (stateBefore c p a nr s rho i) v).signing.legacy g = true) :
    recordTimeout (worldAt (stateBefore c p a nr s rho j) v).signing.legacy g = true :=
  legacy_pres c p a nr s rho (fun rec => recordTimeout rec g = true)
    (fun rec inp h => create_timeout_mono inp.valIndex inp.round inp.confirmed inp.fields inp.hJ inp.j inp.hF h) v h j hij

theorem finalitySafeAt_mono_at {i j : Nat} (hij : i ≤ j) {g : Nat} {T : BlockId}
    (h : FinalitySafeAt (worldAt (stateBefore c p a nr s rho i) v).signing.legacy g T) :
    FinalitySafeAt (worldAt (stateBefore c p a nr s rho j) v).signing.legacy g T :=
  legacy_pres c p a nr s rho (fun rec => FinalitySafeAt rec g T)
    (fun rec inp h => create_finalitySafeAt_mono inp.valIndex inp.round inp.confirmed inp.fields inp.hJ inp.j inp.hF h)
    v h j hij

/-! ## 発行が記録に残すもの -/

/-- `v` の tick(添字 `i`)が出した attestation `row` は、`i` の記録への `createAttestation`(= `legacyCreate`)の行で、
`i + 1` の記録はその結果。 -/
theorem emits_create {i : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t)) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2) :
    ∃ inp, (worldAt (stateBefore c p a nr s rho (i + 1)) v).signing.legacy =
        (legacyCreate (worldAt (stateBefore c p a nr s rho i) v).signing.legacy inp).1 ∧
      eraseAttestation row = (legacyCreate (worldAt (stateBefore c p a nr s rho i) v).signing.legacy inp).2 := by
  obtain ⟨inp, h1, h2⟩ := emits_at_shape c p a nr s rho hi hrow
  exact ⟨inp, by rw [h1, namedCreate_legacy], by rw [h2, namedCreate_erase]⟩

theorem emits_target_recorded {i : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t)) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2)
    {g : Nat} {T : BlockId} (hT : (eraseAttestation row).heightPair = .Target g T) :
    recordTarget (worldAt (stateBefore c p a nr s rho (i + 1)) v).signing.legacy g = some T := by
  obtain ⟨inp, h1, h2⟩ := emits_create c p a nr s rho v hi hrow
  rw [h1, legacyCreate_eq]
  rw [h2, legacyCreate_eq] at hT
  exact create_saves _ _ _ _ _ _ _ (lockCompatible_at c p a nr s rho v i) hT

theorem emits_finality_locked {i : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t)) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2)
    {g : Nat} {T : BlockId} (hT : (eraseAttestation row).finalityPair = some ⟨g, T⟩) :
    recordLock (worldAt (stateBefore c p a nr s rho (i + 1)) v).signing.legacy g = some T := by
  obtain ⟨inp, h1, h2⟩ := emits_create c p a nr s rho v hi hrow
  rw [h1, legacyCreate_eq]
  rw [h2, legacyCreate_eq] at hT
  exact create_finality_locked _ _ _ _ _ _ _ hT

theorem emits_timeout_true {i : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t)) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2)
    {g : Nat} (hT : (eraseAttestation row).heightPair = .Timeout g) :
    recordTimeout (worldAt (stateBefore c p a nr s rho (i + 1)) v).signing.legacy g = true := by
  obtain ⟨inp, h1, h2⟩ := emits_create c p a nr s rho v hi hrow
  rw [h1, legacyCreate_eq]
  rw [h2, legacyCreate_eq] at hT
  exact create_timeout_true _ _ _ _ _ _ _ hT

theorem emits_finalitySafeAt {i : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t)) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2)
    {g : Nat} {T : BlockId} (hT : (eraseAttestation row).finalityPair = some ⟨g, T⟩) :
    FinalitySafeAt (worldAt (stateBefore c p a nr s rho (i + 1)) v).signing.legacy g T := by
  obtain ⟨inp, h1, h2⟩ := emits_create c p a nr s rho v hi hrow
  rw [h1, legacyCreate_eq]
  rw [h2, legacyCreate_eq] at hT
  exact create_finalitySafeAt _ _ _ _ _ _ _ hT

theorem emits_target_eq_of_record {i : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t))
    {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2)
    {g : Nat} {X T : BlockId} (hs : recordTarget (worldAt (stateBefore c p a nr s rho i) v).signing.legacy g = some X)
    (hT : targets (eraseAttestation row) g T) : T = X := by
  obtain ⟨inp, -, h2⟩ := emits_create c p a nr s rho v hi hrow
  rw [h2, legacyCreate_eq] at hT
  exact create_target_eq_of_record _ _ _ _ _ _ _ (lockCompatible_at c p a nr s rho v i) hs hT

theorem emits_target_eq_of_lock {i : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t))
    {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2)
    {g : Nat} {X T : BlockId} (hs : recordLock (worldAt (stateBefore c p a nr s rho i) v).signing.legacy g = some X)
    (hT : targets (eraseAttestation row) g T) : T = X := by
  obtain ⟨inp, -, h2⟩ := emits_create c p a nr s rho v hi hrow
  rw [h2, legacyCreate_eq] at hT
  exact create_target_eq_of_lock _ _ _ _ _ _ _ hs hT

theorem emits_no_self_E1 {i : Nat} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t)) {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2)
    {g : Nat} {T T' : BlockId} (hhp : (eraseAttestation row).heightPair = .Target g T)
    (hfp : (eraseAttestation row).finalityPair = some ⟨g, T'⟩) : T = T' := by
  obtain ⟨inp, -, h2⟩ := emits_create c p a nr s rho v hi hrow
  rw [h2, legacyCreate_eq] at hhp hfp
  exact create_no_self_E1 _ _ _ _ _ _ _ hhp hfp

/-! ## 2 つの発行 -/

/-- 同じ validator の 2 つの発行が同じ高さに名指す target は等しい。手書き `honestNoDoubleTarget`。 -/
theorem no_double_target {i j : Nat} {ta tb : Int} {ra rb : NamedAttestation}
    (hi : rho.events[i]? = some (NamedEvent.Tick v ta))
    (ha : NamedObject.Attest ra ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) ta).2)
    (hj : rho.events[j]? = some (NamedEvent.Tick v tb))
    (hb : NamedObject.Attest rb ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho j) v) tb).2)
    {g : Nat} {T U : BlockId} (hT : targets (eraseAttestation ra) g T) (hU : targets (eraseAttestation rb) g U) : T = U := by
  rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
  · rcases hT with hhp | hfp
    · have hrec := target_mono_at c p a nr s rho v (i := i + 1) (j := j) hlt
        (emits_target_recorded c p a nr s rho v hi ha hhp)
      exact (emits_target_eq_of_record c p a nr s rho v hj hb hrec hU).symm
    · have hlock := lock_mono_at c p a nr s rho v (i := i + 1) (j := j) hlt
        (emits_finality_locked c p a nr s rho v hi ha hfp)
      exact (emits_target_eq_of_lock c p a nr s rho v hj hb hlock hU).symm
  · have hev := Option.some.inj (hj.symm.trans hi)
    injection hev with _ hta
    subst hta
    have hab : ra = rb := rows_eq_of_same_tick c p a nr s v _ _ ha hb
    subst hab
    rcases hT with hT | hT <;> rcases hU with hU | hU
    · rw [hT] at hU
      simp only [HeightPair.Target.injEq] at hU
      exact hU.2
    · exact emits_no_self_E1 c p a nr s rho v hi ha hT hU
    · exact (emits_no_self_E1 c p a nr s rho v hi ha hU hT).symm
    · rw [hT] at hU
      have h := Option.some.inj hU
      exact congrArg FinalityPair.target h
  · rcases hU with hhp | hfp
    · have hrec := target_mono_at c p a nr s rho v (i := j + 1) (j := i) hgt
        (emits_target_recorded c p a nr s rho v hj hb hhp)
      exact emits_target_eq_of_record c p a nr s rho v hi ha hrec hT
    · have hlock := lock_mono_at c p a nr s rho v (i := j + 1) (j := i) hgt
        (emits_finality_locked c p a nr s rho v hj hb hfp)
      exact emits_target_eq_of_lock c p a nr s rho v hi ha hlock hT

/-- 同じ validator の 2 つの発行で、同じ高さの finality pair と timeout は両立しない。手書き `no_timeout_against_finality`。 -/
theorem no_timeout_against_finality {i j : Nat} {ta tb : Int} {ra rb : NamedAttestation}
    (hi : rho.events[i]? = some (NamedEvent.Tick v ta))
    (ha : NamedObject.Attest ra ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) ta).2)
    (hj : rho.events[j]? = some (NamedEvent.Tick v tb))
    (hb : NamedObject.Attest rb ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho j) v) tb).2)
    {g : Nat} {T : BlockId} (hfp : (eraseAttestation ra).finalityPair = some ⟨g, T⟩)
    (hhp : (eraseAttestation rb).heightPair = .Timeout g) : False := by
  have hsafe := emits_finalitySafeAt c p a nr s rho v hi ha hfp
  have hto := emits_timeout_true c p a nr s rho v hj hb hhp
  rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
  · have hsafe' := finalitySafeAt_mono_at c p a nr s rho v (i := i + 1) (j := j + 1) (by omega) hsafe
    rw [hsafe'.1] at hto
    exact Bool.false_ne_true hto
  · rw [hsafe.1] at hto
    exact Bool.false_ne_true hto
  · have hto' := timeout_mono_at c p a nr s rho v (i := j + 1) (j := i + 1) (by omega) hto
    rw [hsafe.1] at hto'
    exact Bool.false_ne_true hto'

/-- `ra` の finality pair と `rb` の height pair は衝突しない。 -/
theorem conflict_false {i j : Nat} {ta tb : Int} {ra rb : NamedAttestation}
    (hi : rho.events[i]? = some (NamedEvent.Tick v ta))
    (ha : NamedObject.Attest ra ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) ta).2)
    (hj : rho.events[j]? = some (NamedEvent.Tick v tb))
    (hb : NamedObject.Attest rb ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho j) v) tb).2) :
    Option.getD (Option.map (fun pair => conflictsWithFinality (eraseAttestation rb).heightPair pair)
      (eraseAttestation ra).finalityPair) false = false := by
  cases hfa : (eraseAttestation ra).finalityPair with
  | none => rfl
  | some pr =>
    obtain ⟨g, T⟩ := pr
    simp only [Option.map_some, Option.getD_some]
    cases hpb : (eraseAttestation rb).heightPair with
    | Empty => rfl
    | Timeout g' =>
      simp only [conflictsWithFinality]
      by_cases hg : g' = g
      · subst hg
        exact absurd (no_timeout_against_finality c p a nr s rho v hi ha hj hb hfa hpb) id
      · simp [hg]
    | Target g' U =>
      simp only [conflictsWithFinality]
      by_cases hg : g' = g
      · subst hg
        have hTU := no_double_target c p a nr s rho v hi ha hj hb (Or.inr hfa) (Or.inl hpb)
        subst hTU
        simp
      · simp [hg]

/-- 同じ validator の 2 つの発行の消去は slashable でない。手書き `emissionVoteSafety`。 -/
theorem emission_not_slashable {i j : Nat} {ta tb : Int} {ra rb : NamedAttestation}
    (hi : rho.events[i]? = some (NamedEvent.Tick v ta))
    (ha : NamedObject.Attest ra ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) ta).2)
    (hj : rho.events[j]? = some (NamedEvent.Tick v tb))
    (hb : NamedObject.Attest rb ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho j) v) tb).2) :
    slashable (eraseAttestation ra) (eraseAttestation rb) = false := by
  have he2 : e2Fields (eraseAttestation ra) (eraseAttestation rb) = false := by
    unfold e2Fields
    cases hpa : (eraseAttestation ra).heightPair with
    | Empty => rfl
    | Timeout g1 => rfl
    | Target g1 T =>
      cases hpb : (eraseAttestation rb).heightPair with
      | Empty => rfl
      | Timeout g2 => rfl
      | Target g2 U =>
        simp only
        by_cases hg : g1 = g2
        · subst hg
          have hTU := no_double_target c p a nr s rho v hi ha hj hb (Or.inl hpa) (Or.inl hpb)
          subst hTU
          simp
        · simp [hg]
  have he1 : e1Fields (eraseAttestation ra) (eraseAttestation rb) = false := by
    unfold e1Fields
    rw [conflict_false c p a nr s rho v hi ha hj hb, conflict_false c p a nr s rho v hj hb hi ha]
    rfl
  unfold slashable e1Slashable e2Slashable
  rw [he1, he2]
  simp

end Run

end Proofs.Consensus.EmissionSafety
