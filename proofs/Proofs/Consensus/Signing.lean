import Model.Consensus.Execution.Run
import Statements.Consensus.Spec.Execution
import Proofs.Consensus.Records
import Proofs.Consensus.Runs
import Mathlib.Tactic

/-!
# run に沿った署名の記録(C71 の補題)

生成 Model の tick(`Model/Consensus/Protocol/Tick.lean`)で validator client の記録 `NamedRecord` を書くのは attestation の務め
`attestWith` → `roundActionWith` → `namedCreate` だけで、tick は attestation を高々 1 つ出し、出すときは記録をその
`namedCreate` の結果に進める(`tick_attest_shape`)。配送の処理 `nodeProcess` は記録に触れない(`nodeProcess_signing`)。
run の world では `stateBefore (i + 1)` は添字 `i` の event だけを `stateBefore i` に畳んだもので、ノード `v` の記録が変わるのは
`v` 自身の tick のときだけ(`signing_succ`)。したがって `createAttestation` で保たれる記録の性質(`Records.lean`)は、
run のどの添字でも成り立ち(`legacy_init`)、一度成り立てば以後も成り立つ(`legacy_pres`)。
`Emits v (Attest row) t`(`Statements/Consensus/Spec/Execution.lean`: 添字 `i` の event が `Tick v t` で `emittedAt i v t` が
`Attest row` を含む)は、その tick の `namedCreate` の行が `row` で、`stateBefore (i + 1)` の記録がその結果であることに言い換わる
(`emits_at_shape`)。
手書き `HealingSurface.on_tick_emit_attest_shape` / `process_record` / `stateBefore_lockCompatible` / `stateBefore_target_mono` /
`stateBefore_lock_mono` / `stateBefore_succ_record`(`DecoupledConsensusProofs/Protocol/ValidatorClient/Bridge.lean`)と
`RecordFresh.stateBefore_timeout_mono` / `SlashableBound.stateBefore_finalitySafeAt_mono` に当たる。
-/

namespace Proofs.Consensus.Signing

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers
open Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick Model.Consensus.Protocol.ValidatorClient
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution
open Proofs.Consensus.Records Proofs.Consensus.Runs

/-! ## tick -/

/-- attestation の務めは記録を `namedCreate` の結果に進め、その行を返す。 -/
theorem attestWith_shape (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : NamedRecord) :
    ∃ inp, (attestWith cache e hc nd st rec).2.1 = (namedCreate rec inp).1 ∧
      (attestWith cache e hc nd st rec).2.2 = (namedCreate rec inp).2 :=
  ⟨creatorInput (Model.Consensus.Protocol.Duties.Inputs.attestationInput cache e hc nd (storeToHealing st.core)), rfl, rfl⟩

/-- tick の attestation の分岐: attestation でない出力 `E` の後ろに `attestWith` の行が 1 つ付く。 -/
theorem attest_branch (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : NamedRecord) (E : List NamedObject) (hE : ∀ row, NamedObject.Attest row ∉ E) :
    ∃ inp, (attestWith cache e hc nd st rec).2.1 = (namedCreate rec inp).1 ∧
      ∀ row, NamedObject.Attest row ∈ E ++ [NamedObject.Attest (attestWith cache e hc nd st rec).2.2] →
        row = (namedCreate rec inp).2 := by
  obtain ⟨inp, h1, h2⟩ := attestWith_shape cache e hc nd st rec
  refine ⟨inp, h1, fun row h => ?_⟩
  rcases List.mem_append.mp h with h | h
  · exact absurd h (hE row)
  · rw [List.mem_singleton] at h
    injection h with h
    rw [h, h2]

/-- 1 tick は attestation を出さず記録をそのままにするか、attestation をちょうど 1 つ出して記録を `namedCreate` の結果に進める。
手書き `on_tick_emit_attest_shape`。 -/
theorem tick_attest_shape (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore) (rec : NamedRecord) (t : Int) :
    ((tick c p a nr cache e hc cfg nd st rec t).2.1 = rec ∧
        ∀ row, NamedObject.Attest row ∉ (tick c p a nr cache e hc cfg nd st rec t).2.2) ∨
      ∃ inp, (tick c p a nr cache e hc cfg nd st rec t).2.1 = (namedCreate rec inp).1 ∧
        ∀ row, NamedObject.Attest row ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2 → row = (namedCreate rec inp).2 := by
  unfold tick
  dsimp only
  split_ifs
  all_goals first
    | exact Or.inl ⟨rfl, fun row h => by
        simp only [List.mem_append] at h
        rcases h with h | h <;> (try split at h) <;> simp at h⟩
    | exact Or.inr (attest_branch _ _ _ _ _ _ _ (fun row h => by
        simp only [List.mem_append] at h
        rcases h with h | h <;> (try split at h) <;> simp at h))

/-! ## node -/

theorem nodeTick_signing (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId) (n : NamedNodeState)
    (t : Int) :
    (nodeTick c p a nr s v n t).1.signing =
      (tick c p a nr (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc (storeToHealing n.st.core) t n.cache) s.e s.hc s.cfg
        (Model.Consensus.Execution.Setup.setupNode v) n.st n.signing t).2.1 := by
  unfold nodeTick profileTick
  dsimp only

theorem nodeTick_out (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId) (n : NamedNodeState)
    (t : Int) :
    (nodeTick c p a nr s v n t).2 =
      (tick c p a nr (Model.Consensus.Protocol.Grades.onPhaseTick s.e s.hc (storeToHealing n.st.core) t n.cache) s.e s.hc s.cfg
        (Model.Consensus.Execution.Setup.setupNode v) n.st n.signing t).2.2 := by
  unfold nodeTick profileTick
  dsimp only

/-- ノードの tick の形(記録と出力)。 -/
theorem nodeTick_attest_shape (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId) (n : NamedNodeState)
    (t : Int) :
    ((nodeTick c p a nr s v n t).1.signing = n.signing ∧
        ∀ row, NamedObject.Attest row ∉ (nodeTick c p a nr s v n t).2) ∨
      ∃ inp, (nodeTick c p a nr s v n t).1.signing = (namedCreate n.signing inp).1 ∧
        ∀ row, NamedObject.Attest row ∈ (nodeTick c p a nr s v n t).2 → row = (namedCreate n.signing inp).2 := by
  rw [nodeTick_signing, nodeTick_out]
  exact tick_attest_shape c p a nr _ s.e s.hc s.cfg _ n.st n.signing t

/-- 配送の処理は記録に触れない。手書き `process_record`。 -/
theorem nodeProcess_signing (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) (n : NamedNodeState) (o : NamedObject) :
    (nodeProcess c p s n o).signing = n.signing := rfl

/-- `legacyCreate` で保たれる記録の性質は、ノードの tick で保たれる。 -/
theorem nodeTick_legacy_pres (P : Record → Prop) (hP : ∀ rec inp, P rec → P (legacyCreate rec inp).1)
    (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId) {n : NamedNodeState}
    (h : P n.signing.legacy) (t : Int) : P (nodeTick c p a nr s v n t).1.signing.legacy := by
  rcases nodeTick_attest_shape c p a nr s v n t with ⟨hrec, -⟩ | ⟨inp, hrec, -⟩
  · rw [hrec]; exact h
  · rw [hrec, namedCreate_legacy]
    exact hP _ _ h

/-! ## world -/

theorem worldAt_insert_self (w : NamedWorld) (u : ValidatorId) (n : NamedNodeState) :
    worldAt (NaruStd.Table.insert w u n) u = n := by
  unfold worldAt
  exact Proofs.Consensus.Tables.getOr_insert_self Proofs.Consensus.Tables.vid_compare_eq_iff w u n initialNode

theorem worldAt_insert_ne (w : NamedWorld) (u : ValidatorId) (n : NamedNodeState) (v : ValidatorId) (hne : u ≠ v) :
    worldAt (NaruStd.Table.insert w u n) v = worldAt w v := by
  unfold worldAt
  exact Proofs.Consensus.Tables.getOr_insert_ne Proofs.Consensus.Tables.vid_compare_eq_iff w u n v initialNode hne

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- `stateBefore (i + 1)` は添字 `i` の event(あれば)を `stateBefore i` に畳んだもの。 -/
theorem stateBefore_succ (i : Nat) :
    stateBefore c p a nr s rho (i + 1) =
      (rho.events[i]?.toList).foldl (fun w ev => worldStep c p a nr s w ev) (stateBefore c p a nr s rho i) := by
  unfold stateBefore
  rw [List.take_add_one, List.foldl_append]

theorem stateBefore_succ_of_get {i : Nat} {ev : NamedEvent} (hi : rho.events[i]? = some ev) :
    stateBefore c p a nr s rho (i + 1) = worldStep c p a nr s (stateBefore c p a nr s rho i) ev := by
  rw [stateBefore_succ, hi]
  rfl

theorem stateBefore_succ_of_none {i : Nat} (hi : rho.events[i]? = none) :
    stateBefore c p a nr s rho (i + 1) = stateBefore c p a nr s rho i := by
  rw [stateBefore_succ, hi]
  rfl

/-- 添字 `0` の前の記録は初期の記録。 -/
theorem signing_zero (v : ValidatorId) : (worldAt (stateBefore c p a nr s rho 0) v).signing = initialNamedRecord := rfl

/-- `v` 自身の tick の後の記録はその tick の出力。手書き `stateBefore_succ_record`。 -/
theorem signing_succ_tick {i : Nat} {v : ValidatorId} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t)) :
    (worldAt (stateBefore c p a nr s rho (i + 1)) v).signing =
      (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).1.signing := by
  rw [stateBefore_succ_of_get c p a nr s rho hi]
  unfold worldStep
  dsimp only
  rw [worldAt_insert_self]

/-- ノード `v` の記録は、添字 `i` の event が `v` 自身の tick でなければ変わらない。 -/
theorem signing_succ (i : Nat) (v : ValidatorId) :
    (worldAt (stateBefore c p a nr s rho (i + 1)) v).signing = (worldAt (stateBefore c p a nr s rho i) v).signing ∨
      ∃ t, rho.events[i]? = some (NamedEvent.Tick v t) ∧
        (worldAt (stateBefore c p a nr s rho (i + 1)) v).signing =
          (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).1.signing := by
  cases hev : rho.events[i]? with
  | none => exact Or.inl (by rw [stateBefore_succ_of_none c p a nr s rho hev])
  | some ev =>
    cases ev with
    | Tick u t =>
      by_cases huv : u = v
      · subst huv
        exact Or.inr ⟨t, rfl, signing_succ_tick c p a nr s rho hev⟩
      · left
        rw [stateBefore_succ_of_get c p a nr s rho hev]
        unfold worldStep
        dsimp only
        rw [worldAt_insert_ne _ _ _ _ huv]
    | Deliver u o t =>
      left
      rw [stateBefore_succ_of_get c p a nr s rho hev]
      unfold worldStep
      dsimp only
      by_cases huv : u = v
      · subst huv
        rw [worldAt_insert_self, nodeProcess_signing]
      · rw [worldAt_insert_ne _ _ _ _ huv]

/-- `legacyCreate` で保たれる記録の性質は、添字 `i` で成り立てば以後の添字 `j ≥ i` でも成り立つ。 -/
theorem legacy_pres (P : Record → Prop) (hP : ∀ rec inp, P rec → P (legacyCreate rec inp).1) (v : ValidatorId) {i : Nat}
    (h : P (worldAt (stateBefore c p a nr s rho i) v).signing.legacy) :
    ∀ j, i ≤ j → P (worldAt (stateBefore c p a nr s rho j) v).signing.legacy := by
  intro j
  induction j with
  | zero =>
    intro hj
    have : i = 0 := Nat.le_zero.mp hj
    subst this
    exact h
  | succ j ih =>
    intro hj
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have ih' := ih (Nat.lt_succ_iff.mp hlt)
      rcases signing_succ c p a nr s rho j v with heq | ⟨t, -, heq⟩
      · rw [heq]; exact ih'
      · rw [heq]
        exact nodeTick_legacy_pres P hP c p a nr s v ih' t
    · have : i = j + 1 := Nat.le_antisymm hj hge
      subst this
      exact h

/-- 初期の記録で成り立ち `legacyCreate` で保たれる性質は、run のどの添字でも成り立つ。 -/
theorem legacy_init (P : Record → Prop) (h0 : P initialRecord) (hP : ∀ rec inp, P rec → P (legacyCreate rec inp).1)
    (v : ValidatorId) (i : Nat) : P (worldAt (stateBefore c p a nr s rho i) v).signing.legacy :=
  legacy_pres c p a nr s rho P hP v (i := 0) (by rw [signing_zero]; exact h0) i (Nat.zero_le i)

/-! ## 発行 -/

theorem emittedAt_eq (i : Nat) (v : ValidatorId) (t : Int) :
    emittedAt c p a nr s rho i v t = (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2 := by
  unfold emittedAt
  dsimp only

/-- `Emits` の言い換え: 添字 `i` の event が `Tick v t` で、その tick の出力に `o` がある。 -/
theorem emits_iff (v : ValidatorId) (o : NamedObject) (t : Int) :
    Emits c p a nr s rho v o t ↔
      ∃ i, rho.events[i]? = some (NamedEvent.Tick v t) ∧
        o ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2 := by
  unfold Emits
  simp only [emittedAt_eq, List.contains_iff_mem]

/-- `v` の tick が attestation `row` を出したなら、その tick の記録は `namedCreate` の結果で `row` はその行。 -/
theorem emits_at_shape {i : Nat} {v : ValidatorId} {t : Int} (hi : rho.events[i]? = some (NamedEvent.Tick v t))
    {row : NamedAttestation}
    (hrow : NamedObject.Attest row ∈ (nodeTick c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t).2) :
    ∃ inp, (worldAt (stateBefore c p a nr s rho (i + 1)) v).signing =
        (namedCreate (worldAt (stateBefore c p a nr s rho i) v).signing inp).1 ∧
      row = (namedCreate (worldAt (stateBefore c p a nr s rho i) v).signing inp).2 := by
  rw [signing_succ_tick c p a nr s rho hi]
  rcases nodeTick_attest_shape c p a nr s v (worldAt (stateBefore c p a nr s rho i) v) t with ⟨-, hno⟩ | ⟨inp, hrec, hr⟩
  · exact absurd hrow (hno row)
  · exact ⟨inp, hrec, hr row hrow⟩

/-- 1 つの tick が出す attestation は 1 つ。 -/
theorem rows_eq_of_same_tick (v : ValidatorId) (n : NamedNodeState) (t : Int) {ra rb : NamedAttestation}
    (ha : NamedObject.Attest ra ∈ (nodeTick c p a nr s v n t).2) (hb : NamedObject.Attest rb ∈ (nodeTick c p a nr s v n t).2) :
    ra = rb := by
  rcases nodeTick_attest_shape c p a nr s v n t with ⟨-, hno⟩ | ⟨inp, -, hr⟩
  · exact absurd ha (hno ra)
  · rw [hr ra ha, hr rb hb]

end Run

end Proofs.Consensus.Signing
