import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.Carrier
import Proofs.Consensus.Signing
import Proofs.Consensus.FinalizedAccountable
import Mathlib.Tactic

/-!
# store の attestation は honest な発行(C71 の補題)

honest なノード `u` の時刻 `t` の store の attestation(`storeAttestations (storeAt u t).core`: tree の各ブロックの chain の
行)のうち honest な `w` の署名のものは、`w` が実際に出した(`Emits`)名前付きの行 `row` の消去である(`attributed`)。筋
(手書き `NamedStoreBridge.carriedByHonest_of_storeAt`、`DecoupledConsensusProofs/Protocol/Handlers/StoreBridge.lean`):
1. `EventsSorted` の下で `storeAt u t` はある `stateBefore i₀` の `u` の store(`readAt_eq_stateBefore`)。
2. store の不変条件(`Carrier.lean`)で tree の各ブロックは bodies の名前付きブロック `D` の消去で、`chainAttestations (eraseBlock D)` の
   行は `D` の名前付き祖先 `X` の行 `row` の消去(`chain_row_of_mem`)。bodies は親について閉じているので `X ∈ bodies`
   (`ancestor_mem_bodies`)。
3. bodies の genesis でないブロックは、そのノードがある event で処理した(`Processes`)ブロック(`bodies_processed`: bodies が増えるのは
   ブロックの配送か自分の提案の tick だけ)。
4. `UnforgeableSignatures` の後半(carried)から、処理したブロックが運ぶ honest な署名の行は署名者が実際に出した行。
-/

namespace Proofs.Consensus.Attribution

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers
open Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick Model.Consensus.Protocol.Evidence
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.NamedBlocks Proofs.Consensus.Runs
open Proofs.Consensus.Carrier Proofs.Consensus.Signing Proofs.Consensus.FinalizedAccountable

/-! ## bodies を増やすハンドラ -/

theorem admitRow_bodies (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : NamedStore) (row : NamedAttestation) :
    (admitRow hc st row).bodies = st.bodies := by
  unfold admitRow
  dsimp only
  split_ifs <;> rfl

theorem admitRows_bodies (hc : Model.Consensus.Protocol.Grades.HealConfig) :
    ∀ (rows : List NamedAttestation) (st : NamedStore), (admitRows hc st rows).bodies = st.bodies
  | [], _ => rfl
  | row :: rows, st => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_bodies hc rows (admitRow hc st row)
    unfold admitRows at ih
    rw [ih, admitRow_bodies]

theorem admitCarried_bodies (adm : CarriedAdmission) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (before after : NamedStore) (b : NamedBlock) : (admitCarried adm hc before after b).bodies = after.bodies := by
  unfold admitCarried
  split_ifs
  · exact admitRows_bodies hc _ _
  · rfl

theorem commitBlock_bodies {before : NamedStore} {after : Store} {b : NamedBlock} {D : NamedBlock}
    (hD : D ∈ (commitBlock before after b).bodies.elems) : D ∈ before.bodies.elems ∨ D = b := by
  unfold commitBlock at hD
  dsimp only at hD
  split_ifs at hD
  · have hD' : D ∈ (before.bodies.insert b).elems := hD
    rw [mem_insert_iff nb_compare_eq_iff] at hD'
    rcases hD' with rfl | hD'
    · exact Or.inr rfl
    · exact Or.inl hD'
  · exact Or.inl hD

theorem processBlockCore_bodies (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    {st : NamedStore} {B D : NamedBlock} (hD : D ∈ (processBlockCore c p e hc cfg st B).bodies.elems) :
    D ∈ st.bodies.elems ∨ D = B := by
  unfold processBlockCore at hD
  split_ifs at hD
  · exact Or.inl hD
  · dsimp only at hD
    exact commitBlock_bodies hD

theorem onBlockWith_bodies (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) {st : NamedStore} {B D : NamedBlock}
    (hD : D ∈ (onBlockWith c p adm e hc cfg st B).bodies.elems) : D ∈ st.bodies.elems ∨ D = B := by
  unfold onBlockWith at hD
  rw [admitCarried_bodies] at hD
  exact processBlockCore_bodies c p e hc cfg hD

theorem receiptProcess_bodies (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {st : NamedStore} {o : NamedObject} {D : NamedBlock}
    (hD : D ∈ (receiptProcess c p s st o).bodies.elems) : D ∈ st.bodies.elems ∨ o = NamedObject.Block D := by
  cases o with
  | Block b =>
    rcases onBlockWith_bodies c p CarriedAdmission.AlsoCarried s.e s.hc s.cfg hD with h | rfl
    · exact Or.inl h
    · exact Or.inr rfl
  | GfVote u => exact Or.inl hD
  | Attest row =>
    left
    have h : (receiptProcess c p s st (NamedObject.Attest row)).bodies = st.bodies := admitRow_bodies s.hc st row
    rw [h] at hD
    exact hD

theorem nodeProcess_bodies (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} {o : NamedObject} {D : NamedBlock}
    (hD : D ∈ (nodeProcess c p s n o).st.bodies.elems) : D ∈ n.st.bodies.elems ∨ o = NamedObject.Block D :=
  receiptProcess_bodies c p s hD

theorem proposeBlockWith_bodies (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} {D : NamedBlock}
    (hD : D ∈ (proposeBlockWith c p nr cache e hc cfg nd st).1.bodies.elems) :
    D ∈ st.bodies.elems ∨ (proposeBlockWith c p nr cache e hc cfg nd st).2 = some D := by
  unfold proposeBlockWith at hD ⊢
  cases hm : proposalWith nr cache ProposalRowSource.PoolAndCarried e hc nd st with
  | none =>
    rw [hm] at hD
    exact Or.inl hD
  | some b =>
    rw [hm] at hD
    rcases onBlockWith_bodies c p CarriedAdmission.AlsoCarried e hc cfg hD with h | rfl
    · exact Or.inl h
    · exact Or.inr rfl

theorem namedGoldfishVoteWith_bodies (c : Nat → NaruStd.Set ValidatorId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) : (namedGoldfishVoteWith c cache e hc nd st).1.bodies = st.bodies := by
  unfold namedGoldfishVoteWith
  dsimp only

theorem namedUpdateConfirmationWith_bodies (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (st : NamedStore) (k : Nat) :
    (namedUpdateConfirmationWith cache e hc st k).bodies = st.bodies := rfl

theorem attestWith_bodies (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    (attestWith cache e hc nd st rec).1.bodies = st.bodies := by
  unfold attestWith
  dsimp only
  exact admitRow_bodies hc st _

/-- 1 tick で bodies に入るブロックは、元からあるか、その tick が出力したブロック。 -/
theorem tick_bodies (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : Model.Consensus.Protocol.ChainState.HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) (st : NamedStore)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) {D : NamedBlock}
    (hD : D ∈ (tick c p a nr cache e hc cfg nd st rec t).1.bodies.elems) :
    D ∈ st.bodies.elems ∨ NamedObject.Block D ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2 := by
  unfold tick at hD ⊢
  dsimp only at hD ⊢
  split_ifs at hD ⊢
  all_goals
    (try simp only [attestWith_bodies, namedUpdateConfirmationWith_bodies, namedGoldfishVoteWith_bodies] at hD)
  all_goals first
    | exact Or.inl hD
    | (rcases proposeBlockWith_bodies c p nr cache e hc cfg nd hD with hD | hD
       · exact Or.inl hD
       · right
         rw [hD]
         simp)

theorem nodeTick_bodies (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId) (n : NamedNodeState)
    (t : Int) {D : NamedBlock} (hD : D ∈ (nodeTick c p a nr s v n t).1.st.bodies.elems) :
    D ∈ n.st.bodies.elems ∨ NamedObject.Block D ∈ (nodeTick c p a nr s v n t).2 := by
  unfold nodeTick profileTick at hD ⊢
  dsimp only at hD ⊢
  exact tick_bodies c p a nr _ s.e s.hc s.cfg _ n.st n.signing t hD

/-! ## run の中で bodies に入ったブロックは処理されたブロック -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- `stateBefore i` のノード `u` の bodies の genesis でないブロックは、`u` がある時刻に処理した(`Processes`)ブロック。
手書き `Bridges.processes_block_of_mem_T`。 -/
theorem bodies_processed (u : ValidatorId) :
    ∀ (i : Nat) (X : NamedBlock), X ∈ (worldAt (stateBefore c p a nr s rho i) u).st.bodies.elems →
      X = NamedBlock.Genesis ∨ ∃ t, Processes c p a nr s rho u (NamedObject.Block X) t
  | 0, X, hX => by
    left
    have hX' : X ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hX
    exact (mem_singleton_iff _ _).mp hX'
  | i + 1, X, hX => by
    cases hev : rho.events[i]? with
    | none =>
      rw [stateBefore_succ_of_none c p a nr s rho hev] at hX
      exact bodies_processed u i X hX
    | some ev =>
      rw [stateBefore_succ_of_get c p a nr s rho hev] at hX
      cases ev with
      | Tick w t =>
        unfold worldStep at hX
        dsimp only at hX
        by_cases hwu : w = u
        · subst hwu
          rw [worldAt_insert_self] at hX
          rcases nodeTick_bodies c p a nr s w _ t hX with h | h
          · exact bodies_processed w i X h
          · exact Or.inr ⟨t, Or.inl ((emits_iff c p a nr s rho w _ t).mpr ⟨i, hev, h⟩)⟩
        · rw [worldAt_insert_ne _ _ _ _ hwu] at hX
          exact bodies_processed u i X hX
      | Deliver w o t =>
        unfold worldStep at hX
        dsimp only at hX
        by_cases hwu : w = u
        · subst hwu
          rw [worldAt_insert_self] at hX
          rcases nodeProcess_bodies c p s hX with h | rfl
          · exact bodies_processed w i X h
          · exact Or.inr ⟨t, Or.inr ⟨i, hev⟩⟩
        · rw [worldAt_insert_ne _ _ _ _ hwu] at hX
          exact bodies_processed u i X hX

end Run

/-! ## chain の行は名前付き祖先の行 -/

/-- 親について閉じた bodies は名前付き祖先について閉じている。手書き `ancestor_body_mem`。 -/
theorem ancestor_mem_bodies {st : NamedStore} (hclosed : ∀ D, D ∈ st.bodies.elems → namedParent D ∈ st.bodies.elems)
    {X : NamedBlock} : ∀ {D : NamedBlock}, D ∈ st.bodies.elems → namedPreceq X D = true → X ∈ st.bodies.elems
  | NamedBlock.Genesis, hD, hXD => by
    rw [namedPreceq_genesis hXD]
    exact hD
  | NamedBlock.Node p s r v sup rows i, hD, hXD => by
    simp only [namedPreceq, Bool.or_eq_true, beq_iff_eq] at hXD
    rcases hXD with rfl | hXD
    · exact hD
    · exact ancestor_mem_bodies hclosed (hclosed _ hD) hXD

/-- 消去した chain の attestation は、名前付き祖先のどれかの行の消去。手書き `named_mem_chain_attestations`。 -/
theorem chain_row_of_mem {x : CombinedAttestation} :
    ∀ {D : NamedBlock}, x ∈ (chainAttestations (eraseBlock D)).elems →
      ∃ X row, namedPreceq X D = true ∧ row ∈ namedAttestations X ∧ eraseAttestation row = x
  | NamedBlock.Genesis, h => by
    simp [eraseBlock, chainAttestations, NaruStd.Set.empty] at h
  | NamedBlock.Node p s r v sup rows i, h => by
    simp only [eraseBlock, chainAttestations] at h
    rw [mem_union_iff ca_compare_eq_iff] at h
    rcases h with h | h
    · rw [mem_toSet_iff ca_compare_eq_iff] at h
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp h
      exact ⟨NamedBlock.Node p s r v sup rows i, row, namedPreceq_self _, hrow, rfl⟩
    · obtain ⟨X, row, hX, hrow, hx⟩ := chain_row_of_mem h
      exact ⟨X, row, namedPreceq_node hX s r v sup rows i, hrow, hx⟩

/-- ブロックはその行を運ぶ(`Carries`)。 -/
theorem carries_attest {X : NamedBlock} {row : NamedAttestation} (hrow : row ∈ namedAttestations X) :
    Carries (NamedObject.Block X) (NamedObject.Attest row) := by
  dsimp only [Carries]
  right
  rw [List.any_eq_true]
  exact ⟨row, hrow, by simp⟩

/-! ## 本体 -/

/-- honest な `w` の署名の store の attestation は、`w` の tick が実際に出した行の消去。手書き `carriedByHonest_of_storeAt`。 -/
theorem attributed (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)
    (hcar : ∀ v o t, Processes c p a nr s rho v o t → ∀ o2, Carries o o2 →
      ∀ u, rho.honest.contains u = true ∧ author o2 = some u → ∃ t2, t2 ≤ t ∧ Emits c p a nr s rho u o2 t2)
    (hs : EventsSorted rho) (u : ValidatorId) (t : Int) {x : CombinedAttestation}
    (hx : (storeAttestations (storeAt c p a nr s rho u t).core).contains x = true) {w : ValidatorId}
    (hxw : x.valIndex = w) (hw : rho.honest.contains w = true) :
    ∃ (row : NamedAttestation) (i : Nat) (t' : Int), rho.events[i]? = some (NamedEvent.Tick w t') ∧
      NamedObject.Attest row ∈ (nodeTick c p a nr s w (worldAt (stateBefore c p a nr s rho i) w) t').2 ∧
      eraseAttestation row = x := by
  obtain ⟨i₀, hi₀⟩ := readAt_eq_stateBefore c p a nr s rho hs t
  unfold storeAt at hx
  rw [hi₀, contains_iff_mem ca_compare_eq_iff] at hx
  unfold storeAttestations at hx
  rw [mem_flatMap_iff ca_compare_eq_iff] at hx
  obtain ⟨B, hB, hxB⟩ := hx
  have hinv := stateBefore_inv c p a nr s rho i₀ u
  obtain ⟨D, hD, rfl⟩ := hinv.named B hB
  obtain ⟨X, row, hXD, hrow, rfl⟩ := chain_row_of_mem hxB
  have hX : X ∈ (worldAt (stateBefore c p a nr s rho i₀) u).st.bodies.elems := ancestor_mem_bodies hinv.closed hD hXD
  rcases bodies_processed c p a nr s rho u i₀ X hX with rfl | ⟨t', hproc⟩
  · simp [namedAttestations] at hrow
  · have hauthor : author (NamedObject.Attest row) = some w := congrArg Option.some hxw
    obtain ⟨t2, -, hem⟩ := hcar u (NamedObject.Block X) t' hproc (NamedObject.Attest row) (carries_attest hrow) w ⟨hw, hauthor⟩
    obtain ⟨i, hi, hmem⟩ := (emits_iff c p a nr s rho w _ t2).mp hem
    exact ⟨row, i, t2, hi, hmem, rfl⟩

end Proofs.Consensus.Attribution
