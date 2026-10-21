import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.TreeInv
import Proofs.Consensus.Attribution
import Mathlib.Tactic

/-!
# store の bodies は重複が無く、消去が単射(C77 の補題)

run の中のどの store でも、bodies のリストに重複が無く、消去 `eraseBlock` が bodies の上で単射である(`UniqueBodies`)。
- bodies を変えるのは `commitBlock` だけで、`b` を足すのは消去 `eraseBlock b` が前の tree に無いときだけ
  (`Model/Consensus/Protocol/Handlers.lean`)。前の bodies の消去はどれも前の tree にある(`Carrier.StoreInv.tree`)ので、
  `b` は前の bodies に無く(`TreeInv.nodup_insertSorted`)、前の bodies のどれとも消去が違う。
- 他のハンドラは bodies を変えない(`Attribution.lean` の `*_bodies`)。初期の bodies は `{Genesis}`。
したがって選んだ親 `parent` が bodies のどれかの消去なら、`parentBody?`(`findUnique?`)はその body を返す(`parentBody?_of_mem`)。
手書き `NamedStore.Coherent` の bodies の消去の単射性(`parent_body_eq_some` が使う)に当たる。run の root の衝突の無さ
(`NamedRootCollisionFree`)は使わない(周回 312)。
-/

namespace Proofs.Consensus.BodiesUnique

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.Runs Proofs.Consensus.Carrier
open Proofs.Consensus.Attribution

/-- store の bodies は重複が無く、消去が bodies の上で単射。 -/
def UniqueBodies (st : NamedStore) : Prop :=
  st.bodies.elems.Nodup ∧
    ∀ D, D ∈ st.bodies.elems → ∀ D', D' ∈ st.bodies.elems → eraseBlock D = eraseBlock D' → D = D'

theorem of_bodies_eq {st st' : NamedStore} (hb : st'.bodies = st.bodies) (h : UniqueBodies st) : UniqueBodies st' := by
  unfold UniqueBodies
  rw [hb]
  exact h

theorem initial_bodiesUnique : UniqueBodies initialNamedStore := by
  refine ⟨List.nodup_singleton _, ?_⟩
  intro D hD D' hD' _
  have hD1 : D ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hD
  have hD2 : D' ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hD'
  rw [mem_singleton_iff] at hD1 hD2
  rw [hD1, hD2]

/-- `commitBlock` は、前の bodies の消去が前の tree にあれば `UniqueBodies` を保つ。 -/
theorem commitBlock_bodiesUnique {before : NamedStore} {after : Store} {b : NamedBlock}
    (htree : ∀ D, D ∈ before.bodies.elems → eraseBlock D ∈ before.core.tree.elems) (h : UniqueBodies before) :
    UniqueBodies (commitBlock before after b) := by
  unfold commitBlock
  dsimp only
  split_ifs with hc
  · have hnot : eraseBlock b ∉ before.core.tree.elems := by
      intro hm
      have := (contains_iff_mem block_compare_eq_iff _ _).mpr hm
      simp [this] at hc
    have hb : b ∉ before.bodies.elems := fun hm => hnot (htree b hm)
    refine ⟨Proofs.Consensus.Trees.nodup_insertSorted nb_compare_eq_iff b h.1 hb, ?_⟩
    intro D hD D' hD' he
    have hD1 : D ∈ (before.bodies.insert b).elems := hD
    have hD2 : D' ∈ (before.bodies.insert b).elems := hD'
    rw [mem_insert_iff nb_compare_eq_iff] at hD1 hD2
    rcases hD1 with rfl | hD1 <;> rcases hD2 with rfl | hD2
    · rfl
    · exact absurd (he ▸ htree D' hD2) hnot
    · exact absurd (he.symm ▸ htree D hD1) hnot
    · exact h.2 D hD1 D' hD2 he
  · exact h

theorem processBlockCore_bodiesUnique (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) {st : NamedStore}
    (htree : ∀ D, D ∈ st.bodies.elems → eraseBlock D ∈ st.core.tree.elems) (h : UniqueBodies st) (B : NamedBlock) :
    UniqueBodies (processBlockCore c p e hc cfg st B) := by
  unfold processBlockCore
  split_ifs
  · exact h
  · dsimp only
    exact commitBlock_bodiesUnique htree h

theorem onBlockWith_bodiesUnique (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) {st : NamedStore}
    (htree : ∀ D, D ∈ st.bodies.elems → eraseBlock D ∈ st.core.tree.elems) (h : UniqueBodies st) (B : NamedBlock) :
    UniqueBodies (onBlockWith c p adm e hc cfg st B) := by
  unfold onBlockWith
  exact of_bodies_eq (admitCarried_bodies adm hc _ _ B) (processBlockCore_bodiesUnique c p e hc cfg htree h B)

theorem nodeProcess_bodiesUnique (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} (hinv : StoreInv s.e s.cfg n.st)
    (h : UniqueBodies n.st) (o : NamedObject) : UniqueBodies (nodeProcess c p s n o).st := by
  show UniqueBodies (receiptProcess c p s n.st o)
  cases o with
  | Block b => exact onBlockWith_bodiesUnique c p _ _ _ _ hinv.tree h b
  | GfVote u => exact h
  | Attest row => exact of_bodies_eq (admitRow_bodies s.hc n.st row) h

theorem proposeBlockWith_bodiesUnique (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (htree : ∀ D, D ∈ st.bodies.elems → eraseBlock D ∈ st.core.tree.elems) (h : UniqueBodies st) :
    UniqueBodies (proposeBlockWith c p nr cache e hc cfg nd st).1 := by
  unfold proposeBlockWith
  split
  · exact h
  · rename_i b _
    exact onBlockWith_bodiesUnique c p CarriedAdmission.AlsoCarried _ _ _ htree h b

/-- 1 tick の後の bodies は、前の bodies か、時計を合わせた store での提案の務めの後の bodies(他の務めは bodies を変えない)。 -/
theorem tick_bodies_cases (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache) (e : ProtocolEnv)
    (hc : Model.Consensus.Protocol.Grades.HealConfig) (cfg : HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    (st : NamedStore) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    (tick c p a nr cache e hc cfg nd st rec t).1.bodies = st.bodies ∨
      (tick c p a nr cache e hc cfg nd st rec t).1.bodies =
        (proposeBlockWith c p nr cache e hc cfg nd { st with core := { st.core with t := t, s := slotOf e t } }).1.bodies := by
  unfold tick
  dsimp only
  split_ifs
  all_goals
    (try simp only [attestWith_bodies, namedUpdateConfirmationWith_bodies, namedGoldfishVoteWith_bodies])
  all_goals first
    | exact Or.inl trivial
    | exact Or.inr trivial

theorem nodeTick_bodiesUnique (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId) {n : NamedNodeState}
    (hinv : StoreInv s.e s.cfg n.st) (h : UniqueBodies n.st) (t : Int) :
    UniqueBodies (nodeTick c p a nr s v n t).1.st := by
  unfold nodeTick profileTick
  dsimp only
  rcases tick_bodies_cases c p a nr _ s.e s.hc s.cfg _ n.st n.signing t with hb | hb
  · exact of_bodies_eq hb h
  · exact of_bodies_eq hb (proposeBlockWith_bodiesUnique c p nr _ s.e s.hc s.cfg _
      (st := { n.st with core := { n.st.core with t := t, s := slotOf s.e t } }) hinv.tree h)

/-! ## world -/

/-- world のどのノードの store も `UniqueBodies`。 -/
def WorldBodiesUnique (w : NamedWorld) : Prop := ∀ v, UniqueBodies (worldAt w v).st

theorem worldInit_bodiesUnique : WorldBodiesUnique worldInit := fun _ => initial_bodiesUnique

theorem worldStep_bodiesUnique (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup)
    {w : NamedWorld} (hinv : WorldInv s.e s.cfg w) (h : WorldBodiesUnique w) (ev : NamedEvent) :
    WorldBodiesUnique (worldStep c p a nr s w ev) := by
  intro v
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeTick_bodiesUnique c p a nr s u (hinv u) (h u) t
    · rw [hw]
      exact h v
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeProcess_bodiesUnique c p s (hinv u) (h u) o
    · rw [hw]
      exact h v

theorem foldl_worldStep_bodiesUnique (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) {w : NamedWorld}, WorldInv s.e s.cfg w → WorldBodiesUnique w →
      WorldBodiesUnique (List.foldl (fun w ev => worldStep c p a nr s w ev) w l)
  | [], _, _, h => h
  | ev :: l, _, hinv, h => by
    rw [List.foldl_cons]
    exact foldl_worldStep_bodiesUnique c p a nr s l (worldStep_inv c p a nr s hinv ev)
      (worldStep_bodiesUnique c p a nr s hinv h ev)

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- 時刻 `t` より前の event を畳んだ world のどのノードの store も `UniqueBodies`。 -/
theorem stateBeforeTime_bodiesUnique (t : Int) : WorldBodiesUnique (stateBeforeTime c p a nr s rho t) := by
  unfold stateBeforeTime
  exact foldl_worldStep_bodiesUnique c p a nr s _ (worldInit_inv s.e s.cfg) worldInit_bodiesUnique

end Run

/-! ## 親の body の検索 -/

/-- **bodies の消去は `parentBody?` で引ける**: `UniqueBodies` な store で、`D` が bodies にあれば、`parentBody? st (eraseBlock D)`
(`findUnique?`)は `D` を返す(条件を満たす要素は消去の単射性で `D` だけ、重複が無いので 1 つ)。 -/
theorem parentBody?_of_mem {st : NamedStore} (h : UniqueBodies st) {D : NamedBlock} (hD : D ∈ st.bodies.elems) :
    parentBody? st (eraseBlock D) = some D := by
  unfold parentBody? NaruStd.Set.findUnique?
  have hall : ∀ X ∈ st.bodies.elems.filter (fun b => eraseBlock b == eraseBlock D), X = D := by
    intro X hX
    obtain ⟨hX1, hXe⟩ := List.mem_filter.mp hX
    exact h.2 X hX1 D hD (beq_iff_eq.mp hXe)
  have hm : D ∈ st.bodies.elems.filter (fun b => eraseBlock b == eraseBlock D) :=
    List.mem_filter.mpr ⟨hD, beq_iff_eq.mpr rfl⟩
  have hl : st.bodies.elems.filter (fun b => eraseBlock b == eraseBlock D) = [D] := by
    have hnd := h.1.filter (fun b => eraseBlock b == eraseBlock D)
    generalize st.bodies.elems.filter (fun b => eraseBlock b == eraseBlock D) = l at hall hm hnd
    cases l with
    | nil => simp at hm
    | cons x rest =>
      have hx : x = D := hall x List.mem_cons_self
      subst hx
      cases rest with
      | nil => rfl
      | cons y rest' =>
        have hy : y = x := hall y (by simp)
        subst hy
        simp at hnd
  rw [hl]

/-- **提案は親の body を引ける**: tree の `j` / `f` が tree にあり(`TreeInv`)、tree の元が bodies の消去で(`StoreInv.named`)、
`UniqueBodies` な store では、提案の入力の親(fork choice の head。`ghost` の結果なので tree の元: `Trees.ghost_mem`)は bodies の
ある `D` の消去で、`parentBody?` は `D` を返すので `proposalWith` は `some`。手書き `NamedActions.runtime_proposal_some`。 -/
theorem proposalWith_isSome {nr : ValidatorId → Nat → BlockId} {cache : Model.Consensus.Protocol.Grades.Cache}
    {e : ProtocolEnv} {hc : Model.Consensus.Protocol.Grades.HealConfig} {cfg : HeightConfig}
    {nd : Model.Consensus.Protocol.Schedule.Node} {st : NamedStore} (hinv : StoreInv e cfg st)
    (hti : Proofs.Consensus.Trees.TreeInv st.core) (hu : UniqueBodies st) :
    ∃ B, proposalWith nr cache .PoolAndCarried e hc nd st = some B := by
  have hpar : (Model.Consensus.Protocol.Duties.Inputs.proposalInput nr cache e hc nd (storeToHealing st.core)).parent ∈
      st.core.tree.elems := by
    unfold Model.Consensus.Protocol.Duties.Inputs.proposalInput Model.Consensus.Protocol.ForkChoice.Head.getHeadWith
      Model.Consensus.Protocol.ForkChoice.Head.getHeadInTreeWithLayer
      Model.Consensus.Protocol.ForkChoice.Goldfish.goldfishForkChoice
    dsimp only
    exact Proofs.Consensus.Trees.ghost_mem hti.j hti.f _ _ _ _ _ _
  obtain ⟨D, hD, hDe⟩ := hinv.named _ hpar
  unfold proposalWith
  dsimp only
  rw [← hDe, parentBody?_of_mem hu hD]
  exact ⟨_, rfl⟩

end Proofs.Consensus.BodiesUnique
