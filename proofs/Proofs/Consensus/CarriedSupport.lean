import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.TreeInv
import Proofs.Consensus.Attribution
import Mathlib.Tactic

/-!
# store の tree のブロックの運ぶ支持の投票は運ぶ投票に含まれる(C71 / C77 の補題)

run の中のどの store でも、bodies の各名前付きブロック `D` の消去 `eraseBlock D` は受理の検査 `carriedSupportWellFormed`
(`gfSupportVotes ⊆ gfVotes`。`Model/Consensus/Protocol/Schedule.lean`)を満たす(`BodiesCarried`)。tree の各ブロックは bodies の
消去(`Carrier.StoreInv.named`)なので、tree のブロックの運ぶ支持の投票は運ぶ投票に含まれる(`stateBeforeTime_tree_carried`)。
- bodies が増えるのはブロックの配送か自分の提案だけ(`Attribution.lean` の `*_bodies`)。
- 配送のブロックは wire の検査 `wellFormed`(`Node.lean`)を通る(run の前提 `DeliveryWellFormed`)。
- 自分の提案は、運ぶ投票が提案者の生の view `proposerView`(バケツ `gfVotes[s − 1]`)、運ぶ支持の投票がその解決できる票の部分列
  `proposerSupportView` なので、組み立てから満たす(`proposalWith_carried`)。
- 初期の bodies は `{Genesis}` で、Genesis の運ぶ投票は空。
`AvailableHoles.voteDutyHead_passes_supporter_majority_of_carried` の前提 `hcar` を外すのに使う(周回 280)。
-/

namespace Proofs.Consensus.CarriedSupport

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Schedule
open Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Sets Proofs.Consensus.Runs Proofs.Consensus.Carrier Proofs.Consensus.Attribution

/-- store の bodies の各ブロックの消去は、運ぶ支持の投票が運ぶ投票に含まれる。 -/
def BodiesCarried (st : NamedStore) : Prop :=
  ∀ D, D ∈ st.bodies.elems → carriedSupportWellFormed (eraseBlock D) = true

/-- `carriedSupportWellFormed` を所属の形にする。 -/
theorem carried_mem {b : Block} (h : carriedSupportWellFormed b = true) : ∀ u ∈ gfSupportVotes b, u ∈ gfVotes b := by
  intro u hu
  unfold carriedSupportWellFormed at h
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h u hu)

theorem initial_bodiesCarried : BodiesCarried initialNamedStore := by
  intro D hD
  have hD' : D ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hD
  rw [mem_singleton_iff] at hD'
  subst hD'
  rfl

/-- honest な提案のブロックは、運ぶ支持の投票(`proposerSupportView` = バケツの解決できる票)が運ぶ投票(`proposerView` = バケツ)に
含まれる。 -/
theorem proposalWith_carried {nr : ValidatorId → Nat → BlockId} {cache : Model.Consensus.Protocol.Grades.Cache}
    {src : ProposalRowSource} {e : Model.Consensus.Objects.Parameters.ProtocolEnv}
    {hc : Model.Consensus.Protocol.Grades.HealConfig} {nd : Model.Consensus.Protocol.Schedule.Node} {st : NamedStore}
    {D : NamedBlock} (h : proposalWith nr cache src e hc nd st = some D) :
    carriedSupportWellFormed (eraseBlock D) = true := by
  unfold proposalWith at h
  dsimp only at h
  obtain ⟨parent, -, rfl⟩ := Option.map_eq_some_iff.mp h
  unfold carriedSupportWellFormed
  simp only [eraseBlock, gfSupportVotes, gfVotes]
  unfold Model.Consensus.Protocol.Duties.Inputs.proposalInput
    Model.Consensus.Protocol.ForkChoice.Views.proposerSupportView Model.Consensus.Protocol.ForkChoice.Views.proposerView
  dsimp only
  rw [List.all_eq_true]
  intro u hu
  exact List.contains_iff_mem.mpr (List.mem_filter.mp hu).1

/-- 提案の務めの出したブロックは `proposalWith` の結果。 -/
theorem proposeBlockWith_some (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} {D : NamedBlock} (h : (proposeBlockWith c p nr cache e hc cfg nd st).2 = some D) :
    proposalWith nr cache ProposalRowSource.PoolAndCarried e hc nd st = some D := by
  unfold proposeBlockWith at h
  cases hm : proposalWith nr cache ProposalRowSource.PoolAndCarried e hc nd st with
  | none =>
    rw [hm] at h
    exact absurd h (by simp)
  | some b =>
    rw [hm] at h
    exact h

theorem proposeBlockWith_bodiesCarried (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : BodiesCarried st) : BodiesCarried (proposeBlockWith c p nr cache e hc cfg nd st).1 := by
  intro D hD
  rcases proposeBlockWith_bodies c p nr cache e hc cfg nd hD with hD | hD
  · exact h D hD
  · exact proposalWith_carried (proposeBlockWith_some c p nr cache e hc cfg nd hD)

/-- 1 tick の務めは `BodiesCarried` を保つ(`Attribution.tick_bodies` と同じ場合分け)。 -/
theorem tick_bodiesCarried (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : BodiesCarried st) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    BodiesCarried (tick c p a nr cache e hc cfg nd st rec t).1 := by
  intro D hD
  unfold tick at hD
  dsimp only at hD
  split_ifs at hD
  all_goals
    (try simp only [attestWith_bodies, namedUpdateConfirmationWith_bodies, namedGoldfishVoteWith_bodies] at hD)
  all_goals first
    | exact h D hD
    | exact proposeBlockWith_bodiesCarried c p nr cache e hc cfg nd 
        (st := { st with core := { st.core with t := t, s := Model.Consensus.Objects.Parameters.slotOf e t } }) h D hD

theorem nodeTick_bodiesCarried (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup)
    (v : ValidatorId) {n : NamedNodeState} (h : BodiesCarried n.st) (t : Int) :
    BodiesCarried (nodeTick c p a nr s v n t).1.st := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_bodiesCarried c p a nr _ s.e s.hc s.cfg _ h n.signing t

/-- 配送のブロックが受理の検査を満たせば、受信は `BodiesCarried` を保つ。 -/
theorem nodeProcess_bodiesCarried (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} (h : BodiesCarried n.st) {o : NamedObject}
    (ho : ∀ b, o = NamedObject.Block b → carriedSupportWellFormed (eraseBlock b) = true) :
    BodiesCarried (nodeProcess c p s n o).st := by
  intro D hD
  rcases nodeProcess_bodies c p s hD with hD | hD
  · exact h D hD
  · exact ho D hD

/-! ## world -/

/-- world のどのノードの bodies も `BodiesCarried`。 -/
def WorldBodiesCarried (w : NamedWorld) : Prop := ∀ v, BodiesCarried (worldAt w v).st

/-- event が配送するブロックは受理の検査を満たす。 -/
def EventCarried (ev : NamedEvent) : Prop :=
  ∀ u b t, ev = NamedEvent.Deliver u (NamedObject.Block b) t → carriedSupportWellFormed (eraseBlock b) = true

theorem worldInit_bodiesCarried : WorldBodiesCarried worldInit := fun _ => initial_bodiesCarried

theorem worldStep_bodiesCarried (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup)
    {w : NamedWorld} (h : WorldBodiesCarried w) {ev : NamedEvent} (hev : EventCarried ev) :
    WorldBodiesCarried (worldStep c p a nr s w ev) := by
  intro v
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeTick_bodiesCarried c p a nr s u (h u) t
    · rw [hw]
      exact h v
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeProcess_bodiesCarried c p s (h u) fun b hb => hev u b t (by rw [hb])
    · rw [hw]
      exact h v

theorem foldl_worldStep_bodiesCarried (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) {w : NamedWorld}, (∀ ev ∈ l, EventCarried ev) → WorldBodiesCarried w →
      WorldBodiesCarried (List.foldl (fun w ev => worldStep c p a nr s w ev) w l)
  | [], _, _, h => h
  | ev :: l, _, hl, h => by
    rw [List.foldl_cons]
    exact foldl_worldStep_bodiesCarried c p a nr s l (fun ev' hev' => hl ev' (List.mem_cons_of_mem _ hev'))
      (worldStep_bodiesCarried c p a nr s h (hl ev List.mem_cons_self))

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- run の event が配送するブロックは受理の検査を満たす(`DeliveryWellFormed` の `wellFormed`)。 -/
theorem events_carried (hdw : DeliveryWellFormed c p a nr s rho) : ∀ ev ∈ rho.events, EventCarried ev := by
  intro ev hev u b t hb
  subst hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hev
  obtain ⟨⟨hwf, -⟩, -⟩ := hdw i u _ t hi
  unfold wellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  exact hwf.1.2

/-- 時刻 `t` より前の event を畳んだ world のどのノードの bodies も `BodiesCarried`。 -/
theorem stateBeforeTime_bodiesCarried (hdw : DeliveryWellFormed c p a nr s rho) (t : Int) :
    WorldBodiesCarried (stateBeforeTime c p a nr s rho t) := by
  unfold stateBeforeTime
  exact foldl_worldStep_bodiesCarried c p a nr s _
    (fun ev hev => events_carried c p a nr s rho hdw ev (List.mem_filter.mp hev).1) worldInit_bodiesCarried

/-- **時刻 `t` より前の event を畳んだ world のどのノードの tree のブロックも、運ぶ支持の投票が運ぶ投票に含まれる**
(`BodiesCarried` と `StoreInv.named`。周回 280)。 -/
theorem stateBeforeTime_tree_carried (hdw : DeliveryWellFormed c p a nr s rho) (t : Int) (x : ValidatorId) :
    ∀ b ∈ (worldAt (stateBeforeTime c p a nr s rho t) x).st.core.tree.elems, ∀ u ∈ gfSupportVotes b, u ∈ gfVotes b := by
  intro b hb
  have hinv : StoreInv s.e s.cfg (worldAt (stateBeforeTime c p a nr s rho t) x).st := by
    unfold stateBeforeTime
    exact foldl_worldStep_inv c p a nr s _ (worldInit_inv s.e s.cfg) x
  obtain ⟨D, hD, rfl⟩ := hinv.named b hb
  exact carried_mem (stateBeforeTime_bodiesCarried c p a nr s rho hdw t x D hD)

end Run

end Proofs.Consensus.CarriedSupport
