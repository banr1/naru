import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.TreeInv
import Proofs.Consensus.Attribution
import Proofs.Consensus.Votes
import Proofs.Consensus.CarriedSupport
import Mathlib.Tactic

/-!
# store の tree のブロックの運ぶ投票の投票者は committee の要素(C71 / C77 の補題)

run の中のどの store でも、bodies の各名前付きブロック `D` の消去 `eraseBlock D` の運ぶ投票 `gfVotes` の投票者は、その投票の slot の
committee の要素(`BodiesCommittee`)。tree の各ブロックは bodies の消去(`Carrier.StoreInv.named`)なので、tree のブロックの運ぶ投票の
投票者も committee の要素(`stateBeforeTime_tree_committee`)。`CarriedSupport.lean`(周回 280)と同じ積み上げで、
- bodies が増えるのはブロックの配送か自分の提案だけ(`Attribution.lean` の `*_bodies`)。
- 配送のブロックは wire の検査 `wellFormed`(`Node.lean`)の第 3 の連言(運ぶ投票の投票者が `committee' u.slot` の要素)を通る
  (run の前提 `DeliveryWellFormed`)。
- 自分の提案は、運ぶ投票が提案者の生の view `proposerView`(バケツ `gfVotes[s − 1]`)なので、pool の不変条件 `Votes.PoolInv`
  (鍵の pool の投票は適格)から満たす(`proposalWith_committee`)。そのため world の不変条件は pool の不変条件と組にして運ぶ
  (`WorldCommittee`)。
- 初期の bodies は `{Genesis}` で、Genesis の運ぶ投票は空。
手書きでは `coreCarriedVoteCommittee`(`DecoupledConsensusProofs/Protocol/Schedule/WeakGoldfishCone.lean`: 配送は wire の検査、自分の
提案は `CommitteePools.stateBefore`)に当たり、`corePreparedVoteViewValid` の carried の部分を出すのに使う(周回 291)。
-/

namespace Proofs.Consensus.CarriedCommittee

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Schedule
open Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Tick
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Sets Proofs.Consensus.Runs Proofs.Consensus.Carrier Proofs.Consensus.Attribution
open Proofs.Consensus.Votes

/-- ブロックの運ぶ投票の投票者は、その投票の slot の committee の要素。 -/
def BlockCommittee (c : Nat → NaruStd.Set ValidatorId) (b : Block) : Prop :=
  ∀ u ∈ gfVotes b, (c u.slot).contains u.valIndex = true

/-- store の bodies の各ブロックの消去は `BlockCommittee`。 -/
def BodiesCommittee (c : Nat → NaruStd.Set ValidatorId) (st : NamedStore) : Prop :=
  ∀ D, D ∈ st.bodies.elems → BlockCommittee c (eraseBlock D)

theorem initial_bodiesCommittee (c : Nat → NaruStd.Set ValidatorId) : BodiesCommittee c initialNamedStore := by
  intro D hD
  have hD' : D ∈ (NaruStd.Set.singleton NamedBlock.Genesis).elems := hD
  rw [mem_singleton_iff] at hD'
  subst hD'
  intro u hu
  exact absurd hu (by simp [eraseBlock, gfVotes])

/-- honest な提案のブロックの運ぶ投票(`proposerView` = バケツ `gfVotes[s − 1]`)の投票者は、pool の不変条件の下で committee の要素。 -/
theorem proposalWith_committee {c : Nat → NaruStd.Set ValidatorId} {nr : ValidatorId → Nat → BlockId}
    {cache : Model.Consensus.Protocol.Grades.Cache}
    {src : ProposalRowSource} {e : Model.Consensus.Objects.Parameters.ProtocolEnv}
    {hc : Model.Consensus.Protocol.Grades.HealConfig} {nd : Model.Consensus.Protocol.Schedule.Node} {st : NamedStore}
    (hp : PoolInv c st.core) {D : NamedBlock} (h : proposalWith nr cache src e hc nd st = some D) :
    BlockCommittee c (eraseBlock D) := by
  unfold proposalWith at h
  dsimp only at h
  obtain ⟨parent, -, rfl⟩ := Option.map_eq_some_iff.mp h
  intro u hu
  simp only [eraseBlock, gfVotes] at hu
  unfold Model.Consensus.Protocol.Duties.Inputs.proposalInput Model.Consensus.Protocol.ForkChoice.Views.proposerView at hu
  exact (hp _ u hu).2

theorem proposeBlockWith_bodiesCommittee (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : BodiesCommittee c st) (hp : PoolInv c st.core) :
    BodiesCommittee c (proposeBlockWith c p nr cache e hc cfg nd st).1 := by
  intro D hD
  rcases proposeBlockWith_bodies c p nr cache e hc cfg nd hD with hD | hD
  · exact h D hD
  · exact proposalWith_committee hp (Proofs.Consensus.CarriedSupport.proposeBlockWith_some c p nr cache e hc cfg nd hD)

/-- 1 tick の務めは、pool の不変条件の下で `BodiesCommittee` を保つ(`CarriedSupport.tick_bodiesCarried` と同じ場合分け)。 -/
theorem tick_bodiesCommittee (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Model.Consensus.Protocol.Grades.Cache)
    (e : Model.Consensus.Objects.Parameters.ProtocolEnv) (hc : Model.Consensus.Protocol.Grades.HealConfig)
    (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : BodiesCommittee c st) (hp : PoolInv c st.core)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    BodiesCommittee c (tick c p a nr cache e hc cfg nd st rec t).1 := by
  intro D hD
  unfold tick at hD
  dsimp only at hD
  split_ifs at hD
  all_goals
    (try simp only [attestWith_bodies, namedUpdateConfirmationWith_bodies, namedGoldfishVoteWith_bodies] at hD)
  all_goals first
    | exact h D hD
    | exact proposeBlockWith_bodiesCommittee c p nr cache e hc cfg nd
        (st := { st with core := { st.core with t := t, s := Model.Consensus.Objects.Parameters.slotOf e t } }) h hp D hD

theorem nodeTick_bodiesCommittee (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup)
    (v : ValidatorId) {n : NamedNodeState} (h : BodiesCommittee c n.st) (hp : PoolInv c n.st.core) (t : Int) :
    BodiesCommittee c (nodeTick c p a nr s v n t).1.st := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_bodiesCommittee c p a nr _ s.e s.hc s.cfg _ h hp n.signing t

/-- 配送のブロックが committee の検査を満たせば、受信は `BodiesCommittee` を保つ。 -/
theorem nodeProcess_bodiesCommittee (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} (h : BodiesCommittee c n.st) {o : NamedObject}
    (ho : ∀ b, o = NamedObject.Block b → BlockCommittee c (eraseBlock b)) :
    BodiesCommittee c (nodeProcess c p s n o).st := by
  intro D hD
  rcases nodeProcess_bodies c p s hD with hD | hD
  · exact h D hD
  · exact ho D hD

/-! ## world -/

/-- world のどのノードの bodies も `BodiesCommittee` で、pool も不変条件を満たす。 -/
def WorldCommittee (c : Nat → NaruStd.Set ValidatorId) (w : NamedWorld) : Prop :=
  ∀ v, BodiesCommittee c (worldAt w v).st ∧ PoolInv c (worldAt w v).st.core

/-- event が配送するブロックは committee の検査を満たす。 -/
def EventCommittee (c : Nat → NaruStd.Set ValidatorId) (ev : NamedEvent) : Prop :=
  ∀ u b t, ev = NamedEvent.Deliver u (NamedObject.Block b) t → BlockCommittee c (eraseBlock b)

theorem worldInit_committee (c : Nat → NaruStd.Set ValidatorId) : WorldCommittee c worldInit :=
  fun v => ⟨initial_bodiesCommittee c, worldInit_pool c v⟩

theorem worldStep_committee (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup)
    {w : NamedWorld} (h : WorldCommittee c w) {ev : NamedEvent} (hev : EventCommittee c ev) :
    WorldCommittee c (worldStep c p a nr s w ev) := by
  intro v
  refine ⟨?_, (h v).2.of_poolExt (worldStep_poolExt c p a nr s w ev v)⟩
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeTick_bodiesCommittee c p a nr s u (h u).1 (h u).2 t
    · rw [hw]
      exact (h v).1
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeProcess_bodiesCommittee c p s (h u).1 fun b hb => hev u b t (by rw [hb])
    · rw [hw]
      exact (h v).1

theorem foldl_worldStep_committee (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) {w : NamedWorld}, (∀ ev ∈ l, EventCommittee c ev) → WorldCommittee c w →
      WorldCommittee c (List.foldl (fun w ev => worldStep c p a nr s w ev) w l)
  | [], _, _, h => h
  | ev :: l, _, hl, h => by
    rw [List.foldl_cons]
    exact foldl_worldStep_committee c p a nr s l (fun ev' hev' => hl ev' (List.mem_cons_of_mem _ hev'))
      (worldStep_committee c p a nr s h (hl ev List.mem_cons_self))

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- run の event が配送するブロックは committee の検査を満たす(`DeliveryWellFormed` の `wellFormed` の第 3 の連言)。 -/
theorem events_committee (hdw : DeliveryWellFormed c p a nr s rho) : ∀ ev ∈ rho.events, EventCommittee c ev := by
  intro ev hev u b t hb
  subst hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hev
  obtain ⟨⟨hwf, -⟩, -⟩ := hdw i u _ t hi
  unfold wellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  intro v hv
  exact List.all_eq_true.mp hwf.2 v hv

/-- 時刻 `t` より前の event を畳んだ world のどのノードの bodies も `BodiesCommittee`(pool の不変条件と組で)。 -/
theorem stateBeforeTime_committee (hdw : DeliveryWellFormed c p a nr s rho) (t : Int) :
    WorldCommittee c (stateBeforeTime c p a nr s rho t) := by
  unfold stateBeforeTime
  exact foldl_worldStep_committee c p a nr s _
    (fun ev hev => events_committee c p a nr s rho hdw ev (List.mem_filter.mp hev).1) (worldInit_committee c)

/-- **時刻 `t` より前の event を畳んだ world のどのノードの tree のブロックも、運ぶ投票の投票者がその投票の slot の committee の要素**
(`BodiesCommittee` と `StoreInv.named`。手書き `coreCarriedVoteCommittee`。周回 291)。 -/
theorem stateBeforeTime_tree_committee (hdw : DeliveryWellFormed c p a nr s rho) (t : Int) (x : ValidatorId) :
    ∀ b ∈ (worldAt (stateBeforeTime c p a nr s rho t) x).st.core.tree.elems, BlockCommittee c b := by
  intro b hb
  have hinv : StoreInv s.e s.cfg (worldAt (stateBeforeTime c p a nr s rho t) x).st := by
    unfold stateBeforeTime
    exact foldl_worldStep_inv c p a nr s _ (worldInit_inv s.e s.cfg) x
  obtain ⟨D, hD, rfl⟩ := hinv.named b hb
  exact (stateBeforeTime_committee c p a nr s rho hdw t x).1 D hD

/-- 時刻 `t` より前の event を畳んだ world のどのノードの pool も不変条件を満たす(run への前提なし)。 -/
theorem stateBeforeTime_pool (t : Int) (x : ValidatorId) :
    PoolInv c (worldAt (stateBeforeTime c p a nr s rho t) x).st.core := by
  unfold stateBeforeTime
  exact (worldInit_pool c x).of_poolExt (foldl_worldStep_poolExt c p a nr s _ _ x)

end Run

end Proofs.Consensus.CarriedCommittee
