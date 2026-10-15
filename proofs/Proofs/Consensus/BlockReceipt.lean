import Proofs.Consensus.BlockStamps
import Proofs.Consensus.Attribution
import Mathlib.Tactic

/-!
# 受理の条件を満たす配送されたブロックは受信者の tree に入る(C71 の補題)

`Majority.HonestSupport.vote` に向けて、honest な提案のブロックが締切より前に honest な各ノードの tree に入ることを示す
層の入口。投票の側の `Delivery.mem_onGoldfishVote` / `deliver_gfVote_mem` に当たる。

ブロックの受理 `onBlockUsing`(`Model/Consensus/Protocol/Handlers.lean`)は 6 つの守りを持つ: ブロックの slot が受信者の slot
`st.s` 以下、まだ tree に無い、親が tree にある、確定のブロック `st.f` の子孫(`preceq st.f b`)、提案者が `proposer' (slot b)`、
親の slot が小さい。まだ tree に無いことを除く 5 つを `Admits` にまとめると、`Admits` の下で受理の後の tree に `b` がある
(既にあればそのまま、無ければ受理の分岐 `Carrier.acceptBody` が入れる: `onBlockUsing_mem_tree`)。名前付きの処理
`processBlockCore` はさらに名前付きの親が bodies にあることと、運ばれた attestation の round の守り
(`carriedAttestationsAdmissible`)を持ち、その下で消去したブロックが tree にある(`processBlockCore_mem_tree`)。tree に
新しく入ったなら `commitBlock` が名前付きのブロックを bodies に入れる(`processBlockCore_mem_bodies`)。運ばれた attestation の
取り込み `admitCarried` は tree のブロックを保存し(`BlockStamps.admitCarried_step`)bodies を変えない
(`Attribution.admitCarried_bodies`)ので、受信の処理 `onBlockWith` / `receiptProcess` でも同じ(`onBlockWith_mem_tree` /
`onBlockWith_mem_bodies`)。

run では、添字 `j` が `w` へのブロック `b` の配送で、配送の直前の `w` の store が上の条件を満たせば、`stateBefore (j + 1)` の
`w` の tree に `eraseBlock b` がある(`deliver_block_mem`。tree に無かったなら bodies に `b` がある: `deliver_block_mem_bodies`)。
`BlockStamps.tree_stamped` と合わせると、配送の時刻が `γ` より前なら、`j` より後のどの添字でも `w` の tree にあり受信の印が
`γ` より前(`deliver_block_stamped`)。

条件を run の事実から外すこと(受信者の slot が提案の slot 以上、親が先に届いていること、honest な提案が `st.f` の子孫であること、
提案者・attestation の round)は後続の層。`PartialSynchrony` の除外が外れること(`¬ excludes`)が与えるのは
`compatible st.f (eraseBlock b)` で、`preceq st.f b` より弱い。しかも `excludes` は締切の時刻の store(`stateBeforeTime … deadline`)で
評価され、配送の直前の store ではない。

手書きでは `DecoupledConsensusProofs/Protocol/Handlers/Blocks.lean` の `on_block` の受理の分岐と、`AdmittedBefore`
(名前付きのブロックが時刻 `Γ` より前に新しく受理される。この節の `deliver_block_mem_bodies` と `deliver_block_stamped` の組に近い)に当たる。
手書きは受信側のブロックの受理を明示の前提として立てる(`Protocol/Schedule/AdoptionTransport.lean` の冒頭の説明。
そこで呼ぶ `ResolvedTargetsAdmittedBefore` は説明の中の名前で、Lean の定義ではない)。
-/

namespace Proofs.Consensus.BlockReceipt

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Orders Proofs.Consensus.Sets Proofs.Consensus.Carrier

/-! ## 受理の条件 -/

/-- `onBlockUsing` の受理の守りのうち「まだ tree に無い」を除く 5 つ。 -/
structure Admits (p : Nat → ValidatorId) (st : Store) (b : Block) : Prop where
  slot_le : slot b ≤ st.s
  parent_mem : parent b ∈ st.tree.elems
  extends_f : preceq st.f b = true
  proposer : proposer? b = some (p (slot b))
  parent_slot : slot (parent b) < slot b

/-- **受理の条件の下で、受理の後の tree にブロックがある**(既にあればそのまま、無ければ受理の分岐が入れる)。 -/
theorem onBlockUsing_mem_tree (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) {st : Store} {b : Block}
    (build : ChainState → ChainState) (h : Admits p st b) : b ∈ (onBlockUsing c p st b build).tree.elems := by
  by_cases hb : b ∈ st.tree.elems
  · exact ((Proofs.Consensus.BlockStamps.onBlockUsing_step c p st b build).keep b hb).1
  · have hc1 : st.tree.contains b = false := by
      cases hx : st.tree.contains b with
      | false => rfl
      | true => exact absurd ((contains_iff_mem block_compare_eq_iff _ _).mp hx) hb
    have hc2 : st.tree.contains (parent b) = true := (contains_iff_mem block_compare_eq_iff _ _).mpr h.parent_mem
    have hs : decide (st.s < slot b) = false := decide_eq_false (by have := h.slot_le; omega)
    have hp : (proposer? b != some (p (slot b))) = false := by rw [h.proposer]; exact bne_self_eq_false _
    have hps : decide (slot (parent b) < slot b) = true := decide_eq_true h.parent_slot
    unfold onBlockUsing
    simp only [hs, hc1, hc2, h.extends_f, hp, hps, Bool.or_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    show b ∈ (acceptBody c st b _).tree.elems
    rw [acceptBody_tree, mem_insert_iff block_compare_eq_iff]
    exact Or.inl rfl

/-- 運ばれた attestation の round の守りが通れば、`onBlockCheckedUsing` は処理そのもの。 -/
theorem onBlockCheckedUsing_of_admissible (handle : Store → Store) (hc : HealConfig) (st : Store) {b : Block}
    (hca : carriedAttestationsAdmissible hc b = true) : onBlockCheckedUsing handle hc st b = handle st := by
  unfold onBlockCheckedUsing
  simp only [hca, ↓reduceIte]

/-! ## 名前付きのブロックの処理 -/

section Named

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv) (hc : HealConfig)
  (cfg : HeightConfig)

/-- **名前付きのブロックの処理**: 名前付きの親が bodies にあり、attestation の round の守りと受理の条件を満たせば、
消去したブロックは処理の後の tree にある。 -/
theorem processBlockCore_mem_tree {st : NamedStore} {b : NamedBlock} (hpar : namedParent b ∈ st.bodies.elems)
    (hca : carriedAttestationsAdmissible hc (eraseBlock b) = true) (h : Admits p st.core (eraseBlock b)) :
    eraseBlock b ∈ (processBlockCore c p e hc cfg st b).core.tree.elems := by
  have hpar' : st.bodies.contains (namedParent b) = true := (contains_iff_mem nb_compare_eq_iff _ _).mpr hpar
  unfold processBlockCore
  simp only [hpar', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [Proofs.Consensus.Stores.commitBlock_core, onBlockCheckedUsing_of_admissible _ hc _ hca]
  exact onBlockUsing_mem_tree c p _ h

/-- 処理の前の tree に無かったなら、処理の後の bodies に名前付きのブロックがある(`commitBlock` の受理)。 -/
theorem processBlockCore_mem_bodies {st : NamedStore} {b : NamedBlock} (hpar : namedParent b ∈ st.bodies.elems)
    (hca : carriedAttestationsAdmissible hc (eraseBlock b) = true) (h : Admits p st.core (eraseBlock b))
    (hnew : eraseBlock b ∉ st.core.tree.elems) : b ∈ (processBlockCore c p e hc cfg st b).bodies.elems := by
  have hin := processBlockCore_mem_tree c p e hc cfg hpar hca h
  have hpar' : st.bodies.contains (namedParent b) = true := (contains_iff_mem nb_compare_eq_iff _ _).mpr hpar
  have hnot : st.core.tree.contains (eraseBlock b) = false := by
    cases hx : st.core.tree.contains (eraseBlock b) with
    | false => rfl
    | true => exact absurd ((contains_iff_mem block_compare_eq_iff _ _).mp hx) hnew
  revert hin
  unfold processBlockCore
  simp only [hpar', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  intro hin
  rw [Proofs.Consensus.Stores.commitBlock_core] at hin
  rw [commitBlock_accept hnot ((contains_iff_mem block_compare_eq_iff _ _).mpr hin)]
  show b ∈ (st.bodies.insert b).elems
  rw [mem_insert_iff nb_compare_eq_iff]
  exact Or.inl rfl

/-- 受信の処理 `onBlockWith` でも tree にある(`admitCarried` は tree のブロックを保存する)。 -/
theorem onBlockWith_mem_tree (adm : CarriedAdmission) {st : NamedStore} {b : NamedBlock}
    (hpar : namedParent b ∈ st.bodies.elems) (hca : carriedAttestationsAdmissible hc (eraseBlock b) = true)
    (h : Admits p st.core (eraseBlock b)) : eraseBlock b ∈ (onBlockWith c p adm e hc cfg st b).core.tree.elems := by
  unfold onBlockWith
  exact ((Proofs.Consensus.BlockStamps.admitCarried_step adm hc st _ b).keep _
    (processBlockCore_mem_tree c p e hc cfg hpar hca h)).1

/-- 受信の処理 `onBlockWith` でも bodies にある(`admitCarried` は bodies を変えない)。 -/
theorem onBlockWith_mem_bodies (adm : CarriedAdmission) {st : NamedStore} {b : NamedBlock}
    (hpar : namedParent b ∈ st.bodies.elems) (hca : carriedAttestationsAdmissible hc (eraseBlock b) = true)
    (h : Admits p st.core (eraseBlock b)) (hnew : eraseBlock b ∉ st.core.tree.elems) :
    b ∈ (onBlockWith c p adm e hc cfg st b).bodies.elems := by
  unfold onBlockWith
  rw [Proofs.Consensus.Attribution.admitCarried_bodies]
  exact processBlockCore_mem_bodies c p e hc cfg hpar hca h hnew

end Named

/-- **配送されたブロックの受信の処理**(`receiptProcess` のブロックの腕)。 -/
theorem receiptProcess_block_mem_tree (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {st : NamedStore} {b : NamedBlock}
    (hpar : namedParent b ∈ st.bodies.elems) (hca : carriedAttestationsAdmissible s.hc (eraseBlock b) = true)
    (h : Admits p st.core (eraseBlock b)) :
    eraseBlock b ∈ (receiptProcess c p s st (NamedObject.Block b)).core.tree.elems :=
  onBlockWith_mem_tree c p s.e s.hc s.cfg _ hpar hca h

theorem receiptProcess_block_mem_bodies (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {st : NamedStore} {b : NamedBlock}
    (hpar : namedParent b ∈ st.bodies.elems) (hca : carriedAttestationsAdmissible s.hc (eraseBlock b) = true)
    (h : Admits p st.core (eraseBlock b)) (hnew : eraseBlock b ∉ st.core.tree.elems) :
    b ∈ (receiptProcess c p s st (NamedObject.Block b)).bodies.elems :=
  onBlockWith_mem_bodies c p s.e s.hc s.cfg _ hpar hca h hnew

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **添字 `j` の配送の後、受信者の tree にブロックがある**: 条件は配送の直前の `w` の store について。 -/
theorem deliver_block_mem {j : Nat} {w : ValidatorId} {b : NamedBlock} {t : Int}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block b) t))
    (hpar : namedParent b ∈ (worldAt (stateBefore c p a nr s rho j) w).st.bodies.elems)
    (hca : carriedAttestationsAdmissible s.hc (eraseBlock b) = true)
    (h : Admits p (worldAt (stateBefore c p a nr s rho j) w).st.core (eraseBlock b)) :
    eraseBlock b ∈ (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems := by
  rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hj]
  unfold worldStep
  dsimp only
  rw [Proofs.Consensus.Signing.worldAt_insert_self]
  exact receiptProcess_block_mem_tree c p s hpar hca h

/-- 配送の直前の tree に無かったなら、配送の後の bodies に名前付きのブロックがある(受信済み `processed`)。 -/
theorem deliver_block_mem_bodies {j : Nat} {w : ValidatorId} {b : NamedBlock} {t : Int}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block b) t))
    (hpar : namedParent b ∈ (worldAt (stateBefore c p a nr s rho j) w).st.bodies.elems)
    (hca : carriedAttestationsAdmissible s.hc (eraseBlock b) = true)
    (h : Admits p (worldAt (stateBefore c p a nr s rho j) w).st.core (eraseBlock b))
    (hnew : eraseBlock b ∉ (worldAt (stateBefore c p a nr s rho j) w).st.core.tree.elems) :
    b ∈ (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.bodies.elems := by
  rw [Proofs.Consensus.Signing.stateBefore_succ_of_get c p a nr s rho hj]
  unfold worldStep
  dsimp only
  rw [Proofs.Consensus.Signing.worldAt_insert_self]
  exact receiptProcess_block_mem_bodies c p s hpar hca h hnew

/-- **配送の時刻が `γ` より前なら、以後ずっと tree にあり受信の印が `γ` より前**(`BlockStamps.tree_stamped`)。 -/
theorem deliver_block_stamped (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    {j : Nat} {w : ValidatorId} {b : NamedBlock} {t γ : Int}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block b) t)) (htγ : t < γ)
    (hpar : namedParent b ∈ (worldAt (stateBefore c p a nr s rho j) w).st.bodies.elems)
    (hca : carriedAttestationsAdmissible s.hc (eraseBlock b) = true)
    (h : Admits p (worldAt (stateBefore c p a nr s rho j) w).st.core (eraseBlock b)) {i : Nat} (hji : j < i) :
    eraseBlock b ∈ (worldAt (stateBefore c p a nr s rho i) w).st.core.tree.elems ∧
      Model.Consensus.Objects.Time.occurrenceBefore
        ((worldAt (stateBefore c p a nr s rho i) w).st.core.timestampBlock.get? (eraseBlock b)) γ = true :=
  Proofs.Consensus.BlockStamps.tree_stamped c p a nr s rho hs hnn hj htγ
    (deliver_block_mem c p a nr s rho hj hpar hca h) hji

end Run

end Proofs.Consensus.BlockReceipt
