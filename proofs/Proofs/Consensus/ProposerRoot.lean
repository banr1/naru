import Proofs.Consensus.ProposerReceipt
import Mathlib.Tactic

/-!
# 発行されたブロックは提案者の FG root を延ばす(C71 の補題)

`ProposerReceipt.partialSynchrony_emitted_block_mem_honest` に残る仮定 `hroot`(締切の読みの受信者の FG root がブロックの消去の
祖先)の、提案者の側の半分。`ProposerFinality` は提案されたブロックが提案者の `f` を延ばすことを示した。ここでは同じ筋を FG root
(`getFgRoot`: `hMax = hJ + 1` なら `j`、そうでなければ `f`)に強める。

- **fork choice**: filtered tree(`getFilteredBlockTreeFrom`)は `viableTree` を `preceq fgRoot` でさらに絞った集合なので、その要素は
  FG root を延ばす(`filtered_extends_fgRoot`)。anchor(`Grades.anchor`)は filtered tree の `activePrefix` か FG root そのものなので
  FG root を延ばし(`anchor_extends_fgRoot`)、head は anchor から `ghost` で辿った先(`getHeadWith_extends_fgRoot`)。`f ⪯ j` は
  要らない。
- **提案**: 提案されたブロックの親は head なので、ブロックは提案を作った store の FG root を延ばす(`proposalWith_extends_fgRoot`)。
  tick の時計合わせは `t` / `s` だけを変え、FG root が読む `f` / `j` / `hJ` / `hMax` を変えないので、tick が出すブロックは tick の
  直前の store の FG root を延ばす(`nodeTick_block_extends_fgRoot`)。run では発行の tick の直前の提案者の FG root
  (`emits_block_extends_fgRoot`)。
- **還元**: 締切の読みの honest な受信者の FG root が、発行の tick の直前の提案者の FG root の祖先なら、ブロックは締切の読みの
  受信者の tree にある(`partialSynchrony_emitted_block_mem_of_fgRoot`)。ただし受信者の FG root は提案者の FG root より新しい
  (`D` の祖先の、新しく justified になった `j` など)こともありうるので、この仮定は強すぎて示せない場合がある。
  もう 1 つの還元は、受信者の FG root がブロックの親(提案者の head)の祖先なら tree にある(`partialSynchrony_emitted_block_mem_of_parent`)。

手書きの対応: `HealingSurface.finalized_preceq_proposedParent`(`ProposalBridge.lean`)の `fgRoot ⪯ anchor ⪯ head` の部分。
手書きの `ProposalAdoptionNamedClosed.lean` は、すべての honest なノードの読みの FG root を共通の上界 `E` で抑え(`hreadBound`。
`hsourceRoot` はその提案者の読みへの当てはめ)、`E` が提案の親の祖先であることとつなぐ。`hreadBound` の中身は
`FGSafetyRootNamed.fgRoot_preceq_previousHead_through_confirmation_after_GST`(honest な読みの FG root ⪯ honest な投票の head)で、GST 後の
`fgSafetyProgressDeadline` 以後の読みについて、height の regime と `MultiProposerRecurrence` / `TimeoutDelayBound` から出る。その上界は残る。
-/

namespace Proofs.Consensus.ProposerRoot

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Duties.Inputs
open Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.ForkChoice.Goldfish Model.Consensus.Protocol.ForkChoice.Head Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Blocks Proofs.Consensus.Trees Proofs.Consensus.Runs

/-! ## fork choice の head は FG root を延ばす -/

/-- filtered tree の要素は FG root を延ばす(`preceq fgRoot` で絞っている)。 -/
theorem filtered_extends_fgRoot {hs : FGStore} {b : Block} (h : b ∈ (getFilteredBlockTree hs).elems) :
    preceq (getFgRoot hs) b = true := by
  unfold getFilteredBlockTree getFilteredBlockTreeFrom at h
  exact ((mem_filter_iff _ _ _).mp h).2

/-- anchor(filtered tree の `activePrefix` か FG root)は FG root を延ばす(前提なし)。 -/
theorem anchor_extends_fgRoot (e : ProtocolEnv) (hc : HealConfig) (hs : FGStore) (r : Nat)
    (g1 : Option (Option Block)) : preceq (getFgRoot hs) (anchor e hc hs r g1) = true := by
  unfold anchor
  cases g1 with
  | none => exact preceq_self _
  | some g =>
    cases g with
    | none => exact preceq_self _
    | some r' =>
      dsimp only
      cases hap : activePrefix (getFilteredBlockTree hs) r' with
      | some b =>
        simp only [Option.getD_some]
        exact filtered_extends_fgRoot (activePrefix_mem hap)
      | none =>
        simp only [Option.getD_none]
        exact preceq_self _

theorem getSgRootWith_extends_fgRoot (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (hs : FGStore) (r : Nat) :
    preceq (getFgRoot hs) (getSgRootWith c e hc hs r) = true :=
  anchor_extends_fgRoot e hc hs r _

/-- **fork choice の head は FG root を延ばす**(前提なし。anchor から `ghost` で辿る)。 -/
theorem getHeadWith_extends_fgRoot (c : Cache) (e : ProtocolEnv) (hc : HealConfig) (hs : FGStore)
    (votes sv : NaruStd.Set GoldfishVote) (k : Nat) :
    preceq (getFgRoot hs) (getHeadWith c e hc hs votes sv k) = true := by
  unfold getHeadWith getHeadInTreeWithLayer goldfishForkChoice
  dsimp only
  exact preceq_trans (getSgRootWith_extends_fgRoot c e hc hs _) (Proofs.Consensus.Goldfish.ghost_preceq _ _ _ _)

/-- **提案されたブロックは、提案を作った store の FG root を延ばす**: 消去したブロックの親は head(`proposalWith_parent`)。 -/
theorem proposalWith_extends_fgRoot (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore}
    {b : NamedBlock} (hb : proposalWith nr cache .PoolAndCarried e hc nd st = some b) :
    preceq (getFgRoot (storeToHealing st.core)) (eraseBlock b) = true := by
  have hpar := (Proofs.Consensus.Proposal.proposalWith_parent nr cache e hc nd st hb).2
  have hhead : preceq (getFgRoot (storeToHealing st.core))
      (proposalInput nr cache e hc nd (storeToHealing st.core)).parent = true :=
    getHeadWith_extends_fgRoot cache e hc (storeToHealing st.core) _ _ _
  rw [← hpar, ← Proofs.Consensus.NamedBlocks.parent_eraseBlock] at hhead
  exact preceq_trans hhead (Proofs.Consensus.Goldfish.preceq_parent _)

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- tick が出すブロックは、その tick の直前の store の FG root を延ばす(時計合わせは `f` / `j` / `hJ` / `hMax` を変えない)。 -/
theorem nodeTick_block_extends_fgRoot (v : ValidatorId) (n : NamedNodeState) (t : Int) {D : NamedBlock}
    (hD : NamedObject.Block D ∈ (nodeTick c p a nr s v n t).2) :
    preceq (getFgRoot (storeToHealing n.st.core)) (eraseBlock D) = true := by
  rw [Proofs.Consensus.Signing.nodeTick_out] at hD
  obtain ⟨-, -, -, hp⟩ := Proofs.Consensus.Proposal.tick_block_shape c p a nr _ s.e s.hc s.cfg _ n.st n.signing t hD
  exact proposalWith_extends_fgRoot nr _ s.e s.hc _
    (st := { n.st with core := { n.st.core with t := t, s := slotOf s.e t } }) hp

/-- **発行されたブロックは、発行した tick の直前の提案者の FG root を延ばす**(前提なし)。 -/
theorem emits_block_extends_fgRoot {v : ValidatorId} {D : NamedBlock} {t : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) :
    ∃ i, rho.events[i]? = some (NamedEvent.Tick v t) ∧
      preceq (getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core)) (eraseBlock D) = true := by
  obtain ⟨i, hi, ho⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t).mp hem
  exact ⟨i, hi, nodeTick_block_extends_fgRoot c p a nr s v _ t ho⟩

/-- **締切の読みの受信者の FG root の仮定を、FG root どうしの順序に還元する**: honest な `v` が時刻 `t` に発行したブロック `D` は、
honest な `w` の締切 `max t tGST + Δ`(horizon 以内)の時刻の読みの FG root が、`Tick v t` に当たるどの添字 `i` の直前の提案者 `v` の
FG root の祖先でもあれば、その読みの tree にある(`w = v` も可)。 -/
theorem partialSynchrony_emitted_block_mem_of_fgRoot (hps : PartialSynchrony c p a nr s rho)
    (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho) (hδ : 0 < s.e.delta)
    (hnd : EventsNodup rho) {v w : ValidatorId} {D : NamedBlock} {t : Int}
    (hv : rho.honest.contains v = true) (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) (hd : max t s.e.tGST + s.e.delta ≤ rho.horizon)
    (hroot : ∀ i, rho.events[i]? = some (NamedEvent.Tick v t) →
      preceq (getFgRoot (storeToHealing
          (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core))
        (getFgRoot (storeToHealing (worldAt (stateBefore c p a nr s rho i) v).st.core)) = true) :
    eraseBlock D ∈
      (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core.tree.elems := by
  obtain ⟨i, hi, hext⟩ := emits_block_extends_fgRoot c p a nr s rho hem
  exact Proofs.Consensus.ProposerReceipt.partialSynchrony_emitted_block_mem_honest c p a nr s rho hps hsch hdw hδ hnd
    hv hem hw hd (preceq_trans (hroot i hi) hext)

/-- **締切の読みの受信者の FG root の仮定を、提案の親(提案者の head)での上界に還元する**: 締切の読みの honest な `w` の FG root が
`D` の消去の親の祖先なら、その読みの tree にある(`w = v` も可)。手書きの筋(すべての honest な読みの FG root ⪯ 共通の上界 `E` ⪯ 提案の親)
はこの形で使う。 -/
theorem partialSynchrony_emitted_block_mem_of_parent (hps : PartialSynchrony c p a nr s rho)
    (hsch : ScheduleWellFormed s rho) (hdw : DeliveryWellFormed c p a nr s rho) (hδ : 0 < s.e.delta)
    (hnd : EventsNodup rho) {v w : ValidatorId} {D : NamedBlock} {t : Int}
    (hv : rho.honest.contains v = true) (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) (hd : max t s.e.tGST + s.e.delta ≤ rho.horizon)
    (hroot : preceq (getFgRoot (storeToHealing
        (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core))
      (parent (eraseBlock D)) = true) :
    eraseBlock D ∈
      (worldAt (stateBeforeTime c p a nr s rho (max t s.e.tGST + s.e.delta)) w).st.core.tree.elems :=
  Proofs.Consensus.ProposerReceipt.partialSynchrony_emitted_block_mem_honest c p a nr s rho hps hsch hdw hδ hnd
    hv hem hw hd (preceq_trans hroot (Proofs.Consensus.Goldfish.preceq_parent _))

end Run

end Proofs.Consensus.ProposerRoot
