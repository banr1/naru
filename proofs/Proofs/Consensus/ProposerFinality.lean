import Proofs.Consensus.DeliveredBlock
import Proofs.Consensus.TreeInv
import Proofs.Consensus.Goldfish
import Proofs.Consensus.Stores
import Mathlib.Tactic

/-!
# 発行されたブロックは提案者の finalized を延ばす(C71 の補題)

`DeliveredBlock.deliver_emitted_block_mem` に残る受理の守り `extends_f`(`preceq st.f b`)の、提案者の側の半分。
提案の務め `proposalWith`(`Model/Consensus/Protocol/Duties/Proposals.lean`)の親は fork choice の head
`getHeadWith`(`ForkChoice/Head.lean`)で、head は anchor から `ghost` で辿った先(`Goldfish.ghost_preceq`)。anchor
(`Grades.anchor`)は filtered tree の `activePrefix` か `getFgRoot`(`j` か `f`)で、filtered tree は `finalizedDescendants f`
で絞った集合なので、その要素はどれも `f` を延ばす(`filtered_extends`)。したがって `f ⪯ j` の下で `f ⪯ head`
(`getHeadWith_extends`)、提案されたブロックは `f` を延ばす(`proposalWith_extends`)。

`f ⪯ j`(`FJ`)は store の不変条件で、前提は要らない: `f` / `j` を書くのは `updateFinality` だけで、`j := σ.j` の分岐の守りに
`preceq afterMax.f σ.j`、`f := σ.f` の分岐の守りに `preceq σ.f afterJustification.j` が入っている(`updateFinality_fj`)。
他のハンドラは `f` / `j` を変えない(`Trees.SameOut`)。初期 store は両方 `Genesis`。`Stores.lean` と同じ順に
`Store` → `NamedStore` → tick → world → `readAt` / `stateBefore` と積み上げる(`stateBefore_fj` / `readAt_fj`)。

run では、tick が発行したブロックはその tick の直前の提案者の `f` を延ばす(`emits_block_extends`)。受信者の `f` が
その `f` の祖先なら `extends_f` が出るので、`deliver_emitted_block_mem` の仮定 `hf` はこの形に還元できる
(`deliver_emitted_block_mem_of_finalized`)。残るのは、honest な受信者の確定のブロックが提案者の確定のブロックの祖先であること
(finality の事実)。

手書き `HealingSurface.finalized_preceq_proposedParent`(`ProposalBridge.lean`。`F ⪯ fgRoot ⪯ anchor ⪯ head` で、`F ⪯ fgRoot` は `F ⪯ J` から)と
`NamedStoreBridge.finalized_preceq_justified_stateBeforeTime`(`StoreBridge.lean`)に当たる。手書きは `fgRoot ⪯ anchor` を通るが、ここでは anchor が
filtered tree の要素なら `filtered_extends` を直接使い、`fgRoot ⪯ anchor` を経由しない。
-/

namespace Proofs.Consensus.ProposerFinality

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.ChainState Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Duties.Inputs
open Model.Consensus.Protocol.Tick
open Model.Consensus.Protocol.ForkChoice.Goldfish Model.Consensus.Protocol.ForkChoice.Head Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions
open Proofs.Consensus.Blocks Proofs.Consensus.Trees Proofs.Consensus.Runs

/-! ## fork choice の head は `f` を延ばす -/

/-- filtered tree の要素は `f` を延ばす(`finalizedDescendants f` で絞っている)。 -/
theorem filtered_extends {hs : FGStore} {b : Block} (h : b ∈ (getFilteredBlockTree hs).elems) :
    preceq hs.f b = true := by
  unfold getFilteredBlockTree getFilteredBlockTreeFrom viableTree finalizedDescendants at h
  exact ((mem_filter_iff _ _ _).mp ((mem_filter_iff _ _ _).mp ((mem_filter_iff _ _ _).mp h).1).1).2

/-- `f ⪯ j` なら FG root(`j` か `f`)は `f` を延ばす。 -/
theorem fgRoot_extends {hs : FGStore} (h : preceq hs.f hs.j = true) : preceq hs.f (getFgRoot hs) = true := by
  rcases getFgRoot_cases hs with he | he <;> rw [he]
  · exact h
  · exact preceq_self _

/-- anchor(filtered tree の `activePrefix` か FG root)は `f` を延ばす。 -/
theorem anchor_extends (e : ProtocolEnv) (hc : HealConfig) {hs : FGStore} (h : preceq hs.f hs.j = true) (r : Nat)
    (g1 : Option (Option Block)) : preceq hs.f (anchor e hc hs r g1) = true := by
  unfold anchor
  cases g1 with
  | none => exact fgRoot_extends h
  | some g =>
    cases g with
    | none => exact fgRoot_extends h
    | some r' =>
      dsimp only
      cases hap : activePrefix (getFilteredBlockTree hs) r' with
      | some b =>
        simp only [Option.getD_some]
        exact filtered_extends (activePrefix_mem hap)
      | none =>
        simp only [Option.getD_none]
        exact fgRoot_extends h

theorem getSgRootWith_extends (c : Cache) (e : ProtocolEnv) (hc : HealConfig) {hs : FGStore}
    (h : preceq hs.f hs.j = true) (r : Nat) : preceq hs.f (getSgRootWith c e hc hs r) = true :=
  anchor_extends e hc h r _

/-- **fork choice の head は `f` を延ばす**(`f ⪯ j` の下で。anchor から `ghost` で辿る)。 -/
theorem getHeadWith_extends (c : Cache) (e : ProtocolEnv) (hc : HealConfig) {hs : FGStore}
    (h : preceq hs.f hs.j = true) (votes sv : NaruStd.Set GoldfishVote) (k : Nat) :
    preceq hs.f (getHeadWith c e hc hs votes sv k) = true := by
  unfold getHeadWith getHeadInTreeWithLayer goldfishForkChoice
  dsimp only
  exact preceq_trans (getSgRootWith_extends c e hc h _) (Proofs.Consensus.Goldfish.ghost_preceq _ _ _ _)

/-- **提案されたブロックは提案者の `f` を延ばす**(`f ⪯ j` の下で): 消去したブロックの親は head(`proposalWith_parent`)。 -/
theorem proposalWith_extends (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (h : preceq st.core.f st.core.j = true)
    {b : NamedBlock} (hb : proposalWith nr cache .PoolAndCarried e hc nd st = some b) :
    preceq st.core.f (eraseBlock b) = true := by
  have hpar := (Proofs.Consensus.Proposal.proposalWith_parent nr cache e hc nd st hb).2
  have hhead : preceq st.core.f (proposalInput nr cache e hc nd (storeToHealing st.core)).parent = true :=
    getHeadWith_extends cache e hc (hs := storeToHealing st.core) h _ _ _
  rw [← hpar, ← Proofs.Consensus.NamedBlocks.parent_eraseBlock] at hhead
  exact preceq_trans hhead (Proofs.Consensus.Goldfish.preceq_parent _)

/-! ## 不変条件 `f ⪯ j` -/

/-- finalized は justified の祖先。 -/
def FJ (st : Store) : Prop := preceq st.f st.j = true

theorem FJ.of_eq {st st' : Store} (h : FJ st) (hf : st'.f = st.f) (hj : st'.j = st.j) : FJ st' := by
  unfold FJ
  rw [hf, hj]
  exact h

theorem FJ.congr {st st' : Store} (h : FJ st) (hs : SameOut st' st) : FJ st' := h.of_eq hs.f hs.j

theorem initial_fj : FJ initStore := preceq_self _

/-- **`updateFinality` は `f ⪯ j` を保つ**: `j` を変える分岐の守りに `preceq afterMax.f σ.j`、`f` を変える分岐の守りに
`preceq σ.f afterJustification.j` が入っている。 -/
theorem updateFinality_fj {st : Store} (h : FJ st) (σ : ChainState) : FJ (updateFinality st σ) := by
  unfold FJ at h ⊢
  unfold updateFinality
  dsimp only
  split_ifs with h1 h2 h3
  all_goals first
    | exact h
    | exact (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp h2).1).2
    | exact (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp h3).1).2
    | exact (Bool.and_eq_true _ _ |>.mp h1).1

theorem onBlockUsing_fj (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) {st : Store} (h : FJ st) (b : Block)
    (build : ChainState → ChainState) : FJ (onBlockUsing c p st b build) := by
  unfold onBlockUsing
  split_ifs
  · exact h
  · exact h
  · exact h
  · exact h
  · refine updateFinality_fj (h.of_eq ?_ ?_) _
    · exact (foldl_out _ (fun s u => onGoldfishVoteChecked_out c s u) _ _).f
    · exact (foldl_out _ (fun s u => onGoldfishVoteChecked_out c s u) _ _).j

theorem onBlockCheckedUsing_fj (handle : Store → Store) (hh : ∀ s, FJ s → FJ (handle s)) (hc : HealConfig)
    {st : Store} (h : FJ st) (b : Block) : FJ (onBlockCheckedUsing handle hc st b) := by
  unfold onBlockCheckedUsing
  split_ifs
  · exact hh st h
  · exact h

theorem processBlockCore_fj (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (e : ProtocolEnv)
    (hc : HealConfig) (cfg : HeightConfig) {st : NamedStore} (h : FJ st.core) (b : NamedBlock) :
    FJ (processBlockCore c p e hc cfg st b).core := by
  unfold processBlockCore
  dsimp only
  split_ifs
  · exact h
  · rw [Proofs.Consensus.Stores.commitBlock_core]
    exact onBlockCheckedUsing_fj _ (fun _ hcur => onBlockUsing_fj c p hcur _ _) hc h _

theorem admitRow_fj (hc : HealConfig) {st : NamedStore} (h : FJ st.core) (row : NamedAttestation) :
    FJ (admitRow hc st row).core := by
  unfold admitRow
  dsimp only
  split_ifs <;> exact h.congr (onSgVote_out hc st.core _)

theorem admitRows_fj (hc : HealConfig) :
    ∀ (rows : List NamedAttestation) {st : NamedStore}, FJ st.core → FJ (admitRows hc st rows).core
  | [], _, h => h
  | row :: rows, st, h => by
    unfold admitRows
    rw [List.foldl_cons]
    have ih := admitRows_fj hc rows (admitRow_fj hc h row)
    unfold admitRows at ih
    exact ih

theorem admitCarried_fj (adm : CarriedAdmission) (hc : HealConfig) (before : NamedStore) {after : NamedStore}
    (h : FJ after.core) (b : NamedBlock) : FJ (admitCarried adm hc before after b).core := by
  unfold admitCarried
  split_ifs
  · exact admitRows_fj hc _ h
  · exact h

theorem onBlockWith_fj (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (adm : CarriedAdmission)
    (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig) {st : NamedStore} (h : FJ st.core) (b : NamedBlock) :
    FJ (onBlockWith c p adm e hc cfg st b).core := by
  unfold onBlockWith
  exact admitCarried_fj adm hc st (processBlockCore_fj c p e hc cfg h b) b

theorem nodeProcess_fj (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (s : Model.Consensus.Execution.Setup.Setup) {n : NamedNodeState} (h : FJ n.st.core) (o : NamedObject) :
    FJ (nodeProcess c p s n o).st.core := by
  show FJ (receiptProcess c p s n.st o).core
  cases o with
  | Block b => exact onBlockWith_fj c p _ _ _ _ h b
  | GfVote u =>
    show FJ { n.st with core := onGoldfishVoteChecked c n.st.core u }.core
    exact h.congr (onGoldfishVoteChecked_out c n.st.core u)
  | Attest a =>
    show FJ (admitRow s.hc n.st a).core
    exact admitRow_fj s.hc h a

/-! ## Tick の務め -/

theorem proposeBlockWith_fj (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (h : FJ st.core) :
    FJ (proposeBlockWith c p nr cache e hc cfg nd st).1.core := by
  unfold proposeBlockWith
  split
  · exact h
  · rename_i b _
    exact onBlockWith_fj c p CarriedAdmission.AlsoCarried e hc cfg h b

theorem namedGoldfishVoteWith_fj (c : Nat → NaruStd.Set ValidatorId) (cache : Cache) (e : ProtocolEnv)
    (hc : HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (h : FJ st.core) :
    FJ (namedGoldfishVoteWith c cache e hc nd st).1.core := by
  unfold namedGoldfishVoteWith
  split
  rename_i core out hm
  show FJ { st with core := core }.core
  have h1 : core = (goldfishVoteWith c cache e hc nd st.core).1 := by rw [hm]
  refine h.congr ?_
  show SameOut core st.core
  rw [h1]
  exact goldfishVoteWith_out c cache e hc nd st.core

theorem namedUpdateConfirmationWith_fj (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) {st : NamedStore}
    (h : FJ st.core) (k : Nat) : FJ (namedUpdateConfirmationWith cache e hc st k).core :=
  h.of_eq rfl rfl

theorem attestWith_fj (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (nd : Model.Consensus.Protocol.Schedule.Node)
    {st : NamedStore} (h : FJ st.core) (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) :
    FJ (attestWith cache e hc nd st rec).1.core := by
  unfold attestWith
  split
  exact admitRow_fj hc h _

/-- 1 tick の務めは `f ⪯ j` を保つ(`Trees.tick_treeInv` と同じ 16 経路)。 -/
theorem tick_fj (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig) (cfg : HeightConfig)
    (nd : Model.Consensus.Protocol.Schedule.Node) {st : NamedStore} (h : FJ st.core)
    (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int) :
    FJ (tick c p a nr cache e hc cfg nd st rec t).1.core := by
  have h0 : FJ { st with core := { st.core with t := t, s := slotOf e t } }.core := h
  unfold tick
  dsimp only
  split_ifs
  all_goals first
    | with_reducible exact attestWith_fj cache e hc nd (namedUpdateConfirmationWith_fj cache e hc (namedGoldfishVoteWith_fj c cache e hc nd (proposeBlockWith_fj c p nr cache e hc cfg nd h0)) _) _
    | with_reducible exact attestWith_fj cache e hc nd (namedUpdateConfirmationWith_fj cache e hc (namedGoldfishVoteWith_fj c cache e hc nd h0) _) _
    | with_reducible exact attestWith_fj cache e hc nd (namedUpdateConfirmationWith_fj cache e hc (proposeBlockWith_fj c p nr cache e hc cfg nd h0) _) _
    | with_reducible exact attestWith_fj cache e hc nd (namedUpdateConfirmationWith_fj cache e hc h0 _) _
    | with_reducible exact attestWith_fj cache e hc nd (namedGoldfishVoteWith_fj c cache e hc nd (proposeBlockWith_fj c p nr cache e hc cfg nd h0)) _
    | with_reducible exact attestWith_fj cache e hc nd (namedGoldfishVoteWith_fj c cache e hc nd h0) _
    | with_reducible exact attestWith_fj cache e hc nd (proposeBlockWith_fj c p nr cache e hc cfg nd h0) _
    | with_reducible exact attestWith_fj cache e hc nd h0 _
    | with_reducible exact namedUpdateConfirmationWith_fj cache e hc (namedGoldfishVoteWith_fj c cache e hc nd (proposeBlockWith_fj c p nr cache e hc cfg nd h0)) _
    | with_reducible exact namedUpdateConfirmationWith_fj cache e hc (namedGoldfishVoteWith_fj c cache e hc nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_fj cache e hc (proposeBlockWith_fj c p nr cache e hc cfg nd h0) _
    | with_reducible exact namedUpdateConfirmationWith_fj cache e hc h0 _
    | with_reducible exact namedGoldfishVoteWith_fj c cache e hc nd (proposeBlockWith_fj c p nr cache e hc cfg nd h0)
    | with_reducible exact namedGoldfishVoteWith_fj c cache e hc nd h0
    | with_reducible exact proposeBlockWith_fj c p nr cache e hc cfg nd h0
    | with_reducible exact h0

theorem nodeTick_fj (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (v : ValidatorId)
    {n : NamedNodeState} (h : FJ n.st.core) (t : Int) : FJ (nodeTick c p a nr s v n t).1.st.core := by
  unfold nodeTick profileTick
  dsimp only
  exact tick_fj c p a nr _ s.e s.hc s.cfg _ h n.signing t

/-! ## world と run -/

/-- world のどのノードの store も `f ⪯ j`。 -/
def WorldFJ (w : NamedWorld) : Prop := ∀ v, FJ (worldAt w v).st.core

theorem worldInit_fj : WorldFJ worldInit := fun _ => initial_fj

theorem worldStep_fj (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) {w : NamedWorld} (h : WorldFJ w)
    (ev : NamedEvent) : WorldFJ (worldStep c p a nr s w ev) := by
  intro v
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeTick_fj c p a nr s u (h u) t
    · rw [hw]
      exact h v
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, hw⟩ | hw
    · rw [hw]
      exact nodeProcess_fj c p s (h u) o
    · rw [hw]
      exact h v

theorem foldl_worldStep_fj (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) {w : NamedWorld}, WorldFJ w →
      WorldFJ (List.foldl (fun w ev => worldStep c p a nr s w ev) w l)
  | [], _, h => h
  | ev :: l, _, h => by
    rw [List.foldl_cons]
    exact foldl_worldStep_fj c p a nr s l (worldStep_fj c p a nr s h ev)

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **run のどの添字の直前でも、どのノードの store も `f ⪯ j`**(前提なし)。 -/
theorem stateBefore_fj (i : Nat) : WorldFJ (stateBefore c p a nr s rho i) := by
  unfold stateBefore
  exact foldl_worldStep_fj c p a nr s _ worldInit_fj

/-- 時刻 `t` の読みのどのノードの store も `f ⪯ j`(前提なし)。 -/
theorem readAt_fj (t : Int) : WorldFJ (readAt c p a nr s rho t) := by
  unfold readAt
  exact foldl_worldStep_fj c p a nr s _ worldInit_fj

/-! ## 発行されたブロック -/

/-- tick が出すブロックは、その tick の直前の store の `f` を延ばす(時計合わせは `f` / `j` を変えない)。 -/
theorem nodeTick_block_extends (v : ValidatorId) {n : NamedNodeState} (h : FJ n.st.core) (t : Int) {D : NamedBlock}
    (hD : NamedObject.Block D ∈ (nodeTick c p a nr s v n t).2) : preceq n.st.core.f (eraseBlock D) = true := by
  rw [Proofs.Consensus.Signing.nodeTick_out] at hD
  obtain ⟨-, -, -, hp⟩ := Proofs.Consensus.Proposal.tick_block_shape c p a nr _ s.e s.hc s.cfg _ n.st n.signing t hD
  exact proposalWith_extends nr _ s.e s.hc _ (st := { n.st with core := { n.st.core with t := t, s := slotOf s.e t } })
    h hp

/-- **発行されたブロックは、発行した tick の直前の提案者の `f` を延ばす**(前提なし)。 -/
theorem emits_block_extends {v : ValidatorId} {D : NamedBlock} {t : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) :
    ∃ i, rho.events[i]? = some (NamedEvent.Tick v t) ∧
      preceq (worldAt (stateBefore c p a nr s rho i) v).st.core.f (eraseBlock D) = true := by
  obtain ⟨i, hi, ho⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t).mp hem
  exact ⟨i, hi, nodeTick_block_extends c p a nr s v (stateBefore_fj c p a nr s rho i v) t ho⟩

/-- **`extends_f` を finality の事実に還元する**: setup と run の前提(`ScheduleWellFormed` / `DeliveryWellFormed` / `0 < Δ`)の下で、
honest な `w` に発行より後に配送された発行されたブロック `D` は、配送の直前の `w` の `f` が、`Tick v t` に当たるどの添字 `i` の直前の
提案者 `v` の `f` の祖先でもあれば、配送の後の `w` の tree にある。 -/
theorem deliver_emitted_block_mem_of_finalized (hsch : ScheduleWellFormed s rho)
    (hdw : DeliveryWellFormed c p a nr s rho) (hδ : 0 < s.e.delta) {v w : ValidatorId} {D : NamedBlock} {t t2 : Int}
    (hem : Emits c p a nr s rho v (NamedObject.Block D) t) (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t < t2)
    (hfin : ∀ i, rho.events[i]? = some (NamedEvent.Tick v t) →
      preceq (worldAt (stateBefore c p a nr s rho j) w).st.core.f
        (worldAt (stateBefore c p a nr s rho i) v).st.core.f = true) :
    eraseBlock D ∈ (worldAt (stateBefore c p a nr s rho (j + 1)) w).st.core.tree.elems := by
  obtain ⟨i, hi, hext⟩ := emits_block_extends c p a nr s rho hem
  exact Proofs.Consensus.DeliveredBlock.deliver_emitted_block_mem c p a nr s rho hsch hdw hδ hem hw hj ht
    (preceq_trans (hfin i hi) hext)

end Run

end Proofs.Consensus.ProposerFinality
