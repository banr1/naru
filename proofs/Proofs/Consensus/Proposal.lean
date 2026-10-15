import Proofs.Consensus.BlockReceipt
import Proofs.Consensus.Carried
import Proofs.Consensus.Window
import Mathlib.Tactic

/-!
# 提案されたブロックの形と、受理の守りのうち提案の形から出るもの(C71 の補題)

`BlockReceipt.deliver_block_mem` は配送されたブロック `b` の受理に、配送の直前の受信者の store について
名前付きの親が bodies にあること・運ばれた attestation の round の守り(`carriedAttestationsAdmissible`)・`Admits`
(slot ≤ 受信者の slot、親が tree、`preceq st.f b`、提案者、親の slot が小さい)を仮定する。ここではそのうち
ブロックそのものの形で決まるものを、提案の務め(`proposalWith` / `proposeBlockWith`、`Model/Consensus/Protocol/Duties/Proposals.lean`)
と tick(`Model/Consensus/Protocol/Tick.lean`)の定義から示す:
- `proposalWith` が出すブロックは `Node par st.s (newRoot' v st.s) … (proposalRows par (selectRows …)) v`(`proposalWith_some`)。
  親 `par` は提案者の bodies から `parentBody?`(`findUnique?`)で引いたもので、提案者の bodies にあり消去すると入力の親
  `(proposalInput …).parent`(`proposalInput` の定義では fork choice の head)に等しい(`proposalWith_parent` / `proposalWith_parent_mem`)。slot は提案者の slot、提案者は自分
  (`proposalWith_slot` / `proposalWith_proposer`)。
- 運ぶ attestation の行は `selectRows`(pool の行と bodies の運んだ行。どちらも `inWindow` で絞る)の部分集合
  (`excludeOnChain` は filter、`capPerSigner` は畳み込みで足すだけ: `capPerSigner_subset`)なので、round はどれも提案者の round
  `roundOf hc st.s` 以下で、ブロックの slot は `st.s` だから round の守りを通る(`proposalWith_admissible`)。
- tick がブロックを出すのは提案の務めが走ったとき(`0 < s`、`t = proposalTime e s`、`proposer' s = 自分`、`s = slotOf e t`)だけで、
  務めは時計を合わせた store で `proposalWith` を呼ぶ(`tick_block_shape`)。したがって tick が出すブロックの slot は `slotOf e t`、
  提案者は `proposer' (slot b)`、round の守りを通り、名前付きの親は tick の前の bodies にある(`tick_block_fields`)。
- run では、発行されたブロック(`Emits`)はその slot の提案の時刻に発行され、提案者は `proposer' (slot b)`、round の守りを通る
  (`emits_block_fields`)。honest な受信者への配送の時刻が発行の時刻より後なら、受信の直前の受信者の slot はブロックの slot 以上
  (`Admits.slot_le`、`emits_block_slot_le`。`Window.slot_ge_of_deliver`)。

`Admits` の残り(親が受信者の tree / bodies にあること、`preceq st.f b`、親の slot が小さいこと)は後続の層。
手書きでは `DecoupledConsensusProofs/Protocol/ChainState/ProposalBridge.lean` の `proposedParent_mem` / `proposedBlockAt_slot` /
`proposedBlockAt_proposer` / `proposedBlockAt_parent` に当たる(手書きは提案を slot の関数 `proposedBlockAt` として立てる。
手書きの `proposedParent_mem` は消去した親が提案者の tree にあることで、ここの `proposalWith_parent_mem` は名前付きの親が bodies にあること)。
-/

namespace Proofs.Consensus.Proposal

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Objects.Parameters Model.Consensus.Protocol.Store
open Model.Consensus.Protocol.Handlers Model.Consensus.Protocol.Duties.Proposals Model.Consensus.Protocol.Duties.Inputs
open Model.Consensus.Protocol.Tick Model.Consensus.Protocol.Schedule Model.Consensus.Protocol.Grades
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Execution Statements.Consensus.Spec.Conditions

/-! ## 行の部分集合 -/

/-- `capPerSigner` の畳み込みは行を足すだけ。 -/
theorem capPerSigner_foldl_subset (l acc : List NamedAttestation) {x : NamedAttestation}
    (h : x ∈ List.foldl (fun (acc : List NamedAttestation) (row : NamedAttestation) =>
      if (List.contains acc row) || (decide (2 ≤ (List.filter (fun (a : NamedAttestation) =>
          (a.valIndex == row.valIndex) && (a.round == row.round)) acc).length)) then acc else acc ++ [row]) acc l) :
    x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => exact Or.inl h
  | cons y ys ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h | h
    · split_ifs at h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton] at h
          exact Or.inr (h ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- `capPerSigner` の行は元の行。 -/
theorem capPerSigner_subset {rows : List NamedAttestation} {x : NamedAttestation} (h : x ∈ capPerSigner rows) :
    x ∈ rows := by
  unfold capPerSigner at h
  rcases capPerSigner_foldl_subset rows [] h with h | h
  · simp at h
  · exact h

/-- 提案の行は `selectRows` の行。 -/
theorem proposalRows_subset {par : NamedBlock} {rows : List NamedAttestation} {x : NamedAttestation}
    (h : x ∈ proposalRows par rows) : x ∈ rows := by
  unfold proposalRows excludeOnChain at h
  exact (List.mem_filter.mp (capPerSigner_subset h)).1

/-- `inWindow` の round は store の round 以下。 -/
theorem round_le_of_inWindow {hc : HealConfig} {st : Store} {r : Nat} (h : inWindow hc st r = true) :
    r ≤ roundOf hc st.s := by
  unfold inWindow at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- `selectRows` の行の round は提案者の round 以下(pool の行も運んだ行も `inWindow` で絞る)。 -/
theorem selectRows_round_le {hc : HealConfig} {st : NamedStore} {x : NamedAttestation}
    (h : x ∈ selectRows .PoolAndCarried hc st) : x.round ≤ roundOf hc st.core.s := by
  unfold selectRows at h
  rcases List.mem_append.mp h with h | h
  · unfold poolRows at h
    exact round_le_of_inWindow (List.mem_filter.mp h).2
  · unfold carriedRows at h
    obtain ⟨b, -, hb⟩ := List.mem_flatMap.mp h
    split_ifs at hb
    · exact round_le_of_inWindow (List.mem_filter.mp hb).2
    · simp at hb

/-! ## 提案の務めの出力 -/

section Shape

variable (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
  (nd : Node) (st : NamedStore)

/-- **`proposalWith` の出力の形**: 親は `parentBody?` で引いた名前付きのブロック、slot は提案者の slot、行は `selectRows` から、
提案者は自分。 -/
theorem proposalWith_some {b : NamedBlock} (h : proposalWith nr cache .PoolAndCarried e hc nd st = some b) :
    ∃ par, parentBody? st (proposalInput nr cache e hc nd (storeToHealing st.core)).parent = some par ∧
      b = NamedBlock.Node par st.core.s (nr nd.valIndex st.core.s)
        (proposalInput nr cache e hc nd (storeToHealing st.core)).gfVotes
        (proposalInput nr cache e hc nd (storeToHealing st.core)).gfSupportVotes
        (proposalRows par (selectRows .PoolAndCarried hc st)) nd.valIndex := by
  unfold proposalWith at h
  dsimp only at h
  cases hp : parentBody? st (proposalInput nr cache e hc nd (storeToHealing st.core)).parent with
  | none => rw [hp] at h; simp at h
  | some par =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨par, rfl, h.symm⟩

/-- 名前付きの親は提案者の bodies にあり、消去すると入力の親 `(proposalInput …).parent`。 -/
theorem proposalWith_parent {b : NamedBlock} (h : proposalWith nr cache .PoolAndCarried e hc nd st = some b) :
    namedParent b ∈ st.bodies.elems ∧
      eraseBlock (namedParent b) = (proposalInput nr cache e hc nd (storeToHealing st.core)).parent := by
  obtain ⟨par, hp, rfl⟩ := proposalWith_some nr cache e hc nd st h
  unfold parentBody? at hp
  obtain ⟨hm, he⟩ := Proofs.Consensus.Trees.findUnique?_mem hp
  exact ⟨hm, beq_iff_eq.mp he⟩

theorem proposalWith_parent_mem {b : NamedBlock} (h : proposalWith nr cache .PoolAndCarried e hc nd st = some b) :
    namedParent b ∈ st.bodies.elems :=
  (proposalWith_parent nr cache e hc nd st h).1

/-- slot は提案者の slot。 -/
theorem proposalWith_slot {b : NamedBlock} (h : proposalWith nr cache .PoolAndCarried e hc nd st = some b) :
    slot (eraseBlock b) = st.core.s := by
  obtain ⟨par, -, rfl⟩ := proposalWith_some nr cache e hc nd st h
  rfl

/-- 提案者は自分。 -/
theorem proposalWith_proposer {b : NamedBlock} (h : proposalWith nr cache .PoolAndCarried e hc nd st = some b) :
    proposer? (eraseBlock b) = some nd.valIndex := by
  obtain ⟨par, -, rfl⟩ := proposalWith_some nr cache e hc nd st h
  rfl

/-- **運ばれた attestation の round の守りを通る**: 行の round はどれも提案者の round 以下で、ブロックの slot は提案者の slot。 -/
theorem proposalWith_admissible {b : NamedBlock} (h : proposalWith nr cache .PoolAndCarried e hc nd st = some b) :
    carriedAttestationsAdmissible hc (eraseBlock b) = true := by
  obtain ⟨par, -, rfl⟩ := proposalWith_some nr cache e hc nd st h
  unfold carriedAttestationsAdmissible
  rw [List.all_eq_true]
  intro x hx
  simp only [eraseBlock, attestations, slot, List.mem_map] at hx ⊢
  obtain ⟨row, hrow, rfl⟩ := hx
  exact decide_eq_true (selectRows_round_le (proposalRows_subset hrow))

end Shape

/-! ## tick が出すブロック -/

section Tick

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (cache : Cache) (e : ProtocolEnv) (hc : HealConfig)
  (cfg : Model.Consensus.Protocol.ChainState.HeightConfig) (nd : Node) (st : NamedStore)
  (rec : Model.Consensus.Protocol.ValidatorClient.NamedRecord) (t : Int)

/-- **tick が出すブロックの形**: 提案の務めが走った tick(`0 < slotOf e t`、提案の時刻、提案者が自分)で、時計を合わせた store の
`proposalWith` の出力。 -/
theorem tick_block_shape {D : NamedBlock} (h : NamedObject.Block D ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2) :
    0 < slotOf e t ∧ t = proposalTime e (slotOf e t) ∧ p (slotOf e t) = nd.valIndex ∧
      proposalWith nr cache .PoolAndCarried e hc nd
        { st with core := { st.core with t := t, s := slotOf e t } } = some D := by
  unfold tick at h
  dsimp only at h
  split_ifs at h
  all_goals simp only [List.mem_append] at h
  all_goals repeat' (obtain h | h := (h : _ ∨ _))
  all_goals first
    | (simp at h)
    | ((revert h; split <;> intro h <;> simp at h) <;> done)
    | (have hp : ((decide (0 < slotOf e t) && t == proposalTime e (slotOf e t)) && (p (slotOf e t) == nd.valIndex)) = true := by
          assumption
       simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
       refine ⟨hp.1.1, hp.1.2, hp.2, ?_⟩
       revert h
       unfold proposeBlockWith
       split
       · intro h; simp at h
       · rename_i b hb
         intro h
         simp only [List.mem_singleton, NamedObject.Block.injEq] at h
         subst h
         revert hb
         split
         · intro hb; simp at hb
         · rename_i b' hb'
           intro hb
           simp only [Option.some.injEq] at hb
           rw [← hb]
           exact hb')

/-- **tick が出すブロックの、受理の守りのうち形で決まるもの**: slot は `slotOf e t`、提案者は `proposer' (slot)`、round の守りを通り、
名前付きの親は tick の前の bodies にある。 -/
theorem tick_block_fields {D : NamedBlock} (h : NamedObject.Block D ∈ (tick c p a nr cache e hc cfg nd st rec t).2.2) :
    0 < slotOf e t ∧ t = proposalTime e (slotOf e t) ∧ slot (eraseBlock D) = slotOf e t ∧
      proposer? (eraseBlock D) = some (p (slot (eraseBlock D))) ∧
      carriedAttestationsAdmissible hc (eraseBlock D) = true ∧ namedParent D ∈ st.bodies.elems := by
  obtain ⟨h0, ht, hp, hD⟩ := tick_block_shape c p a nr cache e hc cfg nd st rec t h
  have hs := proposalWith_slot nr cache e hc nd _ hD
  have hpar := proposalWith_parent_mem nr cache e hc nd _ hD
  refine ⟨h0, ht, hs, ?_, proposalWith_admissible nr cache e hc nd _ hD, hpar⟩
  rw [proposalWith_proposer nr cache e hc nd _ hD, hs, hp]

end Tick

/-! ## run -/

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

theorem nodeTick_block_fields (v : ValidatorId) (n : NamedNodeState) (t : Int) {D : NamedBlock}
    (h : NamedObject.Block D ∈ (nodeTick c p a nr s v n t).2) :
    0 < slotOf s.e t ∧ t = proposalTime s.e (slotOf s.e t) ∧ slot (eraseBlock D) = slotOf s.e t ∧
      proposer? (eraseBlock D) = some (p (slot (eraseBlock D))) ∧
      carriedAttestationsAdmissible s.hc (eraseBlock D) = true ∧ namedParent D ∈ n.st.bodies.elems := by
  rw [Proofs.Consensus.Signing.nodeTick_out] at h
  exact tick_block_fields c p a nr _ s.e s.hc s.cfg _ n.st n.signing t h

/-- **発行されたブロックの形**: その slot の提案の時刻に発行され、提案者は `proposer' (slot)`、round の守りを通る。 -/
theorem emits_block_fields {v : ValidatorId} {D : NamedBlock} {t : Int}
    (h : Emits c p a nr s rho v (NamedObject.Block D) t) :
    0 < slot (eraseBlock D) ∧ t = proposalTime s.e (slot (eraseBlock D)) ∧
      proposer? (eraseBlock D) = some (p (slot (eraseBlock D))) ∧
      carriedAttestationsAdmissible s.hc (eraseBlock D) = true := by
  obtain ⟨i, -, ho⟩ := (Proofs.Consensus.Signing.emits_iff c p a nr s rho v _ t).mp h
  obtain ⟨h0, ht, hs, hp, hca, -⟩ := nodeTick_block_fields c p a nr s v _ t ho
  rw [hs]
  exact ⟨h0, ht, hs ▸ hp, hca⟩

/-- **配送の直前の受信者の slot はブロックの slot 以上**(`Admits.slot_le`): honest な `w` への配送の時刻 `t2` が
発行の時刻(= ブロックの slot の提案の時刻)より後なら、`Window.slot_ge_of_deliver`。 -/
theorem emits_block_slot_le (hsch : ScheduleWellFormed s rho) (hδ : 0 < s.e.delta) {v w : ValidatorId}
    {D : NamedBlock} {t t2 : Int} (hem : Emits c p a nr s rho v (NamedObject.Block D) t)
    (hw : rho.honest.contains w = true) {j : Nat}
    (hj : rho.events[j]? = some (NamedEvent.Deliver w (NamedObject.Block D) t2)) (ht : t < t2) :
    slot (eraseBlock D) ≤ (worldAt (stateBefore c p a nr s rho j) w).st.core.s := by
  obtain ⟨-, htp, -, -⟩ := emits_block_fields c p a nr s rho hem
  rw [htp] at ht
  exact Proofs.Consensus.Window.slot_ge_of_deliver c p a nr s rho hsch hδ hw hj ht

end Run

end Proofs.Consensus.Proposal
