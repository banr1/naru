import Proofs.Consensus.BlockStamps
import Proofs.Consensus.ReceiverFinality
import Proofs.Consensus.JustifiedCarrier
import Proofs.Consensus.ProposerFinality
import Mathlib.Tactic

/-!
# 投票の処理済み tree は祖先について閉じ、band の子孫の下の途中は歩みの tree にある(C71 / C77 の補題)

投票の務めの歩みの tree `voterFilteredBlockTree` は store の tree の 4 段の絞り込み(処理済み `voterProcessedBlockTree`・
finalized の子孫・viable・FG root の下)。手書き `coreCandidatePathOfBandDescendant`(`DecoupledConsensusProofs/Protocol/Schedule/
WeakGoldfishCone.lean`)は、処理済みで高さが band(`hMax - 1` 以上)のブロック `D` があれば、FG root から `D` の祖先 `C` までの途中は
すべて歩みの tree にあることを示す。この節はその生成 Model 版。
- 処理済みの判定の 1 つ目の枝(受信の印が freeze より前)を祖先へ運ぶのが印の祖先の不変条件 `AncestorStamped`: tree のブロックの
  印が `γ` より前なら、その祖先はどれも tree にあり印が `γ` より前。新しく入るブロックの印はその時点の時計で(`BlockStamps.Fresh`)、
  そのときの tree は親について閉じ(`Trees.tree_closed`)、祖先の印は時計以下(`BlockStamps.StampInv`)なので保たれる
  (手書き `ancestorProcessed_of_voterProcessed`(`Protocol/Schedule/WeakProcessedTree.lean`)は freeze の時刻の読みに戻して
  示すが、ここは 1 段の保存で済む)。
- 2 つ目の枝(slot `s` の提案の祖先)は定義から祖先について閉じている。
- finalized の子孫は `f ⪯ j`(`ProposerFinality.FJ`)から `f ⪯ FG root`、viable は `D` を証人にする。
`AvailableHoles.voteDutyHead_passes_supporter_majority_of_band` の前提 `hpath` を外すのに使う(周回 281)。
-/

namespace Proofs.Consensus.ProcessedAncestor

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.Time
open Model.Consensus.Protocol.Store Model.Consensus.Protocol.ForkChoice.Goldfish
open Model.Consensus.Execution.Objects Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Statements.Consensus.Spec.Conditions
open Proofs.Consensus.BlockStamps

/-- 印の祖先: tree のブロック `B` の受信の印が `γ` より前なら、`B` の祖先はどれも tree にあり受信の印が `γ` より前。 -/
def AncestorStamped (st : Store) : Prop :=
  ∀ B, B ∈ st.tree.elems → ∀ γ : Int, occurrenceBefore (st.timestampBlock.get? B) γ = true →
    ∀ C, preceq C B = true → C ∈ st.tree.elems ∧ occurrenceBefore (st.timestampBlock.get? C) γ = true

/-- 1 段の保存: 印を保存して新しいブロックの印が時計の時刻(`Grow`)、後の store の印が時計以下(`StampInv`)で tree が親について
閉じていれば、印の祖先は保たれる。 -/
theorem AncestorStamped.of_grow {a b : Store} (h : AncestorStamped a) (hg : Grow a b) (hb : StampInv b)
    (hcl : ∀ x, x ∈ b.tree.elems → parent x ∈ b.tree.elems) : AncestorStamped b := by
  intro B hB γ hγ C hCB
  rcases hg.2 B hB with ha | ⟨τ, hτ, hclk⟩
  · obtain ⟨-, heq⟩ := hg.1 B ha
    rw [heq] at hγ
    obtain ⟨hCa, hCγ⟩ := h B ha γ hγ C hCB
    obtain ⟨hCb, hCeq⟩ := hg.1 C hCa
    rw [hCeq]
    exact ⟨hCb, hCγ⟩
  · have hC : C ∈ b.tree.elems := Proofs.Consensus.Trees.ancestor_mem_tree hcl hCB hB
    refine ⟨hC, (hb C hC).before ?_⟩
    rw [hτ] at hγ
    unfold occurrenceBefore at hγ
    rcases (Proofs.Consensus.Majority.stampBefore_iff _ _).mp hγ with h0 | ⟨a', ha', hlt⟩
    · cases h0
    · cases ha'
      rw [hclk]
      exact hlt

/-- 初期の store: tree は `{Genesis}` で、genesis の祖先は genesis だけ。 -/
theorem initial_ancestorStamped : AncestorStamped initStore := by
  intro B hB γ hγ C hCB
  have hB' : B ∈ (NaruStd.Set.singleton Block.Genesis).elems := hB
  rw [Proofs.Consensus.Sets.mem_singleton_iff] at hB'
  subst hB'
  simp only [preceq, beq_iff_eq] at hCB
  subst hCB
  exact ⟨hB, hγ⟩

section Run

variable (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
  (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)

/-- **run のどの添字・どのノードでも印の祖先**(event の整列と時刻の非負の下で。`StampInv` と同じ前提)。 -/
theorem stateBefore_ancestorStamped (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev) :
    ∀ (i : Nat) (v : ValidatorId), AncestorStamped (worldAt (stateBefore c p a nr s rho i) v).st.core
  | 0, _ => initial_ancestorStamped
  | i + 1, v => by
    have ih := stateBefore_ancestorStamped hs hnn i v
    refine ih.of_grow ?_ (stateBefore_stampInv c p a nr s rho hs hnn (i + 1) v)
      (Proofs.Consensus.Trees.tree_closed (Proofs.Consensus.Carrier.stateBefore_inv c p a nr s rho (i + 1) v))
    rw [Proofs.Consensus.Signing.stateBefore_succ]
    cases rho.events[i]? with
    | none => exact Grow.refl _
    | some ev =>
      show Grow _ (worldAt (worldStep c p a nr s (stateBefore c p a nr s rho i) ev) v).st.core
      exact worldStep_grow c p a nr s _ ev v

/-- 時刻 `< t` の読みのどのノードの store も印の祖先を満たす(`stateBeforeTime_eq_stateBefore_idxLt`)。 -/
theorem stateBeforeTime_ancestorStamped (hs : EventsSorted rho) (hnn : ∀ ev, ev ∈ rho.events → 0 ≤ eventTime ev)
    (t : Int) (v : ValidatorId) : AncestorStamped (worldAt (stateBeforeTime c p a nr s rho t) v).st.core := by
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs t]
  exact stateBefore_ancestorStamped c p a nr s rho hs hnn _ v

/-- 時刻 `< t` の読みのどのノードの store の tree も親について閉じている(前提なし)。 -/
theorem stateBeforeTime_tree_closed (t : Int) (v : ValidatorId) :
    ∀ x, x ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.core.tree.elems →
      parent x ∈ (worldAt (stateBeforeTime c p a nr s rho t) v).st.core.tree.elems :=
  Proofs.Consensus.Trees.tree_closed (Proofs.Consensus.JustifiedCarrier.stateBeforeTime_inv c p a nr s rho t v)

/-- 時刻 `< t` の読みのどのノードの store も `f ⪯ j`(`stateBeforeTime_eq_stateBefore_idxLt` と `ProposerFinality.stateBefore_fj`)。 -/
theorem stateBeforeTime_fj (hs : EventsSorted rho) (t : Int) (v : ValidatorId) :
    Proofs.Consensus.ProposerFinality.FJ (worldAt (stateBeforeTime c p a nr s rho t) v).st.core := by
  rw [Proofs.Consensus.ReceiverFinality.stateBeforeTime_eq_stateBefore_idxLt c p a nr s rho hs t]
  exact Proofs.Consensus.ProposerFinality.stateBefore_fj c p a nr s rho _ v

end Run

/-! ## 処理済み tree と歩みの tree -/

/-- **投票の処理済み tree は祖先について閉じている**(手書き `ancestorProcessed_of_voterProcessed`): 印の枝は `AncestorStamped`、
提案の枝は `C ⪯ B ⪯ P`。 -/
theorem voterProcessed_ancestor {e : Model.Consensus.Objects.Parameters.ProtocolEnv} {st : Store}
    (hanc : AncestorStamped st) (hcl : ∀ x, x ∈ st.tree.elems → parent x ∈ st.tree.elems) (k : Nat) {B C : Block}
    (hB : B ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree e
      (fgToGoldfish (storeToHealing st)) k).elems)
    (hCB : preceq C B = true) :
    C ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree e
      (fgToGoldfish (storeToHealing st)) k).elems := by
  unfold Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree at hB ⊢
  dsimp only at hB ⊢
  obtain ⟨hBt, hcond⟩ := (Proofs.Consensus.Trees.mem_filter_iff _ _ _).mp hB
  have hBt' : B ∈ st.tree.elems := hBt
  have hCt : C ∈ st.tree.elems := Proofs.Consensus.Trees.ancestor_mem_tree hcl hCB hBt'
  rw [Proofs.Consensus.Trees.mem_filter_iff]
  refine ⟨hCt, ?_⟩
  rw [Bool.or_eq_true] at hcond ⊢
  rcases hcond with h | h
  · exact Or.inl (hanc B hBt' _ h C hCB).2
  · right
    unfold NaruStd.Set.any at h ⊢
    obtain ⟨P, hP, hBP⟩ := List.any_eq_true.mp h
    exact List.any_eq_true.mpr ⟨P, hP, Proofs.Consensus.Blocks.preceq_trans hCB hBP⟩

/-- **band の子孫の下の途中は歩みの tree にある**(手書き `coreCandidatePathOfBandDescendant` の `hmem`): 処理済み tree に
高さが band(`hMax - 1` 以上)のブロック `D` があり、`C ⪯ D` で FG root ⪯ `C` なら、`C` は歩みの tree `voterFilteredBlockTree`
にある(処理済みは `voterProcessed_ancestor`、finalized の子孫は `f ⪯ j` から `f ⪯ FG root`、viable の証人は `D`)。 -/
theorem voterFiltered_mem_of_band {e : Model.Consensus.Objects.Parameters.ProtocolEnv} {st : Store}
    (hanc : AncestorStamped st) (hcl : ∀ x, x ∈ st.tree.elems → parent x ∈ st.tree.elems)
    (hfj : Proofs.Consensus.ProposerFinality.FJ st) {C D : Block} (hCD : preceq C D = true)
    (hD : D ∈ (Model.Consensus.Protocol.ForkChoice.Views.voterProcessedBlockTree e
      (fgToGoldfish (storeToHealing st)) st.s).elems)
    (hband : st.hMax - 1 ≤ (chainStateOf st.sigma D).h)
    (hroot : preceq (getFgRoot (storeToHealing st)) C = true) :
    C ∈ (Model.Consensus.Protocol.Handlers.voterFilteredBlockTree e st st.s).elems := by
  have hfroot : preceq st.f (getFgRoot (storeToHealing st)) = true := by
    unfold getFgRoot
    split
    · exact hfj
    · exact Proofs.Consensus.Blocks.preceq_self _
  have hC := voterProcessed_ancestor hanc hcl st.s hD hCD
  unfold Model.Consensus.Protocol.Handlers.voterFilteredBlockTree getFilteredBlockTreeFrom viableTree finalizedDescendants
  dsimp only
  rw [Proofs.Consensus.Trees.mem_filter_iff, Proofs.Consensus.Trees.mem_filter_iff, Proofs.Consensus.Trees.mem_filter_iff]
  refine ⟨⟨⟨hC, Proofs.Consensus.Blocks.preceq_trans hfroot hroot⟩, ?_⟩, hroot⟩
  unfold viable NaruStd.Set.any
  exact List.any_eq_true.mpr ⟨D, hD, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hCD, hband⟩⟩

end Proofs.Consensus.ProcessedAncestor
