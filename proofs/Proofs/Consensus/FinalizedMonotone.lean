import Model.Consensus.Spec.Interface
import Statements.Consensus.Spec.Properties
import Proofs.Consensus.Blocks
import Proofs.Consensus.Stores
import Proofs.Consensus.Runs
import Mathlib.Tactic

/-!
# finalized の単調性(claim `finalizedMonotone` の補題)

property `MonotoneFrom … Finalized 0`(`Statements/Consensus/Spec/Properties.lean`): honest なノード `v` と `0 ≤ t ≤ t2 ≤ horizon` に
対して `outputAt Finalized v t ⪯ outputAt Finalized v t2`。`outputAt Finalized` は `(storeAt v t).core.f` で、
`storeAt v t = (worldAt (readAt t) v).st`、`readAt t` は `filter (eventTime ≤ t)` した event 列の `worldStep` による畳み込み。
証明は、(1) 各 `worldStep` がどのノードの `f` も縮めない(`Stores.lean` の `nodeTick_f` / `nodeProcess_f` と `Runs.lean` の
`worldAt_insert`)、(2) `EventsSorted` の下で `filter (≤ t)` が `filter (≤ t2)` の接頭辞(`Runs.lean` の `filter_le_append`)、
の 2 つを `List.foldl_append` と `preceq` の推移律でつなぐ。前提に使うのは `RunWellFormed` の中の `EventsSorted` だけで、
`SetupWellFormed` / `RunDomain` / `Idealization` / honest / `0 ≤ t` / `t2 ≤ horizon` は使わない。
手書き `accountable_finalizedMonotone` → `finalized_readAt_mono_of_sorted`(`DecoupledConsensusProofs/Bridge/FinalizedLive.lean`)の筋。
-/

namespace Proofs.Consensus.FinalizedMonotone

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers
open Model.Consensus.Execution.Node Model.Consensus.Execution.Run
open Proofs.Consensus.Blocks Proofs.Consensus.Stores Proofs.Consensus.Runs

/-- 1 event の `worldStep` は、どのノード `v` の `f` も縮めない(当該ノードは `nodeTick_f` / `nodeProcess_f`、他は不変)。 -/
theorem worldStep_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup)
    (w : NamedWorld) (ev : NamedEvent) (v : ValidatorId) :
    preceq (worldAt w v).st.core.f (worldAt (worldStep c p a nr s w ev) v).st.core.f = true := by
  cases ev with
  | Tick u t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeTick c p a nr s u (worldAt w u) t).1 v with ⟨rfl, h⟩ | h
    · rw [h]
      exact nodeTick_f c p a nr s u (worldAt w u) t
    · rw [h]
      exact preceq_self _
  | Deliver u o t =>
    unfold worldStep
    dsimp only
    rcases worldAt_insert w u (nodeProcess c p s (worldAt w u) o) v with ⟨rfl, h⟩ | h
    · rw [h]
      exact nodeProcess_f c p s (worldAt w u) o
    · rw [h]
      exact preceq_self _

/-- event の列の畳み込みは、どのノードの `f` も縮めない(`worldStep_f` と `preceq` の推移律)。 -/
theorem foldl_worldStep_f (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId) (a : ValidatorId → Nat → Bool)
    (nr : ValidatorId → Nat → BlockId) (s : Model.Consensus.Execution.Setup.Setup) :
    ∀ (l : List NamedEvent) (w : NamedWorld) (v : ValidatorId),
      preceq (worldAt w v).st.core.f
        (worldAt (List.foldl (fun w ev => worldStep c p a nr s w ev) w l) v).st.core.f = true
  | [], _, _ => preceq_self _
  | ev :: l, w, v => by
    rw [List.foldl_cons]
    exact preceq_trans (worldStep_f c p a nr s w ev v) (foldl_worldStep_f c p a nr s l _ v)

/-- `EventsSorted rho` の下で finalized の読みは時刻について単調(property `MonotoneFrom … Finalized 0`)。 -/
theorem monotoneFrom_finalized (c : Nat → NaruStd.Set ValidatorId) (p : Nat → ValidatorId)
    (a : ValidatorId → Nat → Bool) (nr : ValidatorId → Nat → BlockId)
    (s : Model.Consensus.Execution.Setup.Setup) (rho : NamedRun)
    (hs : Statements.Consensus.Spec.Conditions.EventsSorted rho) :
    Statements.Consensus.Spec.Properties.MonotoneFrom c p a nr s rho
      Model.Consensus.Spec.Interface.Output.Finalized 0 := by
  unfold Statements.Consensus.Spec.Properties.MonotoneFrom
  intro v t t2 h
  obtain ⟨⟨⟨_, _⟩, htt2⟩, _⟩ := h
  show preceq (storeAt c p a nr s rho v t).core.f (storeAt c p a nr s rho v t2).core.f = true
  unfold storeAt readAt
  obtain ⟨l2, hl2⟩ := filter_le_append t t2 htt2 rho.events (pairwise_of_eventsSorted rho hs)
  rw [hl2, List.foldl_append]
  exact foldl_worldStep_f c p a nr s l2 _ v

end Proofs.Consensus.FinalizedMonotone
