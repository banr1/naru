import Model.Consensus.Execution.Run
import Statements.Consensus.Spec.Conditions
import Proofs.Consensus.Tables
import Mathlib.Tactic

/-!
# run の読みの接頭辞(C71 の補題)

生成 Model の run(`Model/Consensus/Execution/Run.lean`)は event の列 `rho.events` を `worldStep` で畳み込み、時刻 `t` の読み
`readAt … t` は `eventTime ev ≤ t` の event だけを `List.filter` してから畳み込む。条件 `EventsSorted rho`
(`Statements/Consensus/Spec/Conditions.lean`: 添字 `i < j` の 2 event の `eventKey` の `compare` が `.gt` でない)の下では
event の時刻は非減少なので、`t ≤ t2` なら `filter (≤ t)` は `filter (≤ t2)` の接頭辞になる(`filter_le_append`)。
あわせて、`worldStep` が `Table.insert` で 1 ノードだけを置き換えることの読み(`worldAt_insert`)をここに置く。
手書き `finalized_readAt_mono_of_sorted`(`DecoupledConsensusProofs/Bridge/FinalizedLive.lean`)が sorted な event 列に
対して使う接頭辞の議論に当たる。
-/

namespace Proofs.Consensus.Runs

open Model.Consensus.Objects.Identifiers Model.Consensus.Execution.Node Model.Consensus.Execution.Run

/-- `eventKey`(時刻, phase)の辞書式 `compare` が `.gt` でなければ時刻は非減少(`lexOrd` は先頭成分の `compare` が
`.gt` なら `.gt`)。 -/
theorem time_le_of_key_ne_gt {a b : NamedEvent} (h : compare (eventKey a) (eventKey b) ≠ .gt) :
    eventTime a ≤ eventTime b := by
  by_contra hlt
  have hlt' := not_le.mp hlt
  apply h
  show (compare (eventTime a) (eventTime b)).then (compare (eventPhase a) (eventPhase b)) = .gt
  rw [Int.compare_eq_gt.mpr hlt']
  rfl

/-- `EventsSorted rho` から、event の列が時刻で `Pairwise` に非減少であること。 -/
theorem pairwise_of_eventsSorted (rho : NamedRun) (h : Statements.Consensus.Spec.Conditions.EventsSorted rho) :
    rho.events.Pairwise (fun a b => eventTime a ≤ eventTime b) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hs := h i j hij
  simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hs
  exact time_le_of_key_ne_gt hs

/-- 時刻が非減少な event の列では、`t ≤ t2` のとき `filter (≤ t)` は `filter (≤ t2)` の接頭辞。 -/
theorem filter_le_append (t t2 : Int) (ht : t ≤ t2) :
    ∀ (l : List NamedEvent), l.Pairwise (fun a b => eventTime a ≤ eventTime b) →
      ∃ l2, l.filter (fun ev => decide (eventTime ev ≤ t2)) =
        l.filter (fun ev => decide (eventTime ev ≤ t)) ++ l2
  | [], _ => ⟨[], rfl⟩
  | x :: xs, hp => by
    rw [List.pairwise_cons] at hp
    obtain ⟨hx, hxs⟩ := hp
    by_cases hxt : eventTime x ≤ t
    · have hxt2 : eventTime x ≤ t2 := le_trans hxt ht
      obtain ⟨l2, hl2⟩ := filter_le_append t t2 ht xs hxs
      exact ⟨l2, by simp [List.filter_cons, hxt, hxt2, hl2]⟩
    · refine ⟨(x :: xs).filter (fun ev => decide (eventTime ev ≤ t2)), ?_⟩
      have hnil : (x :: xs).filter (fun ev => decide (eventTime ev ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hxt
        · exact fun hyt => hxt (le_trans (hx y hy') hyt)
      rw [hnil, List.nil_append]

/-- world の 1 ノードの置き換え: `worldAt (insert w u n) v` は `u = v` なら `n`、さもなければ `worldAt w v`。 -/
theorem worldAt_insert (w : NamedWorld) (u : ValidatorId) (n : NamedNodeState) (v : ValidatorId) :
    (u = v ∧ worldAt (NaruStd.Table.insert w u n) v = n) ∨
      worldAt (NaruStd.Table.insert w u n) v = worldAt w v := by
  unfold worldAt
  rcases Proofs.Consensus.Tables.getOr_insert Proofs.Consensus.Tables.vid_compare_eq_trans w u n v initialNode
    with ⟨hk, h⟩ | h
  · exact Or.inl ⟨(Proofs.Consensus.Tables.vid_compare_eq_iff u v).mp hk, h⟩
  · exact Or.inr h

end Proofs.Consensus.Runs
