import NaruStd
import Model.Consensus.Objects.Identifiers
import Mathlib.Tactic

/-!
# `NaruStd.Table` の読み書きと `ValidatorId` の順序の補題(C71 の補題)

生成 Model の world(`Model.Consensus.Execution.Run.NamedWorld = NaruStd.Table ValidatorId NamedNodeState`)は、
`worldStep` が `Table.insert` で 1 ノードの状態を置き換え、`worldAt` が `Table.getOr` で読む。stdlib の `Table`
(`stdlib/Model/NaruStd/Table.lean`: 鍵の昇順・重複なしの連想リスト。`insert` は `insertSorted`、`get?` は `find?`)には theorem が
無いので、ここで「挿入した鍵を読めば挿入した値、他の鍵を読めば元の値」を示す。鍵の `compare` には `.eq` の推移性
(`compare a b = .eq → compare b c = .eq → compare a c = .eq`)だけを前提にし、`ValidatorId`(欄 `value : Nat` の record、
`deriving Ord` = `(compare a.value b.value).then .eq`)ではそれが `a = b` と同値であることから満たす。
手書きの world は `ValidatorId → NodeState` の関数なので、対応する手書きの補題は無い(naru 側だけの補助)。
-/

namespace Proofs.Consensus.Tables

open Model.Consensus.Objects.Identifiers

/-- `ValidatorId` の派生 `Ord`: `compare a b = .eq` は `a = b` と同値(`Nat.compare_eq_eq`)。 -/
theorem vid_compare_eq_iff (a b : ValidatorId) : compare a b = .eq ↔ a = b := by
  cases a with
  | mk x =>
    cases b with
    | mk y =>
      have h : compare (ValidatorId.mk x) (ValidatorId.mk y) = compare x y := by
        show (compare x y).then .eq = compare x y
        cases compare x y <;> rfl
      rw [h, Nat.compare_eq_eq, ValidatorId.mk.injEq]

/-- `ValidatorId` の `compare` の `.eq` は推移的(`Table` の補題の前提)。 -/
theorem vid_compare_eq_trans (a b c : ValidatorId) (hab : compare a b = .eq) (hbc : compare b c = .eq) :
    compare a c = .eq := by
  rw [vid_compare_eq_iff] at hab hbc ⊢
  exact hab.trans hbc

section Table

variable {κ ν : Type} [Ord κ]

/-- `insertSorted k v es` を鍵 `k'` で `find?` すると、`compare k k' = .eq` なら挿入した項目 `(k, v)`、
さもなければ元の `es` と同じ結果。`es` の帰納法で `compare k e.1` の 3 分岐を追う。 -/
theorem find?_insertSorted
    (heq : ∀ a b c : κ, compare a b = .eq → compare b c = .eq → compare a c = .eq)
    (k : κ) (v : ν) (k' : κ) :
    ∀ es : List (κ × ν),
      (compare k k' = .eq ∧
        (NaruStd.Table.insertSorted k v es).find? (fun e => compare e.1 k' == .eq) = some (k, v)) ∨
      (NaruStd.Table.insertSorted k v es).find? (fun e => compare e.1 k' == .eq) =
        es.find? (fun e => compare e.1 k' == .eq)
  | [] => by
    by_cases hk : compare k k' = .eq
    · exact Or.inl ⟨hk, by simp [NaruStd.Table.insertSorted, hk]⟩
    · exact Or.inr (by simp [NaruStd.Table.insertSorted, hk])
  | e :: es => by
    cases hc : compare k e.1 with
    | lt =>
      simp only [NaruStd.Table.insertSorted, hc]
      by_cases hk : compare k k' = .eq
      · exact Or.inl ⟨hk, List.find?_cons_of_pos (by simp [hk])⟩
      · exact Or.inr (List.find?_cons_of_neg (by simp [hk]))
    | eq =>
      simp only [NaruStd.Table.insertSorted, hc]
      by_cases hk : compare k k' = .eq
      · exact Or.inl ⟨hk, List.find?_cons_of_pos (by simp [hk])⟩
      · refine Or.inr ?_
        have he : ¬ compare e.1 k' = .eq := fun h => hk (heq k e.1 k' hc h)
        rw [List.find?_cons_of_neg (by simp [hk]), List.find?_cons_of_neg (by simp [he])]
    | gt =>
      simp only [NaruStd.Table.insertSorted, hc]
      by_cases he : compare e.1 k' = .eq
      · exact Or.inr (by rw [List.find?_cons_of_pos (by simp [he]), List.find?_cons_of_pos (by simp [he])])
      · rw [List.find?_cons_of_neg (by simp [he]), List.find?_cons_of_neg (by simp [he])]
        exact find?_insertSorted heq k v k' es

/-- `(t.insert k v).getOr k' d` は、`compare k k' = .eq` なら `v`、さもなければ `t.getOr k' d`。 -/
theorem getOr_insert
    (heq : ∀ a b c : κ, compare a b = .eq → compare b c = .eq → compare a c = .eq)
    (t : NaruStd.Table κ ν) (k : κ) (v : ν) (k' : κ) (d : ν) :
    (compare k k' = .eq ∧ (t.insert k v).getOr k' d = v) ∨ (t.insert k v).getOr k' d = t.getOr k' d := by
  rcases find?_insertSorted heq k v k' t.entries with ⟨hk, hf⟩ | hf
  · exact Or.inl ⟨hk, by simp [NaruStd.Table.getOr, NaruStd.Table.get?, NaruStd.Table.insert, hf]⟩
  · exact Or.inr (by simp [NaruStd.Table.getOr, NaruStd.Table.get?, NaruStd.Table.insert, hf])

end Table

end Proofs.Consensus.Tables
