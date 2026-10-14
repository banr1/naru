import Model.Consensus.Objects.Parameters
import Model.Consensus.Spec.Conditions
import Statements.Consensus.Spec.Accountability
import Proofs.Consensus.Sets
import Mathlib.Tactic

/-!
# 重みと定足数の交わり(C71 の補題)

生成 Model の `weightOf e s = Set.sum s (weightOfValidator e)`、`totalWeight e = weightOf e (validators e)`、
`quorumCheck e s = decide (finalityThreshold e ≤ weightOf e s)` について、`Sorted` な集合の重みを `Finset.sum` に写し、
(1) どの集合の重みも電子集団の総重み `W` を超えない(重みの表に無い validator の重みは `getOr … 0 = 0`)、
(2) `weight (s ∪ t) + weight (s ∩ t) = weight s + weight t`(mathlib `Finset.sum_union_inter`)、
(3) 2 つの定足数(重み `q` 以上)の交わりは `2q ≤ W + weight (s ∩ t)`(`HasIntersectionWeight`)を示す。
手書き `weightOf_le_totalWeight` / `quorum_intersection`(`DecoupledConsensusProofs/Protocol/ChainState/Evidence.lean`)に当たる。
`SetupWellFormed` の `normalizedValidators (validators e) = true` から `Sorted (validators e)` を取る補題も置く。
-/

namespace Proofs.Consensus.Weights

open Model.Consensus.Objects.Weights Model.Consensus.Objects.Parameters Model.Consensus.Objects.Identifiers
open Proofs.Consensus.Sets

/-- `Sorted` な集合の重みは `toFinset` 上の和。 -/
theorem weightOf_eq {e : Electorate} {s : VSet} (hs : Sorted s) :
    weightOf e s = ∑ v ∈ s.elems.toFinset, weightOfValidator e v := by
  unfold weightOf
  exact sum_eq_finset_sum hs _

/-- 総重みは `validators e` の `toFinset` 上の和。 -/
theorem totalWeight_eq {e : Electorate} (hv : Sorted (validators e)) :
    totalWeight e = ∑ v ∈ (validators e).elems.toFinset, weightOfValidator e v := by
  unfold totalWeight
  exact sum_eq_finset_sum hv _

/-- 重みが 0 でない validator は重みの表の鍵(= `validators e`)にある。 -/
theorem mem_validators_of_weight_ne_zero (e : Electorate) (v : ValidatorId) (h : weightOfValidator e v ≠ 0) :
    v ∈ (validators e).elems := by
  unfold weightOfValidator NaruStd.Table.getOr NaruStd.Table.get? at h
  show v ∈ e.weight.entries.map (·.1)
  cases hf : e.weight.entries.find? (fun en => compare en.1 v == .eq) with
  | none =>
    rw [hf] at h
    exact absurd (by simp) h
  | some en =>
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have hp' : compare en.1 v = .eq := by simpa using hp
    rw [Proofs.Consensus.Tables.vid_compare_eq_iff] at hp'
    rw [← hp']
    exact List.mem_map_of_mem hmem

/-- どの `Sorted` な集合の重みも総重みを超えない。 -/
theorem weightOf_le_totalWeight {e : Electorate} (hv : Sorted (validators e)) {s : VSet} (hs : Sorted s) :
    weightOf e s ≤ totalWeight e := by
  rw [weightOf_eq hs, totalWeight_eq hv]
  apply Finset.sum_le_sum_of_ne_zero
  intro v _ hne
  rw [List.mem_toFinset]
  exact mem_validators_of_weight_ne_zero e v hne

/-- 和集合と交わりの重みの和は、両方の重みの和。 -/
theorem weightOf_union_add_inter {e : Electorate} {s t : VSet} (hs : Sorted s) (ht : Sorted t) :
    weightOf e (s.union t) + weightOf e (s.inter t) = weightOf e s + weightOf e t := by
  rw [weightOf_eq (hs.union t), weightOf_eq (hs.inter t), weightOf_eq hs, weightOf_eq ht,
    toFinset_union, toFinset_inter]
  exact Finset.sum_union_inter

/-- 2 つの定足数の交わりは重み `2q − W` 以上(加法の形 `2q ≤ W + weight (s ∩ t)`)。 -/
theorem quorum_intersection {e : ProtocolEnv} (hv : Sorted (validators e.electorate)) {s t : VSet}
    (hs : Sorted s) (ht : Sorted t) (hq : quorumCheck e.electorate s = true)
    (hq' : quorumCheck e.electorate t = true) :
    Statements.Consensus.Spec.Accountability.HasIntersectionWeight e (s.inter t) := by
  unfold quorumCheck at hq hq'
  rw [decide_eq_true_iff] at hq hq'
  unfold Statements.Consensus.Spec.Accountability.HasIntersectionWeight envQ envW
  have h1 := weightOf_union_add_inter (e := e.electorate) hs ht
  have h2 := weightOf_le_totalWeight hv (hs.union t)
  omega

/-- `normalizedValidators xs = true`(`xs` が自分の正規化と等しい)なら `Sorted xs`。 -/
theorem sorted_of_normalized {xs : VSet} (h : Model.Consensus.Spec.Conditions.normalizedValidators xs = true) :
    Sorted xs := by
  unfold Model.Consensus.Spec.Conditions.normalizedValidators at h
  rw [beq_iff_eq] at h
  rw [h]
  exact Sorted.toSet _

end Proofs.Consensus.Weights
