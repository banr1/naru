import NaruStd
import Model.Consensus.Objects.Identifiers
import Proofs.Consensus.Orders
import Mathlib.Tactic

/-!
# stdlib `NaruStd.Set` の所属と整列の補題(C71 の補題)

`NaruStd.Set α`(`stdlib/Model/NaruStd/NaruStd.Set.lean`)は昇順・重複なしのリスト `elems` で、`contains` は
`elems.any (compare x · == .eq)`、`insert` は `insertSorted`、`union` は `foldl insert`、`of` / `List.toSet` は
`foldl insert empty`、`inter` は `filter contains`。stdlib には theorem が無いので、ここで
(1) 要素の `compare` が `.eq ↔ =` を満たす型について所属を `List.Mem` に言い換え(`contains_iff_mem` /
`mem_insert_iff` / `mem_union_iff` / `mem_of_iff` / `mem_inter_iff`)、
(2) `ValidatorId` の集合について狭義昇順 `Sorted` が各構築で保たれることと、`Sorted` なら `NaruStd.Set.sum` が
`Finset.sum` に等しいこと(重複が無いので mathlib の和の補題に乗る)を示す。
手書き側は `Finset V` なので対応する補題は無い(naru 側だけの補助)。
-/

namespace Proofs.Consensus.Sets

/-! ## 所属(`compare` が `.eq ↔ =` の型) -/

section Generic

variable {α : Type} [Ord α] (heq : ∀ a b : α, compare a b = .eq ↔ a = b)
include heq

/-- `insertSorted x l` の要素は `x` か `l` の要素。 -/
theorem mem_insertSorted (x z : α) : ∀ l : List α, z ∈ NaruStd.Set.insertSorted x l ↔ z = x ∨ z ∈ l
  | [] => by simp [NaruStd.Set.insertSorted]
  | y :: ys => by
    cases hc : compare x y with
    | lt =>
      simp only [NaruStd.Set.insertSorted, hc, List.mem_cons]
    | eq =>
      have hxy : x = y := (heq x y).mp hc
      simp only [NaruStd.Set.insertSorted, hc, List.mem_cons]
      rw [hxy]
      tauto
    | gt =>
      simp only [NaruStd.Set.insertSorted, hc, List.mem_cons, mem_insertSorted x z ys]
      tauto

/-- `contains s x = true` は `x ∈ s.elems`。 -/
theorem contains_iff_mem (s : NaruStd.Set α) (x : α) : s.contains x = true ↔ x ∈ s.elems := by
  unfold NaruStd.Set.contains
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h : compare x y = .eq := by simpa using hxy
    rw [heq] at h
    subst h
    exact hy
  · intro hx
    exact ⟨x, hx, by simp [(heq x x).mpr rfl]⟩

/-- `insert` の所属。 -/
theorem mem_insert_iff (s : NaruStd.Set α) (x z : α) : z ∈ (s.insert x).elems ↔ z = x ∨ z ∈ s.elems :=
  mem_insertSorted heq x z s.elems

/-- `foldl insert` の所属。 -/
theorem mem_foldl_insert_iff : ∀ (l : List α) (s : NaruStd.Set α) (z : α),
    z ∈ (l.foldl NaruStd.Set.insert s).elems ↔ z ∈ l ∨ z ∈ s.elems
  | [], s, z => by simp
  | y :: ys, s, z => by
    rw [List.foldl_cons, mem_foldl_insert_iff ys, mem_insert_iff heq, List.mem_cons]
    tauto

/-- `union` の所属。 -/
theorem mem_union_iff (s t : NaruStd.Set α) (z : α) : z ∈ (s.union t).elems ↔ z ∈ s.elems ∨ z ∈ t.elems := by
  show z ∈ (t.elems.foldl NaruStd.Set.insert s).elems ↔ _
  rw [mem_foldl_insert_iff heq]
  tauto

/-- `NaruStd.Set.of` の所属。 -/
theorem mem_of_iff (l : List α) (z : α) : z ∈ (NaruStd.Set.of l).elems ↔ z ∈ l := by
  show z ∈ (l.foldl NaruStd.Set.insert NaruStd.Set.empty).elems ↔ _
  rw [mem_foldl_insert_iff heq]
  simp [NaruStd.Set.empty]

/-- `List.toSet` の所属。 -/
theorem mem_toSet_iff (l : List α) (z : α) : z ∈ (NaruStd.List.toSet l).elems ↔ z ∈ l :=
  mem_of_iff heq l z

/-- `inter` の所属。 -/
theorem mem_inter_iff (s t : NaruStd.Set α) (z : α) : z ∈ (s.inter t).elems ↔ z ∈ s.elems ∧ z ∈ t.elems := by
  show z ∈ s.elems.filter t.contains ↔ _
  rw [List.mem_filter, contains_iff_mem heq]

/-- `foldl (fun acc x => acc.union (f x))` の所属(`flatMap` の内側)。 -/
theorem mem_foldl_union_iff {γ : Type} (f : γ → NaruStd.Set α) : ∀ (l : List γ) (s : NaruStd.Set α) (z : α),
    z ∈ (l.foldl (fun acc x => acc.union (f x)) s).elems ↔ z ∈ s.elems ∨ ∃ x ∈ l, z ∈ (f x).elems
  | [], _, _ => by simp
  | y :: ys, s, z => by
    rw [List.foldl_cons, mem_foldl_union_iff f ys, mem_union_iff heq]
    simp only [List.exists_mem_cons_iff]
    tauto

/-- `flatMap` の所属(各要素の集合の和集合。走査する側の型 `γ` の `compare` には何も要らない)。 -/
theorem mem_flatMap_iff {γ : Type} [Ord γ] (s : NaruStd.Set γ) (f : γ → NaruStd.Set α) (z : α) :
    z ∈ (s.flatMap f).elems ↔ ∃ x ∈ s.elems, z ∈ (f x).elems := by
  show z ∈ (s.elems.foldl (fun acc x => acc.union (f x)) NaruStd.Set.empty).elems ↔ _
  rw [mem_foldl_union_iff heq]
  simp [NaruStd.Set.empty]

end Generic

/-- `singleton` の所属(`compare` の前提は要らない)。 -/
theorem mem_singleton_iff {α : Type} [Ord α] (x z : α) : z ∈ (NaruStd.Set.singleton x).elems ↔ z = x :=
  List.mem_singleton

/-! ## `ValidatorId` の集合: 整列と `Finset` への橋 -/

section Validator

open Model.Consensus.Objects.Identifiers
open Proofs.Consensus.Orders

/-- `ValidatorId` の集合。 -/
abbrev VSet := NaruStd.Set ValidatorId

/-- `ValidatorId` の `compare` は `.eq ↔ =`(`Tables.lean`)。 -/
theorem vid_eq (a b : ValidatorId) : compare a b = .eq ↔ a = b :=
  Proofs.Consensus.Tables.vid_compare_eq_iff a b

/-- 狭義昇順(`value` の `<`)。stdlib の構築関数が保つ表現の不変条件をここで明示する。 -/
def Sorted (s : VSet) : Prop := s.elems.Pairwise (fun a b => a.value < b.value)

/-- 狭義昇順なら重複が無い。 -/
theorem Sorted.nodup {s : VSet} (h : Sorted s) : s.elems.Nodup :=
  List.nodup_iff_pairwise_ne.mpr (h.imp fun hab hab' => by subst hab'; exact Nat.lt_irrefl _ hab)

/-- `insertSorted` は狭義昇順を保つ。 -/
theorem sorted_insertSorted (x : ValidatorId) : ∀ l : List ValidatorId,
    l.Pairwise (fun a b => a.value < b.value) → (NaruStd.Set.insertSorted x l).Pairwise (fun a b => a.value < b.value)
  | [], _ => by simp [NaruStd.Set.insertSorted]
  | y :: ys, hl => by
    rw [List.pairwise_cons] at hl
    obtain ⟨hy, hys⟩ := hl
    cases hc : compare x y with
    | lt =>
      simp only [NaruStd.Set.insertSorted, hc]
      rw [vid_compare, Nat.compare_eq_lt] at hc
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr ⟨hy, hys⟩⟩
      intro b hb
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hc
      · exact Nat.lt_trans hc (hy b hb)
    | eq =>
      simp only [NaruStd.Set.insertSorted, hc]
      exact List.pairwise_cons.mpr ⟨hy, hys⟩
    | gt =>
      simp only [NaruStd.Set.insertSorted, hc]
      rw [vid_compare, Nat.compare_eq_gt] at hc
      rw [List.pairwise_cons]
      refine ⟨?_, sorted_insertSorted x ys hys⟩
      intro b hb
      rw [mem_insertSorted vid_eq] at hb
      rcases hb with rfl | hb
      · exact hc
      · exact hy b hb

theorem Sorted.insert {s : VSet} (h : Sorted s) (x : ValidatorId) : Sorted (s.insert x) :=
  sorted_insertSorted x s.elems h

theorem Sorted.empty : Sorted (NaruStd.Set.empty : VSet) := List.Pairwise.nil

theorem Sorted.foldl_insert : ∀ (l : List ValidatorId) {s : VSet}, Sorted s → Sorted (l.foldl NaruStd.Set.insert s)
  | [], _, hs => hs
  | y :: ys, _, hs => by
    rw [List.foldl_cons]
    exact Sorted.foldl_insert ys (hs.insert y)

theorem Sorted.union {s : VSet} (hs : Sorted s) (t : VSet) : Sorted (s.union t) :=
  Sorted.foldl_insert t.elems hs

theorem Sorted.of (l : List ValidatorId) : Sorted (NaruStd.Set.of l) :=
  Sorted.foldl_insert l Sorted.empty

theorem Sorted.toSet (l : List ValidatorId) : Sorted (NaruStd.List.toSet l) := Sorted.of l

theorem Sorted.inter {s : VSet} (hs : Sorted s) (t : VSet) : Sorted (s.inter t) := by
  show (s.elems.filter t.contains).Pairwise _
  exact List.Pairwise.filter t.contains hs

/-- `union` の `toFinset` は `toFinset` の和。 -/
theorem toFinset_union (s t : VSet) : (s.union t).elems.toFinset = s.elems.toFinset ∪ t.elems.toFinset := by
  ext z
  simp only [List.mem_toFinset, Finset.mem_union, mem_union_iff vid_eq]

/-- `inter` の `toFinset` は `toFinset` の交わり。 -/
theorem toFinset_inter (s t : VSet) : (s.inter t).elems.toFinset = s.elems.toFinset ∩ t.elems.toFinset := by
  ext z
  simp only [List.mem_toFinset, Finset.mem_inter, mem_inter_iff vid_eq]

/-- `List.toSet` の `toFinset` は元のリストの `toFinset`。 -/
theorem toFinset_toSet (l : List ValidatorId) : (NaruStd.List.toSet l).elems.toFinset = l.toFinset := by
  ext z
  simp only [List.mem_toFinset, mem_toSet_iff vid_eq]

/-- `foldl (· + f ·) n l = n + (l.map f).sum`。 -/
theorem foldl_add (f : ValidatorId → Nat) : ∀ (l : List ValidatorId) (n : Nat),
    l.foldl (fun acc x => acc + f x) n = n + (l.map f).sum
  | [], n => by simp
  | x :: l, n => by
    rw [List.foldl_cons, foldl_add f l, List.map_cons, List.sum_cons]
    omega

/-- `Sorted` な集合の `NaruStd.Set.sum` は `toFinset` 上の `Finset.sum`。 -/
theorem sum_eq_finset_sum {s : VSet} (hs : Sorted s) (f : ValidatorId → Nat) :
    s.sum f = ∑ v ∈ s.elems.toFinset, f v := by
  unfold NaruStd.Set.sum
  rw [foldl_add, Nat.zero_add, ← List.sum_toFinset f hs.nodup]

end Validator

end Proofs.Consensus.Sets
