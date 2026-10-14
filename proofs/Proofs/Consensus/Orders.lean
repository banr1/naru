import Model.Consensus.Objects.Blocks
import Proofs.Consensus.Tables

/-!
# 派生 `Ord` の `.eq` と等しさの対応(C71 の補題)

生成 Model の record / enum は `deriving Ord` で辞書式の `compare`(`(compare a.f₁ b.f₁).then (… .then .eq)`)を持ち、
stdlib の `Set` / `Table` はその `compare == .eq` で所属を判定する。ここでは `BlockId` / `ValidatorId` / `Option` /
`HeightPair` / `FinalityPair` / `CombinedAttestation` について `compare a b = .eq ↔ a = b` を示し、`Set` の所属を
Lean の `List.Mem` に言い換えられるようにする(`Proofs/Consensus/Sets.lean`)。手書き側は `Finset` を使うので対応する補題は無い
(naru 側だけの補助)。
-/

namespace Proofs.Consensus.Orders

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers

/-- `o.then p = .eq` は `o = .eq ∧ p = .eq`。 -/
theorem then_eq_eq (o p : Ordering) : o.then p = .eq ↔ o = .eq ∧ p = .eq := by
  cases o <;> cases p <;> simp [Ordering.then]

/-- `o.then .eq = o`。 -/
theorem then_eq (o : Ordering) : o.then .eq = o := by
  cases o <;> rfl

/-- `BlockId` の派生 `Ord`: `compare a b = .eq ↔ a = b`。 -/
theorem bid_compare_eq_iff (a b : BlockId) : compare a b = .eq ↔ a = b := by
  cases a with
  | mk x =>
    cases b with
    | mk y =>
      show (compare x y).then .eq = .eq ↔ _
      rw [then_eq, Nat.compare_eq_eq, BlockId.mk.injEq]

/-- `ValidatorId` の派生 `Ord` は欄 `value : Nat` の `compare` そのもの。 -/
theorem vid_compare (a b : ValidatorId) : compare a b = compare a.value b.value := by
  cases a with
  | mk x =>
    cases b with
    | mk y =>
      show (compare x y).then .eq = compare x y
      exact then_eq _

/-- `Option` の `Ord`(core): `compare o p = .eq ↔ o = p`(中身の `compare` が `.eq ↔ =` なら)。 -/
theorem opt_compare_eq_iff {α : Type} [Ord α] (h : ∀ a b : α, compare a b = .eq ↔ a = b) (o p : Option α) :
    compare o p = .eq ↔ o = p := by
  cases o with
  | none =>
    cases p with
    | none => simp [compare]
    | some b => simp [compare]
  | some a =>
    cases p with
    | none => simp [compare]
    | some b =>
      show compare a b = .eq ↔ _
      rw [h a b, Option.some.injEq]

/-- `HeightPair` の派生 `Ord`: `compare a b = .eq ↔ a = b`。 -/
theorem hp_compare_eq_iff (a b : HeightPair) : compare a b = .eq ↔ a = b := by
  cases a with
  | Empty =>
    cases b with
    | Empty => simp [compare, instOrdHeightPair.ord]
    | Timeout n => simp [compare, instOrdHeightPair.ord]
    | Target n r => simp [compare, instOrdHeightPair.ord]
  | Timeout m =>
    cases b with
    | Empty => simp [compare, instOrdHeightPair.ord]
    | Timeout n =>
      show (compare m n).then .eq = .eq ↔ _
      rw [then_eq, Nat.compare_eq_eq, HeightPair.Timeout.injEq]
    | Target n r => simp [compare, instOrdHeightPair.ord]
  | Target m q =>
    cases b with
    | Empty => simp [compare, instOrdHeightPair.ord]
    | Timeout n => simp [compare, instOrdHeightPair.ord]
    | Target n r =>
      show (compare m n).then ((compare q r).then .eq) = .eq ↔ _
      rw [then_eq_eq, then_eq, Nat.compare_eq_eq, bid_compare_eq_iff, HeightPair.Target.injEq]

/-- `FinalityPair` の派生 `Ord`: `compare a b = .eq ↔ a = b`。 -/
theorem fp_compare_eq_iff (a b : FinalityPair) : compare a b = .eq ↔ a = b := by
  cases a with
  | mk h t =>
    cases b with
    | mk h' t' =>
      show (compare h h').then ((compare t t').then .eq) = .eq ↔ _
      rw [then_eq_eq, then_eq, Nat.compare_eq_eq, bid_compare_eq_iff, FinalityPair.mk.injEq]

/-- `CombinedAttestation` の派生 `Ord`: `compare a b = .eq ↔ a = b`。 -/
theorem ca_compare_eq_iff (a b : CombinedAttestation) : compare a b = .eq ↔ a = b := by
  cases a with
  | mk v r c hp fp =>
    cases b with
    | mk v' r' c' hp' fp' =>
      show (compare v v').then ((compare r r').then ((compare c c').then ((compare hp hp').then
        ((compare fp fp').then .eq)))) = .eq ↔ _
      rw [then_eq_eq, then_eq_eq, then_eq_eq, then_eq_eq, then_eq, Proofs.Consensus.Tables.vid_compare_eq_iff,
        Nat.compare_eq_eq, opt_compare_eq_iff bid_compare_eq_iff, hp_compare_eq_iff,
        opt_compare_eq_iff fp_compare_eq_iff, CombinedAttestation.mk.injEq]

end Proofs.Consensus.Orders
