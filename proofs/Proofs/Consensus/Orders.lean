import Model.Consensus.Objects.Blocks
import Model.Consensus.Objects.NamedBlocks
import Proofs.Consensus.Tables

/-!
# 派生 `Ord` の `.eq` と等しさの対応(C71 の補題)

生成 Model の record / enum は `deriving Ord` で辞書式の `compare`(`(compare a.f₁ b.f₁).then (… .then .eq)`)を持ち、
stdlib の `Set` / `Table` はその `compare == .eq` で所属を判定する。ここでは `BlockId` / `ValidatorId` / `Option` /
`HeightPair` / `FinalityPair` / `CombinedAttestation` / `Bool` / `List` / `GoldfishVote` / `NamedHeightPair` / `NamedAttestation` /
`Block` / `NamedBlock` について `compare a b = .eq ↔ a = b` を示し、`Set` / `Table` の所属を Lean の `List.Mem` に
言い換えられるようにする(`Proofs/Consensus/Sets.lean` / `Tables.lean`)。再帰する `Block` / `NamedBlock` の `compare` は、
Model backend が `deriving Ord` の代わりに構造的再帰で明示的に定義する `Block.naruCompare` / `NamedBlock.naruCompare`
(`docs/architecture.md`「再帰する型の `Ord`」。`deriving Ord` のままでは Lean 4.34 が `partial` にするので不透明で、
この補題が書けない)。手書き側は `Finset` を使うので対応する補題は無い(naru 側だけの補助)。
-/

namespace Proofs.Consensus.Orders

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks

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

/-! ## `Bool` / `List` と、名前付きブロックの構成要素 -/

/-- `Bool` の `Ord`(core): `compare a b = .eq ↔ a = b`。 -/
theorem bool_compare_eq_iff (a b : Bool) : compare a b = .eq ↔ a = b := by
  cases a <;> cases b <;> decide

/-- `List.compareLex`(リストの辞書式比較): 要素の `cmp` が `.eq ↔ =` なら `.eq ↔ =`。 -/
theorem compareLex_eq_iff {α : Type} (cmp : α → α → Ordering) (h : ∀ a b, cmp a b = .eq ↔ a = b) :
    ∀ l m : List α, List.compareLex cmp l m = .eq ↔ l = m
  | [], [] => by rw [List.compareLex_nil_nil]; simp
  | [], _ :: _ => by rw [List.compareLex_nil_cons]; simp
  | _ :: _, [] => by rw [List.compareLex_cons_nil]; simp
  | a :: l, b :: m => by
    rw [List.compareLex_cons_cons, then_eq_eq, h, compareLex_eq_iff cmp h l m, List.cons.injEq]

/-- `List` の `Ord`(core、`List.compareLex compare`): 要素の `compare` が `.eq ↔ =` なら `.eq ↔ =`。 -/
theorem list_compare_eq_iff {α : Type} [Ord α] (h : ∀ a b : α, compare a b = .eq ↔ a = b) (l m : List α) :
    compare l m = .eq ↔ l = m :=
  compareLex_eq_iff compare h l m

/-- `GoldfishVote` の派生 `Ord`: `compare a b = .eq ↔ a = b`。 -/
theorem gv_compare_eq_iff (a b : GoldfishVote) : compare a b = .eq ↔ a = b := by
  cases a with
  | mk v s h =>
    cases b with
    | mk v' s' h' =>
      show (compare v v').then ((compare s s').then ((compare h h').then .eq)) = .eq ↔ _
      rw [then_eq_eq, then_eq_eq, then_eq, Proofs.Consensus.Tables.vid_compare_eq_iff, Nat.compare_eq_eq,
        bid_compare_eq_iff, GoldfishVote.mk.injEq]

/-- `NamedHeightPair` の派生 `Ord`: `compare a b = .eq ↔ a = b`。 -/
theorem nhp_compare_eq_iff (a b : NamedHeightPair) : compare a b = .eq ↔ a = b := by
  cases a with
  | Empty =>
    cases b with
    | Empty => simp [compare, instOrdNamedHeightPair.ord]
    | Vote n r t => simp [compare, instOrdNamedHeightPair.ord]
  | Vote m q u =>
    cases b with
    | Empty => simp [compare, instOrdNamedHeightPair.ord]
    | Vote n r t =>
      show (compare m n).then ((compare q r).then ((compare u t).then .eq)) = .eq ↔ _
      rw [then_eq_eq, then_eq_eq, then_eq, Nat.compare_eq_eq, bid_compare_eq_iff, bool_compare_eq_iff,
        NamedHeightPair.Vote.injEq]

/-- `NamedAttestation` の派生 `Ord`: `compare a b = .eq ↔ a = b`。 -/
theorem na_compare_eq_iff (a b : NamedAttestation) : compare a b = .eq ↔ a = b := by
  cases a with
  | mk v r c hp fp =>
    cases b with
    | mk v' r' c' hp' fp' =>
      show (compare v v').then ((compare r r').then ((compare c c').then ((compare hp hp').then
        ((compare fp fp').then .eq)))) = .eq ↔ _
      rw [then_eq_eq, then_eq_eq, then_eq_eq, then_eq_eq, then_eq, Proofs.Consensus.Tables.vid_compare_eq_iff,
        Nat.compare_eq_eq, opt_compare_eq_iff bid_compare_eq_iff, nhp_compare_eq_iff,
        opt_compare_eq_iff fp_compare_eq_iff, NamedAttestation.mk.injEq]

/-! ## 再帰する `Block` / `NamedBlock`(backend の明示的な `naruCompare`) -/

/-- `Block` の `Ord`(`Block.naruCompare`): `compare a b = .eq ↔ a = b`。`b` の構造帰納法(親の比較に帰納法の仮定)。 -/
theorem block_compare_eq_iff : ∀ a b : Block, compare a b = .eq ↔ a = b
  | Block.Genesis, Block.Genesis => by
    rw [show compare Block.Genesis Block.Genesis = .eq from rfl]
    simp
  | Block.Genesis, Block.Node p' s' r' v' sup' ats' i' => by
    rw [show compare Block.Genesis (Block.Node p' s' r' v' sup' ats' i') = .lt from rfl]
    simp
  | Block.Node p s r v sup ats i, Block.Genesis => by
    rw [show compare (Block.Node p s r v sup ats i) Block.Genesis = .gt from rfl]
    simp
  | Block.Node p s r v sup ats i, Block.Node p' s' r' v' sup' ats' i' => by
    show (compare p p').then ((compare s s').then ((compare r r').then ((compare v v').then ((compare sup sup').then
      ((compare ats ats').then ((compare i i').then .eq)))))) = .eq ↔ _
    rw [then_eq_eq, then_eq_eq, then_eq_eq, then_eq_eq, then_eq_eq, then_eq_eq, then_eq,
      block_compare_eq_iff p p', Nat.compare_eq_eq, bid_compare_eq_iff, list_compare_eq_iff gv_compare_eq_iff,
      list_compare_eq_iff gv_compare_eq_iff, list_compare_eq_iff ca_compare_eq_iff,
      Proofs.Consensus.Tables.vid_compare_eq_iff, Block.Node.injEq]

/-- `Block` の `compare` の `.eq` は推移的(`Table` の補題の前提)。 -/
theorem block_compare_eq_trans (a b c : Block) (hab : compare a b = .eq) (hbc : compare b c = .eq) :
    compare a c = .eq := by
  rw [block_compare_eq_iff] at hab hbc ⊢
  exact hab.trans hbc

/-- `NamedBlock` の `Ord`(`NamedBlock.naruCompare`): `compare a b = .eq ↔ a = b`。 -/
theorem nb_compare_eq_iff : ∀ a b : NamedBlock, compare a b = .eq ↔ a = b
  | NamedBlock.Genesis, NamedBlock.Genesis => by
    rw [show compare NamedBlock.Genesis NamedBlock.Genesis = .eq from rfl]
    simp
  | NamedBlock.Genesis, NamedBlock.Node p' s' r' v' sup' rows' i' => by
    rw [show compare NamedBlock.Genesis (NamedBlock.Node p' s' r' v' sup' rows' i') = .lt from rfl]
    simp
  | NamedBlock.Node p s r v sup rows i, NamedBlock.Genesis => by
    rw [show compare (NamedBlock.Node p s r v sup rows i) NamedBlock.Genesis = .gt from rfl]
    simp
  | NamedBlock.Node p s r v sup rows i, NamedBlock.Node p' s' r' v' sup' rows' i' => by
    show (compare p p').then ((compare s s').then ((compare r r').then ((compare v v').then ((compare sup sup').then
      ((compare rows rows').then ((compare i i').then .eq)))))) = .eq ↔ _
    rw [then_eq_eq, then_eq_eq, then_eq_eq, then_eq_eq, then_eq_eq, then_eq_eq, then_eq,
      nb_compare_eq_iff p p', Nat.compare_eq_eq, bid_compare_eq_iff, list_compare_eq_iff gv_compare_eq_iff,
      list_compare_eq_iff gv_compare_eq_iff, list_compare_eq_iff na_compare_eq_iff,
      Proofs.Consensus.Tables.vid_compare_eq_iff, NamedBlock.Node.injEq]

end Proofs.Consensus.Orders
