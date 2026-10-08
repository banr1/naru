import NaruStd.Set

/-!
# NaruStd.List — naru の `List<T>` のうち Lean core に無いメソッド

`sort(by = …)` は安定ソート(鍵が同じ要素は元の順)。`minBy?` / `maxBy?` は鍵が同じなら先頭に近いもの。
-/

namespace NaruStd.List

def sortBy {α β : Type} [Ord β] (xs : List α) (key : α → β) : List α :=
  xs.mergeSort fun a b => compare (key a) (key b) != .gt

def minBy? {α β : Type} [Ord β] (xs : List α) (key : α → β) : Option α :=
  xs.foldl (init := none) fun acc x =>
    match acc with
    | none => some x
    | some y => if compare (key x) (key y) == .lt then some x else some y

def maxBy? {α β : Type} [Ord β] (xs : List α) (key : α → β) : Option α :=
  xs.foldl (init := none) fun acc x =>
    match acc with
    | none => some x
    | some y => if compare (key x) (key y) == .gt then some x else some y

def toSet {α : Type} [Ord α] (xs : List α) : Set α := Set.of xs

end NaruStd.List
