import NaruStd.Basic

/-!
# NaruStd.Set — naru の `Set<T>`

要素の `Ord`(`compare`)で昇順に正規化した、重複のないリスト。すべての構築は `empty` / `singleton` /
`of` / `insert` / … を通るので表現は一意で、`DecidableEq` が集合としての等しさに一致する。
反復(`filter` / `any` / `all` / `map`)は昇順に回るので決定的。要素を 1 つ取る操作は
`findUnique?` / `minBy?` / `maxBy?` だけ、List 化は `sortBy`(naru の `sort(by = …)`)だけ
(コンパイラが E003 / E004 で他を拒否する)。
-/

namespace NaruStd

structure Set (α : Type) where
  /-- 昇順・重複なし(構築関数が保つ不変条件)。 -/
  elems : List α
deriving DecidableEq, Ord

instance [Repr α] : Repr (Set α) where
  reprPrec s _ := "Set.of " ++ repr s.elems

namespace Set

variable {α : Type} [Ord α]

def empty : Set α := ⟨[]⟩

def singleton (x : α) : Set α := ⟨[x]⟩

/-- 昇順リストへの挿入(既にあれば変えない)。 -/
def insertSorted (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    match compare x y with
    | .lt => x :: y :: ys
    | .eq => y :: ys
    | .gt => y :: insertSorted x ys

def insert (s : Set α) (x : α) : Set α := ⟨insertSorted x s.elems⟩

def of (xs : List α) : Set α := xs.foldl insert empty

def size (s : Set α) : Nat := s.elems.length

def isEmpty (s : Set α) : Bool := s.elems.isEmpty

def contains (s : Set α) (x : α) : Bool := s.elems.any fun y => compare x y == .eq

def remove (s : Set α) (x : α) : Set α := ⟨s.elems.filter fun y => compare x y != .eq⟩

def union (s t : Set α) : Set α := t.elems.foldl insert s

def inter (s t : Set α) : Set α := ⟨s.elems.filter t.contains⟩

def diff (s t : Set α) : Set α := ⟨s.elems.filter fun x => !t.contains x⟩

def subset (s t : Set α) : Bool := s.elems.all t.contains

def filter (s : Set α) (p : α → Bool) : Set α := ⟨s.elems.filter p⟩

def map {β : Type} [Ord β] (s : Set α) (f : α → β) : Set β := of (s.elems.map f)

def any (s : Set α) (p : α → Bool) : Bool := s.elems.any p

def all (s : Set α) (p : α → Bool) : Bool := s.elems.all p

/-- 条件を満たす要素がちょうど 1 つならそれ。 -/
def findUnique? (s : Set α) (p : α → Bool) : Option α :=
  match s.elems.filter p with
  | [x] => some x
  | _ => none

/-- 鍵が最小の要素。鍵が同じなら要素自身の順序で最小のもの(昇順なので最初に見つかるもの)。 -/
def minBy? {β : Type} [Ord β] (s : Set α) (key : α → β) : Option α :=
  s.elems.foldl (init := none) fun acc x =>
    match acc with
    | none => some x
    | some y => if compare (key x) (key y) == .lt then some x else some y

/-- 鍵が最大の要素。鍵が同じなら要素自身の順序で最大のもの(昇順なので最後に見つかるもの)。 -/
def maxBy? {β : Type} [Ord β] (s : Set α) (key : α → β) : Option α :=
  s.elems.foldl (init := none) fun acc x =>
    match acc with
    | none => some x
    | some y => if compare (key x) (key y) == .lt then some y else some x

/-- naru の `sort(by = key)`: 鍵の昇順。鍵が同じ要素は要素自身の順序(安定ソート + 昇順の表現)。 -/
def sortBy {β : Type} [Ord β] (s : Set α) (key : α → β) : List α :=
  s.elems.mergeSort fun a b => compare (key a) (key b) != .gt

end Set

end NaruStd
