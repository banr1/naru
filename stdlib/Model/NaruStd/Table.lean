import NaruStd.Set

/-!
# NaruStd.Table — naru の `Table<K, V>`

鍵の `Ord` で昇順に正規化した、鍵の重複がない連想リスト。`Set` と同じく表現は一意。
-/

namespace NaruStd

structure Table (κ : Type) (ν : Type) where
  /-- 鍵の昇順・鍵の重複なし(構築関数が保つ不変条件)。 -/
  entries : List (κ × ν)
deriving DecidableEq, Ord

instance [Repr κ] [Repr ν] : Repr (Table κ ν) where
  reprPrec t _ := "Table.of " ++ repr t.entries

namespace Table

variable {κ ν : Type} [Ord κ]

def empty : Table κ ν := ⟨[]⟩

def size (t : Table κ ν) : Nat := t.entries.length

def isEmpty (t : Table κ ν) : Bool := t.entries.isEmpty

def get? (t : Table κ ν) (k : κ) : Option ν :=
  (t.entries.find? fun e => compare e.1 k == .eq).map (·.2)

def getOr (t : Table κ ν) (k : κ) (d : ν) : ν := (t.get? k).getD d

def contains (t : Table κ ν) (k : κ) : Bool := (t.get? k).isSome

/-- 昇順リストへの挿入(同じ鍵があれば値を置き換える)。 -/
def insertSorted (k : κ) (v : ν) : List (κ × ν) → List (κ × ν)
  | [] => [(k, v)]
  | e :: es =>
    match compare k e.1 with
    | .lt => (k, v) :: e :: es
    | .eq => (k, v) :: es
    | .gt => e :: insertSorted k v es

def insert (t : Table κ ν) (k : κ) (v : ν) : Table κ ν := ⟨insertSorted k v t.entries⟩

def remove (t : Table κ ν) (k : κ) : Table κ ν := ⟨t.entries.filter fun e => compare e.1 k != .eq⟩

/-- 鍵の集合(鍵の昇順・重複なしなので、そのまま `Set` の表現になる)。 -/
def keys (t : Table κ ν) : Set κ := ⟨t.entries.map (·.1)⟩

/-- 項目の集合(鍵の昇順で鍵が重複しないので、tuple の辞書式順序でも昇順・重複なし)。 -/
def entriesSet [Ord ν] (t : Table κ ν) : Set (κ × ν) := ⟨t.entries⟩

/-- 鍵を保って値だけを写す(全域写像の `fun k => f (t k)`)。鍵の列は変わらないので不変条件を保つ。 -/
def mapValues {μ : Type} (t : Table κ ν) (f : ν → μ) : Table κ μ :=
  ⟨t.entries.map fun e => (e.1, f e.2)⟩

end Table

end NaruStd
