/-!
# NaruStd.Basic — `Result` と、backend が前提にする `Ord` インスタンス

naru の `eq` capability を持つ型には、backend が `DecidableEq` と(`Set` / `Table` の正規化に使う隠れた)
`Ord` を生成する。primitive の合成型(tuple / Unit / Result)にもここで `Ord` を与え、
「`eq` を持つ型は必ず `Ord` を持つ」を帰納的に保つ。
-/

namespace NaruStd

instance : Ord Unit := ⟨fun _ _ => .eq⟩

/-- tuple は成分の辞書式順序。 -/
instance instOrdProd [Ord α] [Ord β] : Ord (α × β) := lexOrd

/-- naru の `Result<T, E>`。`Ok` が `Err` より小さい。 -/
inductive Result (α : Type) (ε : Type) where
  | ok (value : α)
  | err (error : ε)
deriving DecidableEq, Repr, Ord

namespace Result

def isOk : Result α ε → Bool
  | .ok _ => true
  | .err _ => false

def isErr : Result α ε → Bool
  | .ok _ => false
  | .err _ => true

def ok? : Result α ε → Option α
  | .ok a => some a
  | .err _ => none

end Result

/-- `Option` の `Ord` は core にある(`none < some _`)。`List` / `Nat` / `Int` / `Bool` / `String` も core。 -/
example : Ord (Option Nat) := inferInstance
example : Ord (List Nat) := inferInstance

end NaruStd
