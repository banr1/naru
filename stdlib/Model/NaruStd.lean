import NaruStd.Basic
import NaruStd.Set
import NaruStd.Table
import NaruStd.List
import NaruStd.Observe

/-!
# NaruStd — naru の Model 用 stdlib(Lean 側)

生成 Model(`generated/Model`)が import する。naru の primitive 型のうち Lean core に直接の対応が無い
`Set` / `Table` / `Result` と、stdlib メソッド表(`compiler/SYNTAX.md`)の Lean 側の実装を置く。

- 計算可能・決定的・total(`partial` / `unsafe` / `noncomputable` / `sorry` / `axiom` を使わない)。
- `Set` と `Table` は要素の `Ord` で正規化した重複なしの昇順リスト。等しい集合は同じ表現になるので
  `DecidableEq` が外延的な等しさと一致する。`Ord` は backend が `derive eq` の型にも(隠れた全順序として)
  生成するもので、naru のユーザには露出しない(IDEAL.md「capability」)。
- mathlib に依存しない(Lean core のみ)。
-/
