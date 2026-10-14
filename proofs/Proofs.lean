import Proofs.Consensus.Spec.Claims

/-!
# `Proofs` — プロトコル証明のルート(IDEAL.md C68 / C71)

`proofs/` は Lake ライブラリ `Proofs`(`lakefile.toml`。`srcDir` は `naru.toml` の `proofs` への link `.lake/naru/proofs-src`、
`globs = ["Proofs.*"]` なので `proofs/Proofs/**.lean` はこのルートが import しなくてもビルドされる)。各証明義務(`generated/obligations.json`。
`naru compile` が書く)の theorem `Proofs.<生成 Statements の宣言名の `Statements.` の後>` と、その補題をここに置く。
書き方・束縛行・証明状況の見方は `proofs/README.md`、`lake exe naru proofs` が状況を表示する。

import してよいのは生成 Model / Statements(`Model.*` / `Statements.*`)・`NaruStd`・Lean 本体・mathlib(`Mathlib.*` とその依存)だけ
(依存方向 Model ← Statements ← Proofs)。基準の手書き `DecoupledConsensus*`・`NaruSem`・コンパイラ(`Naru.*`)・`NaruTest` は import しない。
このルートは consensus の証明のモジュールをまとめるだけで、定理は持たない。
-/
