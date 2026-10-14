import Proofs.Sample

/-!
証明基盤の検体(C70)の `Proofs` のルート。`Proofs/Sample.lean`(正しい証明・`sorry`・束縛 hash の違い・束縛行の欠落)と
`Proofs/Invalid.lean`(型の違う theorem・`axiom` への依存・一覧に無い修飾名の束縛行。`naru_test proofs` はこれを除いた複製も走らせる)。
`lakefile.toml` の `Proofs` は `globs = ["Proofs.*"]` なので、このルートが import しなくても `Proofs/**.lean` はビルドされる。
-/
