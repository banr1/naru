import NaruTest.Common
import NaruTest.Grammar
import NaruTest.Zed
import NaruTest.Lsp
import NaruTest.ZedInstall
import NaruTest.Golden

/-!
# `NaruTest` — エディタ対応(C16〜C19)と golden test(C10)の検査ドライバ(ライブラリ側)

IDEAL.md「前提」のとおり Lean で書く。実行ファイルは `NaruTestMain.lean`(`lake exe naru_test <群>`)。

- `grammar` — tree-sitter 文法(`editors/tree-sitter-naru/`)の検査(C16)。`NaruTest/Grammar.lean`。
- `zed` — Zed 拡張(`editors/zed-naru/`)の検査(C17)。`NaruTest/Zed.lean`。
- `lsp` — 言語サーバー `naru lsp` の検査(C18)。`NaruTest/Lsp.lean`。
- `zed-install` — 人間の Zed に `editors/zed-naru/` を Dev Extension として入れる(C19)。`NaruTest/ZedInstall.lean`。
- `golden` — 手書き Model と生成 Model を 1 つの Lean プログラムで実行する golden test(C10)。`NaruTest/Golden.lean`(本体は `tests/golden/Golden.lean`)。
- 共通部品(`ok:` / `FAIL:` の蓄積、子プロセス)は `NaruTest/Common.lean`。
-/
