import NaruTest.Common
import NaruTest.Grammar
import NaruTest.Zed
import NaruTest.Lsp
import NaruTest.ZedInstall
import NaruTest.Golden
import NaruTest.Statements
import NaruTest.Repo
import NaruTest.Regression

/-!
# `NaruTest` — エディタ対応(C16〜C19)・golden test(C10)・生成 Statements(C8 / C9)・リポジトリの構成(C21 / C23 / C25)・
非対話の回帰一式(C36)の検査ドライバ(ライブラリ側)

IDEAL.md「前提」のとおり Lean で書く。実行ファイルは `NaruTestMain.lean`(`lake exe naru_test <群>`)。走らせ方は `docs/testing.md`。

- `grammar` — tree-sitter 文法(`editors/tree-sitter-naru/`)の検査(C16)。`NaruTest/Grammar.lean`。
- `zed` — Zed 拡張(`editors/zed-naru/`)の検査(C17)。`NaruTest/Zed.lean`。
- `lsp` — 言語サーバー `naru lsp` の検査(C18)。`NaruTest/Lsp.lean`。
- `zed-install` — 人間の Zed に `editors/zed-naru/` を Dev Extension として入れる(C19)。`NaruTest/ZedInstall.lean`。
- `golden` — 手書き Model と生成 Model を 1 つの Lean プログラムで実行する golden test(C10)。`NaruTest/Golden.lean`(本体は `tests/golden/Golden.lean`)。
- `statements` — 生成 Statements の import 閉包と `sorry`(C8)、claim surface の 13 の欄名(C9)。`NaruTest/Statements.lean`。
- `repo` — README の構成表・リンク・クイックスタート(C21)、`third_party/verified-consensus` の submodule(C23)、`docs/` の文書(C25)。`NaruTest/Repo.lean`。
- `regression` — 非対話の回帰一式(C36): 受理例・反例、C34 の意味(`tests/accept/guard_shadow.naru` の戻り値と命題の真偽)、C1 の決定性、
  C6 / C8 のビルド、C7 の simulate と C26、C24 の設定、`grammar` / `zed` / `lsp` / `statements` / `repo` の各群、C28 / C22 / C27、C10 の golden。
  `NaruTest/Regression.lean`。
- 共通部品(`ok:` / `FAIL:` の蓄積、子プロセス、`naru.toml` のソースルート)は `NaruTest/Common.lean`。
-/
