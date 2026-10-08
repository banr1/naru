import NaruTest.Grammar

/-!
# `NaruTest` — エディタ対応(C16〜C18)の検査ドライバ(ライブラリ側)

IDEAL.md「前提」のとおり Lean で書く。実行ファイルは `NaruTestMain.lean`(`lake exe naru_test <群>`)。

- `grammar` — tree-sitter 文法(`editors/tree-sitter-naru/`)の検査(C16)。`NaruTest/Grammar.lean`。
- `zed` — Zed 拡張(`editors/zed-naru/`)の検査(C17)。未実装。
- `lsp` — 言語サーバー `naru lsp` の検査(C18)。未実装。
-/
