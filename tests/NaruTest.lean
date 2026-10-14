import NaruTest.Common
import NaruTest.Grammar
import NaruTest.Zed
import NaruTest.Lsp
import NaruTest.ZedInstall
import NaruTest.Golden
import NaruTest.Statements
import NaruTest.Repo
import NaruTest.Semantics
import NaruTest.Deps
import NaruTest.Proofs
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
- `semantics` — コンパイラ意味論保存の検査入口 `lake build NaruSem`(C45: 意味論・一般定理・検体・公理監査)、文書との照合(C47)、実際の compiler 経路の
  Core の適格性(C39: `tests/accept/sem_core.naru` の各宣言の Core を引用して `wtR` / `wtS` を `decide` で検査し、引用の一致を照合する)、実生成 Model / Statements
  への接続と保存(C40〜C44)と誤翻訳の負の検体(C46)。`NaruTest/Semantics.lean`。
- `deps` — 依存グラフ `naru deps`(C63〜C66): 生成の入口と失敗時の不変、決定性と先頭の 3 値、手で書いた期待 JSON の検体 `tests/deps/sample/`、移植ソースに対する
  独立な検査(宣言の件数・出現位置の字句・ファイルの辺の集約・推移簡約・成分と層・import との差)、HTML の自己完結、追跡中の `docs/deps/` の鮮度と文書。`NaruTest/Deps.lean`。
- `proofs` — プロトコル証明の分離基盤(C68〜C70 / C72): Lake ライブラリ `Proofs` のビルドと import 閉包の依存方向、`naru compile` が書く証明義務の一覧
  `obligations.json`(決定性・先頭の 3 値・consensus の 14 件・手で書いた期待 JSON の検体 `tests/proofs/sample/`・束縛 hash の独立な再計算と変化の検体)、
  `naru proofs` の証明状況(検体の 5 値と件数・`--json`・不正を除いた複製・別名の証明ディレクトリ・生成先と証明ディレクトリの不変)、書き手の案内と文書。
  `NaruTest/Proofs.lean`。
- `regression` — 非対話の回帰一式(C36): 受理例・反例、C34 の意味(`tests/accept/guard_shadow.naru` の戻り値と命題の真偽)、C1 の決定性、
  C6 / C8 のビルド、C7 の simulate と C26、C24 の設定、`grammar` / `zed` / `lsp` / `semantics` / `statements` / `repo` / `deps` / `proofs` の各群、C28 / C22 / C27、C10 の golden。
  `NaruTest/Regression.lean`。
- 共通部品(`ok:` / `FAIL:` の蓄積、子プロセス、`naru.toml` のソースルート)は `NaruTest/Common.lean`。
-/
