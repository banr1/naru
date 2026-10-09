# naru CLI と naru.toml

`lake exe naru` のコマンド(`compile` / `simulate` / `check-reject` / `lsp`)、コンパイル単位を決める `naru.toml`、言語サーバーの仕様。
診断の番号は [diagnostics.md](diagnostics.md)、検査ドライバは [testing.md](testing.md)。

## naru.toml

リポジトリのルートの `naru.toml` が、コンパイル単位のソースルートと出力先を決める。

```toml
sources = ["specs/consensus"]
generated = "generated"
```

- `sources`: ソースルートのディレクトリの一覧。各ルートの `**/*.naru` 全体を 1 つのコンパイル単位として検査する。
- `generated`: `naru compile` の出力先。`generated/` には `naru compile` の決定的な出力(`Model` と `Statements`)だけを置く。
- モジュール名はソースルートからの相対パスに対応する。`specs/consensus/Consensus/Objects/Time.naru` は `Consensus.Objects.Time`
  (ファイルの `module` 宣言もこれと一致させる)。生成ファイルは `generated/Model/Consensus/Objects/Time.lean`(Lean モジュール `Model.Consensus.Objects.Time`)と、
  spec 宣言があれば `generated/Statements/Consensus/Objects/Time.lean`。

## コマンド

リポジトリのルートで実行する(stdlib の hash のために `stdlib/Model` を読む。`lsp` は cwd に依らない)。

| コマンド | 意味 |
|---|---|
| `compile` | `naru.toml` の各ソースルートを 1 単位として検査し(パス順)、Model と Statements を `generated/` に出力する(`generated/Model.lean` と `generated/Model/**.lean`、`generated/Statements.lean` と `generated/Statements/**.lean` を作り直す)。C1 の検証コマンド |
| `compile [--out <dir>] <files...>` | 指定ファイルを検査する。`--out` があればそこに Model と Statements を出力し、無ければ検査だけ(`checked N module(s)`) |
| `check-reject <file.naru> <Exxx>` | 反例が `Exxx` で拒否されることを検査(PASS で exit 0) |
| `lsp` | 標準入出力で言語サーバー(LSP、JSON-RPC 2.0 の `Content-Length` 枠)として動く(C18。`compiler/Naru/Lsp.lean`)。下の「言語サーバー」 |
| `simulate <specs/consensus/scenarios/basic.naru>` | ソースルート全体を検査して `generated/` を作り直し、そのファイルの scenario を native 実行して observer の値を表示する(C7)。診断があれば exit 1、`naru.toml` のソースルートの外・scenario 無しは exit 2、`lake build naru_simulate` の失敗は exit 1、それ以外は実行ファイルの exit code |

出力の形と `check-reject` の説明は [diagnostics.md](diagnostics.md)。

### simulate

scenario は定理ではなく実行 fixture(言語の側は [language.md](language.md) の「scenario と observer」)。

- ファイルは `naru.toml` のソースルート配下に限る(外なら exit 2)。`./specs/…` やリポジトリの絶対パスで渡しても、実際のパス(`realPath`)で
  ルート配下のファイルと突き合わせる。
- ソースルート全体を検査して `generated/` に Model と Statements を作り直す(`compile` と同じ)。
- 実行入口 `main`(C1 のヘッダ付き。追跡対象外)は `generated/Simulate.lean` ではなく `.lake/naru/simulate/Simulate.lean` に書く。
  lakefile の lean_exe `naru_simulate` の `srcDir` は `.lake/naru/simulate`。`generated/` には `naru compile` の決定的な出力だけがある。
- `lake build naru_simulate`(Model を native にビルド)→ `.lake/build/bin/naru_simulate` を実行する(「naru を実行する」= 生成 Lean を実行する)。
- 出力: `scenario <name>`、scalar は `  <label> = <Repr>`、List は `  <label>:` の下に 1 要素 1 行。値の表示は Lean の `Repr`
  (record は `{ time := 4, node := { value := 0 }, … }`)。

## 言語サーバー(`naru lsp`)

Zed 拡張(`editors/zed-naru/`、[editors.md](editors.md))が起動し、開いた `.naru` の診断を表示する。応じるのは `initialize`(全文同期 `textDocumentSync.change = 1`、
`openClose`、`save`)/ `initialized` / `shutdown` / `exit` と `textDocument/didOpen` / `didChange`(全文)/ `didSave` / `didClose`。
それ以外のリクエストには `MethodNotFound`(-32601)を返し、それ以外の通知(`$/…` 等)は無視する。

- 検査の単位: 文書のパスの祖先で最も近い `naru.toml` を読み、その `sources` のルート配下なら `<ルート>/**/*.naru` 全体を 1 つのコンパイル単位にし、
  開いている文書はディスクではなくバッファの内容で検査する(CLI の `compile` と同じ `Driver.compileSources`)。それ以外の文書は単独。
- 診断は `textDocument/publishDiagnostics`。コンパイラの 1 始まりの行・列を 0 始まりに直し、範囲はその位置のトークン 1 つ分
  (識別子・数・文字列・記号)、severity はエラー、`code` は `E0xx`、`source` は `naru`。列は UTF-16 単位(LSP の既定)。
- 他のファイルに出た診断はそのファイルの URI へ送る(開いていないファイルにも)。文書自身には空でも必ず送り、前回その単位で送った
  URI のうち今回空になったものには空を送って消す。`didClose` には空を送り、同じ単位に開いた文書が残っていればディスクの内容で
  検査し直す(その検査では閉じた文書へは送らず空のままにし、次の検査からは開いていないファイルとして扱う)。残っていなければ
  その単位の診断をすべて消す。
- 意味検査はすべてコンパイラ側(この層は診断の運搬だけ: IDEAL.md「不変条件」)。
