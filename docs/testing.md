# 検査ドライバとテストの走らせ方

`lake exe naru_test <群>` の各群(C8 / C9 / C10 / C16〜C19 / C21 / C23 / C25 の証拠を取る)、`naru check-reject` と `tests/reject/`・`tests/accept/`、golden test の走らせ方と所要時間。
コマンドの全体は [cli.md](cli.md)、診断は [diagnostics.md](diagnostics.md)。

## 反例と受理例

- `tests/reject/*.naru`: 反例。各ファイルの先頭コメントが期待する E 番号を名指しする。`lake exe naru check-reject tests/reject/<file>.naru E0xx` が PASS(exit 0)であること
  が証拠。`compile` と同じ経路を走らせ、診断の中に指定した番号があれば PASS。
- `tests/accept/*.naru`: 受理例。`lake exe naru compile tests/accept/<file>.naru` が exit 0 になる(`backend.naru` は backend、`smoke.naru` は最小の通し、
  `statements.naru` は Statements backend、`editors_syntax.naru` は全構文でエディタ対応の受理例。期待値は `editors_syntax.captures`)。
- 生成 Lean の型検査は、生成 Model の olean を `--out` のディレクトリに作ってから行う。

## 検査ドライバ(`lake exe naru_test`)

| 群 | 意味 |
|---|---|
| `grammar` | tree-sitter 文法(`editors/tree-sitter-naru/`)の検査(C16): `tree-sitter generate` の出力が追跡対象の `src/` と一致、`tree-sitter build` が exit 0、`specs/consensus/`(`naru.toml` のソースルート)・`tests/accept/`・`tests/reject/` の全 `.naru`(E010 を期待する反例は除く)が ERROR / MISSING なしに解析できる、`tests/accept/editors_syntax.naru` への `queries/highlights.scm` の捕捉が `tests/accept/editors_syntax.captures` の行に出る、その受理例がコンパイラの検査を通る、`editors/zed-naru/languages/naru/highlights.scm` が `queries/highlights.scm` と同一 |
| `zed` | Zed 拡張(`editors/zed-naru/`)の検査(C17): 5 ファイル(`extension.toml`・`languages/naru/config.toml`・`highlights.scm`・`Cargo.toml`・`src/lib.rs`)がある、`extension.toml` の `id = "naru"`・`[grammars.naru]` の `repository`(このリポジトリの `file://` URL)/ `rev`(40 桁の SHA)/ `path = "editors/tree-sitter-naru"`・`[language_servers.naru]` の `name` と `languages`、`config.toml` の `name` / `grammar` / `path_suffixes` / `language_servers`、`rev` がこのリポジトリのコミットで `git diff --exit-code <rev> HEAD -- editors/tree-sitter-naru` が空、`rev` の文法(`git archive`)を `tree-sitter build` して作業ツリーの `highlights.scm` が `tree-sitter query` でロードできる、`src/lib.rs` が設定 → `PATH` → `.lake/build/bin/naru` の順で `naru lsp` を起動する形、`cargo build --release --target wasm32-wasip2` が exit 0。一時ファイルは `.lake/naru/test/zed/`、cargo の成果物は `editors/zed-naru/target/` |
| `lsp` | 言語サーバー `naru lsp` の検査(C18): `lake build naru` の後、子プロセスの `.lake/build/bin/naru lsp` と LSP を話す。`initialize` の応答に全文同期がある、未対応のリクエスト(`textDocument/hover`)が `MethodNotFound`(この応答を、通知の処理の終わりを待つ barrier にも使う)、`tests/reject/` の各反例の `didOpen` で `naru compile` と同じ E 番号・行・列の診断(先頭コメントが名指しする E 番号を含む)がその URI に返り `didClose` で空になる、絵文字を含む単独文書で列が UTF-16 単位・範囲がトークン 1 つ分、`specs/consensus/` の全ファイルの `didOpen` で 0 件、`specs/consensus/Consensus/Objects/Time.naru` の `didChange` で末尾に足した未解決名の E011 がその行に出る・`slotStart` の改名で他のファイル(Parameters / Grades)の URI に E011 が出る・壊れたまま Parameters を `didClose` すると空のまま・開き直すと戻る・Time を戻すと消える、`didSave` で 0 件のまま、全ファイルの `didClose` で空、`shutdown` が `null`、`exit` で exit 0。期待値はコンパイラ(`compileSources`)から取る |
| `zed-install` | 起動中の人間の Zed に `editors/zed-naru/` を Dev Extension として入れる(C19): `lake build naru` の後、`~/Library/Application Support/Zed/extensions/installed/naru` が無ければ `zed: install dev extension`(フォルダ選択ダイアログに ⌘⇧G でパスを貼る)、この拡張への symlink なら `zed: rebuild dev extension`(Dev Extension が 2 つ以上なら picker で `naru`)を `osascript`(System Events。文字列はクリップボード経由、前面が Zed であることを確かめてから送る)で実行し、`Zed.log` に操作の開始以後 `compiled grammar naru`・`finished compiling extension <installed/naru>`(install では Zed は拡張のソースのパスで記録するのでそれも受理)・`extensions updated.` の `loading 1` / `reloading 1` が足され、`failed to compile` / `Failed to install dev extension` が 0 件、`installed/naru` が `editors/zed-naru` への symlink、`extension.wasm` と `grammars/naru.wasm` の mtime が操作の開始以後、`grammars/naru/` の checkout が `extension.toml` の `rev`。`grammars/naru.wasm` は操作の前に消す(Zed は `parser.c` より新しい wasm があると文法のコンパイルを飛ばす)。スクリーンショットと AppleScript は `.lake/naru/test/zed-install/` |
| `golden [--finality-horizon N]` | 手書き Model と生成 Model の突き合わせ(C10)。下の「golden test」 |
| `statements` | 生成 Statements の検査(C8 / C9): `lake exe naru compile` で `generated/` を作り直し、`lake build Statements` が exit 0、`Statements` からの import 閉包(`lake env lean --deps-json`。ソースの文字列から推測しない)が `Init` / `NaruStd` / 生成 Model / 生成 Statements だけから成り(Proofs を含まない)、`generated/Statements/` 配下の全ファイルがその閉包にある、閉包の全ファイルに字句 `sorry` が無い、`specs/consensus/`(`naru.toml` のソースルート)に claim bundle `Consensus` がちょうど 1 つあってその項目が verified-consensus の 13 claims と同名、生成 `structure` の欄(`run_cmd` の `getStructureFields`。スクリプトは `.lake/naru/test/statements/SurfaceShape.lean`)が項目と同じ順で並び 13 名を列挙する |
| `repo [--base-commit <sha>]` | リポジトリの構成と文書の検査(C21 / C23 / C25): README の構成表とリンクが実在する、クイックスタートのコマンドを実行して通る、`third_party/verified-consensus` の git submodule の整合(基準コミットとの関係。`--base-commit` で基準コミットを渡す)、`docs/` の 7 ファイル([language.md](language.md)・[diagnostics.md](diagnostics.md)・[cli.md](cli.md)・[architecture.md](architecture.md)・[testing.md](testing.md)・[editors.md](editors.md)・[roadmap.md](roadmap.md))がある、`docs/diagnostics.md` が `compiler/Naru/Diag.lean` にある E 番号をすべて載せてそれ以外の E 番号を載せない、文書の相対リンクが実在する、旧文書への参照が無い |

## golden test(C10)

手書き Model(`third_party/verified-consensus/DecoupledConsensusModel`)と生成 Model(`generated/Model` + `NaruStd`)を 1 つの Lean プログラム(`tests/golden/Golden.lean`)から
import し、同じ fixture(run)を両側で畳み込んで、各 event の前後の両 node の読みと tick が emit した object を行の列にして突き合わせ、MISMATCH を数える。

```
lake exe naru_test golden                         # C10。horizon 100 で約 9 分
lake exe naru_test golden --finality-horizon 40   # 約 30 秒
```

- 引数なしが C10 の証拠(FinalityLiveness は horizon 100 の prefix、StrongRecovery は seed の `rho 30`)。`--finality-horizon N` は短い予行用で、既定以外の N は `note:` が出る。
  所要時間の大半は手書き側の実行。
- 前提: 生成 Model が `lake build Model` 済みで、手書き Model の olean が `third_party/verified-consensus/.lake` にビルド済みであること(git submodule を取得して `lake build` しておく)。
- 出力: case ごとに `ok <case>: n lines agree` か `FAIL <case>: …` と `MISMATCH …` の行、最後に `MISMATCH total: N`。exit 0 ⇔ N = 0。
- case: `witness:weakGenesis` / `witness:outage` / `witness:strongRecovery(seed rho 30)` / `witness:finalityLiveness(horizon N)`(手書きの Witnesses の 4 run を両側で
  Lean に書き写したもの)、`scenario:<name>`(`specs/consensus/scenarios/*.naru` が fn として公開する Setup と run)、`scenario:<name>/observe <label>`(`naru simulate` の出力が
  同じ run の読みと一致する)。`tests/golden/` には `Golden.lean` だけがある。
- scenario 側の約束は [language.md](language.md) の「scenario と observer」。
