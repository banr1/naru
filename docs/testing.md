# 検査ドライバとテストの走らせ方

`lake exe naru_test <群>` の各群(C8 / C9 / C10 / C16〜C19 / C21 / C23 / C25 / C34 / C36 / C37 の証拠を取る)、`naru check-reject` と `tests/reject/`・`tests/accept/`、golden test の走らせ方と所要時間。
コマンドの全体は [cli.md](cli.md)、診断は [diagnostics.md](diagnostics.md)。コードを変えたときの最終検証は 1 コマンド `lake exe naru_test regression`(下の「回帰一式」)。

## 反例と受理例

- `tests/reject/*.naru`: 反例。各ファイルの先頭コメントが期待する E 番号を名指しする。`lake exe naru check-reject tests/reject/<file>.naru E0xx` が PASS(exit 0)であること
  が証拠。`compile` と同じ経路を走らせ、診断の中に指定した番号があれば PASS。行末の `// E0dd`(コードの後ろのコメント)は、その行にその番号の診断が出る印で、
  `naru_test regression` が CLI の診断の (行, 番号) の集合と照合する(`prop_as_value.naru`(C35。先頭は `truthLost`)と `type_name_as_value.naru`(C35))。
- `tests/accept/*.naru`: 受理例。`lake exe naru compile tests/accept/<file>.naru` が exit 0 になる(`backend.naru` は backend、`smoke.naru` は最小の通し、
  `statements.naru` は Statements backend、`editors_syntax.naru` は全構文でエディタ対応の受理例(期待値は `editors_syntax.captures`)、
  `guard_shadow.naru` はガード付き match の束縛の意味(C34)の検体で、戻り値と命題の真偽を `naru_test regression` が照合する、
  `prop_bool.naru` は Prop と Bool の境界(C35)で受理される形(論理式・量化・Prop と値の let・Prop の if / match・型別名の正常な使用)の検体で、
  同じく戻り値と命題の真偽を `naru_test regression` が照合する、
  `legacy_module_name.naru` は生成モジュール名の一般規則(C37)の検体で、移植ソースの改名前と同じ形の利用者モジュール名が特別扱いなしに
  `Model/` と `Statements/` の両方に生成されることを `naru_test regression` が照合する。旧名を意図的に使う唯一のファイルで、`naru_test repo` の
  旧名検索はこれだけを除外する)。`naru_test lsp` は全受理例の `didOpen` で診断 0 件も確かめる。
- 生成 Lean の型検査は、生成 Model の olean を `--out` のディレクトリに作ってから行う(`naru_test regression` が全受理例に対して行う)。

## 検査ドライバ(`lake exe naru_test`)

| 群 | 意味 |
|---|---|
| `grammar` | tree-sitter 文法(`editors/tree-sitter-naru/`)の検査(C16): `tree-sitter generate` の出力が追跡対象の `src/` と一致、`tree-sitter build` が exit 0、`specs/consensus/`(`naru.toml` のソースルート)・`tests/accept/`・`tests/reject/` の全 `.naru`(E010 を期待する反例は除く)が ERROR / MISSING なしに解析できる、`tests/accept/editors_syntax.naru` への `queries/highlights.scm` の捕捉が `tests/accept/editors_syntax.captures` の行に出る、その受理例がコンパイラの検査を通る、`editors/zed-naru/languages/naru/highlights.scm` が `queries/highlights.scm` と同一 |
| `zed` | Zed 拡張(`editors/zed-naru/`)の検査(C17): 5 ファイル(`extension.toml`・`languages/naru/config.toml`・`highlights.scm`・`Cargo.toml`・`src/lib.rs`)がある、`extension.toml` の `id = "naru"`・`[grammars.naru]` の `repository`(このリポジトリの `file://` URL)/ `rev`(40 桁の SHA)/ `path = "editors/tree-sitter-naru"`・`[language_servers.naru]` の `name` と `languages`、`config.toml` の `name` / `grammar` / `path_suffixes` / `language_servers`、`rev` がこのリポジトリのコミットで `git diff --exit-code <rev> HEAD -- editors/tree-sitter-naru` が空、`rev` の文法(`git archive`)を `tree-sitter build` して作業ツリーの `highlights.scm` が `tree-sitter query` でロードできる、`src/lib.rs` が設定 → `PATH` → `.lake/build/bin/naru` の順で `naru lsp` を起動する形、`cargo build --release --target wasm32-wasip2` が exit 0。一時ファイルは `.lake/naru/test/zed/`、cargo の成果物は `editors/zed-naru/target/` |
| `lsp` | 言語サーバー `naru lsp` の検査(C18): `lake build naru` の後、子プロセスの `.lake/build/bin/naru lsp` と LSP を話す。`initialize` の応答に全文同期がある、未対応のリクエスト(`textDocument/hover`)が `MethodNotFound`(この応答を、通知の処理の終わりを待つ barrier にも使う)、`tests/reject/` の各反例の `didOpen` で `naru compile` と同じ E 番号・行・列の診断(先頭コメントが名指しする E 番号を含む)がその URI に返り `didClose` で空になる、`tests/accept/` の各受理例の `didOpen` で診断 0 件(C35 の正常例を含む)、絵文字を含む単独文書で列が UTF-16 単位・範囲がトークン 1 つ分、`specs/consensus/` の全ファイルの `didOpen` で 0 件、`specs/consensus/Consensus/Objects/Time.naru` の `didChange` で末尾に足した未解決名の E011 がその行に出る・`slotStart` の改名で他のファイル(Parameters / Grades)の URI に E011 が出る・壊れたまま Parameters を `didClose` すると空のまま・開き直すと戻る・Time を戻すと消える、`didSave` で 0 件のまま、全ファイルの `didClose` で空、`shutdown` が `null`、`exit` で exit 0。期待値はコンパイラ(`compileSources`)から取る |
| `zed-install` | 起動中の人間の Zed に `editors/zed-naru/` を Dev Extension として入れる(C19): `lake build naru` の後、`~/Library/Application Support/Zed/extensions/installed/naru` が無ければ `zed: install dev extension`(フォルダ選択ダイアログに ⌘⇧G でパスを貼る)、この拡張への symlink なら `zed: rebuild dev extension`(Dev Extension が 2 つ以上なら picker で `naru`)を `osascript`(System Events。文字列はクリップボード経由、前面が Zed であることを確かめてから送る)で実行し、`Zed.log` に操作の開始以後 `compiled grammar naru`・`finished compiling extension <installed/naru>`(install では Zed は拡張のソースのパスで記録するのでそれも受理)・`extensions updated.` の `loading 1` / `reloading 1` が足され、`failed to compile` / `Failed to install dev extension` が 0 件、`installed/naru` が `editors/zed-naru` への symlink、`extension.wasm` と `grammars/naru.wasm` の mtime が操作の開始以後、`grammars/naru/` の checkout が `extension.toml` の `rev`。`grammars/naru.wasm` は操作の前に消す(Zed は `parser.c` より新しい wasm があると文法のコンパイルを飛ばす)。スクリーンショットと AppleScript は `.lake/naru/test/zed-install/` |
| `golden [--finality-horizon N]` | 手書き Model と生成 Model の突き合わせ(C10)。下の「golden test」 |
| `statements` | 生成 Statements の検査(C8 / C9): `lake exe naru compile` で `generated/` を作り直し、`lake build Statements` が exit 0、`Statements` からの import 閉包(`lake env lean --deps-json`。ソースの文字列から推測しない)が `Init` / `NaruStd` / 生成 Model / 生成 Statements だけから成り(Proofs を含まない)、`generated/Statements/` 配下の全ファイルがその閉包にある、閉包の全ファイルに字句 `sorry` が無い、`specs/consensus/`(`naru.toml` のソースルート)に claim bundle `Consensus` がちょうど 1 つあってその項目が verified-consensus の 13 claims と同名、生成 `structure` の欄(`run_cmd` の `getStructureFields`。スクリプトは `.lake/naru/test/statements/SurfaceShape.lean`)が項目と同じ順で並び 13 名を列挙する。C37: 移植ソースの spec 側がソースルートの `Consensus/Spec/` にあり(改名前のディレクトリは無い)、各ファイルの `module` 宣言がルート相対パス(`Consensus.Spec.<ファイル名>`)と一致、単位に改名前の名前のモジュール・import が無い、claim bundle が `Consensus.Spec.*` にある、生成先に改名前のディレクトリが無く生成ファイルのどれも改名前のモジュール名に触れず、`generated/Statements/Consensus/Spec/` の全モジュールが閉包にある |
| `repo [--base-commit <sha>]` | リポジトリの構成と文書の検査(C21 / C23 / C25): README の構成表とリンクが実在する、クイックスタートのコマンドを実行して通る、`third_party/verified-consensus` の git submodule の整合(基準コミットとの関係。`--base-commit` で基準コミットを渡す)、`docs/` の 7 ファイル([language.md](language.md)・[diagnostics.md](diagnostics.md)・[cli.md](cli.md)・[architecture.md](architecture.md)・[testing.md](testing.md)・[editors.md](editors.md)・[roadmap.md](roadmap.md))がある、`docs/diagnostics.md` が `compiler/Naru/Diag.lean` にある E 番号をすべて載せてそれ以外の E 番号を載せない、文書の相対リンクが実在する、旧文書への参照が無い(`.idd/progress.md` と `.idd/knowledge.md` も `git grep` の対象)。C37: 移植ソースの改名前のモジュール名・ディレクトリ名(`Consensus/Spec/` の前の名前)への参照が無い(`git grep -l --untracked -E` で README・docs・tests・compiler・specs・生成先・`.idd/progress.md`・`.idd/knowledge.md` を含む追跡対象と追跡対象外のファイルを検索。除くのは `.idd/cycles/`・`.idd/journal.jsonl`・IDEAL.md・`third_party/` と意図的な検体 `tests/accept/legacy_module_name.naru` だけ) |
| `regression` | 非対話の回帰一式(C36)。下の「回帰一式」。約 12 分 |

## 回帰一式(`lake exe naru_test regression`)

コードを変えた周回の最終検証。`/tmp` のスクリプトや過去の端末出力を要せず、リポジトリのルートで 1 コマンドを走らせると次を順に検査し、
1 つでも期待と違えば `FAIL:` を出して exit 1(段ごとに `== 段` の見出し、項目ごとに `ok:` / `FAIL:` と所要秒)。一時ファイルは `.lake/naru/test/regression/`。

1. `lake build naru naru_test`。
2. 受理例 `tests/accept/*.naru` の `naru compile`(exit 0)、反例 `tests/reject/*.naru` の `naru check-reject <先頭コメントが名指しする E 番号>`。
3. C35: 全反例で `naru compile <file>`(出力指定なし)と `naru compile --out .lake/naru/test/regression/reject/<名前> <file>` がともに exit 1 で同じ診断
   (行・列・番号)を出し、`--out` には何も書かれない(生成に進まない)。行末に `// E0dd` の印のある反例(`prop_as_value.naru`: 量化・spec 宣言の呼出し・
   Prop に束ねた局所名の、fn / メソッドの実引数・list の要素・record の欄・lambda の戻り値・scrutinee への流入と Prop の条件で選ぶ値。先頭は `truthLost`。
   `type_name_as_value.naru`: 型別名 `Count` の値使用と `Count {}` / `Nat { … }` のレコードリテラル)は、印の (行, 番号) の集合と診断の集合が一致する
   (LSP が同じ箇所に返すことは `lsp` 群が全反例で CLI と照合する)。Core の健全性: 全受理例(各 1 単位)と各ソースルート(1 単位)を検査して診断 0 で、
   生成対象 Core の全宣言を再帰的に走査して `.unknown` / 型メタ変数 / エラー用ノードが 0 件(`Core.Module.unsound`)。
4. `grammar`(C16)/ `zed`(C17)/ `lsp`(C18)の各群と golden の短い予行(`--finality-horizon 40`)。
5. C1 の決定性: `lake exe naru compile` を 2 回走らせて生成先の全ファイルの sha256 が一致、各ファイルの先頭 5 行に `naru-compiler` / `naru-stdlib` / `naru-source`、
   `naru-source:` のパスがソースルートのディレクトリ名で始まらない、各ソースの sha256 がヘッダにある。
6. `lake build Model`(C6。`noncomputable` / `unsafe` / `axiom` / `sorry` / `partial` の whole-word grep が 0 件)、`lake build Statements`(C8。`sorry` 0 件)、`statements` 群(C8 / C9)。
7. 受理例ごとに `--out .lake/naru/test/regression/accept/<名前>` へ生成し、生成 Model の olean を作ってから生成 Statements を型検査する。
   生成ファイルはモジュール名の一般規則(`<lib>/<モジュールのパス>.lean`、宣言は `<lib>.<モジュール名>.*`。C37)に従う。
   `guard_shadow.naru`(C34)と `prop_bool.naru`(C35)は加えて検査プログラム `Check.lean`(`NaruTest/Regression.lean` の `semanticsProgram` が書く。期待結果は
   同じファイルの `c34Values` / `c34Props` / `c34Equations` と `c35Values` / `c35Props` / `c35Equations`)を `lean --run` し、実際の戻り値の行
   (`runtimeShadow(0, 7) = true`、`fuelShadow(0, 7) = 7` など 10 行。C35 は `within(fresh(1)) = true`、`tallyValues() = [1, 2, 3, 0]` など 5 行)が期待と
   すべて一致し、命題の真偽(`specShadow 0 7` など真になる入力と、`¬ specShadow 7 0` など偽になる対照入力の否定。C35 は `UpTo 10` / `¬ UpTo 11`(forall)、
   `Reaches 5` / `¬ Reaches 0`(exists)、Prop の let / if / match の 23 件)と戻り値の等式を Lean kernel が `example` で検査する(`decide`、量化は
   `intro` / `omega` / `exact ⟨…⟩`、再帰 fn は `simp [f]` の等式補題。`native_decide` / `sorry` は使わない)。`legacy_module_name.naru`(C37)は、改名前と同じ形の
   利用者モジュール名が `Model/` と `Statements/` の両方に同じ規則で生成され、ルートの `Model.lean` / `Statements.lean` が import することを照合する。
8. C37 の改名: 改名前の最後の commit(`NaruTest/Regression.lean` の `c37BaseCommit`)のソースルートを `git archive` で `.lake/naru/test/regression/c37/old/` に
   取り出し、現在のコンパイラで `--out` に生成して、現在のソースの生成物と、生成パスの集合と各ファイルのヘッダ(5 行)以下の内容(import・宣言・本体)が
   モジュール名の置換を除いて一致することを照合する(宣言構造・依存の保存)。現在の生成物のパス・内容に改名前の名前が無い。移植ソースの宣言を正当に
   変える周回は、`c37BaseCommit` をその変更の直前の commit に進める。
9. C7 の simulate: ソースルート配下の scenario を持つ全ファイルの `naru simulate`(exit 0。`basic.naru` の出力に time / node / confirmed / stable / finalized)、
   ルート外のファイルと scenario の無いファイルは exit 2。C26: simulate の後の生成先のファイル集合が直前の `naru compile` の出力と一致する
   (runner・一時ファイルが無い)、`git status --porcelain --ignored -- generated/` に compile の出力の外の追跡対象外・ignore の項目が無い
   (この周回で新しくできた生成パスの `??` と、作業木に無い旧パスの ` D` は許す)、`.gitignore` に `Simulate` の行が無い、
   runner は `.lake/naru/simulate/Simulate.lean`。
10. C24: `compiler/` にソースルートのディレクトリ名の直書きが無い(`grep -rn '"dsl\|"specs' compiler/` が 0 件)、`naru.toml` の `sources` を別名のコピー
    (`.lake/naru/test/regression/alias/`)に向けて `lake exe naru compile` しても生成先の sha256 が一致する。`naru.toml` は必ず元に戻し(`git diff --exit-code`)、
    もう一度 `compile` して生成先が元に戻ったことも確かめる。
11. `repo` 群(C21 / C23 / C25 / C37 の旧名検索)、C28(`git ls-files tests/golden` が `Golden.lean` だけ)、C22(`cmp LICENSE`)、C27(`git check-attr`)。
12. C10: `golden`(引数なし = horizon 100、全 16 ケース。約 9 分)。

`zed-install`(C19。人間の Zed を操作する)と C20(画面観測)は入れない。IDD の台帳・knowledge を更新した後は、少なくとも `repo` 群を再実行する(C25 / C36)。

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
