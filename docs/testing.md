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
- `tests/config_change/`: 設定変更プロジェクト(C7 / C24 / C26 の検体)。`naru.toml`(`sources = ["src"]`、`generated = "generated"`)と
  `src/Counter.naru`(fn `value()` の値を observer `current()` が表示する scenario `counter`)。`naru_test regression` が複製の上で `generated` を
  `"custom"` に、`value()` の 1 を 2 に書き換えて `naru simulate` を走らせ、observer・生成先・Lake のビルド・実行ファイルの対応を照合する(回帰一式の 10)。
- `tests/units/`: 複数ファイルのコンパイル単位の検体(C18)。`reject/<名前>/` と `accept/<名前>/` に `naru.toml`(`sources = ["src"]`)と `src/*.naru`
  (1 つの単位)。反例は `reject/module_duplicate`(2 ファイルが同じモジュール名)・`reject/runtime_cycle`(runtime 宣言の参照が Alpha → Beta → Gamma →
  Alpha と巡る)・`reject/spec_cycle`(spec 宣言の参照が Left → Right → Left と巡る)・`reject/inferred_cycle`(`make().x` の record の推論された型だけで
  生じる辺を含む循環。その辺の E017 は宣言 `width` の名前の位置)で、各ファイルの行末の `// E017` が診断の出る行の印、`fix/<ファイル>.naru` はその `src/` の
  ファイルを置き換えると誤りが消える内容。受理例は `accept/dependency_ok`(Top → Middle → Base の循環しない依存。spec 宣言が runtime 宣言と他モジュールの
  spec 宣言を使う)と `accept/cross_phase_ok`(Alpha の spec が Beta の runtime を、Beta の spec が Alpha の spec を使う。Model と Statements の import グラフは
  別なので循環しない)。`naru_test regression`(回帰一式の 3)が CLI の診断(出力指定あり / なし)を印と照合し、`naru_test lsp` が LSP の診断の位置・幅と
  `fix/` の didChange で診断が消えることを照合する。検体は `lake exe naru compile tests/units/reject/<名前>/src/*.naru` でも試せる。

## 検査ドライバ(`lake exe naru_test`)

| 群 | 意味 |
|---|---|
| `grammar` | tree-sitter 文法(`editors/tree-sitter-naru/`)の検査(C16): `tree-sitter generate` の出力が追跡対象の `src/` と一致、`tree-sitter build` が exit 0、`specs/consensus/`(`naru.toml` のソースルート)・`tests/accept/`・`tests/reject/` の全 `.naru`(E010 を期待する反例は除く)が ERROR / MISSING なしに解析できる、`tests/accept/editors_syntax.naru` への `queries/highlights.scm` の捕捉が `tests/accept/editors_syntax.captures` の行に出る、その受理例がコンパイラの検査を通る、`editors/zed-naru/languages/naru/highlights.scm` が `queries/highlights.scm` と同一 |
| `zed` | Zed 拡張(`editors/zed-naru/`)の検査(C17): 5 ファイル(`extension.toml`・`languages/naru/config.toml`・`highlights.scm`・`Cargo.toml`・`src/lib.rs`)がある、`extension.toml` の `id = "naru"`・`[grammars.naru]` の `repository`(このリポジトリの `file://` URL)/ `rev`(40 桁の SHA)/ `path = "editors/tree-sitter-naru"`・`[language_servers.naru]` の `name` と `languages`、`config.toml` の `name` / `grammar` / `path_suffixes` / `language_servers`、`rev` がこのリポジトリのコミットで `git diff --exit-code <rev> HEAD -- editors/tree-sitter-naru` が空、`rev` の文法(`git archive`)を `tree-sitter build` して作業ツリーの `highlights.scm` が `tree-sitter query` でロードできる、`src/lib.rs` が設定 → `PATH` → `.lake/build/bin/naru` の順で `naru lsp` を起動する形、`cargo build --release --target wasm32-wasip2` が exit 0。一時ファイルは `.lake/naru/test/zed/`、cargo の成果物は `editors/zed-naru/target/` |
| `lsp` | 言語サーバー `naru lsp` の検査(C18): `lake build naru` の後、子プロセスの `.lake/build/bin/naru lsp` と LSP を話す。`initialize` の応答に全文同期がある、未対応のリクエスト(`textDocument/hover`)が `MethodNotFound`(この応答を、通知の処理の終わりを待つ barrier にも使う)、`tests/reject/` の各反例の `didOpen` で `naru compile` と同じ E 番号・行・列の診断(先頭コメントが名指しする E 番号を含む)がその URI に返り `didClose` で空になる、`tests/accept/` の各受理例の `didOpen` で診断 0 件(C35 の正常例を含む)、絵文字を含む単独文書で列が UTF-16 単位・範囲がトークン 1 つ分、`specs/consensus/` の全ファイルの `didOpen` で 0 件、`specs/consensus/Consensus/Objects/Time.naru` の `didChange` で末尾に足した未解決名の E011 がその行に出る・`slotStart` の改名で他のファイル(Parameters / Grades)の URI に E011 が出る・壊れたまま Parameters を `didClose` すると空のまま・開き直すと戻る・Time を戻すと消える、`didSave` で 0 件のまま、全ファイルの `didClose` で空、`shutdown` が `null`、`exit` で exit 0。期待値はコンパイラ(`compileSources`)から取る。C18 の複数ファイルの検体 `tests/units/`: 反例(`module_duplicate` / `runtime_cycle` / `spec_cycle` / `inferred_cycle`)は `src/` の全ファイルを `didOpen` すると、行末の `// E017` の印の行に、`compileSources` と同じ行・列(UTF-16)でトークン 1 つ分の幅の E017 が関与する全ファイルの URI に返り、`fix/` の内容に `didChange` すると関係する URI すべての診断が消え、戻すと戻り、`didClose` で閉じた文書は空(最後の文書を閉じると単位の診断がすべて消える)。受理例(`dependency_ok` / `cross_phase_ok`)は全ファイルの `didOpen` で 0 件。言語サーバーはファイルを生成しない: 生成先と `tests/units/` の全ファイルの sha256 がセッションの前後で同じ |
| `zed-install` | 起動中の人間の Zed に `editors/zed-naru/` を Dev Extension として入れる(C19): `lake build naru` の後、`~/Library/Application Support/Zed/extensions/installed/naru` が無ければ `zed: install dev extension`(フォルダ選択ダイアログに ⌘⇧G でパスを貼る)、この拡張への symlink なら `zed: rebuild dev extension`(Dev Extension が 2 つ以上なら picker で `naru`)を `osascript`(System Events。文字列はクリップボード経由、前面が Zed であることを確かめてから送る)で実行し、`Zed.log` に操作の開始以後 `compiled grammar naru`・`finished compiling extension <installed/naru>`(install では Zed は拡張のソースのパスで記録するのでそれも受理)・`extensions updated.` の `loading 1` / `reloading 1` が足され、`failed to compile` / `Failed to install dev extension` が 0 件、`installed/naru` が `editors/zed-naru` への symlink、`extension.wasm` と `grammars/naru.wasm` の mtime が操作の開始以後、`grammars/naru/` の checkout が `extension.toml` の `rev`。`grammars/naru.wasm` は操作の前に消す(Zed は `parser.c` より新しい wasm があると文法のコンパイルを飛ばす)。スクリーンショットと AppleScript は `.lake/naru/test/zed-install/` |
| `golden [--finality-horizon N]` / `golden --comparator` | 手書き Model と生成 Model の突き合わせ(C10)と、その比較器の検体。下の「golden test」 |
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
   C18 の複数ファイルの検体 `tests/units/`: 反例 4 組(`module_duplicate` / `runtime_cycle` / `spec_cycle` / `inferred_cycle`)は `naru compile <src の全ファイル>`
   (出力指定なし)と `naru compile --out .lake/naru/test/regression/units/<名前> <同>` がともに exit 1 で同じ診断(ファイル・行・列・番号)を出し、`--out` には
   何も書かれず、診断がすべて E017 で、その (ファイル, 行, 番号) の集合が各ファイルの行末の `// E017` の印と一致し、各診断の列が実在する識別子(メッセージが
   名指しする参照先の名前・宣言・モジュール)を指し、CLI の (ファイル, 行, 列, 番号) が同じ単位の `compileSources`(`lsp` 群が LSP の期待に使う)と等しい。
   受理例 `dependency_ok` / `cross_phase_ok` は exit 0 で、`--out` に生成した Model / Statements の全ファイル(ルートの集約ファイルを含む)が import の順に
   Lean で型検査できる(生成モジュール同士の import が解決する)。
4. `grammar`(C16)/ `zed`(C17)/ `lsp`(C18。`tests/units/` の検体の didOpen / didChange / didClose と、生成ファイルが変わらないことを含む)の各群、
   golden の短い予行(`--finality-horizon 40`)、C10 の比較器回帰(`golden --comparator`。下の「golden test」の「比較器の検体」)。
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
10. C7 / C24 / C26 の設定変更: 設定変更プロジェクト `tests/config_change/` の複製 `.lake/naru/test/regression/c7/` を cwd にして
    `<ルート>/.lake/build/bin/naru simulate src/Counter.naru` を走らせる。既定の生成先・値 1(`current() = 1`)の後、`generated = "custom"`・値 2 で、
    古い `generated/` とビルドキャッシュが残る場合と、設定した生成先だけが存在する場合(値 1 に戻してから `generated/` を消す)の双方で
    `current() = 2` を表示して exit 0(C7。古い `generated/` は書き換えない)。`custom/` は再生成した `naru compile` の出力と sha256 まで一致し、
    プロジェクトに runner・一時ファイル(`.lean` 以外・`Simulate.lean`)が無く、runner はルートの `.lake/naru/simulate/Simulate.lean` のまま(C26)。
    Lake が読む link `.lake/naru/generated` が `custom/` を指し、ルートの `lake build Model Statements` が exit 0 で、その `.lake/build/bin/naru_simulate` が
    `current() = 2` を表示する(C24: lakefile の手修正なし)。現在のソースを不正にすると exit 1(E011)で observer の行を表示せず、`custom/` も書き換えない。
    最後にルートの `lake exe naru compile` で link をルートの生成先に戻し、`lake build Model Statements`。
11. C24: `compiler/` にソースルートのディレクトリ名の直書きが無い(`grep -rn '"dsl\|"specs' compiler/` が 0 件)、`naru.toml` の `sources` を別名のコピー
    (`.lake/naru/test/regression/alias/`)に向けて `lake exe naru compile` しても生成先の sha256 が一致する。`naru.toml` は必ず元に戻し(`git diff --exit-code`)、
    もう一度 `compile` して生成先が元に戻ったことも確かめる。
12. `repo` 群(C21 / C23 / C25 / C37 の旧名検索)、C28(`git ls-files tests/golden` が `Golden.lean` だけ)、C22(`cmp LICENSE`)、C27(`git check-attr`)。
13. C10: `golden`(引数なし = horizon 100、全 16 ケース。約 9 分)。

`zed-install`(C19。人間の Zed を操作する)と C20(画面観測)は入れない。IDD の台帳・knowledge を更新した後は、少なくとも `repo` 群を再実行する(C25 / C36)。

## golden test(C10)

手書き Model(`third_party/verified-consensus/DecoupledConsensusModel`)と生成 Model(`generated/Model` + `NaruStd`)を 1 つの Lean プログラム(`tests/golden/Golden.lean`)から
import し、同じ fixture(run)を両側で畳み込んで、各 event の前後の両 node の読みと tick が emit した object を行の列にして突き合わせ、MISMATCH を数える。

```
lake exe naru_test golden                         # C10。horizon 100 で約 9 分
lake exe naru_test golden --finality-horizon 40   # 約 30 秒
lake exe naru_test golden --comparator            # 比較器の検体だけ。約 10 秒
```

- 引数なしが C10 の証拠(FinalityLiveness は horizon 100 の prefix、StrongRecovery は seed の `rho 30`)。`--finality-horizon N` は短い予行用で、既定以外の N は `note:` が出る。
  所要時間の大半は手書き側の実行。
- ドライバはまず現在の naru ソースを再生成(`lake exe naru compile`。Lake は `.lake/naru/generated` の link 経由で有効な生成先を読む)して `lake build Model` を走らせる
  (C10: 再生成してビルドしてから全 16 ケース)。手書き Model の olean は `third_party/verified-consensus/.lake` にビルド済みであること(git submodule を取得して
  `lake build DecoupledConsensusModel` しておく)。
- 出力: まず比較器の検体の `comparator agree <名前>: ok …` / `comparator probe <名前>: ok (detected)` / `comparator legacy-miss <名前>: …` と `comparator total: …`、
  次に case ごとに `ok <case>: n lines agree` か `FAIL <case>: …` と `MISMATCH …` の行、最後に `MISMATCH total: N`。exit 0 ⇔ 比較器の失敗 0 かつ N = 0。
  ドライバは 16 の case(`expectedCases`)と検体(`expectedAgreements` / `expectedProbes` / `expectedLegacyMisses`)の名前が 1 つずつ報告されたことも要求する。
- case: `witness:weakGenesis` / `witness:outage` / `witness:strongRecovery(seed rho 30)` / `witness:finalityLiveness(horizon N)`(手書きの Witnesses の 4 run を両側で
  Lean に書き写したもの)、`scenario:<name>`(`specs/consensus/scenarios/*.naru` が fn として公開する Setup と run)、`scenario:<name>/observe <label>`(`naru simulate` の出力が
  同じ run の読みと一致する)。`tests/golden/` には `Golden.lean` だけがある。
- emitted objects の共通表現(`Golden.lean` の `Common`): 両 Model の object(block / Goldfish vote / attestation)を、表現上の差(型名・構築子名・欄名、`Fin 2` と
  `ValidatorId`)だけを吸収して 1 つの木に写し、その文字列(数、`true` / `false`、`none` / `(some v)`、`(構築子 引数 …)`、`[要素, …]`)で比べる。
  vote は作者・slot・head、attestation(row)は作者・round・confirmed(`Option`)・height pair(`empty` / `(vote height entry timeout)`)・finality pair(`Option`)、
  block は `genesis` / `node` の variant と、node なら親(genesis までの全祖先を再帰的に。各祖先の votes / support / rows も含む)・slot・root・votes・support・rows
  (どれも順序を保つ列)・proposer。Option の None / Some と全 variant をそのまま写し、正規化は無い(object の中の列は両 Model とも `List`。集合は object に現れず、
  node の状態の `|T|` / `|bodies|` にだけ現れて濃度で比べる)。例(FinalityLiveness の t = 12 の tick。`lean --run tests/golden/Golden.lean --side gen --finality-horizon 12` が
  `longest:` に出す): `12 tick 0 12 -> [(block (node (node (node genesis 1 2 [] [] [] 0) 2 3 [(vote 0 1 2)] [(vote 0 1 2)] [(row 0 0 (some 0) empty none)] 0) 3 4 [(vote 0 2 3)] [(vote 0 2 3)] [] 0))]`。
- 比較器の検体(`--comparator`、`Golden.lean --comparator-check`。`naru_test regression` の 4): 同じ記述(`Probe.DObj`)から手書き側と生成側の object を組み立て、
  同じ意味の両表現が一致する(agree: vote、各 variant の row、2 代の祖先と votes・support・rows を持つ block、genesis、tick の列)ことと、一つだけ変えた検体
  (probe: object の種類、vote の各欄、row の各欄と `none` ↔ `some`・variant・timeout、block の variant・各欄・親と祖父の欄・祖先の追加・votes / support / rows の
  順序・要素・入れ子の欄。`none` と root 99 / root 0 の `some` の区別を含む 42 件)が両側とも一致したうえで基準と不一致になることを確かめる。
  失敗例として、周回 35 までの 3 つ組 `(kind, root, author)`(`H.Legacy`。confirmed の `none` を 99 に潰していた)が見逃す検体を `legacy-miss` で報告し、
  ドライバの `expectedLegacyMisses` がその見逃しを要求する(検体が元の不具合を捉えていることの確認)。
- scenario 側の約束は [language.md](language.md) の「scenario と observer」。
