# IDEAL — naru

## 理想

Lean を知らない分散プロトコルの設計者が、プロトコルを naru で 1 本書くだけで、次の 3 つが同時に成り立っている。

- 書いたプロトコルを実行し、シミュレーションで挙動を確かめられる。
- Safety / Liveness などの定理が AI によって証明され、Lean kernel で検査されている。
- 人間がレビューするのは、生成された仕様のうち短い 3 つの部分 — Model と定理の対応付け(Interface)、定数(Constants)、公開する保証の一覧(Claim Bundle)— だけであり、それで保証を信頼できる。

naru の文法は、Rust / TypeScript / Python / Go を知っている人が想像しやすい形である。書く体験もそれらの言語と同じようにエディタに支えられている: Zed で `.naru` を開くとシンタックスハイライトが付き、コンパイラの診断(E001〜E019)が編集中のその場に表示され、ホバー・定義ジャンプ・補完・リネーム・フォーマットが使える。

naru のリポジトリは、開いた人が README から naru が何か・どこから読むか・どう試すかを知れる入口を持ち、naru 本体と、基準として同梱する外部の参照物(verified-consensus)の境界が構成そのものに表れている。

## 実現する状態

### 必須
- **C1** 同じ naru ソースから生成される Lean は byte-for-byte 同一で、各生成ファイルの先頭にコンパイラ版・stdlib 版・ソースのパスと hash が入っている。ヘッダに書くソースのパスはソースルートからの相対で、ルートのディレクトリ名を含まない — 検証: `lake exe naru compile` を 2 回実行し、`generated/` 配下の全ファイルの sha256 が一致し、各ファイル先頭のコメントに 3 つの値が含まれ、ソースのパスが `specs/consensus/` で始まらない
- **C2** runtime 宣言から spec 宣言への依存(phase leak)はコンパイルエラーになる — 検証: 反例ソース `tests/reject/phase_leak.naru` に対し `lake exe naru compile` が exit 非 0 で `E001` を出力する
- **C3** 無条件の選択(choose / pick / set.first / set.toList 等)はコンパイルエラーになる — 検証: 反例 `tests/reject/choose.naru` で exit 非 0、`E003` を出力する
- **C4** 停止性を確認できない再帰はコンパイルエラーになる — 検証: 反例 `tests/reject/non_total.naru` で exit 非 0、`E002` を出力する
- **C5** 順序指定の無い Set → List 変換はコンパイルエラーになる — 検証: 反例 `tests/reject/order_loss.naru` で exit 非 0、`E004` を出力する
- **C6** 生成 Model は Lean としてビルドでき、`noncomputable` / `unsafe` / `axiom` / `sorry` / 無制限の `partial` を含まない — 検証: 生成 Model の lake target のビルドが exit 0 で、`grep -rwE 'noncomputable|unsafe|axiom|sorry|partial' generated/Model` が 0 件
- **C7** 生成 Model は native 実行でき、scenario をシミュレーションして observer の値を表示する — 検証: `lake exe naru simulate specs/consensus/scenarios/basic.naru` が exit 0 で、time / node / confirmed / stable / finalized を出力する
- **C8** 生成 Statements は生成 Model だけを import し(Proofs を import しない)、`sorry` を含まない — 検証: import 閉包の検査スクリプトが exit 0 で、`grep -rw sorry generated/Statements` が 0 件
- **C9** 生成 Statements の公開 claim surface は naru ソースの claim bundle と一致し、verified-consensus の 13 claims と同名である — 検証: surface shape の検査スクリプトが 13 のフィールド名を列挙して exit 0
- **C10** 具体的な fixture 上で、手書き Model(DecoupledConsensusModel)と生成 Model の confirmed / stable / finalized の読みと emitted objects が一致する — 検証: 両者を同一 Lean プログラムで実行する golden test が、verified-consensus の Witnesses の 4 run(WeakGenesis と Outage は全 horizon、StrongRecovery は seed の `rho 30`、FinalityLiveness は同じ Setup と同じ tick 列の先頭から `horizon = 100` までの prefix(t = 0〜100、101 tick))と、複数ノード・equivocation を含む naru scenario 3 本以上に対し、MISMATCH 0 件で exit 0
- **C16** `.naru` の tree-sitter 文法が `editors/tree-sitter-naru/`(`grammar.js`・`tree-sitter.json`・`tree-sitter generate` の生成物 `src/`・`queries/highlights.scm`)にあり、`docs/language.md` の全構文(予約語、末尾 `?` 付き識別子、入れ子のブロックコメント、module / import / type / record / state / enum / derive / input / fn / observer / predicate / condition / regime / property / claim / claim bundle / protocol / scenario、名前付き引数、record literal と `..` update、ガード付き match、lambda、`forall` / `exists`、関数型)を受理し、`specs/consensus/`・`tests/accept/`・`tests/reject/` 配下のすべての `.naru`(E010 を期待する反例は除く)をパースエラー(ERROR / MISSING)なしに解析し、`highlights.scm` がキーワード・型名・構築子・コメント・文字列・数値・fn 名・欄名を捕捉する — 検証: `lake exe naru_test grammar` が exit 0(`tree-sitter generate` の出力が追跡対象の `src/` と一致、`tree-sitter build` が exit 0、上記の全ファイルの `tree-sitter parse -q` が ERROR / MISSING 0 件、全構文を書いた受理例 `tests/accept/editors_syntax.naru` への `tree-sitter query` で `@keyword` `@type` `@constructor` `@comment` `@string` `@number` `@function` `@property` の捕捉が期待の行に出る、`lake exe naru compile tests/accept/editors_syntax.naru` が exit 0、`editors/zed-naru/languages/naru/highlights.scm` が `queries/highlights.scm` と同一)
- **C17** Zed 拡張が `editors/zed-naru/`(`extension.toml`・`languages/naru/config.toml` と `highlights.scm`・`Cargo.toml`・`src/lib.rs`)にあり、`.naru` を言語 `naru` に対応付け、文法を `[grammars.naru]` の `repository = "file:///Users/banriyanahama/workspace/naru"`・`rev`(このリポジトリのコミット SHA)・`path = "editors/tree-sitter-naru"` で取り、言語サーバー `naru` を Zed の設定 `lsp.naru.binary.path` → `PATH` 上の `naru` → ワークツリーの `.lake/build/bin/naru` の順に探して引数 `lsp` で起動する — 検証: `lake exe naru_test zed` が exit 0(`extension.toml` / `config.toml` に上記の項目がある、`rev` が 40 桁の SHA でこのリポジトリに存在し `git diff --exit-code <rev> HEAD -- editors/tree-sitter-naru` が空、その `rev` の文法(`git archive`)を `tree-sitter build` して作業ツリーの `languages/naru/highlights.scm` がエラーなくロードできる、`editors/zed-naru` で `cargo build --release --target wasm32-wasip2` が exit 0)
- **C18** `lake exe naru lsp` が標準入出力で LSP として動き、`initialize` / `initialized` / `shutdown` / `exit`、`textDocument/didOpen` / `didChange`(全文同期)/ `didSave` / `didClose` に応じ、開いた文書を(`naru.toml` のソースルート配下ならそのルート全体(`<ルート>/**/*.naru`)を 1 つのコンパイル単位としてその文書だけバッファの内容に差し替え、それ以外なら単独で)コンパイラの検査にかけ、診断 E001〜E019 を `textDocument/publishDiagnostics` で該当の行・列の範囲のエラーとして返す(他のファイルに出た診断はそのファイルの URI へ、閉じた文書の診断は空にして消す。C29〜C33 に挙げた以外のリクエストには MethodNotFound) — 検証: `lake exe naru_test lsp` が exit 0(`lake build naru` 後に子プロセスの `naru lsp` へ `initialize` → `initialized` を送り、`tests/reject/` の各反例の `didOpen` で期待の E 番号を持つ診断が `naru compile` と同じ行に返り、`specs/consensus/` の移植ソースの `didOpen` で診断 0 件、`didChange` で誤りを入れると診断が出て戻すと消え、`didClose` で空になる)
- **C19** 周回が人間の Zed(起動中のインスタンス)に `editors/zed-naru` を Dev Extension として入れられる: `~/Library/Application Support/Zed/extensions/installed/naru` が無ければコマンドパレットの `zed: install dev extension`(フォルダ選択ダイアログで `⌘⇧G` → パスの貼り付け → Enter → Enter)、あれば `zed: rebuild dev extension`(Dev Extension が 2 つ以上あると選択が出るので `naru` を選ぶ)を `osascript` で実行し、Zed が文法と拡張をビルドして読み込む — 検証: 操作の開始時刻以降の `~/Library/Logs/Zed/Zed.log` に `compiled grammar naru`、`finished compiling extension "<パス>"`(Zed 1.23.2 はパスを引用符付きで記録し、install では `editors/zed-naru` の実パス、rebuild では `…/extensions/installed/naru` を引く)、`extensions updated.` の行の `loading 1` または `reloading 1` が残り、`failed to compile` / `Failed to install dev extension` が 0 件で、`extensions/installed/naru` が `editors/zed-naru` への symlink であり、`editors/zed-naru/extension.wasm` と `grammars/naru.wasm` が操作後の時刻で更新されている
- **C20** Zed で `.naru` を開くと、`rev` のコミットの文法と作業ツリーの `highlights.scm` に従ってキーワード・型名・構築子・コメント・文字列に色が付き、`naru lsp` が起動して `tests/reject/phase_leak.naru` では E001 の行に赤い診断が、`specs/consensus/` の移植ソースでは診断 0 で表示される — 検証: C19 の直後に周回が `lake build naru` 済みの状態で `zed -n <リポジトリの絶対パス> <ファイルの絶対パス>:<行>:1` で開き、`Zed.log` に `starting language server process. binary path: ".../.lake/build/bin/naru" … args: ["lsp"]` が残り、`screencapture -x -D 1 <png>` で撮った画像を読んで、色分け(キーワード・型名・コメント・文字列が本文と異なる色)と診断(反例では該当行の赤い波線と状態行のエラー数 1 以上、移植ソースでは 0)を確かめる。画像の所在と読み取った内容を observed の証拠として記録し、開いた窓は周回が閉じる
- **C21** ルートに日本語の `README.md` があり、naru とは何か(理想の 3 点を利用者向けの言葉で数行)、前提の道具(elan / Lean 4.34.1、エディタ対応なら tree-sitter / node / cargo / Zed)、クイックスタート(`git clone --recursive` または clone 後の `git submodule update --init`、`lake build`、`lake exe naru compile`、`lake exe naru simulate specs/consensus/scenarios/basic.naru` と期待される出力の抜粋)、ディレクトリ構成の表(ルート直下の追跡対象のディレクトリすべてを 1 行ずつ)、`docs/` の各文書と `IDEAL.md` への案内、検査の走らせ方(`naru_test` の群と golden の所要時間)、Zed 拡張が `extension.toml` の `file://` の絶対パスのためこの機械専用である旨、ライセンス(CC0 1.0)と verified-consensus の出典・引用(`CITATION.cff` の著者・URL)を載せている — 検証: `lake exe naru_test repo` が exit 0(ルート直下の追跡対象のディレクトリ名(`git ls-files` の第 1 要素)がすべて README の構成表に現れる、README と `docs/*.md` の相対リンクがすべて実在するファイルまたは見出しを指す、README のクイックスタートのコードブロックのうち取得(`git clone` / `git submodule`)を除くコマンドを順に実行して exit 0、simulate の出力が README に引いた抜粋の各行を含む)
- **C22** ルートの `LICENSE` は CC0 1.0 Universal の全文である — 検証: `cmp LICENSE third_party/verified-consensus/LICENSE` が exit 0
- **C23** verified-consensus は git submodule `third_party/verified-consensus` として前提の基準コミットを指し、ルート直下に `verified-consensus/` は無い。`third_party/README.md` が上流 URL・基準コミット・ライセンス(CC0)・引用(`CITATION.cff`)・「この submodule の中身は変更しない。指すコミットは IDEAL.md の基準コミットで、変えるのは idd refine だけ」・上流に新しい版が出たかの確かめ方(`git ls-remote https://github.com/fradamt/verified-consensus HEAD` を基準コミットと比べる)と更新したいときは idd refine で基準コミットを書き換える旨・clone 後に `git submodule update --init` が要ること・内側の `.github/` は動かないことを載せている — 検証: `lake exe naru_test repo` が exit 0(ルート直下に `verified-consensus/` が無い、`.gitmodules` の `third_party/verified-consensus` の `url` が `https://github.com/fradamt/verified-consensus`、`git ls-tree HEAD third_party/verified-consensus` が mode 160000、その SHA が `git -C third_party/verified-consensus rev-parse HEAD`・`third_party/README.md` に書かれた SHA・IDEAL.md の基準コミットのすべてと一致(基準コミットは周回が IDEAL.md の前提から読んでドライバに渡す)、`git -C third_party/verified-consensus status --porcelain` が空)
- **C24** コンパイル単位のソースルートはルートの `naru.toml`(ソースルートの一覧 `sources`、例 `sources = ["specs/consensus"]`、と生成先 `generated`)で決まり、`naru compile` / `naru simulate` / `naru lsp` がそれを読む。`compiler/` のコードにソースルートのディレクトリ名の直書きは無い。LSP の「ソースルート配下ならそのルート全体を 1 単位、それ以外は単独」も `naru.toml` のルートで判定する — 検証: `grep -rn '"dsl\|"specs' compiler/` が 0 件、`naru.toml` の `sources` を `specs/consensus` の一時的な別名のコピーに向けて `lake exe naru compile` を実行しても `generated/` の全ファイルの sha256 が元と一致する
- **C25** 文書は `docs/` にある: `docs/language.md`(字句・モジュールと宣言・capability・phase・型・式・パターン・stdlib のメソッド表・Set の規則・量化・再帰・scenario / observer)、`docs/diagnostics.md`(E001〜E019 の一覧と例)、`docs/cli.md`(`naru compile` / `simulate` / `check-reject` / `lsp` と `naru.toml`)、`docs/architecture.md`(パイプライン・Core IR・Model backend・Statements backend・生成物のヘッダと決定性)、`docs/testing.md`(`naru_test` の各群・golden test の走らせ方と所要時間)、`docs/editors.md`(tree-sitter 文法と正本との既知の差・Zed 拡張・`rev` の付け替えの運び)、`docs/roadmap.md`(まだ無いもの)。`compiler/SYNTAX.md` は無く、文書同士とソースからの参照(コード中のコメント・`grammar.js` 冒頭・`.idd/knowledge.md` など)は新しいパスを指す — 検証: `lake exe naru_test repo` が exit 0(上の 7 ファイルがある、`compiler/SYNTAX.md` が無い、`docs/diagnostics.md` が `compiler/Naru/Diag.lean` に定義された E 番号をすべて載せ、それ以外の E 番号を載せない、`git grep -l 'SYNTAX.md'` が `.idd/cycles/` と `.idd/journal.jsonl`(履歴)を除いて 0 件)
- **C26** `generated/` には `naru compile` の決定的な出力だけがある。`naru simulate` の実行入口は `.lake/naru/simulate/Simulate.lean` に書き、lakefile の lean_exe `naru_simulate` の `srcDir` はそこを向く。`.gitignore` に `generated/Simulate.lean` の行は無い — 検証: `lake exe naru simulate specs/consensus/scenarios/basic.naru` の前後とも `git status --porcelain --ignored -- generated/` が空(追跡対象外のファイルが無い)で、`.gitignore` に `Simulate` を含む行が無い
- **C27** ルートの `.gitattributes` が `generated/**` と `editors/tree-sitter-naru/src/**` を `linguist-generated`、`third_party/**` を `linguist-vendored` にしている — 検証: `git check-attr linguist-generated generated/Model.lean editors/tree-sitter-naru/src/parser.c` が両方 `set`、`git check-attr linguist-vendored third_party/README.md third_party/verified-consensus` が両方 `set`
- **C28** `tests/golden/` には C10 の `Golden.lean` だけがあり、周回 6〜8 の予行(`objects_generated.lean` / `objects_handwritten.lean` / `protocol_generated.lean` / `protocol_handwritten.lean`)は無い — 検証: `git ls-files tests/golden` の出力が `tests/golden/Golden.lean` の 1 行だけ

### 望ましい
- **C11** naru のユーザーは Lean 固有の概念を扱わない — 検証: naru の予約語一覧・構文エラーメッセージ・`specs/consensus/` の移植ソースに `Fintype` / `DecidableEq` / `Finset` / `Classical` / `termination_by` / `Prop` / `theorem` / `by` が現れない(grep が 0 件)
- **C12** capability の無い型への `==` や `<` はコンパイルエラーになる — 検証: 反例 `tests/reject/missing_capability.naru` で exit 非 0、`E005` を出力する
- **C13** Model 内での無限量化(`forall n : Nat` 等)の結果による分岐はコンパイルエラーになる — 検証: 反例 `tests/reject/infinite_quantification.naru` で exit 非 0、`E006` を出力する
- **C14** runtime の条件が classical な命題の決定に依存するとコンパイルエラーになる — 検証: 反例 `tests/reject/classical_decision.naru` で exit 非 0、`E007` を出力する
- **C15** 人間のレビュー面(Interface・Constants・Claim Bundle)は生成 Statements の 1 ファイルに集約されている — 検証: `generated/Statements/Review.lean` が存在し、interface binding・constants・claim bundle の 3 つの宣言をその 1 ファイルが含む
- **C29** `naru lsp` が `textDocument/hover` に応じ、識別子(宣言名・欄名・メソッド名)の上では宣言の種類と型(fn なら引数と返り値の型、record / enum なら宣言の形)を Markdown で返し、それ以外の位置では null を返す — 検証: `lake exe naru_test lsp` が exit 0(`specs/consensus/` の移植ソースで、他ファイルの fn の呼び出し位置へのホバーがその fn の名前と型を含む内容を返し、空白の位置では null)
- **C30** `naru lsp` が `textDocument/definition` に応じ、参照の位置から同じコンパイル単位内の宣言(別ファイルを含む)の URI と範囲を返す — 検証: `lake exe naru_test lsp` が exit 0(移植ソースで、別ファイルの fn / type への参照の `definition` がその宣言ファイルの URI と宣言行の範囲を返し、宣言の無い位置では空)
- **C31** `naru lsp` が `textDocument/completion` に応じ、その位置で見える名前(同じ単位の宣言・import 済みモジュールの宣言・予約語)と、`.` の後ではレシーバの型のメソッドと欄を返す — 検証: `lake exe naru_test lsp` が exit 0(移植ソースで、識別子の途中での補完が同じ単位の既知の fn 名を含み、Set 型の式の `.` の後の補完が `contains` 等の stdlib のメソッドを含む)
- **C32** `naru lsp` が `textDocument/prepareRename` と `textDocument/rename` に応じ、宣言名または欄名の変更を同じコンパイル単位の全参照(別ファイルを含む)に及ぶ WorkspaceEdit で返す — 検証: `lake exe naru_test lsp` が exit 0(移植ソースの fn を一時名にリネームした WorkspaceEdit を作業ツリーの複製に適用して `naru compile` が診断 0、編集箇所の数が `grep -w` の出現数と一致)
- **C33** `naru lsp` が `textDocument/formatting` に応じ、字下げ・空白・改行を正規形にする編集(字句と意味は変えない)を返す。整形は冪等で、`specs/consensus/` と `tests/accept/` の全 `.naru` は整形済み(編集が空) — 検証: `lake exe naru_test lsp` が exit 0(各ファイルへの `formatting` の編集が空、わざと崩したコピーへの編集を適用すると元と同一になりもう一度の `formatting` は空、整形前後で `naru compile` の `generated/` の本文(ヘッダを除く)が同一)

## 不変条件

- Model 内に任意の Lean を埋め込む抜け道(`lean { ... }` の類)は存在しない。移植で足りない機能が出たら、計算可能性・phase 分離・決定性を保ったまま naru の言語機能か stdlib に加える(この追加は周回の判断で行ってよく、人間への確認は要らない)。検査(E001〜E004、C6 の 0 件)を緩めて通すことはしない。
- submodule `third_party/verified-consensus` の中身(手書き Model・Statements・Proofs・Witnesses・scripts・docs を含む全体)は変更しない。golden test(C10)と claim surface(C9)の基準だからである。submodule が指すコミットは前提の基準コミットで、周回は自分の判断で進めない・戻さない。基準コミットを変えるのは人間の idd refine だけである。
- 依存方向は Model ← Statements ← Proofs のみ。逆依存(Model が Statements や Proofs を import する、Statements が Proofs を import する)は決して入れない。
- `generated/` は機械生成専用で、人間も AI も直接編集しない。生成結果を直したいときは naru ソース・stdlib・コンパイラのどれかを直して再生成する。
- naru の表現力は Lean より小さく保つ。任意の依存型・型クラスプログラミング・quotient・一般公理・任意の classical choice・一般再帰・runtime での proof 消去・暗黙の非決定性・暗黙の集合順序・tactic・metaprogramming・unsafe な外部呼出しは naru ユーザーに公開しない。
- 一度 met になった条件を退行させない。特に C10 の golden test は、言語機能や stdlib を追加するたびに通し直す。
- 衝突の裁定: 移植の進捗(C7〜C10)と保証(C1〜C6・上記の抜け道禁止)が衝突したら、保証が勝つ。保証を保ったまま進める方法が周回に見つからなければ、推測で進めず ask で止まる。
- tree-sitter 文法は naru の正本ではない。正本は `compiler/Naru/Parser.lean` と `docs/language.md` のままで、文法はハイライトと括弧対応のための第二のパーサとして正本に追従させる(C16)。構文を増やす周回は `docs/language.md`・パーサと同じ周回で文法も直す。文法に意味検査(型・phase・停止性)を持たせない。診断はすべて `naru lsp` を通してコンパイラが出す。
- `editors/tree-sitter-naru/src/` は `tree-sitter generate` の生成物であり、`generated/` と同じく手で編集しない(追跡対象にはする。Zed が `rev` の `src/parser.c` をコンパイルするため)。
- 周回は Zed の設定(`~/.config/zed/`)・macOS の権限設定・人間が開いた Zed の窓に触れず、人間の Zed を再起動しない。周回が `zed -n` で開いた窓は周回が閉じる。
- ルートの README の構成表と実際のディレクトリを一致させ続ける。ルート直下のディレクトリを足す・消す周回は README も同じ周回で直す(C21)。

## 前提

- 技術スタック: Lean 4.34.1 + mathlib v4.34.1(`third_party/verified-consensus/lean-toolchain` と `lakefile.toml` の pin に合わせる)。コンパイラ・stdlib・golden test・検査スクリプトも Lean で書く(既存の Ruby スクリプトの流用は可)。別言語の interpreter もコンパイラも作らない。例外はエディタ対応(`editors/`)だけ: tree-sitter 文法は `grammar.js`(JavaScript)とその生成物(C)、Zed 拡張の glue は Rust(`zed_extension_api`)、Zed の操作は `osascript`(AppleScript / JXA)で書く。これらは naru の意味論・検査・生成に関与しない。言語サーバー本体(`naru lsp`)と検査ドライバ(`naru_test`)はコンパイラと同じ Lean で書く。「naru を実行する」とは、naru を Lean の Model に変換し、その Lean を実行することである。
- 実行環境: この Mac(arm64 / Darwin)に `lean` / `lake` / `elan` / `ruby` が入っている。verified-consensus のフルビルド(5 ライブラリ)は約 1 時間かかる。golden test に要るのは手書きの Model と Statements のビルドだけで、Proofs はビルドしなくてよい。Zed 1.23.2(`/Applications/Zed.app`)と `zed` CLI(`/opt/homebrew/bin/zed`)、tree-sitter CLI 0.27.0、node 24(`tree-sitter generate` に要る)、rustup の cargo / rustc 1.98.1 と `wasm32-wasip2` ターゲットが入っている。Zed は Rust 拡張を `cargo build --target wasm32-wasip2` で、文法を同梱の wasi-sdk(`~/Library/Application Support/Zed/extensions/build/wasi-sdk`、導入済み)の clang で `src/parser.c` からビルドし、Dev Extension を `~/Library/Application Support/Zed/extensions/installed/<id>` への symlink として入れ、`extension.wasm`・`grammars/<name>.wasm`・文法の浅いクローン `grammars/<name>/`・`target/` を拡張ディレクトリ自身に書く(これらは追跡対象にしない)。文法は `git fetch --depth 1 origin <rev>` + `git checkout <rev>` で取るので `rev` はコミット SHA に固定する(ブランチ名は最初の位置に留まる)。file:// の naru リポからは tip でない SHA も取れる(2026-10-08 に確認)。ログは `~/Library/Logs/Zed/Zed.log`。人間の Zed がこのリポジトリを開いたまま動いていることがあり、その PATH には `/opt/homebrew/opt/rustup/bin`(cargo / rustc)が入っている。`extensions/installed/` には Dev Extension `esl` も入っている。
- 周回の運び: 文法を変えた周回は、その周回のコミットがまだ無いので `rev` を新しい文法に向けられない(Zed が使う文法は `rev` のコミットのもの)。その周回では `highlights.scm` を `rev` の文法でもロードできる形に保ち(新しい node を参照する捕捉は次の周回に回す)、次の周回で `rev` を直前の周回のコミットに付け替え、C17 / C19 / C20 を取り直す。
- 構成の移動の運び: 構成の移動(C21〜C28)は対象ファイルを広く変えるので、それより前の証拠はすべて失効する。移動・改名・分割は 1 つの周回にまとめて行い、その周回で C1〜C10 / C12 / C16〜C19 と新しい条件をコマンドで取り直す。C20(画面観測)はその次の、対象ファイルを変えない周回で取り直す。`editors/` は動かさない(C17 の `path = "editors/tree-sitter-naru"` と `rev` の運びを保つ)。`editors/tree-sitter-naru/` の中身を変えないので `rev` の付け替えは要らないはずだが、`naru_test zed` で確かめる。verified-consensus の移動では、追跡対象外の手書き側のビルド成果物 `verified-consensus/.lake/`(約 17 GB、mathlib と手書き Model の olean)を新しい場所へ持ち越して再ビルド(約 1 時間)を避ける。持ち越した `.lake` が新しいパスで使えず再ビルドが要ったら、その旨を記録し、golden の取り直しにそのぶんの時間を見込む。submodule にすると、親リポジトリからは verified-consensus が 1,064 ファイルではなく 1 つの gitlink に見える。`git ls-files` / `git archive` / `git diff` で親リポジトリのファイルを数える・比べる検査(`naru_test` の各群)が verified-consensus の中身を前提にしていないか確かめ、前提にしていれば submodule の中を見るように直す。submodule の取得(`git submodule update --init`)は GitHub へのネットワーク接続が要る。手元の作業ツリーは既存のコピーから作れるので、周回の中で取得が要らない手順を優先する。予行の golden(C28)は回帰一式からも外す。
- 基準コミット: verified-consensus の上流 `https://github.com/fradamt/verified-consensus` のコミット `b241081d344555797205f8718eeb23a8a0e3eb4c`(2026-09-28「Migrate to Lean and Mathlib v4.34.1」)。同梱していたコピー(naru のコミット 2289607 で取り込み、以後変更なし)とこのコミットは tree hash `8dea1403785d86716d70c8a25f375ff22b9e265b` で一致する(2026-10-09 に確認)。SHA を書くのは IDEAL.md ではここだけで、他の文は「基準コミット」の語で参照する。
- 基準コミットの更新の運び: verified-consensus は C9(claim surface)と C10(golden test)の基準そのものなので、基準コミットの更新は依存の更新ではなく理想・前提の変更として扱う。専用のスクリプトや idd の手動コマンドは作らない。人間が上流の新しい版を確かめ、取り込むと決めたら、idd refine で IDEAL.md の基準コミットを書き換える。そのとき上流の差分の要点(claim の名前・数の変更、Model の挙動の変更、Lean / mathlib の版の変更など)も伝え、必要なら C9 の 13 名・技術スタックの版・行数の基準(手書き Model + Statements の行数)も同じ refine で直す。周回は、IDEAL.md の基準コミットと submodule が指すコミットが食い違っていたら、それを最初の仕事にする: submodule の中で基準コミットを fetch / checkout して親でコミットし、手書き側をビルドし直し、上流の変更を `specs/consensus/` の移植に追従させ、C9 / C10 をはじめ失効した証拠を取り直す。上流の変更が保証(C1〜C6・抜け道の禁止)と衝突する、または移植で追従する方法が周回に見つからなければ、不変条件の「衝突の裁定」に従い推測で進めず ask で止まる。上流が Lean / mathlib の版を上げたのに技術スタックの版が古いままなら、周回は版を推測で上げず ask で止まる。
- 画面観測: 周回を動かす端末(XGhostty)には画面収録とアクセシビリティの権限が付与されており(2026-09-16/17 に fv-lean-esl の周回で確認)、`screencapture -x -D 1 <png>` で画面を撮り、`osascript`(System Events)で Zed へキー入力・メニュー操作を送れる。macOS の入力ソースが日本語だと `keystroke` の文字列は IME で化けるので、文字列(パレットのコマンド名・ダイアログのパス)はクリップボード経由(`set the clipboard to "…"` → `keystroke "v" using command down`)で入れ、保存・窓を閉じるはメニュー(`click menu item … of menu "File" of menu bar 1 of process "Zed"`)で行う。人間が同じ機械を使っていると前面のアプリがすぐ戻るので、操作と撮影は同じコマンドの中で `set frontmost of process "Zed" to true` の直後に行い、前面が `zed` であることを確かめてから送る。Zed の窓は AX に名前を出さないが、Window メニューの項目で窓の数と種類が分かる。`zed -n <プロジェクト> <ファイル>:<行>:1` は新しい窓と新しい言語サーバーのプロセスで開く。撮った画像は追跡対象外(`.lake/naru/scratch/` など)に置く。
- 既存資産: `third_party/verified-consensus/`(submodule。基準コミットを指す)。手書き Model(29 ファイル)・Statements(12 ファイル、13 claims の `Consensus`)・Witnesses(4 つの具体的 run)が golden test と claim surface の基準。`scripts/check-review-boundary.rb` と `scripts/ReviewSurfaceShape.lean` は C8 / C9 の検査の雛形になる。手書き側のビルド成果物は submodule の中の `.lake/`(約 17 GB、追跡対象外)にある。
- 対象ソース: 必須の条件はすべて、verified-consensus の Model と Statements を移植した naru ソースに対して検証する(反例ソースを除く)。
- 構成: ルートに `README.md`(入口)・`LICENSE`(CC0 1.0)・`naru.toml`・`.gitattributes`・`lakefile.toml`・`IDEAL.md`。ディレクトリは `docs/`(language / diagnostics / cli / architecture / testing / editors / roadmap)、`compiler/`、`stdlib/`(Model 用 `stdlib/Model`)、`specs/`(`consensus/` にコンセンサスプロトコルの naru ソース `Consensus/**` と `scenarios/`)、`generated/`(Model / Statements)、`tests/`(`accept/`・`reject/`・`golden/`・検査ドライバ `naru_test`)、`editors/`(`tree-sitter-naru/`・`zed-naru/`)、`third_party/`(`README.md` と submodule `verified-consensus/`)、`.idd/`(idd の台帳と周回記録)。`proofs/` は延期項目が昇格して作られた時点で足す。
- コンパイラの構造: Parser → Surface AST → 名前解決 → 型・capability 検査 → phase 検査 → 計算可能性検査 → Typed Core IR → Model backend / Statements backend。Surface syntax を直接 Lean に落とさず、必ず小さな Core IR を経由する。
- 言語の意味論: 宣言は phase(runtime / spec)を持ち、runtime → spec の依存は禁止。primitive 型は Bool / Nat / Int / String / Unit / Option / Result / List / Set / Table / Tuple / Record / Enum。Lean の型クラスは露出せず capability(eq / order / finite / repr)で表す。Set は順序を持たず、List 化は `sort(set, by = …)` で順序を明示する。選択は `find?` / `findUnique?` / `minBy?` / `maxBy?` だけ。runtime の条件は Bool、Statements の述語は Prop 相当。再帰は構造的再帰・明示 fuel・有限集合の反復のみ。非決定性は `input` と Trace として明示する。言語 core は一般の state machine を扱い、consensus 固有の `Event` / `ProtocolSpec` / `Run` は stdlib に置く。Event は (time, phase) で順序付け、Tick = 0 / Deliver = 1、同時刻・同 phase は trace 順。emit と deliver は別事象。Byzantine は注入 object で表す。scenario は定理ではなく実行 fixture で、出力は observer を通す。Statements は predicate / condition / regime / claim / claim bundle で書く。naru に型引数が無いので、Safety / Liveness の一般概念と条件・regime は stdlib ではなく移植ソース(`specs/consensus/Consensus/Statements/`)に monomorphic に書く。Model と Statements の接続は interface binding で明示する。
- MVP 構文: module / type / record / enum / derive eq / derive order / input / fn / if / match / let / List / Set / Table / protocol / predicate / condition / regime / claim / claim bundle / scenario / observer。これ以上は移植で必要になってから加える。
- 理想化: 署名の偽造不能・hash の衝突なし・ネットワーク同期・honest 多数・参加・proposer 再帰は Model に実装せず、Statements の premise として表す。BlockId は単なる識別子でよい。
- 崩れたら報告する前提: 移植した naru ソース(`specs/consensus/` 配下、`scenarios/` を除く。`editors/` と `tests/` は数えない)の行数が、手書きの Model と Statements の合計(約 6,850 行)の 1.5 倍を超えたら、「Lean より簡単」の前提が崩れた兆候として ask で止まり報告する。
- 期限: なし。
- データと秘密: 扱わない。コードはすべて公開可能(naru は CC0 1.0、verified-consensus も CC0)。

## 対象外

### 恒久(有用に見えても作らない)
- production Ethereum client の直接生成。
- P2P networking の実装。
- BLS / hashing などの暗号の実装(Model では識別子と premise で代替する)。
- database の実装。
- 性能最適化された実装。
- Rust / TypeScript など Lean 以外への code generation。
- 別言語による naru の interpreter(naru の実行は生成 Lean の実行だけ)。
- naru 内での tactic / proof script の記述。
- AI による Model / Statements の自由な書き換え(AI が触ってよいのは `proofs/` だけ)。
- Model 内の任意 Lean の抜け道(`lean { ... }`)。

### 延期(理想の一部だが今回は追わない)
- AI による証明の再生成(生成 Model + Statements に対する証明を AI が `proofs/` に書き、Lean kernel が検査する)と、それに付随する proof obligation manifest・model / statements hash への bind・hash 変更時の STALE 化(現段階では実施しない。C1〜C10 がすべて met(realized)になったら昇格を検討)。
- Core IR の意味論と Lean への lowering の対応を Lean 自身で証明すること(現段階では実施しない。`proofs/` に AI 生成の証明が置かれ `lake build` が通る状態が観測されたら昇格を検討)。
- verified-consensus 以外のプロトコルの naru による記述(現段階では実施しない。C1〜C10 がすべて met になったら昇格を検討)。
- Zed 以外のエディタ(VS Code / Neovim など)の対応と、Zed の拡張レジストリへの公開(現段階では実施しない。C16〜C20 がすべて met になり、naru に GitHub の remote ができたら昇格を検討)。

## 用語

- **naru** — この DSL と、そのコンパイラ・stdlib・CLI(`lake exe naru`)の総称。ソースの拡張子は `.naru`。
- **Model** — naru の runtime 宣言から生成される、計算可能・決定的・total な Lean の状態機械。`generated/Model`。
- **Statements** — naru の spec 宣言から生成される、Prop・∀ / ∃・classical 推論を許す Lean の論理仕様。`generated/Statements`。
- **Proofs** — Statements の定理に対する Lean の証明。`proofs/`。今回の周回では空。
- **phase** — すべての naru 宣言が持つ区分。`runtime`(実行に参加: fn / record / enum / state / input / protocol)と `spec`(検証にのみ参加: predicate / condition / regime / property / claim / claim bundle)。
- **phase leak** — runtime 宣言が spec 宣言に依存すること。E001。
- **Interface** — 生成 Model と Statements をつなぐ対応付け(confirmed / stable / finalized / proposer / committee などが Model のどの関数を指すか)。verified-consensus の `Instantiation.lean` の binding に相当。
- **Constants** — Statements が参照する時間・閾値などの定数(Δ、GST、K など)。
- **Claim Bundle** — 公開する保証を 1 つにまとめた宣言。verified-consensus の `Consensus`(13 claims)に相当。
- **claim surface** — Claim Bundle が公開するフィールド名の集合。C9 は verified-consensus の 13 名(constants / nested / certificatesAccountable / finalizedAccountable / honestNeverSlashed / finalizedMonotone / finalizedSafe / available / confirmedLive / stableLive / stableIncludedFast / finalized / stableAsynchronyResilient)との一致を求める。
- **手書き Model** — `third_party/verified-consensus/DecoupledConsensusModel`。golden test の基準。
- **golden test** — 同一の fixture に対して手書き Model と生成 Model を同じ Lean プログラム内で実行し、観測(confirmed / stable / finalized の読みと emitted objects)を突き合わせる検査。
- **fixture** — golden test や simulation に与える具体的な run(validators・environment・event trace)。verified-consensus の Witnesses の 4 run と、naru の scenario で書いたもの。
- **scenario** — naru の実行 fixture 宣言。定理ではない。`observe` で observer の値を確かめる。
- **observer** — simulation の出力を取り出す宣言(confirmed / stable / finalized / head / currentSlot など)。state を直接 dump しない。
- **capability** — 型に付ける性質の宣言(eq / order / finite / repr)。Lean の型クラス(DecidableEq / Ord / Fintype / Repr)への変換は backend が行う。
- **stdlib** — naru の標準ライブラリ。Model 用(Event / ProtocolSpec / Run / Env)。`stdlib/Model`。Statements 用の stdlib は無い(前提「言語の意味論」)。
- **E001〜E019** — コンパイラの診断の番号(E008 / E009 は無い)。E001 phase leak、E002 停止性未確認の再帰、E003 無条件の選択、E004 順序指定なしの Set → List、E005 capability 不足、E006 Model 内の無限量化による分岐、E007 runtime 条件の classical 依存、E010 字句・構文の誤り、E011 解決できない名前、E012 同名の宣言、E013 型の位置に型でない宣言、E014 型の不一致、E015 無い欄・メソッド・引数の不一致、E016 claim bundle の項目が claim でない、E017 生成モジュールの循環・同名、E018 match の腕の形、E019 コンテナ越しに自分に戻る record / enum。
- **反例ソース** — `tests/reject/` に置く、意図的に検査に違反する naru ソース。コンパイラが拒否することを確かめるための fixture。
- **Zed 拡張** — `editors/zed-naru/`。Zed に `.naru` の言語定義(tree-sitter 文法と `highlights.scm`)と言語サーバーの起動を与える Dev Extension。
- **tree-sitter 文法** — `editors/tree-sitter-naru/`。ハイライト用の第二のパーサ。正本ではない。
- **言語サーバー** — `lake exe naru lsp`。LSP を標準入出力で話し、コンパイラの診断(C18)と編集支援(C29〜C33)を返す。
- **Dev Extension** — Zed がローカルのディレクトリから入れる拡張。`extensions/installed/<id>` への symlink で、Zed 側でビルドされる。
- **画面観測** — 周回が `zed` CLI で開き、`osascript` で操作し、`screencapture` で撮った画像を読んで検証すること。台帳の証拠は `observed N:`。
- **Zed.log** — `~/Library/Logs/Zed/Zed.log`。拡張のビルドと言語サーバーの起動の一次資料。
- **`naru_test`** — Lean の検査ドライバ(`lake exe naru_test <群>`)。群は `grammar` / `zed` / `zed-install` / `lsp` / `golden` / `statements` / `repo`。
- **ソースルート** — `naru.toml` の `sources` に列挙するディレクトリ。その配下の `**/*.naru` が 1 つのコンパイル単位で、モジュール名はソースルートからの相対パスで決まる(`specs/consensus/Consensus/Objects/Time.naru` は `Consensus.Objects.Time`)。
- **`naru.toml`** — ルートの設定ファイル。コンパイル単位のソースルートの一覧(`sources`)と生成先(`generated`)を書く。コンパイラ・`naru simulate`・`naru lsp` が読む。
- **基準コミット** — verified-consensus の上流のコミットのうち、submodule `third_party/verified-consensus` が指し、C9 / C10 の基準となるもの。SHA は前提「基準コミット」に 1 か所だけ書く。変えるのは人間の idd refine だけ。
- **third_party** — `third_party/`。naru 本体でない外部の参照物の置き場。`README.md` と submodule `verified-consensus/`。
