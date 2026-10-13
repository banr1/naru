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
- `generated`: `naru compile` の出力先(既定 `generated`)。そこには `naru compile` の決定的な出力(`Model` と `Statements`)だけを置く。
- `generated` は Lake にも反映される(C24): `naru compile` / `naru simulate` は書き終えた生成先への symlink を `<ルート>/.lake/naru/generated`
  (追跡対象外)に置き、`lakefile.toml` の lean_lib `Model` / `Statements` の `srcDir` はそこを向く。`lake build Model` / `lake build Statements` /
  `naru_simulate` はこの link 経由で現在の設定の生成先を読むので、`generated` を変えても lakefile を手で直さない。`lake build Model` の前に
  一度 `lake exe naru compile` が要る(link はそのとき作られる)。
- モジュール名はソースルートからの相対パスに対応する。`specs/consensus/Consensus/Objects/Time.naru` は `Consensus.Objects.Time`
  (ファイルの `module` 宣言もこれと一致させる)。生成ファイルは `generated/Model/Consensus/Objects/Time.lean`(Lean モジュール `Model.Consensus.Objects.Time`)と、
  spec 宣言があれば `generated/Statements/Consensus/Objects/Time.lean`。

## コマンド

`naru.toml` は cwd のものを読む。stdlib / コンパイラ(ヘッダの hash)、`simulate` の実行入口と `lake build`、Lake が読む生成ソースの link は、
実行ファイル `<ルート>/.lake/build/bin/naru` の場所から求めたリポジトリのルート(ホーム)のもの。ふつうはルートで `lake exe naru …` と実行するが、
別のディレクトリに `naru.toml` を置いたプロジェクトでも、そこを cwd にして `<ルート>/.lake/build/bin/naru compile` / `simulate` と直接呼べる
(設定変更プロジェクト `tests/config_change/` はこの形で検査する。[testing.md](testing.md))。`lsp` は cwd に依らない。

| コマンド | 意味 |
|---|---|
| `compile` | `naru.toml` の各ソースルートを 1 単位として検査し(パス順)、Model と Statements を `generated/` に出力する(`generated/Model.lean` と `generated/Model/**.lean`、`generated/Statements.lean` と `generated/Statements/**.lean` を丸ごと作り直す: 旧パスの生成物や以前の規則の不要なファイルは残らない)。Model ファイルは Lean の runtime 宣言を実際に出力するモジュールにだけ、Statements ファイルは spec 宣言のあるモジュールにだけでき、ルートの `Model.lean` / `Statements.lean` は存在するものだけを import する(C38。[architecture.md](architecture.md))。ソースルートが複数のとき、ルートをまたぐ同名のモジュールは全ルートの module を束ねた共通検査が各 `module` 行に E017 を出して exit 1(生成先に触れない)。C1 の検証コマンド |
| `compile [--out <dir>] <files...>` | 指定ファイルを検査する。`--out` があればそこに Model と Statements を出力し、無ければ検査だけ(`checked N module(s)`) |
| `check-reject <file.naru> <Exxx>` | 反例が `Exxx` で拒否されることを検査(PASS で exit 0) |
| `lsp` | 標準入出力で言語サーバー(LSP、JSON-RPC 2.0 の `Content-Length` 枠)として動く(C18。`compiler/Naru/Lsp.lean`)。下の「言語サーバー」 |
| `simulate <specs/consensus/scenarios/basic.naru>` | ソースルート全体を検査して `generated/` を作り直し、そのファイルの scenario を native 実行して observer の値を表示する(C7)。診断があれば exit 1、`naru.toml` のソースルートの外・scenario 無しは exit 2、`lake build naru_simulate` の失敗は exit 1、それ以外は実行ファイルの exit code |

出力の形と `check-reject` の説明は [diagnostics.md](diagnostics.md)。

### simulate

scenario は定理ではなく実行 fixture(言語の側は [language.md](language.md) の「scenario と observer」)。

- ファイルは `naru.toml` のソースルート配下に限る(外なら exit 2)。`./specs/…` やリポジトリの絶対パスで渡しても、実際のパス(`realPath`)で
  ルート配下のファイルと突き合わせる。
- ソースルート全体を検査して有効な生成先に Model と Statements を作り直し、Lake が読む link `.lake/naru/generated` をそこに向ける(`compile` と同じ)。
  診断があれば exit 1 で、生成先も実行ファイルも触らず何も実行しない。
- 実行入口 `main`(C1 のヘッダ付き。追跡対象外)は生成先ではなく `<ルート>/.lake/naru/simulate/Simulate.lean` に書く(生成先を変えても所在は同じ)。
  lakefile の lean_exe `naru_simulate` の `srcDir` は `.lake/naru/simulate`。生成先には `naru compile` の決定的な出力だけがある(C26)。
- ルートで `lake build naru_simulate`(link 経由で現在の生成先の Model を native にビルド。失敗すれば exit 1 で古い実行ファイルは実行しない)→
  `.lake/build/bin/naru_simulate` を実行する(「naru を実行する」= 生成 Lean を実行する)。生成先・Lake が読む Model・実行ファイルは同じ
  `naru.toml` と現在のソースに対応する(C7)。
- 出力: `scenario <name>`、scalar は `  <label> = <Repr>`、List は `  <label>:` の下に 1 要素 1 行。値の表示は Lean の `Repr`
  (record は `{ time := 4, node := { value := 0 }, … }`)。

## 言語サーバー(`naru lsp`)

Zed 拡張(`editors/zed-naru/`、[editors.md](editors.md))が起動し、開いた `.naru` の診断を表示し、ホバー・定義ジャンプ・補完に応える。応じるのは `initialize`(全文同期
`textDocumentSync.change = 1`、`openClose`、`save`、`hoverProvider`、`definitionProvider`、`completionProvider`(`triggerCharacters` は `.`))/ `initialized` / `shutdown` / `exit` と
`textDocument/didOpen` / `didChange`(全文)/ `didSave` / `didClose`、`textDocument/hover`(C29)、`textDocument/definition`(C30)、`textDocument/completion`(C31)。それ以外の
リクエスト(リネーム・整形の C32 / C33 は未対応)には `MethodNotFound`(-32601)を返し、それ以外の通知(`$/…` 等)は無視する。

- 位置にあるもの(ホバーと定義ジャンプの共通): 文書の位置にある参照 — 値の位置・型の位置・scenario の `input … = …;` に書かれた経路(`Phase.Tick` のような経路の上なら
  その最長の接頭辞で解決した宣言と、カーソルのある区切り。UFCS の `x.f(…)` の `f` も)—、宣言名そのもの、record / state / enum の宣言の中の欄名 / variant 名、
  型検査が解決した式の中の欄名 / stdlib のメソッド名の順に探す。位置はトークン(経路)の先頭から終わりまでで、終わりの直後の列(識別子の末尾にあるカーソル)も含む。
  索引は名前解決が集めた参照(`Checked.refs`)と型検査が集めた欄・メソッドの参照(`Checked.members`)・アクセスの受け手の型(`Checked.accesses`、
  [architecture.md](architecture.md))で、単位ごとに直前の検査(全ファイルが構文解析できたもの)の結果を持ち、ホバーと定義ジャンプは検査し直さない。
- 定義ジャンプ(`textDocument/definition`): 参照・宣言名からは同じコンパイル単位の宣言(別ファイルを含む)の URI と宣言の名前のトークンの範囲(`Location`)、欄名
  (式の中・宣言の中)からはその record / state の欄の名前のトークン、宣言の中の variant 名からはその variant を返す。どれも無い位置(コメント・予約語・局所変数・
  stdlib のメソッド)では null。
- ホバー(`textDocument/hover`): Markdown(`contents.kind = "markdown"`)で、宣言の署名のコードブロック(fn / input / observer / spec 宣言なら仮引数と戻り型、
  record / state なら欄と `derive`、enum なら variant と `derive`、type なら右辺、claim bundle なら項目名)、種類・名前・モジュール(protocol の中の宣言ならその
  protocol)、その宣言の宣言コメント(C60: 宣言の直上の `//` ブロック。1 行目の要旨を段落、2 行目以降を行ごとの改行で。バッククォートの外の `\ * _ < > [ ] #` は
  Markdown から逃がす)を返す。経路の残りが enum の variant(`Stamp.At`)と宣言の中の variant 名ならその variant の形(`Stamp.At(Time)`)と variant の直上の
  1 行の説明と enum の宣言コメント、欄名(式の中・宣言の中)なら `Record.欄: 型`(宣言に書かれた型)と欄の直上の 1 行の説明と record の宣言コメント、stdlib の
  メソッド名なら受け手の型で実体化した署名(`Set<ValidatorId>.contains(ValidatorId) -> Bool`)。`range` は参照の経路 / トークンの範囲。識別子でない位置
  (空白・コメント・予約語・局所変数)では null。
- 補完(`textDocument/completion`): `CompletionList`(`isIncomplete = false`: 候補は揃っていて、入力中の語での絞り込みはエディタが行う)。各項目は `label`・`kind`
  (fn / observer は Function、record / state は Struct、enum は Enum、type は Class、spec 宣言は Interface、input と局所名は Variable、欄は Field、stdlib の
  メソッドは Method、variant は EnumMember、予約語は Keyword)・`detail`(宣言の署名 / `Record.欄: 型` / 受け手の型で実体化したメソッドの署名)・
  `documentation`(宣言コメントの要旨と種類・名前・モジュール、欄 / variant の 1 行の説明)。
  - `.` の直後(途中まで書いた名前の中を含む): 受け手の型から — record / state なら欄、stdlib の型(Set / List / Option / Result / Table / Nat / Int / String)なら
    そのメソッド表(常に拒否される Set の選択 E003・順序 E004 のメソッドは表に無いので出ない)、どの型でもその型を最初の仮引数に取る fn 等(UFCS
    `x.f(…)`)。受け手の型は型検査の索引 `Checked.accesses`(欄 / メソッドのアクセスごとの受け手の型。名前が解決できなくても残る)から取り、索引が
    現在の本文に無ければ(`x.` まで書いた構文エラーの途中など)位置の名前を仮の識別子に置き換えた本文で単位を検査し直して取る(診断は送らず索引も
    変えない。移植ソース全体で約 0.06 秒)。型が決まらなければ `.` の前の経路から: enum(`Phase.`)ならその variant、モジュール名(とその接頭辞)なら
    その宣言 / 次の区切り、組み込みの型(`Set.`)なら静的関数(`empty` / `singleton` / `of` …)。UFCS の候補は仮引数の型の表記を型別名の展開と
    表示名で正規化して受け手の型の表示と文字列で比べる近似(別モジュールの同じ表示名の record は区別しない)。
  - それ以外の位置: 位置を含む宣言の仮引数と、その位置より前に束ねられた局所名(`let` / lambda / 量化 / パターン。有効範囲は位置の前後で近似する)、
    単位の全宣言(名前解決は単位の 1 つの大域表なので import の有無に関わらず見える)、予約語、組み込みの型と構築子(`Some` / `None` / `Ok` / `Err` / `sort`)。
  - 行コメント・同じ行で開いたブロックコメント・文字列リテラルの中では空(行をまたぐブロックコメントは見ない)。

- 検査の単位: 文書のパスの祖先で最も近い `naru.toml` を読み、その `sources` のルート配下なら `<ルート>/**/*.naru` 全体を 1 つのコンパイル単位にし、
  開いている文書はディスクではなくバッファの内容で検査する(CLI の `compile` と同じ `Driver.compileSources`)。それ以外の文書は単独。
- 診断は `textDocument/publishDiagnostics`。コンパイラの 1 始まりの行・列を 0 始まりに直し、範囲はその位置のトークン 1 つ分
  (識別子・数・文字列・記号)、severity はエラー、`code` は `E0xx`、`source` は `naru`。列は UTF-16 単位(LSP の既定)。
- 他のファイルに出た診断はそのファイルの URI へ送る(開いていないファイルにも)。文書自身には空でも必ず送り、前回その単位で送った
  URI のうち今回空になったものには空を送って消す。`didClose` には空を送り、同じ単位に開いた文書が残っていればディスクの内容で
  検査し直す(その検査では閉じた文書へは送らず空のままにし、次の検査からは開いていないファイルとして扱う)。残っていなければ
  その単位の診断をすべて消す。
- 意味検査はすべてコンパイラ側(この層は診断の運搬だけ: IDEAL.md「不変条件」)。モジュール名の重複と生成 Model / Statements の import の循環
  (E017)も生成前の共通検査が出すので、CLI の `compile` と同じ行・列に返る(循環はそれに関与する各ファイルの参照の位置に 1 つずつ。
  循環を解消する編集で関係する URI すべての診断が消える)。言語サーバーの検査はファイルを生成しない(生成先には触れない)。
