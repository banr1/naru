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
  旧名検索はこれだけを除外する。`sem_core.naru` はコンパイラ意味論保存の「今回の保存対象」「Surface AST の保存対象」の各構文を 1 宣言ずつ使う検体(C39 / C46 / C48〜C52)、
  `tests/units/accept/sem_calls/` は「関数・input の保存対象」(非再帰の fn / spec 宣言の呼出し・input・位置 / 名前付き引数・UFCS)の検体(C54)で、どちらも `naru_test semantics` が
  Core と Surface AST を引用して検査する(下の「コンパイラ意味論保存」))。`naru_test lsp` は全受理例の `didOpen` で診断 0 件も確かめる。
- 生成 Lean の型検査は、生成 Model の olean を `--out` のディレクトリに作ってから行う(`naru_test regression` が全受理例に対して行う)。
- `tests/config_change/`: 設定変更プロジェクト(C7 / C24 / C26 の検体)。`naru.toml`(`sources = ["src"]`、`generated = "generated"`)と
  `src/Counter.naru`(fn `value()` の値を observer `current()` が、`value()` + input `offset()`(scenario が 10 に束縛)を observer `shifted()` が表示する
  scenario `counter`)、`src/Rules.naru`(spec だけ)、`src/Inputs.naru`(input だけ。C38: 既定以外の生成先でも Model ファイルは `Counter` だけ)。`naru_test regression` が複製の上で `generated` を
  `"custom"` に、`value()` の 1 を 2 に書き換えて `naru simulate` を走らせ、observer・生成先・Lake のビルド・実行ファイルの対応を照合する(回帰一式の 10)。
- `tests/units/`: 複数ファイルのコンパイル単位の検体(C18 / C38)。`reject/<名前>/` と `accept/<名前>/` に `naru.toml`(`sources = ["src"]`)と `src/*.naru`
  (1 つの単位)。反例は `reject/module_duplicate`(2 ファイルが同じモジュール名)・`reject/runtime_cycle`(runtime 宣言の参照が Alpha → Beta → Gamma →
  Alpha と巡る)・`reject/spec_cycle`(spec 宣言の参照が Left → Right → Left と巡る)・`reject/inferred_cycle`(`make().x` の record の推論された型だけで
  生じる辺を含む循環。その辺の E017 は宣言 `width` の名前の位置)・`reject/omitted_duplicate`(C38: Model ファイルを出さない spec だけのモジュールと runtime の
  モジュールが同じモジュール名。出力の省略にかかわらず E017)で、各ファイルの行末の `// E017` が診断の出る行の印、`fix/<ファイル>.naru` はその `src/` の
  ファイルを置き換えると誤りが消える内容。受理例は `accept/dependency_ok`(Top → Middle → Base の循環しない依存。spec 宣言が runtime 宣言と他モジュールの
  spec 宣言を使う)と `accept/cross_phase_ok`(Alpha の spec が Beta の runtime を、Beta の spec が Alpha の spec を使う。Model と Statements の import グラフは
  別なので循環しない)と `accept/omit_model`(C38: runtime だけ / spec だけ / 両方 / input だけ / 宣言なしのモジュールと、別モジュールの input を runtime と
  spec から使う `User`、`Point` を名指しせず input の署名だけを通して RuntimeOnly に依存する `Probe`。Model ファイルは runtime 宣言を出力する 4 モジュールに
  だけでき、`User` / `Probe` は input の宣言元 `Inputs` ではなく署名の型のモジュール `RuntimeOnly` を import する)。`naru_test regression`(回帰一式の 3)が
  CLI の診断(出力指定あり / なし)を印と照合し、生成ファイルの有無・import・宣言・input を渡した実際の値を照合し、`naru_test lsp` が LSP の診断の位置・幅と
  `fix/` の didChange で診断が消えることを照合する。検体は `lake exe naru compile tests/units/reject/<名前>/src/*.naru` でも試せる。
  `roots/duplicate_across_roots/`(C38 / C18)はソースルートをまたぐ同名のモジュールの反例(`naru.toml` の `sources = ["a", "b"]`。ルート `a` は spec だけ、
  ルート `b` は runtime だけで生成パスは衝突しない): 複製を cwd にした `naru compile` が両方の `module` 行(行末の `// E017`)に E017 を出して exit 1 になる。
  言語サーバーの単位は 1 つのルートなので、この反例は CLI(compile-all)だけが検出する。

## 検査ドライバ(`lake exe naru_test`)

| 群 | 意味 |
|---|---|
| `grammar` | tree-sitter 文法(`editors/tree-sitter-naru/`)の検査(C16): `tree-sitter generate` の出力が追跡対象の `src/` と一致、`tree-sitter build` が exit 0、`specs/consensus/`(`naru.toml` のソースルート)・`tests/accept/`・`tests/reject/` の全 `.naru`(E010 を期待する反例は除く)が ERROR / MISSING なしに解析できる、`tests/accept/editors_syntax.naru` への `queries/highlights.scm` の捕捉が `tests/accept/editors_syntax.captures` の行に出る、その受理例がコンパイラの検査を通る、`editors/zed-naru/languages/naru/highlights.scm` が `queries/highlights.scm` と同一 |
| `zed` | Zed 拡張(`editors/zed-naru/`)の検査(C17): 5 ファイル(`extension.toml`・`languages/naru/config.toml`・`highlights.scm`・`Cargo.toml`・`src/lib.rs`)がある、`extension.toml` の `id = "naru"`・`[grammars.naru]` の `repository`(このリポジトリの `file://` URL)/ `rev`(40 桁の SHA)/ `path = "editors/tree-sitter-naru"`・`[language_servers.naru]` の `name` と `languages`、`config.toml` の `name` / `grammar` / `path_suffixes` / `language_servers`、`rev` がこのリポジトリのコミットで `git diff --exit-code <rev> HEAD -- editors/tree-sitter-naru` が空、`rev` の文法(`git archive`)を `tree-sitter build` して作業ツリーの `highlights.scm` が `tree-sitter query` でロードできる、`src/lib.rs` が設定 → `PATH` → `.lake/build/bin/naru` の順で `naru lsp` を起動する形、`cargo build --release --target wasm32-wasip2` が exit 0。一時ファイルは `.lake/naru/test/zed/`、cargo の成果物は `editors/zed-naru/target/` |
| `lsp` | 言語サーバー `naru lsp` の検査(C18): `lake build naru` の後、子プロセスの `.lake/build/bin/naru lsp` と LSP を話す。`initialize` の応答に全文同期がある、未対応のリクエスト(`textDocument/hover`)が `MethodNotFound`(この応答を、通知の処理の終わりを待つ barrier にも使う)、`tests/reject/` の各反例の `didOpen` で `naru compile` と同じ E 番号・行・列の診断(先頭コメントが名指しする E 番号を含む)がその URI に返り `didClose` で空になる、`tests/accept/` の各受理例の `didOpen` で診断 0 件(C35 の正常例を含む)、絵文字を含む単独文書で列が UTF-16 単位・範囲がトークン 1 つ分、`specs/consensus/` の全ファイルの `didOpen` で 0 件、`specs/consensus/Consensus/Objects/Time.naru` の `didChange` で末尾に足した未解決名の E011 がその行に出る・`slotStart` の改名で他のファイル(Parameters / Grades)の URI に E011 が出る・壊れたまま Parameters を `didClose` すると空のまま・開き直すと戻る・Time を戻すと消える、`didSave` で 0 件のまま、全ファイルの `didClose` で空、`shutdown` が `null`、`exit` で exit 0。期待値はコンパイラ(`compileSources`)から取る。C18 の複数ファイルの検体 `tests/units/`: 反例(`module_duplicate` / `runtime_cycle` / `spec_cycle` / `inferred_cycle`)は `src/` の全ファイルを `didOpen` すると、行末の `// E017` の印の行に、`compileSources` と同じ行・列(UTF-16)でトークン 1 つ分の幅の E017 が関与する全ファイルの URI に返り、`fix/` の内容に `didChange` すると関係する URI すべての診断が消え、戻すと戻り、`didClose` で閉じた文書は空(最後の文書を閉じると単位の診断がすべて消える)。受理例(`dependency_ok` / `cross_phase_ok`)は全ファイルの `didOpen` で 0 件。言語サーバーはファイルを生成しない: 生成先と `tests/units/` の全ファイルの sha256 がセッションの前後で同じ |
| `zed-install` | 起動中の人間の Zed に `editors/zed-naru/` を Dev Extension として入れる(C19): `lake build naru` の後、`~/Library/Application Support/Zed/extensions/installed/naru` が無ければ `zed: install dev extension`(フォルダ選択ダイアログに ⌘⇧G でパスを貼る)、この拡張への symlink なら `zed: rebuild dev extension`(Dev Extension が 2 つ以上なら picker で `naru`)を `osascript`(System Events。文字列はクリップボード経由、前面が Zed であることを確かめてから送る)で実行し、`Zed.log` に操作の開始以後 `compiled grammar naru`・`finished compiling extension <installed/naru>`(install では Zed は拡張のソースのパスで記録するのでそれも受理)・`extensions updated.` の `loading 1` / `reloading 1` が足され、`failed to compile` / `Failed to install dev extension` が 0 件、`installed/naru` が `editors/zed-naru` への symlink、`extension.wasm` と `grammars/naru.wasm` の mtime が操作の開始以後、`grammars/naru/` の checkout が `extension.toml` の `rev`。`grammars/naru.wasm` は操作の前に消す(Zed は `parser.c` より新しい wasm があると文法のコンパイルを飛ばす)。スクリーンショットと AppleScript は `.lake/naru/test/zed-install/` |
| `golden [--finality-horizon N]` / `golden --comparator` | 手書き Model と生成 Model の突き合わせ(C10)と、その比較器の検体。下の「golden test」 |
| `statements` | 生成 Statements の検査(C8 / C9): `lake exe naru compile` で `generated/` を作り直し、`lake build Statements` が exit 0、`Statements` からの import 閉包(`lake env lean --deps-json`。ソースの文字列から推測しない)が `Init` / `NaruStd` / 生成 Model / 生成 Statements だけから成り(Proofs を含まない)、`generated/Statements/` 配下の全ファイルがその閉包にある、閉包の全ファイルに字句 `sorry` が無い、`specs/consensus/`(`naru.toml` のソースルート)に claim bundle `Consensus` がちょうど 1 つあってその項目が verified-consensus の 13 claims と同名、生成 `structure` の欄(`run_cmd` の `getStructureFields`。スクリプトは `.lake/naru/test/statements/SurfaceShape.lean`)が項目と同じ順で並び 13 名を列挙する。C37: 移植ソースの spec 側がソースルートの `Consensus/Spec/` にあり(改名前のディレクトリは無い)、各ファイルの `module` 宣言がルート相対パス(`Consensus.Spec.<ファイル名>`)と一致、単位に改名前の名前のモジュール・import が無い、claim bundle が `Consensus.Spec.*` にある、生成先に改名前のディレクトリが無く生成ファイルのどれも改名前のモジュール名に触れず、`generated/Statements/Consensus/Spec/` の全モジュールが閉包にある。C38: `generated/` の Model ファイルは Lean の runtime 宣言を実際に出力するモジュールにだけ、Statements ファイルは spec 宣言のあるモジュールにだけあり、ルート `Model.lean` / `Statements.lean` が存在する生成モジュールをちょうど import し、生成ファイルの全 import が実在し、出力される runtime 宣言と spec 宣言のすべてが生成ファイルに宣言として現れる(`NaruTest.checkOmission`。移植ソースの Core と照合)、`generated/Model/Consensus/Spec/` には混在モジュールの Model が残り spec だけのモジュールの Model は無い |
| `semantics` | コンパイラ意味論保存(C39〜C52。下の「コンパイラ意味論保存」): C45 の検査入口 `lake build NaruSem`(`semantics/NaruSem`: 独立した意味論・適格性の定義、一般定理、検体、公理監査)が exit 0、`lake env lean semantics/NaruSem.lean` の公理監査の出力に必須の定理(`NaruTest/Semantics.lean` の `requiredTheorems`: `eval_total` / `Eval_unique` / `Sem_exists` / `Sem_unique`、`denote_sound` / `preserve_nat` / `preserve_bool` / `check_sound_nat` / `check_sound_bool`、腕の列・腕の `denoteArms_sound` / `denoteArm_sound` と腕の選択の `denoteArmsV_*`、Statements の `Sem_denote`(一般形 `Sem_denote_all`、基礎段階の系 `Sem_denote_basic`)/ `Sem_denoteP` / `check_sound_prop` と境界 `denoteP_iff_denoteB_noProp` / `denoteP_iff_denoteB` / `basic_not_proppy`、`proppyS_congr` / `wtS_noExh`、腕の選択と束縛の `denoteArmsP_*`、量化の `denoteQuant_*_cons`、局所束縛・条件・`==` の読みの形、対応関係の補題)が `audit ok:` で現れて許容しない依存が 0 件、文書との照合(C47: [architecture.md](architecture.md)「一般定理」の表の定理名がすべて監査に載り、この文書に検査のコマンドが記載されている)、検体 `tests/accept/sem_core.naru` の各宣言(`c39Decls`: 今回の保存対象の各構文を 1 つずつ)の Core を実際の compiler 経路(`Naru.compileFiles`)から引用した検査プログラム `.lake/naru/test/semantics/Scope.lean` をモジュール `Scope` として `lean` でコンパイル(適格性 `wtR` / `wtS` を `decide` で、引用した Core と compiler の Core の一致を `run_cmd` の再コンパイルで照合)、段階の境界(`c40Decls` / `c42Decls` は `NaruSem.basic` が真、`c41Decls` の `match` と `c43Decls` の量化 / 命題の `let` / 命題の `if` / ガード付き `match` / Prop を含む `==` は偽)、実際の CLI で `.lake/naru/test/semantics/gen/` に生成した Model をモジュール `Model.Sem.Core` にして `ModelCheck.lean` で一般定理の量化の形(式と腕の列)と各 runtime 宣言の接続(`conn_<f>`: 実生成宣言 = 読み。`rfl`、リテラルパターンの `match` は scrutinee の `cases` の後に `rfl`)・保存(`pres_<f>`)を kernel に検査させて公理監査、実生成文字列から作った誤翻訳の負の検体 `ModelWrong.lean`(`&&` / `||` の取り違え、束縛の取り違え、Bool の腕の入れ替え、ガードの否定、腕の束縛の漏れ)が型検査を通りつつ接続検査だけがその定理の行で失敗(対照は成功)、同じ生成先の Statements をモジュール `Statements.Sem.Core` にして `StatementsCheck.lean` で同値定理・境界・腕と量化の補題の量化の形と各 spec 宣言(`c42Decls` + `c43Decls`)の接続(`conn_<f>`: 実生成宣言の命題 = 読み `denoteP`。`rfl`、リテラルパターンの `match` は `cases` の後に `rfl`)・段階(`stage_<f>`: `basic` の真偽)・保存(`pres_<f>`: `Sem … core_<f> (実生成宣言の命題)`)を kernel に検査させて公理監査、負の検体 `StatementsWrong.lean`(`∧` / `∨` の取り違え、含意の向きの反転、Bool の値を `= false` に写す境界の誤り、`if` の分岐の入れ替え、`∀` / `∃` の取り違え、命題の `let` の束縛の取り違え、ガードの否定、`↔` を `→` に、Prop のガードの `∃` を `∀` に、腕の束縛の漏れ)が接続検査だけで失敗、監査が `sorry` / `native_decide` / 存在しない定数を失敗にする負の検体 3 つ(`Audit_*.lean` が exit 非 0)。C48: 同じ検体の各宣言の実際の構文解析の出力(Surface AST)を最小の fn / spec 宣言の包装 `NaruSem.Surf.Decl`(種別・名前・位置・仮引数・戻り型・本体)に写し(`ofDeclAst?`)、宣言の適格性 `Surf.wtDecl` の phase が一覧と、本体の型が Core の型付けの結果と一致し、引用した宣言と本体の検査プログラム `.lake/naru/test/semantics/SurfaceScope.lean` が適格性(`wtd_<f>` / `wta_<f>`)を `decide` で、埋め込み(`Decl.toAst`)と構文解析の出力の一致を `run_cmd` の再構文解析で照合する。対象外の構文を含む `tests/accept/guard_shadow.naru` の宣言は `ofAst?` が `none`。C49 / C51 / C52(runtime): 同じ `SurfaceScope.lean` が各 runtime 宣言の AST の独立した変換 `Surf.lower`(`semantics/NaruSem/Lower.lean`)が実際の Core に等しいこと(`low_<f>`、`rfl`)を検査し、`ModelCheck.lean`(`SurfaceScope` を import)が一般定理 `Surf.lower_sound` / `Surf.preserve_nat` の量化の形と、各 runtime 宣言の AST → 生成 Lean の合成 `apres_<f>`(`Surf.check_sound_nat` / `Surf.check_sound_bool` が `wta_<f>`・`low_<f>`・`conn_<f>` から導く)を kernel に検査させて公理監査に載せ、実際の Core の値から作った負の検体 `SurfaceWrong.lean`(`&&` / `||` の取り違え、2 つ目の `let_` の改名、ガードの否定。どれも `wtR` は通る)が正しい AST の変換との一致だけで失敗する。C50 / C51 / C52(spec): 各 spec 宣言の AST の独立した変換 `Surf.lowerS`(`semantics/NaruSem/LowerSpec.lean`)が実際の Core に等しいこと(`lows_<f>`、`rfl`)、`StatementsCheck.lean` が一般定理 `Surf.lowerS_sound` / `Surf.Sem_lowerS_iff`(双方向)/ `Surf.preserve_prop` の量化の形と合成 `apres_<f>`(`Surf.check_sound_prop`)を kernel に検査させて公理監査に載せ、負の検体 `SurfaceSpecWrong.lean`(`∀` / `∃` の取り違え、命題の `let` の束縛の取り違え、ガードの否定。どれも `wtS` は通り、具体環境で読みが非同値)が正しい AST の変換との一致だけで失敗する。C54: 検体 `tests/units/accept/sem_calls/`(関数・input の呼出し)の fn / input / spec 宣言すべてを Core と Surface AST の宣言群として依存順に引用した `CallScope.lean` / `SurfaceCallScope.lean` で、宣言群の適格性(`NaruSem.Call.wtProg` / `NaruSem.Surf.Call.wtProg`)・各宣言の署名・実際の Core / AST から作った負の検体(依存順の反転・違う呼出し先・phase・循環・重複・引数の数と型・未解決の名前・名前付き引数の誤り)・input の解釈の下の fn の値と署名に合わない解釈の行き詰まりを kernel の `decide` で、引用の一致と宣言群全体の網羅を再コンパイル / 再構文解析で検査する。C55 / C56 / C57 / C58(runtime): 同じ検体を実際の CLI で生成した Model `Model.Sem.Call` に対し `CallModelCheck.lean` が実生成宣言の表から作った環境が署名を守ること、各 fn の接続 `conn_<f>` と証拠 `evid_<f>`、宣言群の意味と実生成定数の一致 `cgen_call`、各 fn の値 `cval_<f>` を kernel に検査させて公理監査に載せ、負の検体 `CallModelWrong.lean`(同じ署名の別の呼出し先・名前付き実引数の取り違え・UFCS の受け手・input の誤配線)が接続検査だけで失敗する。約 1 分(ビルド済みなら約 50 秒) |
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
   受理例 `dependency_ok` / `cross_phase_ok` / `omit_model` は exit 0 で、`--out` に生成した Model / Statements の全ファイル(ルートの集約ファイルを含む)が import の順に
   Lean で型検査できる(生成モジュール同士の import が解決する)。反例には `omitted_duplicate`(C38)も含む。
   C38 の Model の生成省略(段 `C38 Model omission`): 受理例 `accept/omit_model` を `.lake/naru/test/regression/c38/clean/` に生成し、Model ファイルは
   runtime 宣言を出力するモジュール(`RuntimeOnly` / `Mixed` / `User`)にだけ・Statements ファイルは spec 宣言のあるモジュール(`SpecOnly` / `Mixed` / `User`)に
   だけあり(`Inputs` は input だけ、`Empty` は宣言なし、`SpecOnly` は spec だけなので Model は無い)、ルートの集約ファイルが存在するモジュールをちょうど import し、
   全 import が実在し、全宣言が現れることを Core と照合する(`NaruTest.checkOmission`)。`User` の生成 Model / Statements は input の宣言元 `Inputs` を import せず
   署名の型のモジュール `RuntimeOnly` を import し、input を引数 `origin'` / `seed'` / `scale'` に持つ。生成 Lean 8 ファイルを import 順に型検査し、検査プログラム
   `Check.lean`(`c38Program`)を `lean --run` して input を渡した `start` / `size` の値、scenario `run` の観測(`current() = 5` / `scaled() = 55`)、input を引数に持つ
   命題の真偽 6 件を照合する。旧構成の生成物・不要な空ファイル(コメントだけの Model ファイル、旧パス、古いルート、ビルドの残骸)を置いた `c38/stale/` への
   再生成(直後と、同じ入力でもう一度)がクリーンな生成先とパス集合・sha256 まで一致し、置いたファイルは残らず、省略と import 解決が成立する。
   `Probe`(`Point` を名指ししない)の生成 Model / Statements が `RuntimeOnly` を import する(署名の型の import は input だけを通して入る)。
   ルートの集約ファイルの例外: `Empty.naru` / `RuntimeOnly.naru` / `omitted_duplicate/fix/Claims.naru` を 1 ファイルの単位として生成し、宣言なし / runtime だけ /
   spec だけでも `Model.lean` と `Statements.lean` が生成され、無い側は import 0 件でディレクトリも作られない。`roots/duplicate_across_roots/` の複製を cwd に
   した `naru compile` が両方の `module` 行に E017 を出して exit 1 になり、生成先にも Lake の link `.lake/naru/generated` にも触れない。
   反例 `reject/omitted_duplicate` は `fix/` を当てると診断 0 で、Claims が Model を出さないモジュールであることを確かめる。
4. `semantics`(C39〜C47。C45 の検査入口 `lake build NaruSem` と公理監査、文書との照合、実際の compiler 経路の Core の適格性、実生成 Model の
   runtime 宣言(基礎と `match`)と実生成 Statements の spec 宣言(基礎段階と、量化・命題の `let`・命題の `if`・ガード付き `match`・Prop を含む `==`)の
   接続と保存、誤翻訳の負の検体。下の「コンパイラ意味論保存」)、
   `grammar`(C16)/ `zed`(C17)/ `lsp`(C18。`tests/units/` の検体の didOpen / didChange / didClose と、生成ファイルが変わらないことを含む)の各群、
   golden の短い予行(`--finality-horizon 40`)、C10 の比較器回帰(`golden --comparator`。下の「golden test」の「比較器の検体」)。
5. C1 の決定性: `lake exe naru compile` を 2 回走らせて生成先の全ファイルの sha256 が一致、各ファイルの先頭 5 行に `naru-compiler` / `naru-stdlib` / `naru-source`、
   `naru-source:` のパスがソースルートのディレクトリ名で始まらない、各ソースの sha256 がヘッダにある。
6. `lake build Model`(C6。`noncomputable` / `unsafe` / `axiom` / `sorry` / `partial` の whole-word grep が 0 件)、`lake build Statements`(C8。`sorry` 0 件)、`statements` 群(C8 / C9 / C37 / C38)。
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
    C38(既定以外の生成先でも同じ規則): `custom/` に置いた旧構成の Model ファイル(`Model/Rules.lean` / `Model/Inputs.lean` / 旧パス)が再生成で消え、
    同じ入力での再生成の繰り返しが同じ出力になり、`checkOmission` で Model は `Counter` だけ・Statements は `Counter` と `Rules`・ルートの import・
    全 import の実在・全宣言の出現を照合する(`Rules` は spec だけ、`Inputs` は input だけ)。各実行で observer `shifted()`(`value()` + input `offset()`)が
    `shifted() = 11` / `12` を表示し、ルートの `lake build Model Statements`(`Statements.Rules` が `Model.Counter` を import する)と実行ファイルもこの生成先で通る。
11. C24: `compiler/` にソースルートのディレクトリ名の直書きが無い(`grep -rn '"dsl\|"specs' compiler/` が 0 件)、`naru.toml` の `sources` を別名のコピー
    (`.lake/naru/test/regression/alias/`)に向けて `lake exe naru compile` しても生成先の sha256 が一致する。`naru.toml` は必ず元に戻し(`git diff --exit-code`)、
    もう一度 `compile` して生成先が元に戻ったことも確かめる。
12. `repo` 群(C21 / C23 / C25 / C37 の旧名検索)、C28(`git ls-files tests/golden` が `Golden.lean` だけ)、C22(`cmp LICENSE`)、C27(`git check-attr`)。
13. C10: `golden`(引数なし = horizon 100、全 16 ケース。約 9 分)。

`zed-install`(C19。人間の Zed を操作する)と C20(画面観測)は入れない。IDD の台帳・knowledge を更新した後は、少なくとも `repo` 群を再実行する(C25 / C36)。

## コンパイラ意味論保存(C39〜C47、C48〜C53、C54〜C59)

`semantics/NaruSem`(lean_lib `NaruSem`)に、naru の Core IR と Surface AST の独立した意味論と適格性の定義、Surface AST → Core の変換(runtime / spec)と対応の一般定理、
関数・input の呼出しを含む宣言群の意味論と適格性(C54)と呼出しを含む Model の保存・宣言群の意味と実生成定数の一致(C55〜C57 の runtime)、検体、公理監査がある
(構成と定理の一覧は [architecture.md](architecture.md)「コンパイラ意味論保存」)。検査入口と走らせ方:

```sh
lake build NaruSem                        # C45 の検査入口: 意味論・一般定理・検体を kernel が検査し、公理監査(`#audit_axioms`)が許容しない依存を失敗にする
lake env lean semantics/NaruSem.lean      # 公理監査の出力を取り直す(`audit ok: <定数> depends on axioms […]` の行)
lake exe naru_test semantics              # 上の 2 つ + 実際の compiler 経路の Core の適格性と引用の一致 + 実生成 Model / Statements の接続・保存 + 負の検体。約 1 分
```

- 公理監査(`semantics/NaruSem/Audit.lean`、`semantics/NaruSem.lean`): `#audit_axioms c₁ c₂ …` が各定数の依存閉包の公理を `#print axioms` と同じ
  `Lean.collectAxioms` で集め、許容する Lean 標準の論理公理 `propext` / `Classical.choice` / `Quot.sound`(理由は `Audit.lean`)以外 — `sorryAx`
  (未完了)、`native_decide` の公理(Lean 4.34 では定理ごとの補助公理 `<名前>._native.native_decide.ax_*`。`Lean.ofReduceBool` も同類)、独自の公理 —
  があればビルドを失敗にする。定数が無ければ名前解決で失敗する。
  ルート `NaruSem.lean` が必須の定理・補題・検体をすべて列挙するので、欠落もビルドの失敗。`naru_test semantics` は `sorry` / `native_decide` /
  存在しない定数の負の検体(`.lake/naru/test/semantics/Audit_*.lean`)で、監査が実際に失敗することも確かめる。
- 実際の compiler 経路の検体(C39 / C46): `tests/accept/sem_core.naru` の各宣言(今回の保存対象の構文を 1 つずつ)を `Naru.compileFiles` でコンパイルし、
  Core を Lean の項として引用した `.lake/naru/test/semantics/Scope.lean` を `lean` で検査する。各宣言の適格性(`wtR ctx core = some t` / `wtS ctx core = some τ`)
  は `decide`(kernel の計算)で、引用した Core が compiler の Core と一致することは `run_cmd NaruSem.Quote.checkDecls` が同じソースを再びコンパイルして
  構造の等しさで照合する(誤出力に合わせて期待側を変えない: C44)。検体を足したら `NaruTest/Semantics.lean` の `c39Decls` にも足す(基礎の runtime 宣言は
  `c40Decls`、`match` の runtime 宣言は `c41Decls`、基礎段階の spec 宣言は `c42Decls`、量化 / 命題の `let` / 命題の条件の `if` / ガード付き `match` / Prop を含む
  `==` の spec 宣言は `c43Decls` にも。どの一覧の宣言も実生成宣言への接続を検査する)。
- 実生成 Model の接続と保存(C40 / C41 / C44 / C46、[architecture.md](architecture.md)「Model の保存と実生成宣言への接続」): 同じ検体を実際の CLI
  (`lake exe naru compile --out .lake/naru/test/semantics/gen`)で生成し、生成 Model `gen/Model/Sem/Core.lean` をそのまま Lean のモジュール `Model.Sem.Core`
  にコンパイルして、検査プログラム `.lake/naru/test/semantics/ModelCheck.lean`(`Scope` と `Model.Sem.Core` を import)を `lean` で検査する: 一般定理
  `denote_sound` / `denoteArms_sound` の量化の形(任意の文脈・式・型・環境、任意の腕の列・値)、各 runtime 宣言 `f`(`c40Decls` + `c41Decls`)の接続
  `conn_f : ∀ args, Model.Sem.Core.f args = denoteN (Env.ofList …) core_f`(kernel の定義的等しさ。`match` の無い宣言は `rfl` の項、リテラルパターンの `match` は
  ドライバの `proofOf` が Core から求めた scrutinee の局所名の `cases`(Nat はリテラルの最大値 + 1 の深さ、Bool は 1 回)の後に `rfl`)と保存
  `pres_f : ∀ args, eval (Env.ofList …) core_f = some (.nat (Model.Sem.Core.f args))`(`check_sound_nat` / `check_sound_bool` が `wt_f`・`conn_f` から導く)。
  `conn_f` / `pres_f` は `#audit_axioms` で監査し、ドライバは全部が `audit ok:` に現れることを要求する。
  負の検体 `ModelWrong.lean`: 生成 Model の実際の文字列から誤翻訳 5 つ(`NaruTest/Semantics.lean` の `mistranslations`: `&&` と `||` を取り違えた `Wrong.logic`、
  2 つ目の束縛を改名した `Wrong.letShadow`、`true` / `false` の腕を入れ替えた `Wrong.matchBool`、ガードを否定した `Wrong.matchNat`、腕の束縛が後続の腕に
  漏れた形の `Wrong.matchShadow`)を作り(Lean の型検査は通る)、同じ正しい入力 Core への接続検査 `conn_wrong_*` だけが失敗する(exit 1。`error:` の行番号の
  集合が `conn_wrong_*` の 5 行とちょうど一致し、構文 / import の誤りでない)。正しい出力の対照 `conn_*_ok` は同じファイルで成功する。生成先・検査プログラムは
  追跡対象外で、`generated/` には触れない。
- 実生成 Statements の接続と保存(C42 / C43 / C44 / C46、[architecture.md](architecture.md)「Statements の保存と実生成宣言への接続」): 同じ生成先の
  `gen/Statements/Sem/Core.lean` をモジュール `Statements.Sem.Core` にコンパイルして、検査プログラム `.lake/naru/test/semantics/StatementsCheck.lean`(`Scope` と
  `Statements.Sem.Core` を import)を `lean` で検査する: 一般定理 `Sem_denote`(任意の文脈・`wtS` で適格な式・対応する環境・意味の両方向の同値)、境界
  `denoteP_iff_denoteB_noProp`(`proppyS` が偽の式と任意の環境)、腕の補題 `denoteArmsP_guard`、量化の補題 `denoteQuant_forall_cons` の量化の形、各 spec 宣言 `f`
  (基礎段階 `c42Decls` と、量化・Bool / Prop の `let` と shadowing・Bool / Prop の条件の `if`・ガード付き `match`・Prop を含む `==` / `!=` の `c43Decls`)の接続
  `conn_f : ∀ args, Statements.Sem.Core.f args = denoteP (SEnv.ofList …) core_f`(`Prop` の等式、`rfl`。リテラルパターンの `match` は Model と同じく `proofOf` の
  `cases` の後に `rfl`)、段階 `stage_f : basic core_f = true / false`(`decide`。一覧と一致)、保存 `pres_f : ∀ args, Sem (SEnv.ofList …) core_f (Statements.Sem.Core.f args)`
  (`check_sound_prop` が `wt_f`・`form_f`・`conn_f` から導く)。すべて `#audit_axioms` で監査し、ドライバは全部が `audit ok:` に現れ、接続した宣言数が
  `c42Decls` + `c43Decls`(C43 の段階の数も)と一致することを要求する。
  負の検体 `StatementsWrong.lean`(`specMistranslations`: `∧` と `∨` を取り違えた `Wrong.specLogic`、含意の向きを反転した `Wrong.specCmp`、Bool の値を `= false` に
  写した `Wrong.specVar`、`if` の分岐を入れ替えた `Wrong.specIfBool`、`∀` を `∃` にした `Wrong.specForall`、命題の `let` の束縛を取り違えた `Wrong.specLetProp`、
  ガードを否定した `Wrong.specMatch`、`↔` を `→` にした `Wrong.specIffProp`、命題のガードの `∃` を `∀` にした `Wrong.specGuardProp`、腕の束縛が後続の腕に
  漏れた形の `Wrong.specMatchShadow`。どれも正しい形と意味の異なる命題)は型検査を通り、接続検査 `conn_wrong_*` の 10 行だけが失敗する(対照 `conn_*_ok` は
  成功)。
- 文書との照合(C47): [architecture.md](architecture.md)「一般定理」の表の第 1 列に挙げた定理名がすべて公理監査の `audit ok:` に現れること、上の 3 つの
  コマンドがこの文書に記載されていることを `naru_test semantics` が照合する(文書に挙げた定理の欠落・改名は FAIL)。
- Surface AST の意味論と適格性(C48、[architecture.md](architecture.md)「Surface AST の意味論と適格性」): `lake build NaruSem` が `Surf.wtR` / `Surf.wtS` /
  `Surf.eval` / `Surf.Sem` の定義と一般定理(`Surf.eval_total` / `Surf.Eval_unique` / `Surf.Sem_exists` / `Surf.Sem_unique`、`Surf.eval_mono` / `Surf.Sem_not_nat`)、
  検体(`SurfaceExamples.lean`)を kernel に検査させ、公理監査に載せる(`requiredTheorems` に含む)。`naru_test semantics` は検体 `tests/accept/sem_core.naru` の
  各宣言(`c39Decls`)について、実際の構文解析の出力(`Naru.compileFiles` の `Checked.mods`)を `NaruSem.Surf.Quote.ofDeclAst?` で最小の fn / spec 宣言の包装
  `Surf.Decl`(種別・名前・位置・仮引数・戻り型・本体)に写し(対象外の構文があれば FAIL)、宣言の適格性 `Surf.wtDecl`(仮引数と戻り型の注釈が Nat / Bool、
  runtime は本体が戻り型の型、spec は戻り型の注釈が無く本体が論理の位置の型)の結果の phase が一覧と、本体の型が Core の `wtR` / `wtS` の結果と一致することを
  確かめ、宣言と本体を Lean の項として引用した `.lake/naru/test/semantics/SurfaceScope.lean`(モジュール `SurfaceScope`。`Scope` を import する)を `lean` で検査する:
  本体の適格性 `wta_f : Surf.wtR actx_f ast_f = some t`(spec は `Surf.wtS` と `forma_f`)と宣言の適格性 `wtd_f : Surf.wtDecl decl_f = some (.runtime ctx t)`(spec は `.spec ctx τ`)
  を `decide` で、引用した宣言の埋め込み `Decl.toAst` が構文解析の出力と `==` で一致することを `run_cmd NaruSem.Surf.Quote.checkDecls` の再構文解析で照合する
  (誤った変換結果に合わせて期待側を変えない)。対象外の構文(呼出し・Option のパターン・再帰)を含む `tests/accept/guard_shadow.naru` の宣言が `ofAst?` で
  `none` になることも確かめる。検体を足したら `c39Decls` に足す(AST と Core の両方を検査する)。
- Surface AST → Core → 生成 Lean(runtime。C49 / C51 / C52、[architecture.md](architecture.md)「Surface AST → Core の対応」): `lake build NaruSem` が変換
  `Surf.lower`(`Lower.lean`)と一般定理 `Surf.lower_sound`(系 `Surf.lower_total` / `Surf.lower_wt` / `Surf.lower_eval`)、C40 / C41 との合成 `Surf.preserve_nat` /
  `Surf.preserve_bool`、接続検査の健全性 `Surf.check_sound_nat` / `Surf.check_sound_bool`、検体(`LowerExamples.lean`: 各構文の変換の形、対象外は変換されない、
  意味の異なる適格な Core は変換結果でない)を kernel に検査させ、公理監査に載せる(`requiredTheorems` に含む)。`naru_test semantics` は各 runtime 宣言
  (`c40Decls` + `c41Decls`)について、ドライバで `Surf.lower` の結果が実際の Core と `==` で一致することを確かめた上で、`SurfaceScope.lean` に
  `low_f : Surf.lower actx_f ast_f = some core_f := rfl`(kernel の定義的等しさ。`core_f` は `Scope` の実際の Core の引用)を置いて検査し、`ModelCheck.lean`
  (`SurfaceScope` を import)に一般定理の量化の形(`Surf.lower_sound`: 任意の文脈・適格な AST・型で変換が定まり適格で任意の環境で意味が一致、
  `Surf.preserve_nat`)と合成 `apres_f : ∀ args, Surf.eval (Env.ofList …) ast_f = some (.nat (Model.Sem.Core.f args))`(`Surf.check_sound_nat` / `_bool` が
  `wta_f`・`low_f`・`conn_f` から導く)を置いて `conn_f` / `pres_f` と一緒に `#audit_axioms` で監査する(全部が `audit ok:` に現れることを要求)。
  負の検体 `SurfaceWrong.lean`(`coreMistranslations`: 実際の Core の **値** から作る — 最外の `||` を `&&` にした `WrongCore.logic`(式全体で入れ替えると
  `a || b` と同値になるので最外だけ)、2 つ目の `let_` を `y` に改名した `WrongCore.letShadow`、ガードを否定した `WrongCore.matchNat`)は、ドライバが元の Core と
  異なり同じ文脈で適格(`wtR` が同じ型)で正しい AST の変換と異なり、AST の意味と食い違う具体環境(`witnessEnvs`: Nat は 0〜4、Bool は両方)があることを確かめて
  から、Lean で適格性 `wt_f_wrong`(`decide`)と意味の食い違い `diff_f_wrong : Surf.eval (Env.ofList …) ast_f ≠ eval (Env.ofList …) WrongCore.f`(`decide`)が成功し、
  対応 `conn_wrong_f : Surf.lower actx_f ast_f = some WrongCore.f := rfl` の 3 行だけが失敗する(対照 `conn_f_ok` は成功。構文 / import の誤りでない)ことを
  確かめる。`SurfaceScope.lean` は加えて各宣言の本体の文脈が仮引数のもの(`Surf.declCtx?` / `declSCtx?`)であること(`actx_f_decl`、`rfl`)も検査する。
- Surface AST → Core → 生成 Lean(spec。C50 / C51 / C52、[architecture.md](architecture.md)「Surface AST → Core の対応」): `lake build NaruSem` が変換
  `Surf.lowerS`(`LowerSpec.lean`)と一般定理 `Surf.lowerS_sound`(系 `Surf.lowerS_total` / `Surf.lowerS_wt` / `Surf.lowerS_Sem`)、双方向の同値 `Surf.Sem_lowerS_iff`、
  命題の区分の一致 `Surf.proppyS_lowerS` / `Surf.proppyS_lower`、C42 / C43 との合成 `Surf.preserve_prop`、接続検査の健全性 `Surf.check_sound_prop`、検体
  (`LowerSpecExamples.lean`: 量化・命題の `let`・注釈の無い `==`・命題のガード付き `match` の変換の形、対象外は変換されない、`forall` / `exists` の取り違えと命題の
  `let` の束縛の取り違えは変換結果でない)を kernel に検査させ、公理監査に載せる(`requiredTheorems` に含む)。`naru_test semantics` は各 spec 宣言
  (`c42Decls` + `c43Decls`)について、ドライバで `Surf.lowerS` の結果が実際の Core と `==` で一致することを確かめた上で、`SurfaceScope.lean` に
  `lows_f : Surf.lowerS actx_f ast_f = some core_f := rfl` を置いて検査し、`StatementsCheck.lean`(`SurfaceScope` を import)に一般定理の量化の形(`Surf.lowerS_sound`、
  `Surf.Sem_lowerS_iff`: 任意の命題について双方向、`Surf.preserve_prop`)と合成 `apres_f : ∀ args, Surf.Sem (SEnv.ofList …) ast_f (Statements.Sem.Core.f args)`
  (`Surf.check_sound_prop` が `wta_f`・`forma_f`・`lows_f`・`conn_f` から導く)を置いて `conn_f` / `stage_f` / `pres_f` と一緒に `#audit_axioms` で監査する。
  負の検体 `SurfaceSpecWrong.lean`(`specCoreMistranslations`: 実際の Core の値から `∀` を `∃` にした `WrongCore.specForall`、`∃` を `∀` にした `WrongCore.specExists`、
  命題の `let` の末尾の束縛を取り違えた `WrongCore.specLetProp`、ガードを否定した `WrongCore.specMatch`)は、ドライバが元の Core と異なり同じ文脈で適格(`wtS` が同じ型)で
  正しい AST の変換と異なることを確かめてから、Lean で適格性 `wt_f_wrong`(`decide`)と意味の食い違い `diff_f_wrong : ¬ (denoteP ρ WrongCore.f ↔ denoteP ρ core_f)`
  (食い違う具体環境 `ρ` での読みの非同値。命題の意味は `decide` で評価できないので、`show` で明示した命題と証明を kernel が検査する)が成功し、対応
  `conn_wrong_f : Surf.lowerS actx_f ast_f = some WrongCore.f := rfl` の 4 行だけが失敗する(対照 `conn_f_ok` は成功。構文 / import の誤りでない)ことを確かめる。
- 関数・input の宣言群(C54、[architecture.md](architecture.md)「関数・input の保存対象の意味論」): `lake build NaruSem` が Core の呼出しを含む意味論と適格性
  (`Call.lean`: `Call.wtR` / `Call.wtS` / `Call.eval` / `Call.Sem`、宣言群 `Call.Prog` / `Call.wtProg` / `Call.interp`)、一般定理(`CallTotality.lean`: `Call.eval_total` /
  `Call.Eval_unique` / `Call.evalArgs_total` / `Call.Sem_exists` / `Call.Sem_unique`、宣言群の `Call.interp_respects` / `interp_defined` / `fn_total` / `spec_defined` /
  `spec_meaning`)、Surface AST の呼出しを含む意味論と適格性(`SurfaceCall.lean`: `Surf.Call.wtR` / `wtS` / `eval` / `Sem`、宣言表 `Table` と実引数の並べ替え `arrange`、
  宣言群 `Surf.Call.wtProg` / `interp`)とその一般定理(`SurfaceCallTotality.lean`: `Surf.Call.eval_total` / `Eval_unique` / `evalArgs_total` / `Sem_exists` /
  `Sem_unique`、名前付き引数の並べ替えの可換性 `arrange_map`、評価の単調性 `eval_mono` と `Sem_not_nat`、宣言群の `Surf.Call.interp_respects` / `interp_defined` /
  `fn_total` / `spec_defined` / `spec_meaning`)、検体(`CallExamples.lean`)を kernel に検査させ、公理監査に載せる(`requiredTheorems` に含む)。`naru_test semantics` は検体
  `tests/units/accept/sem_calls/`(input 4・fn 17・spec 宣言 10。`NaruTest/Semantics.lean` の `c54Decls`)の fn / input / spec 宣言すべてを、実際の Core(`Call.Quote.declsOf`)と
  実際の構文解析の出力(`Surf.Call.Quote.declsOf`)の宣言群として依存順(呼出し先が前。ドライバが Core の呼出しの鍵から並べる `dependencyOrder`)に引用した
  `.lake/naru/test/semantics/CallScope.lean`(モジュール `CallScope`)/ `SurfaceCallScope.lean`(モジュール `SurfaceCallScope`)を `lean` で検査する: 宣言群の適格性
  `cwt_call : (Call.wtProg SigEnv.empty cprog_call).isSome = true` と各宣言の署名 `csig_f`(`decide`)、実際の Core から作った負の検体(`coreWrongProgs`: 依存順の反転、`callBase` が
  `base` の代わりに `addTo`(違う呼出し先・引数の数)/ spec 宣言 `posBase`(phase)を呼ぶ、`base` が `callBase` を呼ぶ循環、`base` の重複、`seed()` に実引数(input の引数の数)、
  `base` に Bool(引数の型))が `wtProg = none`(`decide`)、input の解釈(`seed() = 41`、`bias(n) = n * 2`、`otherBias(n) = n + 3`、`flag(b) = !b`)の下の宣言群の意味 `Call.interp` の fn の値 14 件
  (`expectedCallValues`: `twoStep(1) = 86` など。`decide`)と、署名に合わない解釈(`seed()` が Bool)では `useInput(1)` が行き詰まる(`none`)こと、引用した宣言群が実際の Core と
  一致し宣言群全体を網羅すること(`run_cmd Call.Quote.checkProg`)、一般定理が実際の宣言群に適用できること(`cΔ_call` / `cresp_call` / `cdef_call`: 署名を守る任意の
  解釈の下で `Call.interp` が署名を守り spec 宣言の意味が定義される。`#audit_axioms` で監査)。Surface 側は `swt_call : Surf.Call.wtProg sprog_call = true`(`decide`)、
  各宣言の署名が Core の署名と一致(ドライバ)、一般定理の適用 `sresp_call` / `sdef_call`(`Surf.Call.interp_respects` / `interp_defined` を `swt_call` に。`#audit_axioms` で監査)、
  実際の AST から作った負の検体(`surfWrongProgs`: 依存順の反転、`addTwo`(未解決の名前)、名前付き引数 `z = a`(無い名前)、名前付きの後の位置引数、`y` の二重指定、
  UFCS の `a.addTwo(b)`)が `wtProg = false`(`decide`)、引用した宣言群が構文解析の出力と一致し全体を網羅すること(`run_cmd Surf.Call.Quote.checkProg`)。
  検体を足したら `c54Decls` にも足す。
- 実生成 Model への接続と宣言群の意味の合成(C55 / C56 / C57 / C58 の runtime 側、[architecture.md](architecture.md)「関数・input の保存対象の意味論」):
  `lake build NaruSem` が呼出しを含む生成 Model の読み(`CallDenote.lean`: `Call.denoteN` / `denoteB` / `denoteArgs`)と一般定理 `Call.denote_sound`(系 `preserve_nat` /
  `preserve_bool` / `denote_sound_self`、`denoteArms_sound`、接続検査の健全性 `check_sound_nat` / `check_sound_bool`)、実生成定数を包む `Call.wrap`(`wrap_respects`)と
  表 `Call.Shape` / `Gen`(`ofGens_respects`)、宣言群の意味と実生成定数の一致 `Call.interp_agree`(系 `fn_value`)、`SubV_of_cover` / `fnConn_of_curried` を kernel に
  検査させ、公理監査に載せる(`requiredTheorems` に含む)。`naru_test semantics` は検体 `tests/units/accept/sem_calls/` を実際の CLI で
  `.lake/naru/test/semantics/gencall/` に生成し、生成 Model `gencall/Model/Sem/Call.lean`(fn は input の引数 `name'` を名前順に先頭に取る)をモジュール
  `Model.Sem.Call` にコンパイルして、検査プログラム `.lake/naru/test/semantics/CallModelCheck.lean`(モジュール `CallModelCheck`。`CallScope` と `Model.Sem.Call` を
  import)を `lean` で検査する: 一般定理の量化の形(`Call.denote_sound`: 任意の署名・式・環境・一致する関数環境、`Call.interp_agree`: 任意の宣言群・input 解釈・
  実生成定数の環境)、実生成宣言の表 `shapes_call` / `gens_call <inputs>`(input は Lean の値 `bias'` / `flag'` / `otherBias'` / `seed'` で量化、fn は生成定数に推移的な input の引数を
  名前順に適用。ドライバの `inputsOf` が backend と同じ規則で求める)から作った `Δgen_call` / `Φgen_call` が表の署名を守ること `Φgen_call_respects`、宣言群の各 fn /
  input の署名が表にあること `cover_call`(`decide`)、各 fn の接続 `conn_f <inputs> : ∀ args, Model.Sem.Call.f <input 引数> args = Call.denoteN Δgen_call (Φgen_call …)
  (Env.ofList …) ccore_f`(`rfl`。`match` は `proofOf` の `cases` の後に `rfl`。`ccore_f` は `CallScope.lean` の実際の Core の引用)と証拠 `evid_f`(`fnConn_of_curried`)、
  宣言群全体の証拠 `cevid_call`、宣言群の意味と実生成定数の一致 `cgen_call`(`interp_agree`)、各 fn の値 `cval_f`(`fn_value`: 任意の input 解釈が `Φgen_call` と input の
  鍵で同じなら、宣言群の意味の fn は型の合う任意の実引数で実生成定数の値)。すべて `#audit_axioms` で監査し、ドライバは全部が `audit ok:` に現れ、fn の数が
  `c54Decls` の fn の数と一致することを要求する。負の検体 `CallModelWrong.lean`(`callMistranslations`: 実生成文字列から `twoStep` が同じ署名の `base` を `callBase` の
  代わりに呼ぶ `Wrong.twoStep`、`callNamed` の名前付き実引数を仮引数の順に渡す `Wrong.callNamed`、`ufcs` の UFCS の受け手を 2 番目に渡す `Wrong.ufcs`、`useInputArg` の
  `bias(seed())` が `x` を読む input の誤配線 `Wrong.useInputArg`、同型inputの交換 `Wrong.sharedInputs`)は型検査を通り、接続検査 `conn_wrong_*` の 5 行だけが失敗する(対照 `conn_*_ok` は成功)。
  C57 の証拠の欠落・不一致も同じ入口で検査する。`CallEvidenceCheck.lean` は正しい `evid_base` と全宣言の証拠による保存の合成を成功させ、
  `base` を抜いて呼出し側 `callBase` を残した証拠束、本体の定数を変えた同型の Core、その意味の差を kernel に検査させる。対照の 7 定理を公理監査する。
  `CallEvidenceWrong.lean` はその対照に、同じ署名の `callBase` の証拠を `base` に使う、本体変更前の証拠を変更後の Core に使う、
  呼出し先 `base` の証拠を抜いた束を `Call.interp_agree` に渡す、という 3 件だけを加える。その 3 行だけが型の不一致で失敗し、構文・import の誤りや
  未証明の穴による失敗が無いことを要求する。これらは隔離検体であり、現在のソース・生成物・正しい証拠を変更しない。
  spec の `CallStatementsReadCheck.lean` は10宣言の prefix 接続 `read_*` / `spevid_*` と全体の `spevid_call` / `cprops_call` を kernel 検査・公理監査する。
  C57 の spec 証拠の検査は `CallSpecEvidenceCheck.lean` / `CallSpecEvidenceWrong.lean`。正しい対照の8定理は、全 fn/spec の証拠による命題同値の合成、
  同型で意味が異なる変更後の `posBase` の Core、および呼出し先 `posBase` の証拠だけを含まない部分証拠を検査する。
  部分証拠は `specCallSpec` からの suffix に対し、元の prefix 署名を保持する。その署名に `posBase` があり、実際の呼出し側が残ることも検査する。
  署名で呼出し先を知っていてもその接続は証明していないため、この suffix の証拠だけで全体の `Call.interp_prop_agree` は適用できない。
  負のファイルは対照に、別宣言 `specCallSpec` の証拠の流用、変更前の証拠の変更後 Core への流用、部分証拠による全体の合成の3件だけを加える。
  その3行だけの型不一致・構文/import/未証明の穴のエラーなしを要求する。現在の入力・実生成物・正しい証拠は保持する。
  `CallStatementsReadWrong.lean` は論理の取り違えに加えて、spec 呼出し先・名前付き引数・UFCS の受け手・spec→runtime→input の解釈の誤配線を実生成文字列から作る。
  型が合う6件の隔離宣言と任意 input/仮引数の正しい対照は通り、接続定理の6行だけが失敗する。各 `different_*` の閉じた非同値反例も kernel 検査・公理監査し、6件の監査の欠落は失敗にする。
  呼出しを含む Surface AST からの保存とその負検体(C55〜C58 の残り)は未完了。input のみの別モジュールからの接続は検査する。

C56 の任意解釈から Lean への写しは `CallInputs.lean` の `exists_fn` / `input_representable` / `inputs_representable`。`lake build NaruSem` と同じ semantics / regression 入口で公理監査し、必須監査一覧からの欠落を失敗にする。型外で値を返す解釈の対照 `illtyped_total` / `illtyped_not_equal` も kernel 検査する。`CallModelCheck.lean` の `irepr_seed` / `irepr_bias` / `irepr_otherBias` / `irepr_flag` と `ireprs_call` は現在の引用 Core の input の鍵・署名と、任意の `RespectsInputs` 解釈に対する全引数の対応を検査する。これら5証拠の監査欠落も失敗とする。型内の一致から関数全体の等式 `SameInputs` は導かない。`InputsAgree` を前提とする一般合成 `interp_inputs_agree` / `interpFrom_inputs_agree` / `fn_value_inputs` と `interp_prop_inputs_agree` / `interpFrom_prop_inputs_agree` を同じ入口から kernel 検査・公理監査する。`SameInputs.agree` は従来 API を保つ系。`inputs_generated_agree` が任意の元解釈の全 input を同時に表現し、現在の生成環境の lookup 証拠から型内一致を導く。型内一致が成立しても関数全体の等式は成立しない対照 `typed_only_agree` / `typed_only_not_same` も必須監査対象。`CallModelCheck.lean` の `cinputs_generated` と `cgen_inputs_call`、`CallStatementsReadCheck.lean` の `cprops_inputs_call` / `cinputs_connect` は、現在の実4inputの抽出値を実生成17fn/10specへ渡し、任意の元解釈で値対応と双方向の命題同値を同時に検査する。これら4証拠の監査欠落を失敗にする。inputのみの別モジュール `Sem.Inputs` からの接続も検査する。呼出しを含むSurface保存はC55/C57の未完了範囲である。

同型inputの検体(C56)では `bias` と `otherBias` がともに Nat → Nat。`inputPair` が二つを区別し、`sharedInputs` は `inputPair` と `useInputArg` で共有する `bias` / `seed` を重複せず引き回す。`specSharedInputs` はその二段のruntime呼出しに加えて同じ二つのinputを直接参照する。三宣言の推移input列を独立した期待列 `[bias, otherBias, seed]` と照合し、任意の解釈・引数での実生成接続と全宣言群の合成を kernel 検査・公理監査する。`CallModelWrong` は片方のcalleeに渡す二つの解釈だけを交換し、`CallStatementsReadWrong` は spec→runtime の受け渡しで交換する。どちらも型は合うが接続行だけで失敗し、正しい対照は成功する。閉じた差の証拠 `different_sharedInputs` / `different_specSharedInputs` も kernel 検査・監査し、欠落は失敗とする。具体反例は任意解釈での接続の代用にしない。

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

呼出しを含む spec 式の検査(C55 の進展)も `lake exe naru_test semantics` と `lake exe naru_test regression` から実行する。
`CallDenoteProp.lean` の `Call.Sem_denote` / `Sem_denoteP` / `check_sound_prop` と命題環境の一致・署名包含の補題を `NaruSem.lean` で公理監査し、`requiredTheorems` が欠落を失敗にする。
実際の CLI が生成した `gencall/Statements/Sem/Call.lean` を Lean モジュールとしてビルドし、`CallStatementsReadCheck.lean` が現在の引用 Core と10個の実生成 spec の読みの接続 `read_*` を任意の input 解釈・仮引数について検査・監査する。
`CallStatementsReadWrong.lean` の6件は、`specCallSpec` の `∧`→`∨`、`specTwoStep` の spec 呼出し先の置換、`specNamed` の名前付き引数の交換、`specUfcs` の受け手の交換、`specBoolCall` の runtime 経由の input 解釈の変更、`specSharedInputs` の同型inputの交換。型検査・正しい対照・非同値反例 `different_*` の kernel 検査と公理監査は成功し、同じ正しい Core への接続定理の6行だけで失敗する。反例の引数は [architecture.md](architecture.md) に記載する。宣言数・6件の監査・期待するエラー行の欠落は失敗にする。
`CallComposeProp.lean` の `interp_prop_agree` / `interpFrom_prop_agree` / `curried_wrapP` / `specConn_of_curried` も一般定理の必須監査対象。各 spec の前の署名 `Δprefix_*` で `read_*` を検査し、`spevid_*` と全宣言の `spevid_call`、任意の同じ input 解釈で独立宣言群と実生成命題環境が同値となる `cprops_call` を検査・監査する。10 spec の接続・合成証拠の欠落も失敗にする。呼出しを含む Surface 保存は未完了。input のみの別モジュールと、別モジュールのfn/spec呼出し先への実生成接続は検査する。

`tests/units/accept/sem_calls/` は `src/Sem/Inputs.naru` に4 input、`src/Sem/Callees.naru` に基礎の3 fn(`base`・`zero`・`addTo`)と1 spec(`posBase`)、`src/Sem/Call.naru` に呼出し側を置く。runtime→runtime・spec→runtime・spec→spec の別モジュール呼出し、修飾参照・位置/名前付き引数・UFCS・ゼロ引数を実生成 `Model.Sem.Callees` / `Statements.Sem.Callees` と呼出し側へ接続する。単一ファイルの受理例 `tests/accept/sem_call.naru` も維持する。`Call.Quote.checkProg` / `Surf.Call.Quote.checkProg` は同じ3ファイルを再コンパイルし、引用の識別・署名・本体と全31宣言の網羅を照合する。検体の宣言一覧を安定した依存順へ並べ、適格性をkernel検査する。`checkOmission` はinput元のModel/Statements不在、生成宣言の網羅、集約importと全依存の解決を検査する。任意解釈の接続・同型input交換のruntime/spec負検体はこの複数ファイル単位でkernel検査・公理監査する。モジュール全体の保存やSurface/Core宣言群の意味合成はこの接続では保証しない。

別モジュール呼出しの接続も同じ `semantics` / `regression` 入口で再検査する。実際のCoreの呼出し辺と生成Model/Statementsのimportを照合し、calleeの生成モジュールを先にLeanとしてビルドする。全17fn/10specの任意引数の接続・宣言群の合成証拠、公理監査、別宣言/古いCore/callee証拠欠落のruntime/spec各3件、Model5件/spec6件の型が合う誤出力検査は維持する。Surface/Core宣言群の意味合成とspec側のSurface保存は未完了である。

同じ `lake exe naru_test semantics` / `lake exe naru_test regression` は呼出しを含む runtime の AST → Core の構造的対応も検査する。
`SurfaceCallLowerCheck.lean` は再構文解析・再コンパイルで一致を確認した31宣言から、全17 fnの実際の包装・仮引数・本体・prefix宣言表を取る。
独立した `Surf.Call.lower` と実Coreの一致 `slow_* := rfl`、適格性・包装・一般定理からの型保存の計153証拠を kernel 検査・公理監査し、必要な宣言と監査の欠落を失敗にする。
`SurfaceCallLowerWrong.lean` の5件は別callee・名前付き引数の交換・UFCS受け手の交換・同型inputの交換・matchガードの否定。
現在のCoreから作った各検体は同じCore型を持ち、正しい対照が成功し、同じ正しいASTとの変換の一致の5行だけで失敗することを要求する。
この構造的一致は一般意味保存の代用ではない。runtimeの一般定理の適用も検査し、spec側のloweringの一般保存と宣言群の合成は未完了である。

呼出しの局所的な合成補題も同じ入口で検査する。`SurfaceCallLower.lean` の
`allSome_some` / `evalArgs_allSome` / `arrange_eval` / `wtArgs_of_map` / `arrange_wt` /
`lowerCall_wt` / `lowerCall_eval` / `lower_call_eval` / `lower_ufcs_eval` と、
`SurfaceCallLowerExamples.lean` の5検体を `NaruSem.lean` で公理監査し、`requiredTheorems` が全14件の欠落を失敗にする。
名前付き実引数の順序・UFCS受け手・ゼロ引数の引数評価・任意環境でのcallee不在や失敗を扱う。
局所補題では子式の評価・型の対応を合成前提とする。全式のruntime評価保存は以下の一般定理で導く。


ブロックの束縛列の合成も `lake exe naru_test semantics` (および `regression`) から検査する。
`Surf.Call.wtR_mkLets` / `eval_mkLets` / `lowerStmts_cons_eval` / `lower_block_eval` と
`block_shadow` / `stmt_shadow` / `binds_shadow_wt` / `binds_missing_call` / `binds_wrong_annotation` /
`binds_failed_call` / `binds_call_shadow` の全11件を公理監査と `requiredTheorems` の照合に追加している。
NatからBoolへの同名束縛、注釈の型不一致、calleeの不在・失敗・任意の成功値の対照をkernelが検査する。
任意の関数・input環境を保持し、列や末尾式の対応を前提としてブロックへ合成する段階である。
全式のruntime評価保存は以下の一般定理で検査する。specのloweringの一般保存とSurface/Core宣言群の合成は未完了である。

matchの腕の局所合成も同じ `lake exe naru_test semantics` / `regression` から検査する。
`Surf.Call.exhaustiveFrom_lowerArm` / `exhaustiveFrom_lowerArms` / `lowerArm_eval` /
`lowerArms_eval` / `lower_match_eval` / `lower_match_wt` と、
`guard_call` / `guard_arms_eval` / `match_call_guard` / `bool_arms_exhaustive` /
`guard_only_not_exhaustive` / `match_call_guard_wt` / `guard_false_restores_outer` /
`guard_true_shadows_outer` / `guard_false_wrong_shadow` / `guard_missing_stops` /
`guard_failure_stops` / `guard_nonbool_stops` / `guard_mismatch_skips` の全19件を公理監査し、
`requiredTheorems` が欠落を失敗にする。`ArmsEval` は腕の順序と対応先を保持した継続の証拠である。
任意のinput解釈でガードのtrue/false、callee不在・失敗・署名外のNat値、
パターン不一致と外側の値/命題の隠蔽・復元を扱い、Bool/Natの網羅性の対照と型の合成も検査する。
falseガードの後に束縛を漏らしてscrutineeを返す結果との不一致を証明する。具体的な誤変換Coreの型検査ではない。
署名外の環境の対照は失敗の保持の検査であり、適格な宣言群の一般保証ではない。
局所補題で要求する子式の対応は以下のruntimeの帰納定理で導く。specのloweringの完成は含めない。

runtime式のloweringの全域性と型保存は `SurfaceCallLowerSound.lean` の一般定理を同じ入口で検査する。
`Surf.Call.lower_typed` / `lower_total` / `lower_wt` と相互帰納の補題は公理監査と欠落検査の対象となる。
評価の相互帰納定理 `lower_eval_all` と、その系 `lower_eval` / `lowerStmts_eval` / `lowerArgs_eval` /
`lowerArms_eval_wt` / `lowerArm_eval_wt` も同じ監査と必須定理の欠落検査に含む。
`SurfaceCallLowerCheck.lean` は現在の全17 fnについて、包装・仮引数・本体・ASTの適格性・実Coreとの一致に加え、
一般定理から得た実Coreの型保存 `sctyped_*` と評価保存 `seval_*` を検査する(17 × 9 = 153証拠)。
型が合う別callee・引数交換・UFCS・input誤配線・ガード否定の5負検体は維持し、型保存だけでは意味の誤りを検出できないことを区別する。
評価の保存は `Surf.Call.lower_eval` から独立に検査する。任意の `Φ` と `ρ` に対し、`sctx_* = ρ.ctx` と `Φ.Respects stable_*.Δ` を前提に、同じ `Φ` の下で実ASTと実Coreの評価が等しいことを示す。子式の対応を仮定せず、全式の帰納定理を適用する。一般定理と全17件の `seval_*` の監査欠落は失敗となる。specのloweringの一般保存と双方向同値、Surface/Core宣言群の意味合成、Surfaceから実生成Leanまでの合成は未完了として扱う。

別々の関数/input環境へのruntime合成も同じ入口から検査する。`Call.eval_agree` と
`Surf.Call.lower_eval_agree` / `lower_denote_sound` を公理監査と必須定理の欠落検査に含め、
現在全17 fnの `seval_agree_*` / `sread_*` を生成して任意の対応環境と拡張署名についてkernel検査する。
前提は `FEnv.Agree` による署名内の呼出し結果の一致であり、環境全体の等式ではない。
`typed_env_agree` / `typed_env_preserve` / `typed_env_outside_diff` は型内だけで一致する二つのinput閉包の対照で、
任意のNat引数の評価保存とBoolの型外引数での評価不一致を検査する。
全6定理と各fnの2証拠の監査欠落を失敗にする。宣言群から環境対応を導く証明と実生成定数へのSurface宣言群合成は未完了である。

呼出しを含む spec の独立変換 `Surf.Call.lowerS` は `SurfaceCallLowerSpec.lean` にある。
現在の10 specのAST・prefix宣言表・包装・仮引数・本体と実Coreの一致を `SurfaceCallLowerSpecCheck.lean` の90証拠でkernel検査・公理監査する。
論理の位置はspec変換、値の位置と実引数はruntime変換を使い、命題のlet・Bool値・量化・ガードを区別する。
`lowerCallS_eq` / `lowerCallS_spec_wt` / `lowerCallS_spec_Sem` / `lowerCallS_value_Sem` は、解決・署名と引数の型または評価の対応から呼出しの形・命題型・意味を局所的に合成する。
`SurfaceCallLowerSpecWrong.lean` の5件はspec呼出し先・名前付き引数・UFCS受け手・同型input・命題letの型が合う誤対応を作り、正しい対照を成功させ、一致の5行だけで失敗させる。
`SurfaceCallLowerSpecSound.lean` の `Surf.Call.lowerS_typed` は任意の宣言表 `T`・文脈 `Γ`・適格なspec式 `e`・型 `τ` に対し、`wtS T Γ e = some τ` から変換先の存在とCoreの同じ型を示す。
`lowerS_typed_all` は式・let列・腕列・腕を同時に帰納し、値の位置と実引数にはruntimeの型保存を使う。`lowerS_total` / `lowerS_wt` はその系である。
命題専用の構文区分も `proppyS_lowerS` で同じ文脈のAST/Core間で保存する。`proppyS_lowerS_view` は名前の可視性を保ち、命題束縛を増やさない `ScopeView Γ Γ₀` を前提に構文走査文脈へ拡張する。
`SurfaceCallProppy.lean` のruntime命題除外補題を使い、Propを実行可能なBoolへ戻さない。これらの公開補題も必須監査に含める。
現在10宣言の具体的なAST型 `sswtype_*` と実Core一致 `sslower_*` から一般定理を適用した `ssctyped_*` を検査・公理監査し、90証拠と一般定理の欠落を拒否する。
この型保存と変換の存在はspecの双方向同値を保証しない。一般のspec loweringの双方向同値、Surface/Core宣言群からの環境対応、Surface宣言群から実生成Leanまでの合成は未完了である。

`SurfaceCallLowerSpecSem.lean` の `Surf.Call.SpecLetsBridge.sem_iff` / `lowerStmtsS_sem_iff` は、呼出しspecの値と命題のlet列をCoreの入れ子のletへ合成する局所証明である。
`SpecSemEquiv.iff` は同値な意味の証人を移し、`SpecLetsBridge.lower` は証明書の束縛列と独立lowering出力の一致を示す。5補題と境界検体は公理監査と必須一覧の欠落検査に含め、`lake exe naru_test semantics` と同じ回帰入口から実行する。
子spec式と末尾式の双方向の意味対応を明示した証明書を前提に、値の束縛にはruntimeの一般評価保存を使い、命題の同値には命題外延性を使って束縛環境を揃える。
同じ名前の値・命題を再束縛する場合も扱う。この局所合成は子式の対応を全spec式の帰納法から導く一般定理ではなく、Surface/Core宣言群からの環境対応と実生成LeanへのSurface合成も未完了である。

`lowerS_block_sem_iff` は末尾の型と独立変換の一致も照合して、実際の `lowerS` が出力したブロック全体へこの局所合成を適用する。子式の双方向対応は引き続き証明書の前提である。

`SurfaceCallLowerSpecSemExamples.lean` の11検体は、ゼロ引数のBool inputを値として `q` へ束縛し、spec呼出しを命題として同じ `q` へ再束縛する。任意解釈の双方向対応と、spec解釈の存在を明示した意味の証人を検査する。閉じたinput=false / spec=Trueの正対照に対し、命題の子式を否定したCoreは同じ `.prop` 型で適格だが意味が `¬ True` となることと、正しいSurfaceの意味を保存しないことをkernelが検査する。5一般補題・11検体の監査欠落は失敗になる。
