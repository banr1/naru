# 知見

<!-- 周回を跨いで役に立つ事実だけを書く: ビルド/テストの実行方法、ツールの制限と回避策、環境の癖。
     「次にやること」は書かない(それは周回記録の「申し送り」)。古くなった行は消す。50 行以内に保つ。
     周回のエージェントは途中で替わりうる。特定のハーネスのツール名ではなく、コマンドと事実で書く。 -->

## ビルドと実行(リポジトリのルートで)
- `lake build` — naru コンパイラ(`compiler/`、lean_lib `Naru` + lean_exe `naru`)。依存なし(mathlib 不要)。冷えた状態で約 40 秒、差分なら数秒。
- `lake build NaruStd` — Model 用 stdlib(Lean 側、`stdlib/Model`。変えたら先にこれ)。`lake build Model` — 生成 Model(`generated/`。C6 の検証。数秒)。
- `lake exe naru compile` — `dsl/**/*.naru` を検査し `generated/Model.lean` + `generated/Model/**.lean` を作り直す(C1 の検証)。
  `lake exe naru compile <files...>` は検査だけ(`--out <dir>` を付けるとそこに出力)。診断は stderr に `file:line:col: error[E0xx]: msg`、exit 1。
- `lake exe naru check-reject <file.naru> <Exxx>` — 反例が compile で拒否されかつ診断に `Exxx` を含めば PASS で exit 0(台帳の `cycle N:` 出典に使える形)。検査スクリプトは Lean で書く前提なので、シェルのラッパーは置かない。
- 回帰の一式(コードを変えた周回は必ず通し、met 条件の `cycle N:` を取り直す):
  `lake build && lake exe naru compile tests/accept/smoke.naru && lake exe naru compile tests/accept/backend.naru && lake exe naru check-reject tests/reject/phase_leak.naru E001 && lake exe naru check-reject tests/reject/phase_leak_method.naru E001 && lake exe naru check-reject tests/reject/choose.naru E003 && lake exe naru check-reject tests/reject/order_loss.naru E004 && lake exe naru check-reject tests/reject/missing_capability.naru E005 && lake exe naru check-reject tests/reject/non_total.naru E002 && lake exe naru check-reject tests/reject/type_path_escape.naru E011 && lake exe naru check-reject tests/reject/match_shape.naru E018 && lake exe naru check-reject tests/reject/nested_recursion.naru E019`
  (`type_path_escape` / `match_shape` / `nested_recursion` は条件ではなく回帰用: 型検査を黙らせる抜け穴・網羅性の穴・Lean の deriving が落ちる再帰型が再び通らないことを見る)
- 生成コードの回帰(backend を変えたら): `lake exe naru compile --out /tmp/naru-gen tests/accept/backend.naru && lake env lean /tmp/naru-gen/Model/Gen/All.lean`(exit 0。smoke も同様に `Model/Accept/Smoke.lean`)。`lake env lean <生成ファイル>` で単独に型検査できるのは、他の生成モジュールを import しない 1 モジュールだけ(`--out /tmp/…` の複数モジュールは import が解決できない)。複数モジュール(`dsl/` の移植)の型検査は `lake exe naru compile && lake build Model`。
- C1 の検証: `lake exe naru compile` を 2 回、`find generated -type f | sort | xargs shasum -a 256` を比較、各ファイルの `head -5`。C6: `lake build Model && grep -rwE 'noncomputable|unsafe|axiom|sorry|partial' generated/Model`(0 件)。
- `tests/accept/smoke.naru` は MVP 構文と stdlib 表の受理例、`tests/accept/backend.naru` は backend の網羅例(input・Result・Table・guard・fuel・相互再帰・予約語・周回 5 の sum / fdiv / toNat)。パーサ・型検査・backend を変えたら exit 0 と生成コードの型検査を確かめる。文法・stdlib 表・backend の変換規則の正本は `compiler/SYNTAX.md`(構文・メソッド・変換を増やしたら同時に直す)。
- golden test の予行(Objects 層、周回 5): `lake env lean tests/golden/objects_generated.lean`(生成側、ルートで)と `cd verified-consensus && lake env lean ../tests/golden/objects_handwritten.lean`(手書き側)が同じ順で同じ値を出す(46 件)。C10 の golden test(同一 Lean プログラム)はまだ無い。
- zsh: for ループの `set -- $p` は文字列を分割しない(`$=p`)。`${PIPESTATUS[0]}` は空で `${pipestatus[1]}`(小文字・1 始まり)を使う。

## コンパイラの事実
- 段: 字句解析 → 構文解析 → 名前解決・phase 検査(`Resolve.lean`: E001, E011〜E013)→ 型・capability 検査 + Core IR への elaboration(`Typecheck.lean`: E003〜E006, E014〜E016。`infer` が `(型 × Core.Expr)` を返す)→ 停止性検査(`Totality.lean`: E002。受理した再帰の測度を backend に渡す)→ Model backend(`Backend/Model.lean`: E017)。前の段に誤りがあれば次の段には進まない。
- Core IR(`Core.lean`)は型付き・名前解決済み・糖衣展開済み。`TyV` はここで定義(型別名は展開済み、メタ変数は Core には残らない: 残れば E014)。
- E002 が受理する再帰は 2 形だけ: match の構築子パターンで取り出した部分項への構造的再帰と、`n ≥ k` が分かる分岐内で Nat 仮引数(または match の bind 別名)を `n - k` で渡す fuel。下限は `if` の条件(`==` `!=` `<` `<=` `>` `>=` とリテラル、`!`、`&&` の then、`||` の else、`else if` の連鎖)と、`match n` のガード無しリテラル腕(0 から連続して覆った値の次)と腕のガードから取る。サイクル(相互再帰)は全辺で同じ測度が厳密に減ること。`let` 経由・record の欄・lambda 内・Int・関数値の受け渡し・辞書式の測度は E002(保守的)。lambda の中から再帰しない fn を呼ぶのは自由(`rows.map(|r| erase(r))`)。
- backend が Lean に落とす形は SYNTAX.md「Core IR と Model backend」。fuel は `if _h' : c` + `termination_by n` + `decreasing_by all_goals (try simp_all) <;> (first | omega | decreasing_tactic)`、`Nat` の match は `match _hm' : n with` で bind 腕は `_ + m` + `let k := n`、ガードは Option の match、構造的は `termination_by structural p`。生成コードの Lean 組み込み名は完全修飾、局所名・欄名は `«»`。これらは Lean 4.34.1 で実測済み(`tests/accept/backend.naru` が回帰)。
- 名前解決はコンパイル単位(渡された全ファイル)を 1 つの大域表で行う。`import` は受理するだけで意味を持たない(backend はモジュール間の参照から `import` を計算し、循環は E017)。同名の fn はファイルが違っても E012(移植では `named…` のように改名して逃げている)。欄名は大域表に入らないので fn と同名でよい(`v.slot` は欄、`b.slot()` は UFCS)。
- 大文字始まりの経路は大域名(`Phase.Tick`、`Set.empty`)、小文字始まりは値と欄の連鎖。局所名は小文字始まりのみ(大文字は E010)。`x.f(args)` は `f` がユーザ宣言の大域名なら `f(x, args)`(UFCS)、無ければ stdlib メソッド(`Typecheck.lean` の表)。
- 組み込み: primitive 型名、`Some` `None` `Ok` `Err`、自由関数 `sort` `choose` `pick`(再宣言は E012)。`unknown` 型は診断を出した後にだけ作る、が不変(型の位置の経路は完全一致で解決。崩れると E003 / E004 が素通りする)。
- capability: `eq` は primitive と derive eq の record/enum とその合成、`order` は Nat/Int/String・Option/List/tuple・derive order の record/enum。Set/Table は order を持たない。Set → List は `sort(by = …)` だけ。`Set.sum` / `List.sum` は可換な集約なので Set から直接取れる。backend は `eq` に `DecidableEq` と隠れた `Ord` を、`order` に `Ord` を、常に `Repr` を生成する(Lean の型クラスは露出しない)。再帰 enum(`Block`)への `deriving Ord` も Lean 4.34.1 で通る。
- `Naru.sha256Hex`(`Sha256.lean`)は Lean 実装(core に sha256 は無い)。`shasum -a 256` と一致を確認済み。コンパイラの版 `naruVersion`(`Main.lean`)は `lakefile.toml` の `version` と合わせる。stdlib の hash は `stdlib/Model/**/*.lean` の内容から計算する(版は目印)。

## Lean 4.34.1 の癖
- `syntax` と `meta` は予約語(識別子・引数名に使えない)。`String.mk` は非推奨(`"".pushn c n` や `String.ofList`)。docstring `/-- -/` は `mutual` の前に置けない。
- 到達しない match の alternative は **error**(`lean.redundantMatchAlt`)。`match n with | k => …` の本体の `n` は一般化後の測度と切り離される(`match h : n with` の等式 `h : n = …` で結び直す。名前付きパターン `n@(_ + 1)` は別名経由の入れ子で切れる)。`deriving DecidableEq` / `Ord` は入れ子の帰納型(`Option<Self>` 越し)に使えない。`deriving Ord` は structure でも使える。`{ x with }`(欄なし)は使わず `x` を出す。

## verified-consensus(基準。変更しない)
- Lean の module system(`module` / `public import` / `@[expose] public section`)で書かれ、Model は mathlib(`Finset` / `WithBot` …)を使う。`grep '^import'` では import が取れない(`public import`)。
- `verified-consensus/.lake` は部分ビルド済み(Objects 層と Generic 層は olean あり: `cd verified-consensus && lake env lean <file>` で `#eval` できる。Model 12/29 ファイル、Statements 6/12)。フルビルドは約 1 時間(前提)。Witnesses は `V := Fin 2`、`Env` は `proposer := fun _ => 0` / `committees := ⟨fun _ => {0}⟩` / `weight := fun v => if v = 0 then 3 else 1`。
- 行数: Model 5,722 行(29 ファイル)、Statements 1,170 行(12 ファイル)、Witnesses 6,567 行。IDEAL.md の「1.5 倍」判定の分母は約 6,850 行(移植ソースの行数は `find dsl -name '*.naru' -not -path 'dsl/scenarios/*' | xargs wc -l`)。
- 移植の対応(周回 5 で決め、Objects 層で手書きと値の一致を確認): 型引数 `V` → `record ValidatorId { value: Nat }`(Identifiers.naru。`Fin n` の値は `value` で写す)。`WithBot Time` → `enum Stamp { Bottom, At(Time) } derive order`、`Option Stamp` → `Occurrence`(None = +∞)。`TimestampMap α := α → Option Stamp` → 使う側で `Table<T, Stamp>` + `occurrenceBefore(ts.get?(x), Γ)`。関数型の欄のうち環境のオラクル(`proposer` / `committees`)→ `input`、有限型上の関数(`weight : V → Nat`)→ `Table`。証明の欄(`Δ_pos` / `weight_pos` …)→ Statements の premise。`pickUnique?` → `findUnique?`。Prop 版(`Preceq` …)→ Statements。関数を返す def(`tau st : TimestampMap …`)→ 引数を増やした fn(`tau(st, vote)`)。
- `scripts/check-review-boundary.rb` は `lake env lean --deps-json <file>` で import 閉包を取る(C8 の雛形)。`scripts/ReviewSurfaceShape.lean` は `run_cmd` で structure の field 名を照合する(C9 の雛形)。

## 環境の癖
- Bash から `.idd/` や `IDEAL.md` に触れる(ls を含む)とフックが拒否する。記録・台帳は Write ツールで書く。`rm -rf` を含むコマンドも拒否されうる(出力先は毎回別名の一時ディレクトリにするか、`compile` 自身の作り直しに任せる)。
- 一時的な naru ソースの実験は `/tmp/naru-tc/*.naru` に置き、`lake exe naru compile [--out /tmp/naru-gen] /tmp/naru-tc/x.naru` で検査・生成できる(リポジトリ外でも可)。
