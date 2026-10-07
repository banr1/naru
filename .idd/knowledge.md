# 知見

<!-- 周回を跨いで役に立つ事実だけを書く: ビルド/テストの実行方法、ツールの制限と回避策、環境の癖。
     「次にやること」は書かない(それは周回記録の「申し送り」)。古くなった行は消す。50 行以内に保つ。
     周回のエージェントは途中で替わりうる。特定のハーネスのツール名ではなく、コマンドと事実で書く。 -->

## ビルドと実行(リポジトリのルートで)
- `lake build` — naru コンパイラ(`compiler/`、lean_lib `Naru` + lean_exe `naru`)。依存なし(mathlib 不要)。冷えた状態で約 40 秒、差分なら数秒。
- `lake exe naru compile <files...>` — 指定ファイルを検査。省略時は `dsl/**/*.naru`(パス順)。診断は stderr に `file:line:col: error[E0xx]: msg`、exit 1。
- `lake exe naru check-reject <file.naru> <Exxx>` — 反例が compile で拒否され(exit 1 相当)かつ診断に `Exxx` を含むことを検査し、合格なら PASS で exit 0(台帳の `cycle N:` 出典に使える形)。検査スクリプトは Lean で書く前提なので、シェルのラッパーは置かない。
- 回帰の一式(コードを変えた周回は必ず通し、met 条件の `cycle N:` を取り直す):
  `lake build && lake exe naru compile tests/accept/smoke.naru && lake exe naru check-reject tests/reject/phase_leak.naru E001 && lake exe naru check-reject tests/reject/phase_leak_method.naru E001 && lake exe naru check-reject tests/reject/choose.naru E003 && lake exe naru check-reject tests/reject/order_loss.naru E004 && lake exe naru check-reject tests/reject/missing_capability.naru E005 && lake exe naru check-reject tests/reject/type_path_escape.naru E011`
  (`type_path_escape` は条件ではなく回帰用: 型の位置の未解決経路で型検査を黙らせる抜け穴が再び開かないことを見る)
- `tests/accept/smoke.naru` は MVP 構文と stdlib 表の受理例。パーサ・型検査を変えたら exit 0 を確かめる。
- 文法と stdlib 表の正本は `compiler/SYNTAX.md`。構文・メソッドを増やしたら同時に直す。

## コンパイラの事実
- 段: 字句解析 → 構文解析 → 名前解決・phase 検査(`Resolve.lean`: E001, E011〜E013)→ 型・capability 検査(`Typecheck.lean`: E003〜E006, E014〜E016)。前の段に誤りがあれば次の段には進まない。
- Lean 4.34.1。`syntax` と `meta` は Lean の予約語(識別子・構築子名に使えない)。`String.mk` は非推奨(`String.ofList`)。
- 名前解決はコンパイル単位(渡された全ファイル)を 1 つの大域表で行う。`import` は受理するだけで意味を持たない。
- 大文字始まりの経路は大域名(`Phase.Tick`、`Set.empty`)、小文字始まりは値と欄の連鎖、としてパーサが振り分ける。局所名は小文字始まりのみ(大文字は E010)。
- `x.f(args)` は `f` がユーザ宣言の大域名なら `f(x, args)` の糖衣(UFCS)。大域名でなければ stdlib メソッドとして `Typecheck.lean` の表(`setSigs` 等)で解決し、無ければ E015。
- 組み込み: primitive 型名(Bool Nat Int String Unit Option Result List Set Table)、`Some` `None` `Ok` `Err`、自由関数 `sort` `choose` `pick`。これらは再宣言できない(E012)。stdlib はまだ Lean 側の表だけで、naru で書いたものは無い。
- 型検査はメタ変数の単一化。lambda の引数型は期待される型(メソッド表・fn の署名・`let x: T`)から取る。期待が無い受け手の `.f()` や `.field` は E014「add a type annotation」。
- `unknown` 型(誤りの波及抑制)は診断を出した後にだけ作る、が不変。型の位置の経路は完全一致で解決(`Resolve.checkTyPath`)し、`Set.X` / `Nat.X` / `Record.x` は E011。この不変が崩れると E003 / E004 が素通りする(周回 2 の reviewer が発見)。
- 数値リテラルは Nat だが、Int が期待される位置では Int として読む(`i > 0`、`let x: Int = 5`)。Nat → Int は `toInt()`、単項 `-` は Int 専用。位置引数は名前付き引数より前(後ろは E015)。
- capability: `eq` は primitive と derive eq の record/enum とそれらの Option/List/Set/Result/Table/tuple。`order` は Nat/Int/String、Option/List/tuple、derive order の record/enum。Set/Table は order を持たない → Set を含む record は `derive order` できない(E005)。
- Set → List の経路は `sort(by = …)` だけ。`Set.minBy?` / `maxBy?` / `sort` は鍵と要素の両方に order を要求する(同鍵の要素を要素の順序で決める)。

## verified-consensus(基準。変更しない)
- Lean の module system(`module` / `public import` / `@[expose] public section`)で書かれている。`grep '^import'` では import が取れない(`public import`)。
- `verified-consensus/.lake` は部分ビルド済み(Model 12/29 ファイル、Statements 6/12、mathlib は一部)。フルビルドは約 1 時間(前提)。
- 行数: Model 5,722 行(29 ファイル)、Statements 1,170 行(12 ファイル)、Witnesses 6,567 行。IDEAL.md の「1.5 倍」判定の分母は約 6,850 行。
- `scripts/check-review-boundary.rb` は `lake env lean --deps-json <file>` で import 閉包を取る(C8 の雛形)。`scripts/ReviewSurfaceShape.lean` は `run_cmd` で structure の field 名を照合する(C9 の雛形)。

## 環境の癖
- Bash から `.idd/` や `IDEAL.md` に触れる(ls を含む)とフックが拒否する。記録・台帳は Write ツールで書く。
- zsh では `${PIPESTATUS[0]}` は空。`${pipestatus[1]}`(小文字・1 始まり)を使う。
- 一時的な naru ソースの実験は `/tmp/naru-tc/*.naru` に置き、`lake exe naru compile /tmp/naru-tc/x.naru` で検査できる(リポジトリ外でも可)。
