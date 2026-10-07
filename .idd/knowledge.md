# 知見

<!-- 周回を跨いで役に立つ事実だけを書く: ビルド/テストの実行方法、ツールの制限と回避策、環境の癖。
     「次にやること」は書かない(それは周回記録の「申し送り」)。古くなった行は消す。50 行以内に保つ。
     周回のエージェントは途中で替わりうる。特定のハーネスのツール名ではなく、コマンドと事実で書く。 -->

## ビルドと実行(リポジトリのルートで)
- `lake build` — naru コンパイラ(`compiler/`、lean_lib `Naru` + lean_exe `naru`)。依存なし(mathlib 不要)。冷えた状態で約 40 秒。
- `lake exe naru compile <files...>` — 指定ファイルを検査。省略時は `dsl/**/*.naru`(パス順)。診断は stderr に `file:line:col: error[E0xx]: msg`、exit 1。
- `lake exe naru check-reject <file.naru> <Exxx>` — 反例が compile で拒否され(exit 1 相当)かつ診断に `Exxx` を含むことを検査し、合格なら PASS で exit 0(台帳の `cycle N:` 出典に使える形)。検査スクリプトは Lean で書く前提なので、シェルのラッパーは置かない。
- `lake exe naru compile tests/accept/smoke.naru` — MVP 構文の受理例。パーサを変えたら exit 0 を確かめる。
- 文法の正本は `compiler/SYNTAX.md`。構文を増やしたら同時に直す。

## コンパイラの事実
- Lean 4.34.1。`syntax` は Lean の予約語(識別子に使えない)。`String.mk` は非推奨(`String.ofList`)。
- 名前解決はコンパイル単位(渡された全ファイル)を 1 つの大域表で行う。`import` は受理するだけで意味を持たない。
- 大文字始まりの経路は大域名(`Phase.Tick`、`Set.empty`)、小文字始まりは値と欄の連鎖、としてパーサが振り分ける。局所名は小文字始まりのみ(大文字は E010)。
- `x.f(args)` は `f` がユーザ宣言の大域名なら `f(x, args)` の糖衣(UFCS)として phase 検査する。大域名でなければ stdlib メソッド扱い(型検査が未実装なので今は未検査で通る)。
- 組み込み: primitive 型名(Bool Nat Int String Unit Option Result List Set Table)と `Some` `None` `Ok` `Err` だけ。stdlib はまだ無い。

## verified-consensus(基準。変更しない)
- Lean の module system(`module` / `public import` / `@[expose] public section`)で書かれている。`grep '^import'` では import が取れない(`public import`)。
- `verified-consensus/.lake` は部分ビルド済み(Model 12/29 ファイル、Statements 6/12、mathlib は一部)。フルビルドは約 1 時間(前提)。
- 行数: Model 5,722 行(29 ファイル)、Statements 1,170 行(12 ファイル)、Witnesses 6,567 行。IDEAL.md の「1.5 倍」判定の分母は約 6,850 行。
- `scripts/check-review-boundary.rb` は `lake env lean --deps-json <file>` で import 閉包を取る(C8 の雛形)。`scripts/ReviewSurfaceShape.lean` は `run_cmd` で structure の field 名を照合する(C9 の雛形)。

## 環境の癖
- Bash から `.idd/` や `IDEAL.md` に触れる(ls を含む)とフックが拒否する。記録・台帳は Write ツールで書く。
- zsh では `${PIPESTATUS[0]}` は空。`${pipestatus[1]}`(小文字・1 始まり)を使う。
