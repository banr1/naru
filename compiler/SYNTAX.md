# naru 構文リファレンス(MVP)

コンパイラ(`compiler/Naru/Lexer.lean`、`Parser.lean`)が受理する文法の正本。
IDEAL.md「前提」の MVP 構文を Rust / TypeScript / Python / Go 利用者が想像しやすい形にしたもの。
ここに無い構文は受理しない。構文を増やすときはこの文書とパーサを同時に直す。

## 字句

- 空白・改行は意味を持たない。コメントは `// …` と `/* … */`(入れ子可)。
- 識別子: `[A-Za-z_][A-Za-z0-9_]*` に末尾の `?` を許す(`find?`、`minBy?`)。
- 命名規約(パーサが依存する): **大文字始まり**は型・モジュール・enum・構築子(`Block`、`Phase.Tick`、`Some`)、
  **小文字始まり**は値(変数・fn・input・predicate 以外の spec 宣言も小文字で良い)。
  式の中で `a.b.c` は、先頭が小文字なら「値 `a` の欄 `b` の欄 `c`」、大文字なら大域経路 `A.b.c` として扱う。
  **局所名(引数・`let`・lambda・`forall` / `exists` の束縛)は小文字か `_` で始める**(大文字は E010)。
  これで大文字始まりの経路は常に大域名を指し、読みが一意になる。
- 組み込み名(primitive 型名と `Some` `None` `Ok` `Err`)は再宣言できない(E012)。
- 数値: 10 進 Nat リテラル。文字列: `"…"`(`\n` `\t` `\"` `\\`)。
- 予約語: `module import type record enum derive input fn state protocol predicate condition regime property claim bundle scenario observer let if else match forall exists in implies true false`。

## モジュールと宣言

```
module A.B.C            // 先頭に必ず 1 つ
import X.Y              // 任意個。現状は名前空間の宣言のみで、解決はコンパイル単位全体の表で行う

type Slot = Nat                                   // 型別名
record Block { slot: Slot, parent: Option<BlockId> } derive eq, order
state Store { head: Block, seen: List<Block> }    // record と同じ形。protocol の状態に使う
enum Phase { Tick, Deliver } derive eq, order     // variant は `Name` または `Name(T1, T2)`
input proposer(slot: Slot) -> ValidatorId         // 本体なし。非決定性の明示(環境からの入力)
fn head(st: Store) -> BlockId { … }               // runtime 関数。本体はブロック式
observer confirmed(st: Store) -> Nat { … }        // simulation の出力。fn と同形
predicate Safe(run: Run) { … }                    // spec。本体は Prop 相当の式
condition Synchronous(delta: Nat) { … }           // spec
regime Honest(run: Run) { … }                     // spec
property Monotone(run: Run) { … }                 // spec
claim finalizedSafe(run: Run) { … }               // spec。定理。引数は省略可
claim bundle Consensus { finalizedSafe, live: confirmedLive }   // 公開する保証の一覧
protocol Demo { fn step(st: Store) -> Store { … } }             // 中の宣言は owner = Demo として平坦化
scenario basic { … }                              // runtime の実行 fixture。本体はブロック式
```

`derive` の capability は `eq` / `order` / `finite` / `repr` のみ。

### phase

| 宣言 | phase |
|---|---|
| type / record / state / enum / input / fn / protocol / scenario / observer | runtime |
| predicate / condition / regime / property / claim / claim bundle | spec |

runtime 宣言が spec 宣言を参照すると **E001**(phase leak)。spec → runtime は自由。

## 型

```
Nat  Int  Bool  String  Unit            // primitive
Option<T>  Result<T, E>  List<T>  Set<T>  Table<K, V>
(T1, T2)                                 // tuple。`()` は Unit
Block  Phase  A.B.Name                   // ユーザ定義(型別名・record・state・enum)
```

## 式

優先順位(弱 → 強): `implies`(右結合)< `||` < `&&` < `==` `!=` < `<` `<=` `>` `>=` < `+` `-` < `*` `/` `%` < 前置 `!` `-` < 後置(呼出し・欄・メソッド)。

```
42  "s"  true  false  ()                 // リテラル
x  x.slot  x.votes.size()                // 値・欄・メソッド呼出し
f(x, y)  sort(xs, by = |b| b.slot)       // 呼出し。`name = e` は名前付き引数
s.tall()                                 // `f` がユーザ宣言の大域名なら `tall(s)` の糖衣(UFCS)。phase 検査の対象。
                                         // 大域名でなければ stdlib のメソッド(型検査の段で解決)
Phase.Tick  Some(x)  None  Set.empty()   // 大域経路・構築子
Block { slot: 1, parent: None }          // record literal
Store { head: b, ..st }                  // record update(`..base` は末尾)
[a, b, c]  (a, b)                        // list / tuple literal
{ let x = e; let y: T = e; x + y }       // ブロック。`let` は `;` 必須。末尾の式が値
if c { a } else { b }                    // else 必須。else if 可。頭部では record literal 不可
match e { Some(x) if x > 0 => x, Some(_) => 0, None => 0 }   // ガード付き arm。`,` 区切り(本体がブロックなら `,` 省略可)
|x, y| x + y                             // lambda(Rust 風)。`||` は引数なし
forall b: Block { … }  exists t: Time { … }   // 量化(spec 専用。本体はブロック)
```

## パターン

`_`、変数(小文字)、リテラル、`Ctor(p1, p2)` / `Enum.Variant`、`(p1, p2)`。

## 診断

出力は `file:line:col: error[E0xx]: message`。終了コードは誤りがあれば 1。
反例ソースの検査は `lake exe naru check-reject <file.naru> <Exxx>`(compile と同じ経路を走らせ、
診断があってその中に Exxx があれば PASS で exit 0。`tests/reject/` の条件の証拠はこれで取る)。

| 番号 | 意味 | 実装 |
|---|---|---|
| E001 | phase leak(runtime → spec) | 済(`Resolve.lean`) |
| E002 | 停止性を確認できない再帰 | 未 |
| E003 | 無条件の選択 | 未 |
| E004 | 順序指定の無い Set → List | 未 |
| E005 | capability 不足 | 未 |
| E006 | Model 内の無限量化による分岐 | 未 |
| E007 | runtime 条件の classical 依存 | 未 |
| E010 | 字句・構文の誤り | 済 |
| E011 | 解決できない名前 | 済 |
| E012 | 同名の宣言 | 済 |
| E013 | 型の位置に型でない宣言 | 済 |

## まだ無いもの

型検査・capability 検査・Core IR・Model / Statements backend・`import` の意味(現状は全ファイルが 1 つの大域表)・
組み込み値の正式な stdlib(現状は `Some` / `None` / `Ok` / `Err` と primitive 型の名前だけを組み込みとして解決する)。
