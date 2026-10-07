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
- 組み込み名(primitive 型名と `Some` `None` `Ok` `Err`、自由関数 `sort` `choose` `pick`)は再宣言できない(E012)。
  `choose` / `pick` は常に E003(無条件の選択は naru に無い)。
- 数値: 10 進 Nat リテラル。Int が期待される位置(`let x: Int = 5`、`i > 0`、`i + 1`)では Int として読む。
  Nat の値を Int にするのは `n.toInt()`(暗黙の変換は無い。単項 `-` は Int 専用)。文字列: `"…"`(`\n` `\t` `\"` `\\`)。
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
`claim bundle` の項目は claim か入れ子の claim bundle だけ(他の宣言は E016)。

### capability(型検査 `Typecheck.lean`)

Lean の型クラス(DecidableEq / Ord)は露出せず、型が持つ capability で表す。

| capability | 持つ型 |
|---|---|
| `eq` | Bool Nat Int String Unit、`Option<T>` `List<T>` `Set<T>` `Result<T, E>` `Table<K, V>` tuple(成分がすべて eq)、`derive eq` した record / enum |
| `order` | Bool Nat Int String、`Option<T>` `List<T>` tuple(成分がすべて order)、`derive order` した record / enum。`Set` と `Table` は順序を持たない |

- `==` `!=` は両辺の型に `eq`、`<` `<=` `>` `>=` は `order` を要求する(無ければ **E005**)。
- stdlib メソッドの要求(`Set.contains` → eq、`sort(by = …)` → 鍵の order 等)も E005。
- `derive eq` / `derive order` した record / enum は、すべての欄・variant の型がその capability を持たなければならない(E005)。
  `Set` を含む record は `order` を derive できない。

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
Block  Phase  A.B.Name                   // ユーザ定義(型別名・record・state・enum)。経路は完全一致で解決する
                                         // (`Block.x` / `Set.x` / `Nat.x` は型ではない → E011。不明な型で検査を黙らせる抜け穴を塞ぐ)
```

## 式

優先順位(弱 → 強): `implies`(右結合)< `||` < `&&` < `==` `!=` < `<` `<=` `>` `>=` < `+` `-` < `*` `/` `%` < 前置 `!` `-` < 後置(呼出し・欄・メソッド)。

```
42  "s"  true  false  ()                 // リテラル
x  x.slot  x.votes.size()                // 値・欄・メソッド呼出し
f(x, y)  sort(xs, by = |b| b.slot)       // 呼出し。`name = e` は名前付き引数(ユーザ fn の引数名にも使える)。
                                         // 位置引数は名前付き引数より前に置く(後ろは E015)
s.tall()                                 // `f` がユーザ宣言の大域名なら `tall(s)` の糖衣(UFCS)。phase 検査の対象。
                                         // 大域名でなければ stdlib のメソッド(型検査の段で解決)
Phase.Tick  Some(x)  None  Set.empty()   // 大域経路・構築子
Block { slot: 1, parent: None }          // record literal
Store { head: b, ..st }                  // record update(`..base` は末尾)
[a, b, c]  (a, b)                        // list / tuple literal
{ let x = e; let y: T = e; x + y }       // ブロック。`let` は `;` 必須。末尾の式が値
if c { a } else { b }                    // else 必須。else if 可。頭部では record literal 不可
match e { Some(x) if x > 0 => x, Some(_) => 0, None => 0 }   // ガード付き arm。`,` 区切り(本体がブロックなら `,` 省略可)。
                                         // arm は 1 つ以上(無ければ E014)。網羅性はまだ検査しない(backend の段で Lean が拒否する)
|x, y| x + y                             // lambda(Rust 風)。`||` は引数なし
forall b: Block { … }  exists t: Time { … }   // 量化(spec 専用。本体はブロック)
```

## パターン

`_`、変数(小文字)、リテラル、`Ctor(p1, p2)` / `Enum.Variant`、`(p1, p2)`。
構築子は `Some` / `None` / `Ok` / `Err` と `Enum.Variant`(引数の数は宣言どおり。違えば E015)。

## stdlib(組み込みのメソッド表。`Typecheck.lean` が正本)

naru で書いた stdlib ができるまで、型検査がここに書いた署名で型を与える。`T` `U` `K` `V` `E` は型変数。
メソッドの無い型(record / enum)に `x.f()` と書くと、`f` がユーザ宣言なら `f(x)` の糖衣、無ければ E015。

| 型 | メソッド |
|---|---|
| `Set<T>` | `size() -> Nat`、`isEmpty() -> Bool`、`contains(T) -> Bool`ᵉ、`insert(T)`ᵉ、`remove(T)`ᵉ、`union(Set<T>)`ᵉ、`inter`ᵉ、`diff`ᵉ、`subset(Set<T>) -> Bool`ᵉ、`filter(T -> Bool) -> Set<T>`、`map(T -> U) -> Set<U>`(U に eq)、`any(T -> Bool)`、`all(T -> Bool)`、`findUnique?(T -> Bool) -> Option<T>`、`minBy?(T -> U) -> Option<T>`ᵒ、`maxBy?(T -> U) -> Option<T>`ᵒ、`sort(by = T -> U) -> List<T>`ᵒ |
| `List<T>` | `size`、`isEmpty`、`contains(T)`ᵉ、`push(T)`、`append(List<T>)`、`head?`、`last?`、`get?(Nat)`、`find?(T -> Bool)`、`filter`、`map(T -> U) -> List<U>`、`any`、`all`、`count(T -> Bool) -> Nat`、`fold(U, (U, T) -> U) -> U`、`sort(by = T -> U)`(U に order)、`minBy?` / `maxBy?`(U に order)、`reverse`、`take(Nat)`、`drop(Nat)`、`toSet() -> Set<T>`ᵉ |
| `Option<T>` | `isSome`、`isNone`、`getOr(T) -> T`、`map(T -> U)`、`andThen(T -> Option<U>)`、`filter(T -> Bool)` |
| `Result<T, E>` | `isOk`、`isErr`、`ok?() -> Option<T>` |
| `Table<K, V>` | `size`、`isEmpty`、`get?(K) -> Option<V>`ᵏ、`getOr(K, V) -> V`ᵏ、`contains(K)`ᵏ、`insert(K, V)`ᵏ、`remove(K)`ᵏ、`keys() -> Set<K>`ᵏ、`entries() -> Set<(K, V)>`(K・V に eq) |
| `Nat` | `min(Nat)`、`max(Nat)`、`toInt() -> Int` |
| `Int` | `min(Int)`、`max(Int)`、`abs() -> Nat` |
| `String` | `size() -> Nat`、`append(String)` |

ᵉ T に `eq` を要求。ᵏ K に `eq` を要求。ᵒ 鍵 U と要素 T の両方に `order` を要求(鍵が同じ要素は要素自身の順序で並べ、決定的にする)。

静的関数: `Set.empty()`、`Set.singleton(x)`、`Set.of(List<T>)`、`List.empty()`、`List.range(Nat)`、`Table.empty()`。
自由関数: `sort(xs, by = …)` は `xs.sort(by = …)` の糖衣。名前付き引数 `by` は位置で渡してもよい。

### Set の規則(E003 / E004)

Set は順序を持たない。IDEAL.md「言語の意味論」のとおり、選択は `findUnique?` / `minBy?` / `maxBy?`(List には `find?` も)だけ、
List 化は `sort(by = …)` だけ。

- **E003(無条件の選択)**: `Set` への `choose` `pick` `first` `first?` `head` `head?` `last` `last?` `find?` `get?` `any?` `take` `drop`、
  および自由関数 `choose(x)` / `pick(x)`(受け手の型を問わない)。
- **E004(順序指定の無い Set → List)**: `Set` への `toList` `fold` `foldl` `foldr` `reduce` `enumerate` `zip` `join`、
  および `by = …` の無い `sort`(`s.sort()` / `sort(s)`)。

Set から List への経路は `sort(by = …)` だけ。`Set.map` は Set を返し、`Table.keys` / `entries` も Set を返す。

### 量化(E006)

`forall` / `exists` は spec 宣言専用。runtime 宣言(fn / observer / scenario …)に書くと E006。
有限の集合を回すには `all` / `any` / `filter` を使う。

## 診断

出力は `file:line:col: error[E0xx]: message`。終了コードは誤りがあれば 1。
反例ソースの検査は `lake exe naru check-reject <file.naru> <Exxx>`(compile と同じ経路を走らせ、
診断があってその中に Exxx があれば PASS で exit 0。`tests/reject/` の条件の証拠はこれで取る)。

| 番号 | 意味 | 実装 |
|---|---|---|
| E001 | phase leak(runtime → spec) | 済(`Resolve.lean`) |
| E002 | 停止性を確認できない再帰 | 未 |
| E003 | 無条件の選択(Set の `choose` / `pick` / `first` / `find?` …) | 済(`Typecheck.lean`) |
| E004 | 順序指定の無い Set → List(`toList` / `by` 無しの `sort` / `fold` …) | 済(`Typecheck.lean`) |
| E005 | capability 不足(`==` `<`、eq / order を要する stdlib メソッド、`derive` の欄) | 済(`Typecheck.lean`) |
| E006 | runtime 宣言内の量化(`forall` / `exists`) | 済(`Typecheck.lean`) |
| E007 | runtime 条件の classical 依存 | 未 |
| E010 | 字句・構文の誤り | 済 |
| E011 | 解決できない名前 | 済 |
| E012 | 同名の宣言 | 済 |
| E013 | 型の位置に型でない宣言 | 済 |
| E014 | 型の不一致・推論できない型・値でないものの値としての使用 | 済 |
| E015 | 無い欄・無いメソッド・引数の数や名前の不一致 | 済 |
| E016 | claim bundle の項目が claim でない | 済 |

名前解決(E011〜E013、E001)に誤りがあれば型検査には進まない(未解決名の波及を避ける)。

## まだ無いもの

計算可能性検査(E002)・E007・Core IR・Model / Statements backend・`import` の意味(現状は全ファイルが 1 つの大域表)・
型引数付きのユーザ宣言(`record R<T>`)・Constants と interface binding の構文・naru で書いた stdlib(現状は上の表)・
未確定のメタ変数の報告(`[]` や `None` の型が最後まで決まらなくても誤りにしない)。
