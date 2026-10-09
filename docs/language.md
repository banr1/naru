# naru 言語リファレンス(MVP)

コンパイラ(`compiler/Naru/Lexer.lean`、`Parser.lean`)が受理する文法の正本。構文を増やすときはこの文書とパーサ、tree-sitter 文法([editors.md](editors.md))を同じ周回で直す。
IDEAL.md「前提」の MVP 構文を Rust / TypeScript / Python / Go 利用者が想像しやすい形にしたもの。ここに無い構文は受理しない。
診断の番号(E0xx)は [diagnostics.md](diagnostics.md)、生成される Lean は [architecture.md](architecture.md)、`naru simulate` は [cli.md](cli.md) を参照。

## 字句

- 空白・改行は意味を持たない。コメントは `// …` と `/* … */`(入れ子可)。
- 識別子: `[A-Za-z_][A-Za-z0-9_]*` に末尾の `?` を許す(`find?`、`minBy?`)。
- 命名規約(パーサが依存する): **大文字始まり**は型・モジュール・enum・構築子(`Block`、`Phase.Tick`、`Some`)、
  **小文字始まり**は値(変数・fn・input・predicate 以外の spec 宣言も小文字で良い)。
  式の中で `a.b.c` は、先頭が小文字なら「値 `a` の欄 `b` の欄 `c`」、大文字なら大域経路 `A.b.c` として扱う。
  **局所名(引数・`let`・lambda・`forall` / `exists` の束縛)は小文字か `_` で始める**(大文字は E010)。
  これで大文字始まりの経路は常に大域名を指し、読みが一意になる。
- 組み込み名(primitive 型名と `Some` `None` `Ok` `Err`、自由関数 `sort` `choose` `pick`)は再宣言できない(E012)。
  `choose` / `pick` は常に E003(無条件の選択は naru に無い)。record の欄名・enum の variant 名に Lean が自動生成する
  名前(`mk` `rec` `recOn` `casesOn` `noConfusion` `below` `brecOn` `sizeOf` …)は使えない(E012)。
  それ以外の名前は Lean の予約語(`from` `at` `end` …)でもよい(backend が `«»` で逃がす)。
- 数値: 10 進 Nat リテラル。Int が期待される位置(`let x: Int = 5`、`i > 0`、`i + 1`)では Int として読む。
  Nat の値を Int にするのは `n.toInt()`(暗黙の変換は無い。単項 `-` は Int 専用)。文字列: `"…"`(`\n` `\t` `\"` `\\`)。
- 予約語: `module import type record enum derive input fn state protocol predicate condition regime property claim bundle scenario observer observe let if else match forall exists in implies true false`。

## モジュールと宣言

```
module A.B.C            // 先頭に必ず 1 つ
import X.Y              // 任意個。現状は名前空間の宣言のみで、解決はコンパイル単位全体の表で行う

type Slot = Nat                                   // 型別名
record Block { slot: Slot, parent: Option<BlockId> } derive eq, order
state Store { head: Block, seen: List<Block> }    // record と同じ形。protocol の状態に使う
enum Phase { Tick, Deliver } derive eq, order     // variant は `Name` または `Name(T1, T2)`。自分への再帰は直接の引数・欄でだけ
                                                  // (`Option<Self>` / `List<Self>` 越しは E019。rose tree は相互再帰の enum で書く)
input proposer(slot: Slot) -> ValidatorId         // 本体なし。非決定性の明示(環境からの入力)
fn head(st: Store) -> BlockId { … }               // runtime 関数。本体はブロック式
observer confirmed(st: Store) -> Nat { … }        // simulation の出力を取り出す宣言。fn と同形(`observe` できるのは observer だけ)
predicate Safe(run: Run) { … }                    // spec。本体は Prop 相当の式
condition Synchronous(delta: Nat) { … }           // spec
regime Honest(run: Run) { … }                     // spec
property Monotone(run: Run) { … }                 // spec
claim finalizedSafe(run: Run) { … }               // spec。定理。引数は省略可
claim bundle Consensus { finalizedSafe, live: confirmedLive }   // 公開する保証の一覧
protocol Demo { fn step(st: Store) -> Store { … } }             // 中の宣言は owner = Demo として平坦化
scenario basic {                                  // runtime の実行 fixture(下の「scenario と observer」)
  input proposer(slot) = ValidatorId { value: 0 };   //   先頭: 環境の入力に値を与える
  let st = Store { … };                           //   局所束縛
  observe confirmed(st);                          //   出力: observer の呼出しだけ
}
```

モジュール名はファイルのパスに対応する(ソースルートからの相対パス。`naru.toml` は [cli.md](cli.md) の「naru.toml」)。

`derive` の capability は `eq` / `order` / `finite` / `repr` のみ。
`claim bundle` の項目は claim か入れ子の claim bundle だけ(他の宣言は E016)。

### capability

型検査(`compiler/Naru/Typecheck.lean`)が見る。Lean の型クラス(DecidableEq / Ord)は露出せず、型が持つ capability で表す。

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
(Block) -> Nat  (Nat, Nat) -> Bool       // 関数型(first-order の関数値)。fn / observer / spec 宣言の仮引数と closure の引数、
                                         // `let` の注釈にだけ書ける。欄・variant・別名・戻り型・input・コレクションの中に
                                         // 書くと E014(`() -> U` も)。関数を返す fn・関数を持つ record / enum は作れない
```

関数型の仮引数には lambda(`|b| score(b)`)も fn の名前(`inc`)も渡せ、本体では `f(x)` と呼ぶ(局所名なので名前付き引数は
使えず、UFCS `x.f()` にもならない)。停止性検査では、関数値の呼出しは呼出しグラフの辺にならず、fn を値として渡した場所が
その fn への辺になる(引数が読めないので、サイクルの中なら E002。lambda の中からの再帰も同じ)。
型注釈の無い位置では推論が関数の List(`[inc, |x| x * 2]`)や関数を返す closure(`|x| |y| x + y`)を一時的に作ることを
許す(単純型付きの範囲で、停止性・決定性は変わらない)。ただし Set / Table の要素には置けず(`Set.of` / `Set.singleton` /
`toSet` / `insert` … は要素に `eq` を要求するので E005)、欄・variant・戻り型・input は注釈が必須なので E014 になる。

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
                                         // arm は 1 つ以上(無ければ E014)。最後の arm にガードは置けず、Nat / Int / String の
                                         // match には無条件の `_` か変数の arm が要る(E018)。他の型の網羅性は backend の段で Lean が検査する
|x, y| x + y                             // lambda(Rust 風)。`||` は引数なし
forall b: Block { … }  exists t: Time { … }   // 量化(spec 専用。本体はブロック)
```

## パターン

`_`、変数(小文字)、リテラル、`Ctor(p1, p2)` / `Enum.Variant`、`(p1, p2)`。
構築子は `Some` / `None` / `Ok` / `Err` と `Enum.Variant`(引数の数は宣言どおり。違えば E015)。

## stdlib(組み込みのメソッド表)

`compiler/Naru/Typecheck.lean` が正本、Lean 側の実装は `stdlib/Model/NaruStd`。
naru で書いた stdlib ができるまで、型検査がここに書いた署名で型を与える。`T` `U` `K` `V` `E` は型変数。
メソッドの無い型(record / enum)に `x.f()` と書くと、`f` がユーザ宣言なら `f(x)` の糖衣、無ければ E015。

| 型 | メソッド |
|---|---|
| `Set<T>` | `size() -> Nat`、`isEmpty() -> Bool`、`contains(T) -> Bool`ᵉ、`insert(T)`ᵉ、`remove(T)`ᵉ、`union(Set<T>)`ᵉ、`inter`ᵉ、`diff`ᵉ、`subset(Set<T>) -> Bool`ᵉ、`filter(T -> Bool) -> Set<T>`、`map(T -> U) -> Set<U>`(U に eq)、`flatMap(T -> Set<U>) -> Set<U>`(U に eq)、`any(T -> Bool)`、`all(T -> Bool)`、`sum(T -> Nat) -> Nat`、`findUnique?(T -> Bool) -> Option<T>`、`minBy?(T -> U) -> Option<T>`ᵒ、`maxBy?(T -> U) -> Option<T>`ᵒ、`sort(by = T -> U) -> List<T>`ᵒ |
| `List<T>` | `size`、`isEmpty`、`contains(T)`ᵉ、`push(T)`、`append(List<T>)`、`head?`、`last?`、`get?(Nat)`、`find?(T -> Bool)`、`filter`、`map(T -> U) -> List<U>`、`flatMap(T -> List<U>) -> List<U>`、`filterMap(T -> Option<U>) -> List<U>`、`any`、`all`、`count(T -> Bool) -> Nat`、`sum(T -> Nat) -> Nat`、`fold(U, (U, T) -> U) -> U`、`sort(by = T -> U)`(U に order)、`minBy?` / `maxBy?`(U に order)、`reverse`、`take(Nat)`、`drop(Nat)`、`toSet() -> Set<T>`ᵉ |
| `Option<T>` | `isSome`、`isNone`、`getOr(T) -> T`、`map(T -> U)`、`andThen(T -> Option<U>)`、`filter(T -> Bool)` |
| `Result<T, E>` | `isOk`、`isErr`、`ok?() -> Option<T>` |
| `Table<K, V>` | `size`、`isEmpty`、`get?(K) -> Option<V>`ᵏ、`getOr(K, V) -> V`ᵏ、`contains(K)`ᵏ、`insert(K, V)`ᵏ、`remove(K)`ᵏ、`keys() -> Set<K>`ᵏ、`entries() -> Set<(K, V)>`(K・V に eq)、`mapValues(V -> U) -> Table<K, U>`ᵏ(鍵を保って値だけを写す。全域写像の `fun k => f (t k)`) |
| `Nat` | `min(Nat)`、`max(Nat)`、`toInt() -> Int` |
| `Int` | `min(Int)`、`max(Int)`、`abs() -> Nat`、`fdiv(Int) -> Int`(床除算。`(-7).fdiv(2) == -4`、除数 0 なら 0)、`toNat() -> Nat`(負は 0) |
| `String` | `size() -> Nat`、`append(String)` |

ᵉ T に `eq` を要求。ᵏ K に `eq` を要求。ᵒ 鍵 U と要素 T の両方に `order` を要求(鍵が同じ要素は要素自身の順序で並べ、決定的にする)。

静的関数: `Set.empty()`、`Set.singleton(x)`ᵉ、`Set.of(List<T>)`ᵉ、`List.empty()`、`List.range(Nat)`、`Table.empty()`
(`Set.singleton` / `Set.of` は要素の型に `eq` を要求する。宣言の終わりに検査するので、要素の型が後から決まってもよい)。
自由関数: `sort(xs, by = …)` は `xs.sort(by = …)` の糖衣。名前付き引数 `by` は位置で渡してもよい。

### Set の規則(E003 / E004)

Set は順序を持たない。IDEAL.md「言語の意味論」のとおり、選択は `findUnique?` / `minBy?` / `maxBy?`(List には `find?` も)だけ、
List 化は `sort(by = …)` だけ。

- **E003(無条件の選択)**: `Set` への `choose` `pick` `first` `first?` `head` `head?` `last` `last?` `find?` `get?` `any?` `take` `drop`、
  および自由関数 `choose(x)` / `pick(x)`(受け手の型を問わない)。
- **E004(順序指定の無い Set → List)**: `Set` への `toList` `fold` `foldl` `foldr` `reduce` `enumerate` `zip` `join`、
  および `by = …` の無い `sort`(`s.sort()` / `sort(s)`)。

Set から List への経路は `sort(by = …)` だけ。`Set.map` は Set を返し、`Table.keys` / `entries` も Set を返す。
`Set.sum(f)` は可換な集約(Nat の和)なので要素の順序に依存せず、Set から直接取れる(E004 の対象ではない。
`fold` は結合法則も可換性も保証できないので E004 のまま)。`Set.flatMap(f)`(各要素の集合の和集合)も同じ理由で
Set から直接取れる。

### 量化(E006)

`forall` / `exists` は spec 宣言専用。runtime 宣言(fn / observer / scenario …)に書くと E006。
有限の集合を回すには `all` / `any` / `filter` を使う。

### 再帰(E002)

停止性検査は `compiler/Naru/Totality.lean`。IDEAL.md「言語の意味論」: 再帰は構造的再帰・明示 fuel・有限集合の反復のみ。有限集合の反復は stdlib のメソッド
(`all` / `any` / `filter` / `map` / `fold` …)で、ユーザが書く再帰は次の 2 つの形だけを受理する。それ以外の再帰
(自己再帰・相互再帰とも)は **E002**。再帰しない関数には何の制限も無い。

| 形 | 受理する書き方 |
|---|---|
| 構造的再帰 | 仮引数(またはそれより小さい値)を `match` し、**構築子パターンの中**で束縛した名前を再帰呼出しの同じ測度の位置に渡す。`Tree.Node(l, _, r) => sum(l) + sum(r)`、`Chain.Link(_, next) => len(next)`(`Option<Chain>` 越しの再帰型は E019 なので、部分項は直接の引数から取る) |
| 明示 fuel | `Nat` の仮引数 `n`(型別名でもよい)を、`n ≥ k` が分かる分岐の中で `n - k`(k ≥ 1 のリテラル)として渡す。分かる分岐: `if n == 0 { … } else { ここ }`、`if n > 0 { ここ }`、`n != 0`、`n >= k`、`k < n`、`!(…)`、`&&` の then 側、`||` の else 側、`else if n == 1 { … } else { ここ }` の連鎖(n ≥ 2)、`match n { 0 => …, k => ここ }`(`k` は `n` の別名。`_` でもよい。**ガードの無い**リテラルの腕が 0 から連続して覆った値の次が下限: `0 => …, 1 => …, k =>` なら k ≥ 2。`0 if c => …` はガードが偽なら 0 が落ちてくるので数えない)、腕のガード `k if k > 0 => …` |

- サイクル(相互再帰を含む)の各関数に測度(仮引数の位置)を 1 つずつ割り当て、サイクル内の**すべての**呼出しで
  呼出し先の測度の実引数が呼出し元の測度より厳密に小さくなければならない(`ping(n - 1)` ↔ `pong(n - 1)` は可、
  片方が `ping(n)` なら両方 E002)。辞書式など複合の測度は無い。
- 検査は保守的で、Lean が受理できる形でも E002 になることがある: `let k = n - 1;` を経由する、record の欄(`c.rest`)に再帰する、
  lambda の引数(`xs.map(|x| f(x))`)から再帰する、`Int` の引数を減らす(下に有界でない)、仮引数と同名の `let` / lambda 引数で隠す、
  関数を値として渡す(`let g = f;`)。書き方を上の形に寄せる(検査は緩めない)。
- spec 宣言(predicate / claim …)の再帰も同じ規則で検査する。

## scenario と observer

scenario は定理ではなく実行 fixture で、非決定性(`input`)に値を与え、observer を通して値を表示する(IDEAL.md「言語の意味論」「用語」。C7)。
実行の仕方(`naru simulate`)は [cli.md](cli.md)。

```
scenario basic {
  input proposer(slot) = ValidatorId { value: 0 };           // 先頭にまとめて: input の束縛(後ろに置くと E010)
  input awake(node, round) = node.value == 0;                // 仮引数は名前だけ。型と数は `input` 宣言から(数が違う・同名は E015)
  let v0 = ValidatorId { value: 0 };                          // let(型注釈可)
  let rho = NamedRun { … };
  observe trace(s, rho, v0);                                  // observer の呼出しだけ(fn や式は E014)。戻り型が List なら 1 要素 1 行
  observe readsAt(s, rho, v0, 30);
}                                                             // 末尾の式は無い(scenario は値を持たない)
```

- `input f(x, y) = e;` は、この scenario の中で input `f` の値を naru の式 `e` で決める。`e` は `f` の戻り型で検査し、他の fn と同じ検査
  (E002〜E006、E014 …)を通る(Model に任意の Lean を入れる抜け道ではない)。`f` が input でなければ E014、無ければ E011、
  同じ input を 2 度束縛すると E012。
- **scenario は閉じていなければならない(E015)**: `let` / `observe` が直接・間接(呼ぶ fn / observer を辿って)に使う input はすべて
  先頭で束縛し、束縛の値 `e` が使う input はそれより前に束縛する(`input awake(…) = … proposer(…) …;` なら `proposer` が先)。
  閉じた scenario は入力の引数を持たない Lean の値になり、`simulate` がそのまま実行できる。
- `observe e;` の `e` は observer の呼出し(`name(args)` か UFCS `x.name(args)`)。表示のラベルはソースの式(`trace(s, rho, v0)`。
  文字列リテラルはエスケープしたまま、分岐・ブロック・lambda は `…`)。observer の戻り型は `Repr` を持つ値(primitive・record・enum・
  コレクション・tuple)であること。関数型の値を返す observer の `observe` は naru の診断ではなく `lake build naru_simulate` で落ちる。
- 生成 Lean(backend)は [architecture.md](architecture.md) の Model backend の表。`NaruStd.Observation` / `observe` / `observeList` / `runScenario` は
  `stdlib/Model/NaruStd/Observe.lean`。
- まだ無いもの: `protocol` 宣言の意味、observer の表示を naru 風にする `derive repr`、scenario の中の配達(deliver)の生成子
  ([roadmap.md](roadmap.md))。いまは scenario のファイルの fn が event 列を作る: `specs/consensus/scenarios/two_nodes.naru` の `twoNodeEvents` は各 t で
  node 0 の `nodeTick` の出力を `NamedEvent.Deliver(v1, o, t)` に並べ、`specs/consensus/scenarios/equivocation.naru` の `deliveredVotesEvents` は
  Byzantine な validator の票(注入 object)を決めた時刻に配達する。scenario 共通の observer は `specs/consensus/scenarios/trace.naru`。
  1 つの scenario に複数の run(`let` で束ねた `NamedRun`)を並べ、同じ observer を両方に `observe` すれば対照実験になる(`equivocation.naru`)。
- golden test との結び付き(C10、`tests/golden/Golden.lean`): scenario の Setup と run は scenario 本体の `let` に閉じ込めず、同じファイルの
  fn として公開する(`fn basicSetup() -> Setup`、`fn basicRun(v0: ValidatorId) -> NamedRun`、`twoNodesRun(s, v0, v1)`、`twoFacedRun(v0, v1)` …。
  fn の名前は大域なので scenario ごとに固有にする)。scenario 本体は `let s = basicSetup(); let rho = basicRun(v0);` のようにそれを呼ぶ。
  golden test は生成 Model の `Model.Scenarios.<Mod>.<fn>` から同じ Setup / run を取って手書き Model と突き合わせ、scenario の
  `observe` の行(`naru simulate` の出力)が同じ run の読みと一致することも照合する(`scenario:<name>/observe <label>` の case)。
  `input` 束縛は scenario に閉じているので、golden 側は同じ値を Lean で書き写す(`Golden.G.Inputs`)。走らせ方は [testing.md](testing.md)。
