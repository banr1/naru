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
scenario basic {                                  // runtime の実行 fixture(下の「scenario と simulate」)
  input proposer(slot) = ValidatorId { value: 0 };   //   先頭: 環境の入力に値を与える
  let st = Store { … };                           //   局所束縛
  observe confirmed(st);                          //   出力: observer の呼出しだけ
}
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

## stdlib(組み込みのメソッド表。`Typecheck.lean` が正本、Lean 側の実装は `stdlib/Model/NaruStd`)

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

### 再帰(E002、`Totality.lean`)

IDEAL.md「言語の意味論」: 再帰は構造的再帰・明示 fuel・有限集合の反復のみ。有限集合の反復は stdlib のメソッド
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

## scenario と simulate(C7)

scenario は定理ではなく実行 fixture で、非決定性(`input`)に値を与え、observer を通して値を表示する(IDEAL.md「言語の意味論」「用語」)。

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
- 生成 Lean(backend): `def Model.A.B.basic : List NaruStd.Observation := let proposer' := fun («slot» : Nat) => …; let «v0» := …;
  NaruStd.observe "readsAt(…)" (Model.A.B.readsAt committee' proposer' … «s» «rho» «v0» 30) :: (… :: ([]))`。束縛した input は
  本体の先頭の `let f'`(fn の引数名 `f'` と同じ名前)になり、呼出しがそれを引き回す。observer の戻り型が `List<T>` なら
  `NaruStd.observeList`。`NaruStd.Observation` / `observe` / `observeList` / `runScenario` は `stdlib/Model/NaruStd/Observe.lean`。
- `lake exe naru simulate dsl/scenarios/basic.naru`: `dsl/**/*.naru` 全体を検査して `generated/` に Model を作り直し(`compile` と同じ。
  ファイルは `dsl/` 配下に限る: exit 2。`./dsl/…` とリポジトリの絶対パスは `dsl/…` に正規化する)、そのファイルの scenario(無ければ exit 2)を順に `NaruStd.runScenario` で表示する
  `generated/Simulate.lean`(`main`。C1 のヘッダ付き。追跡対象外)を書き、`lake build naru_simulate`(lakefile の lean_exe。
  Model を native にビルド)→ `.lake/build/bin/naru_simulate` を実行する(「naru を実行する」= 生成 Lean を実行する)。
  出力: `scenario <name>`、scalar は `  <label> = <Repr>`、List は `  <label>:` の下に 1 要素 1 行。値の表示は Lean の `Repr`
  (record は `{ time := 4, node := { value := 0 }, … }`)。
- まだ無いもの: `protocol` 宣言の意味(現状は中の宣言を平坦化するだけ。Node.naru の fn 群を `ProtocolSpec` の hook として束ねる
  のは stdlib の generic な `Event` / `Run` と型引数が入ってから)、observer の表示を naru 風にする `derive repr`、scenario の中の
  配達(deliver)の生成子(いまは `NamedEvent.Deliver` を直接書く)。

## 診断

出力は `file:line:col: error[E0xx]: message`。終了コードは誤りがあれば 1。
反例ソースの検査は `lake exe naru check-reject <file.naru> <Exxx>`(compile と同じ経路を走らせ、
診断があってその中に Exxx があれば PASS で exit 0。`tests/reject/` の条件の証拠はこれで取る)。

| 番号 | 意味 | 実装 |
|---|---|---|
| E001 | phase leak(runtime → spec) | 済(`Resolve.lean`) |
| E002 | 停止性を確認できない再帰(構造的再帰・保護された fuel 以外) | 済(`Totality.lean`) |
| E003 | 無条件の選択(Set の `choose` / `pick` / `first` / `find?` …) | 済(`Typecheck.lean`) |
| E004 | 順序指定の無い Set → List(`toList` / `by` 無しの `sort` / `fold` …) | 済(`Typecheck.lean`) |
| E005 | capability 不足(`==` `<`、eq / order を要する stdlib メソッド、`derive` の欄) | 済(`Typecheck.lean`) |
| E006 | runtime 宣言内の量化(`forall` / `exists`) | 済(`Typecheck.lean`) |
| E007 | runtime 条件の classical 依存 | 未 |
| E010 | 字句・構文の誤り(scenario の input 束縛が先頭にない・末尾の式、も) | 済 |
| E011 | 解決できない名前 | 済 |
| E012 | 同名の宣言(scenario で同じ input を 2 度束縛、も) | 済 |
| E013 | 型の位置に型でない宣言 | 済 |
| E014 | 型の不一致・推論できない型・値でないものの値としての使用(`observe` に observer の呼出し以外、input でないものの束縛、も) | 済 |
| E015 | 無い欄・無いメソッド・引数の数や名前の不一致(閉じていない scenario: 使う input の未束縛・束縛の順序・仮引数の数、も) | 済 |
| E016 | claim bundle の項目が claim でない | 済 |
| E017 | 生成モジュールの構造: モジュール同士の循環参照・同名のモジュール(backend) | 済(`Backend/Model.lean`) |
| E018 | match の腕の形: 最後の腕にガード / `Nat` `Int` `String` の match に無条件の腕が無い(網羅性の穴) | 済(`Typecheck.lean`) |
| E019 | コンテナ(Option / List / Set / Table / Result / tuple)越しに自分に戻る record / enum(Lean の deriving が入れ子の帰納型に使えない) | 済(`Typecheck.lean`) |

名前解決(E011〜E013、E001)に誤りがあれば型検査には進まない(未解決名の波及を避ける)。
型検査(E003〜E006、E014〜E016)に誤りがあれば停止性検査(E002)には進まない(呼出し先の署名が要る)。
診断が 1 つでもあれば backend には進まない(`generated/` は書き換えない)。

E014 には「型が決まらない」も含む: `let` の値・lambda の引数・`[]` / `None` / `Set.empty()` などの空のコレクション・
比較の被演算子の型が、宣言の終わりまでにその使われ方から決まらなければ `cannot infer the type of …; add a type annotation`。

## CLI(`lake exe naru`)

| コマンド | 意味 |
|---|---|
| `compile` | `dsl/**/*.naru`(パス順)を検査し、Model を `generated/` に出力する(`generated/Model.lean` と `generated/Model/**.lean` を作り直す)。C1 の検証コマンド |
| `compile [--out <dir>] <files...>` | 指定ファイルを検査する。`--out` があればそこに Model を出力し、無ければ検査だけ(`checked N module(s)`) |
| `check-reject <file.naru> <Exxx>` | 反例が `Exxx` で拒否されることを検査(PASS で exit 0) |
| `lsp` | 標準入出力で言語サーバー(LSP、JSON-RPC 2.0 の `Content-Length` 枠)として動く(C18。`Naru/Lsp.lean`)。下の「言語サーバー」 |
| `simulate <dsl/…/scenario.naru>` | `dsl/` 全体を検査して `generated/` を作り直し、そのファイルの scenario を native 実行して observer の値を表示する(C7。上の「scenario と simulate」)。診断があれば exit 1、`dsl/` 外・scenario 無しは exit 2、`lake build naru_simulate` の失敗は exit 1、それ以外は実行ファイルの exit code |

リポジトリのルートで実行する(stdlib の hash のために `stdlib/Model` を読む。`lsp` は cwd に依らない)。

### 言語サーバー(`naru lsp`)

Zed 拡張(`editors/zed-naru/`)が起動し、開いた `.naru` の診断を表示する。応じるのは `initialize`(全文同期 `textDocumentSync.change = 1`、
`openClose`、`save`)/ `initialized` / `shutdown` / `exit` と `textDocument/didOpen` / `didChange`(全文)/ `didSave` / `didClose`。
それ以外のリクエストには `MethodNotFound`(-32601)を返し、それ以外の通知(`$/…` 等)は無視する。

- 検査の単位: 文書のパスの祖先に `dsl` という名のディレクトリがあれば、その `dsl/**/*.naru` 全体を 1 つのコンパイル単位にし、
  開いている文書はディスクではなくバッファの内容で検査する(CLI の `compile` と同じ `Driver.compileSources`)。それ以外の文書は単独。
- 診断は `textDocument/publishDiagnostics`。コンパイラの 1 始まりの行・列を 0 始まりに直し、範囲はその位置のトークン 1 つ分
  (識別子・数・文字列・記号)、severity はエラー、`code` は `E0xx`、`source` は `naru`。列は UTF-16 単位(LSP の既定)。
- 他のファイルに出た診断はそのファイルの URI へ送る(開いていないファイルにも)。文書自身には空でも必ず送り、前回その単位で送った
  URI のうち今回空になったものには空を送って消す。`didClose` には空を送り、同じ単位に開いた文書が残っていればディスクの内容で
  検査し直す(その検査では閉じた文書へは送らず空のままにし、次の検査からは開いていないファイルとして扱う)。残っていなければ
  その単位の診断をすべて消す。
- 意味検査はすべてコンパイラ側(この層は診断の運搬だけ: IDEAL.md「不変条件」)。

### エディタ対応の検査(`lake exe naru_test`)

| 群 | 意味 |
|---|---|
| `grammar` | tree-sitter 文法(`editors/tree-sitter-naru/`)の検査(C16): `tree-sitter generate` の出力が追跡対象の `src/` と一致、`tree-sitter build` が exit 0、`dsl/`・`tests/accept/`・`tests/reject/` の全 `.naru`(E010 を期待する反例は除く)が ERROR / MISSING なしに解析できる、`tests/accept/editors_syntax.naru` への `queries/highlights.scm` の捕捉が `tests/accept/editors_syntax.captures` の行に出る、その受理例がコンパイラの検査を通る、`editors/zed-naru/languages/naru/highlights.scm` が `queries/highlights.scm` と同一 |
| `zed` | Zed 拡張(`editors/zed-naru/`)の検査(C17): 5 ファイル(`extension.toml`・`languages/naru/config.toml`・`highlights.scm`・`Cargo.toml`・`src/lib.rs`)がある、`extension.toml` の `id = "naru"`・`[grammars.naru]` の `repository`(このリポジトリの `file://` URL)/ `rev`(40 桁の SHA)/ `path = "editors/tree-sitter-naru"`・`[language_servers.naru]` の `name` と `languages`、`config.toml` の `name` / `grammar` / `path_suffixes` / `language_servers`、`rev` がこのリポジトリのコミットで `git diff --exit-code <rev> HEAD -- editors/tree-sitter-naru` が空、`rev` の文法(`git archive`)を `tree-sitter build` して作業ツリーの `highlights.scm` が `tree-sitter query` でロードできる、`src/lib.rs` が設定 → `PATH` → `.lake/build/bin/naru` の順で `naru lsp` を起動する形、`cargo build --release --target wasm32-wasip2` が exit 0。一時ファイルは `.lake/naru/test/zed/`、cargo の成果物は `editors/zed-naru/target/` |
| `lsp` | 言語サーバー `naru lsp` の検査(C18): `lake build naru` の後、子プロセスの `.lake/build/bin/naru lsp` と LSP を話す。`initialize` の応答に全文同期がある、未対応のリクエスト(`textDocument/hover`)が `MethodNotFound`(この応答を、通知の処理の終わりを待つ barrier にも使う)、`tests/reject/` の各反例の `didOpen` で `naru compile` と同じ E 番号・行・列の診断(先頭コメントが名指しする E 番号を含む)がその URI に返り `didClose` で空になる、絵文字を含む単独文書で列が UTF-16 単位・範囲がトークン 1 つ分、`dsl/` の全ファイルの `didOpen` で 0 件、`dsl/Consensus/Objects/Time.naru` の `didChange` で末尾に足した未解決名の E011 がその行に出る・`slotStart` の改名で他のファイル(Parameters / Grades)の URI に E011 が出る・壊れたまま Parameters を `didClose` すると空のまま・開き直すと戻る・Time を戻すと消える、`didSave` で 0 件のまま、全ファイルの `didClose` で空、`shutdown` が `null`、`exit` で exit 0。期待値はコンパイラ(`compileSources`)から取る |
| `zed-install` | 起動中の人間の Zed に `editors/zed-naru/` を Dev Extension として入れる(C19): `lake build naru` の後、`~/Library/Application Support/Zed/extensions/installed/naru` が無ければ `zed: install dev extension`(フォルダ選択ダイアログに ⌘⇧G でパスを貼る)、この拡張への symlink なら `zed: rebuild dev extension`(Dev Extension が 2 つ以上なら picker で `naru`)を `osascript`(System Events。文字列はクリップボード経由、前面が Zed であることを確かめてから送る)で実行し、`Zed.log` に操作の開始以後 `compiled grammar naru`・`finished compiling extension <installed/naru>`(install では Zed は拡張のソースのパスで記録するのでそれも受理)・`extensions updated.` の `loading 1` / `reloading 1` が足され、`failed to compile` / `Failed to install dev extension` が 0 件、`installed/naru` が `editors/zed-naru` への symlink、`extension.wasm` と `grammars/naru.wasm` の mtime が操作の開始以後、`grammars/naru/` の checkout が `extension.toml` の `rev`。`grammars/naru.wasm` は操作の前に消す(Zed は `parser.c` より新しい wasm があると文法のコンパイルを飛ばす)。スクリーンショットと AppleScript は `.lake/naru/test/zed-install/` |

## エディタ対応(tree-sitter 文法)

`editors/tree-sitter-naru/grammar.js` は、この文書とパーサを正本として追従させるハイライト用の第二のパーサ(IDEAL.md「不変条件」)。
意味検査(型・phase・停止性)は持たず、診断はすべて `naru lsp` を通してコンパイラが出す。**構文を増やす周回は、この文書・`Parser.lean` と
同じ周回で `grammar.js` も直し、`tree-sitter generate` で `src/`(追跡対象。手で編集しない)を作り直して `lake exe naru_test grammar` を通す。**
`tests/accept/editors_syntax.naru` は全構文の受理例なので、新しい構文はここにも足し(`lake exe naru compile` が exit 0 のまま)、
捕捉の期待値 `tests/accept/editors_syntax.captures`(行番号・捕捉名・字句)も直す。

正本との既知の差(ハイライト用なので広く受理する側に倒してある): 入れ子のブロックコメントは深さ 9 まで(字句が正規表現のため)、
予約語 `in` は構文に現れないので予約できない(他の 28 語は予約)、`match` の腕の `,` は常に省略可、`if` / `match` の頭部の `Name { … }` は
GLR で record literal とブロックの両方を試す。

Zed 拡張(`editors/zed-naru/`、C17)は文法をこのリポジトリの `extension.toml` の `rev`(コミット SHA)から取るので、**文法を変えた周回は
`rev` を動かせない**(その周回のコミットがまだ無い)。その周回では `highlights.scm` を `rev` の文法でもロードできる形に保ち(新しい node を
参照する捕捉は次の周回に回す)、次の周回で `rev` を直前の周回のコミット(`git log -1 --format=%H -- editors/tree-sitter-naru`)に付け替えて
`lake exe naru_test zed` を通す(IDEAL.md「前提」の「周回の運び」)。

node の名前(`queries/highlights.scm` が使う): 宣言は `<kind>_declaration`(`name` 欄)、型は `type_identifier` / `named_type` /
`tuple_type` / `function_type`、大域経路は `path_expression`(前置の段は `type_identifier`、最後の段は `constructor_identifier` か
`identifier`)、record literal は `record_literal`(`type_path` + `field_initializer` / `base_initializer`)、欄は `field_identifier`、
メソッドは `method_call_expression`(`method_identifier`)、構築子は `constructor_identifier`、モジュール経路は `module_identifier`、
`derive` の capability は `capability`。scenario の本体は `scenario_body`(`input_binding`(`name` / `parameters` = `binding_parameters` /
`value`)、`let_statement`、`observe_statement`(`value`))。予約語 `observe` と `input_binding` の捕捉(`@keyword` / `name` の `@function` /
`binding_parameters` の `@variable.parameter`)は、Zed 拡張の `rev` がこの文法を指す周回で `highlights.scm` に足す(下の「周回の運び」)。

## Core IR と Model backend

型検査(`Typecheck.lean`)は検査と同時に Surface AST を Typed Core IR(`Core.lean`)に elaborate する。名前は解決済み、
UFCS と名前付き引数は展開済み、ブロックは `let` の入れ子、型が要る位置には解決済みの型を持つ。backend は Core だけを読む。

Model backend(`Backend/Model.lean`)は runtime 宣言だけを Lean に落とす(spec 宣言は Statements backend の仕事)。

| naru | 生成 Lean |
|---|---|
| `module A.B` | ファイル `generated/Model/A/B.lean`、Lean モジュール `Model.A.B`。宣言は `Model.A.B.name` と完全修飾で参照。他モジュールの参照は `import`(循環は E017) |
| `type T = U` | `abbrev Model.A.B.T : Type := U`(参照は展開した型で書く) |
| `record` / `state` | `structure … deriving DecidableEq, Ord, Repr`(`derive eq` → `DecidableEq` + `Ord`、`derive order` → `Ord`。`Repr` は常に。`finite` はまだ何も生成しない。`Ord` は `Set` / `Table` の正規化に使う隠れた全順序で、欄・variant の宣言順の辞書式)。欄名と局所名は常に `«»` で囲む(予約語の一覧に頼らない) |
| `enum` | `inductive`(variant の引数は `a0 a1 …`) |
| `fn` / `observer` | `def`。再帰は `Totality` の測度で `termination_by n` + `decreasing_by`(fuel)/ `termination_by structural p`(構造的)。相互再帰は `mutual … end` |
| `scenario` | `def … : List NaruStd.Observation`。先頭の input 束縛は `let f' : (T → U) := fun («x» : T) => …`、`let` は `let`、`observe e;` は `NaruStd.observe "<ソースの式>" e ::`(observer の戻り型が `List` なら `observeList`)、末尾は `[]`(「scenario と simulate」) |
| `input f(x: T) -> U` | Lean の宣言にならない。それを(推移的に)使う fn / observer の先頭の引数 `f'`(名前 + `'`)になり、呼出しで引き回す。scenario は束縛した input を同名の `let f'` で与える(束縛していない input は E015 で退ける) |
| 型 | `Nat Int Bool String Unit` はそのまま、`Option<T>` → `Option T`、`List<T>` → `List T`、`Result<T, E>` → `NaruStd.Result T E`、`Set<T>` → `NaruStd.Set T`、`Table<K, V>` → `NaruStd.Table K V`、tuple → `×`。引数 0 個の関数型は値として扱う(`f()` は `f`) |
| `==` `<` 等 | `==` / `!=` はそのまま。`<` 等は `Nat` / `Int` / `String` なら `Decidable.decide (a < b)`、他は `Ord.compare a b == .lt` 等(`Ord` だけで決める)。生成コードが使う Lean の組み込み名は完全修飾し(`Option.some` / `Min.min` …)、naru の局所名に捕獲されない |
| stdlib メソッド | `stdlib/Model/NaruStd/*.lean` の関数(`Set` / `Table` は要素の `Ord` で昇順に正規化した重複なしリスト。`DecidableEq` が集合の等しさに一致する)と Lean core の `List` / `Option` |
| `match` のガード | Lean に無いので、最初のガード付き腕 i の前の腕はそのまま、`\| _ =>` の中で `match (match s with \| p_i => if g then some b else none \| _ => none) with \| some g' => g' \| none => REST`(REST = i 以外の腕の match。`p_i` が必ず一致する形 — `_` / 変数 / `()` / variant 1 つだけの enum — なら `\| _ => none` は出さない)。再帰 fn の `Nat` の match にガードがあれば `if _h' : v == k && g then … else …` の連鎖 |
| 再帰 fn の `if` と `Nat` の `match` | `if _h' : c then`(事実を証明に残す。`_h'` は naru で書けない名前)。`Nat` の局所変数 v の match は `match _hm' : v with`(等式を証明に残す)にし、bind / `_` の腕は `_ + m`(m = 先行するガード無しリテラル腕が 0 から覆った値の次。m = 0 なら `_`)+ `let k : Nat := v`(束縛名は match の変数にせず別名にする) |

生成ファイルの先頭 5 行はコメント: `naru-compiler: <版> sha256:<compiler/**/*.lean の hash>`、`naru-stdlib: <版> sha256:<stdlib 全ファイルの hash>`、
`naru-source: <ファイル> sha256:<そのファイルの hash>`、`naru-unit: sha256:<全ソースの hash>`。
同じソースと stdlib からは同じバイト列を生成する(表の反復順・時刻・環境に依存しない)。

既知の制限(backend): naru は enum / Option / Bool / tuple の match の網羅性を検査しないので、網羅していない match は
Lean が拒否する(E018 が最後の腕のガードと Nat / Int / String の穴を塞ぐので、生成コードの `panic!` は到達しない位置にだけある)。
到達しない腕(先行する腕が必ず一致する)は Lean の「redundant alternative」で拒否される。ガード 1 つにつき残りの腕が
2 回生成される。ヘッダとコメントにはソースのパスが渡された文字列のまま入る(既定の `compile` は `dsl/…` の相対パス)。

## まだ無いもの

E007・Statements backend(predicate / … / claim bundle は生成しない)・`protocol` 宣言の意味と stdlib の generic な `Event` / `Run`
(「scenario と simulate」)・`import` の意味(現状は全ファイルが 1 つの大域表。backend は参照からモジュールの依存を計算する)・
型引数付きのユーザ宣言(`record R<T>`)・関数を返す fn と関数を持つ record(関数型は仮引数にだけ)・`let` のパターン(`let (a, b) = …`)・
Constants と interface binding の構文・naru で書いた stdlib(現状は上の表と Lean 側の `NaruStd`)・`derive finite` / `derive repr` の生成・
enum / Option / Bool / tuple の match の網羅性検査(Lean に任せている)。
