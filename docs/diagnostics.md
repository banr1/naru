# naru 診断一覧

コンパイラが出す診断 E001〜E019(E007 の次は E010 で、間の番号は使っていない)の意味・出す段・最小の例。文法は [language.md](language.md)、段の並びは [architecture.md](architecture.md)。

## 出力の形

```
file:line:col: error[E0xx]: message
```

行・列は 1 始まり。終了コードは誤りがあれば 1。

反例ソースの検査は `lake exe naru check-reject <file.naru> <Exxx>`。`compile` と同じ経路を走らせ、診断があってその中に指定した E 番号があれば PASS で exit 0(無ければ exit 非 0)。
`tests/reject/` の条件の証拠はこれで取る([testing.md](testing.md))。コマンドの全体は [cli.md](cli.md)。

## 段と進み方

構文解析の後、同名のモジュール(E017)があれば名前解決には進まない(大域表の鍵がモジュール名で決まる)。
名前解決(E011〜E013、E001)に誤りがあれば型検査には進まない(未解決名の波及を避ける)。
型検査(E003〜E006、E014〜E016、E018、E019)に誤りがあれば Core の健全性の検査・モジュールの循環(E017)・停止性検査(E002)には進まない(呼出し先の署名が要る)。
診断が 1 つでもあれば backend には進まない(`generated/` は書き換えない)。すべての診断は生成前の共通の検査が出すので、CLI の `compile`
(出力指定あり / なし)と言語サーバー `naru lsp` は同じ入力・コンパイル単位に同じ診断を同じ行・列に出す(`compile --out` も診断があれば何も書かない)。

## 一覧

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
| E014 | 型の不一致・推論できない型・値でないものの値としての使用(`observe` に observer の呼出し以外、input でないものの束縛、型別名を含む型名の値使用と record でない型へのレコードリテラル、spec 宣言で Prop 相当の式(量化・spec 宣言の呼出し・Prop に束ねた局所名)を Bool の値が要る位置に書く、も) | 済 |
| E015 | 無い欄・無いメソッド・引数の数や名前の不一致(閉じていない scenario: 使う input の未束縛・束縛の順序・仮引数の数、も) | 済 |
| E016 | claim bundle の項目が claim でない | 済 |
| E017 | 生成モジュールの構造: 同名のモジュール(各ファイルの `module` 行)・モジュール同士の循環参照(runtime 宣言の参照は生成 Model、spec 宣言の参照は生成 Statements の import の循環。循環に関与する参照の位置) | 済(`Modules.lean`。生成前の共通検査。backend の検査は安全網) |
| E018 | match の腕の形: 最後の腕にガード / `Nat` `Int` `String` の match に無条件の腕が無い(網羅性の穴) | 済(`Typecheck.lean`) |
| E019 | コンテナ(Option / List / Set / Table / Result / tuple)越しに自分に戻る record / enum(Lean の deriving が入れ子の帰納型に使えない) | 済(`Typecheck.lean`) |

E014 には「型が決まらない」も含む: `let` の値・lambda の引数・`[]` / `None` / `Set.empty()` などの空のコレクション・
比較の被演算子の型が、宣言の終わりまでにその使われ方から決まらなければ `cannot infer the type of …; add a type annotation`。

## 例

`tests/reject/` に反例があるものは、そのファイルを要約した。無いものは表の意味から最小の例を書いた。

### E001 phase leak

runtime 宣言(fn)が spec 宣言(predicate)を参照する。メソッド記法 `s.tall()` も `tall(s)` の糖衣なので同じ(`tests/reject/phase_leak.naru`、`phase_leak_method.naru`)。

```
predicate Tall(s: Store) { s.height > 3 }

fn bump(s: Store) -> Store {
  if Tall(s) { s } else { Store { height: s.height + 1 } }   // E001
}
```

### E002 停止性を確認できない再帰

引数が小さくならない再帰(`tests/reject/non_total.naru`)。受理される形は [language.md](language.md) の「再帰」。

```
fn spin(n: Nat) -> Nat {
  spin(n)                     // E002
}
```

### E003 無条件の選択

Set の `choose` / `pick` / `first` / `find?` …(`tests/reject/choose.naru`)。

```
record Committee { members: Set<Nat> } derive eq

fn leader(c: Committee) -> Option<Nat> {
  c.members.first?()          // E003
}
```

### E004 順序指定の無い Set → List

`toList` / `by` 無しの `sort` / `fold` …(`tests/reject/order_loss.naru`)。`sort(by = …)` なら通る。

```
fn roster(c: Committee) -> List<Nat> {
  c.members.toList()          // E004
}
```

### E005 capability 不足

`derive eq` の無い型への `==`(`tests/reject/missing_capability.naru`)。

```
record Vote { slot: Nat, voter: Nat }       // derive なし

fn same(a: Vote, b: Vote) -> Bool {
  a == b                      // E005
}
```

### E006 runtime 宣言内の量化

```
fn allBelow(n: Nat) -> Bool {
  forall k: Nat { k < n }     // E006(forall / exists は spec 宣言専用)
}
```

### E007 runtime 条件の classical 依存

未実装。この番号を出す検査はまだ無い。

### E010 字句・構文の誤り

```
fn f(x: Nat) -> Nat {
  let Y = x;                  // E010(局所名は小文字か `_` で始める)
  x
}
```

scenario で `input` の束縛を `let` の後ろに置く、末尾に式を置く、も E010。

### E011 解決できない名前

型の位置の `Nat.X` のような経路も(`tests/reject/type_path_escape.naru`)。

```
fn f(x: Nat) -> Nat { g(x) }  // E011(g は無い)
```

### E012 同名の宣言

```
fn f() -> Nat { 1 }
fn f() -> Nat { 2 }           // E012
```

組み込み名(`Some` `Option` `choose` …)の再宣言、scenario で同じ input を 2 度束縛する、も。

### E013 型の位置に型でない宣言

```
fn g() -> Nat { 1 }
fn f(x: g) -> Nat { 1 }       // E013(g は fn であって型ではない)
```

### E014 型の不一致・推論できない型

関数型を欄・variant・戻り型・コレクションの中に書く場合も(`tests/reject/fn_type_position.naru`)。

```
fn f(x: Nat) -> Bool { x }    // E014
record Scorer { score: (Nat) -> Nat }   // E014
fn g() -> Nat { let xs = []; 0 }        // E014(xs の型が決まらない。`cannot infer the type of …`)
```

spec 宣言の中で、Prop 相当の式(量化・spec 宣言の呼出し・`let` で Prop に束ねた局所名)を実行可能な Bool の値が要る位置
(fn / stdlib メソッドの実引数・コレクションの要素・record の欄・Bool を要求する lambda の戻り値・`match` の scrutinee・算術 / 比較の被演算子)に
書く場合と、Prop の条件や Prop のガードで Bool 以外の値を選ぶ場合も E014(`tests/reject/prop_as_value.naru`。Prop は Bool に戻せず、naru は量化も
spec 宣言も決定しない。置ける位置は [language.md](language.md)「Prop と Bool」)。

```
predicate truthLost(rho: Run) { boolId(forall b: Block { … }) }            // E014(量化は Bool の値にならない: 真偽が失われる)
predicate P(rho: Run) { rho.blocks.all(|b| Below(b, 10)) }                 // E014(lambda の戻り値に spec 宣言の呼出し)
predicate Q(rho: Run) { let n = if AllHonest(rho) { 1 } else { 2 }; n > 0 }   // E014(Prop の条件で Nat を選ぶ)
```

型名(型別名 `type Count = Nat` の `Count` を含む)を値に使う場合と、record / state でない型へのレコードリテラルも E014
(`tests/reject/type_name_as_value.naru`)。

```
type Count = Nat
fn f(x: Count) -> Count { x + Count }   // E014(型別名は値ではない)
fn g() -> Count { Count {} }            // E014(Count は record ではない)
```

### E015 無い欄・無いメソッド・引数の不一致

```
record P { x: Nat }
fn f(p: P) -> Nat { p.y }     // E015(欄 y は無い)
```

位置引数を名前付き引数の後ろに置く、構築子の引数の数が違う、使う input を束縛していない scenario、も。

### E016 claim bundle の項目が claim でない

```
fn helper() -> Nat { 1 }
claim bundle Guarantees { helper }   // E016(fn は項目にできない)
```

### E017 生成モジュールの構造

同名のモジュールと、モジュール同士の循環参照(runtime 宣言の参照は生成 Model の import、spec 宣言の参照は生成 Statements の import になる)。
生成前の共通検査(`compiler/Naru/Modules.lean`)が出すので、CLI と言語サーバーが同じ行・列に出す。複数ファイルの検体は `tests/units/reject/`
(`module_duplicate` / `runtime_cycle` / `spec_cycle` / `inferred_cycle` / `omitted_duplicate`。[testing.md](testing.md))。

- 同名のモジュール: 同じ名前を宣言するすべてのファイルの `module` 行(名前の位置)に 1 つずつ。メッセージが他の所在を列挙する。出力の省略
  (Model ファイルを出さない spec だけのモジュールなど。C38)にかかわらず全入力が対象で、`naru compile` のソースルートが複数ならルートをまたぐ同名も
  (全ルートの module を束ねて)同じ検査で出す(`tests/units/roots/duplicate_across_roots`。言語サーバーの単位は 1 つのルート)。
- 循環の辺を作るのは、出力される宣言への参照だけ。input への参照は辺にならない(input は Lean の宣言にならず、その宣言元のモジュールは import しない。
  input の署名が参照する型のモジュールへの依存は辺になる)。
- 循環: 循環に関与する辺 `A → B`(`A` の宣言が `B` の宣言を参照し、`B` から `A` に戻れる)ごとに、`A` の中でその参照を作る最初の宣言の、
  `B` への最初の参照(呼出し・型の位置の名前など)の行・列に 1 つ。メッセージが宣言と参照先、循環の経路を示す。循環のすべての辺に出るので、
  どれか 1 つの辺を解消すれば関係するファイルすべての診断が消える(言語サーバーでは `didChange` で関係する URI すべてが空になる)。
  参照が構文上その宣言に現れない依存(推論された型 — `make().x` の record や呼出しの結果の型 — や、使う input の署名を通した依存)は
  その宣言の名前の位置に出る(`inferred_cycle` の `width`)。

```
// Alpha.naru
module Alpha
record Point { x: Nat } derive eq
fn shifted(n: Nat) -> Nat { bump(n) }          // E017(`bump` の位置: Alpha → Beta)

// Beta.naru
module Beta
fn bump(n: Nat) -> Nat { n + 1 }
fn origin(n: Nat) -> Point { Point { x: n } }  // E017(戻り型 `Point` の位置: Beta → Alpha で循環)

// Same1.naru / Same2.naru
module Units.Same                              // E017(両方のファイルの module 行)
```

### E018 match の腕の形

最後の腕にガード、または `Nat` `Int` `String` の match に無条件の腕が無い(`tests/reject/match_shape.naru`)。

```
fn lastGuarded(s: Shape) -> Nat {
  match s {
    Shape.Dot => 0,
    Shape.Line(a, b) if a > b => a - b,   // E018(最後の腕にガード)
  }
}

fn pick(n: Nat) -> Nat {
  match n { 0 => 1, 1 => 2 }              // E018(`_` の腕が無い)
}
```

### E019 コンテナ越しの再帰型

`tests/reject/nested_recursion.naru`。

```
record Chain { next: Option<Chain> }      // E019
enum Rose { Node(Nat, List<Rose>) }       // E019(rose tree は相互再帰の enum で書く)
```
