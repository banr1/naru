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

名前解決(E011〜E013、E001)に誤りがあれば型検査には進まない(未解決名の波及を避ける)。
型検査(E003〜E006、E014〜E016、E018、E019)に誤りがあれば停止性検査(E002)には進まない(呼出し先の署名が要る)。
診断が 1 つでもあれば backend には進まない(`generated/` は書き換えない)。

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
| E014 | 型の不一致・推論できない型・値でないものの値としての使用(`observe` に observer の呼出し以外、input でないものの束縛、も) | 済 |
| E015 | 無い欄・無いメソッド・引数の数や名前の不一致(閉じていない scenario: 使う input の未束縛・束縛の順序・仮引数の数、も) | 済 |
| E016 | claim bundle の項目が claim でない | 済 |
| E017 | 生成モジュールの構造: モジュール同士の循環参照(runtime の参照は Model、spec の参照は Statements)・同名のモジュール(backend) | 済(`Backend/Model.lean`、`Backend/Statements.lean`) |
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

モジュール同士の循環参照(runtime の参照は Model、spec の参照は Statements)と同名のモジュール。backend の段で出る。

```
// A.naru
module A
fn a() -> Nat { b() }         // A → B

// B.naru
module B
fn b() -> Nat { a() }         // B → A(循環)
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
