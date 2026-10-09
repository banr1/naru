# naru コンパイラの構成

コンパイラのパイプライン、Typed Core IR、Model backend と Statements backend の対応表、生成ファイルのヘッダと決定性。
文法は [language.md](language.md)、診断は [diagnostics.md](diagnostics.md)、コマンドは [cli.md](cli.md)。

## パイプライン

```
Parser → Surface AST
  → 同名のモジュール            (Modules.lean:   E017)
  → 名前解決・phase 検査        (Resolve.lean:   E001, E011〜E013。解決した参照の索引 `Resolve.Ref` も作る)
  → 型・capability 検査 + Core IR への elaboration
                                (Typecheck.lean: E003〜E006, E014〜E016, E018, E019)
  → Core の健全性               (Driver.lean:    E014「internal」。C35)
  → モジュールの循環            (Modules.lean:   E017。生成 Model / Statements の import グラフ)
  → 停止性検査                  (Totality.lean:  E002)
  → Model backend               (Backend/Model.lean)
  → Statements backend          (Backend/Statements.lean)
```

前の段に誤りがあれば次の段には進まない。診断が 1 つでもあれば backend には進まず、`generated/` は書き換えない。
入口は `compiler/Naru/Driver.lean` の `compileFiles`(指定ファイル)/ `compileSources`(ソースルート。`naru lsp` はバッファの内容でこれを呼ぶ)。
すべての診断は backend より前の共通の検査が出すので、CLI の `compile`(出力指定あり / なし)と言語サーバーは同じ入力・コンパイル単位に同じ診断を
同じ行・列に出す(C18)。
型検査を診断なしに通った Core には、推論用のメタ変数・誤りの波及を抑える「不明」の型・エラー用ノードが残ってはならない(型検査は誤りを診断してから
それらを作る)。`compileSources` は停止性検査の前に Core の全宣言を再帰的に走査し(`Core.Decl.unsound`)、残っていればコンパイラの不変条件の破れとして
E014 を出して backend に渡さない(C35。`naru_test regression` は全受理例と移植ソースの Core で 0 件を確かめる)。
モジュール構造(`Modules.lean`): 同名のモジュールは構文解析の直後に各ファイルの `module` 行へ、循環は Core と参照の索引から、生成 Model の import グラフ
(`Backend.Model.modelGraph`: 出力する runtime 宣言が参照する他のモジュール)と生成 Statements の import グラフ(`Backend.Statements.specGraph`: spec 宣言が
参照する他のモジュールの spec 宣言)のそれぞれで、循環に関与する辺ごとに参照元の宣言の中の参照先モジュールへの最初の参照の行・列へ E017 を出す
(参照が構文上その宣言に現れない依存 — 推論された型(欄の参照の record・呼出しの結果の型)や使う input の署名を通したもの — は宣言の名前の位置)。
グラフは backend が import を書くのと同じ関数で計算する(生成の規則を変えれば検査も揃う)。backend に残る同名・循環の検査は安全網で、届かない。

## Core IR と Model backend

型検査(`Typecheck.lean`)は検査と同時に Surface AST を Typed Core IR(`Core.lean`)に elaborate する。名前は解決済み、
UFCS と名前付き引数は展開済み、ブロックは `let` の入れ子、型が要る位置には解決済みの型を持つ。backend は Core だけを読む。

Model backend(`Backend/Model.lean`)は runtime 宣言だけを Lean に落とす(spec 宣言は下の「Statements backend」)。

| naru | 生成 Lean |
|---|---|
| `module A.B` | ファイル `generated/Model/A/B.lean`、Lean モジュール `Model.A.B`。宣言は `Model.A.B.name` と完全修飾で参照。他モジュールの参照は `import`(循環と同名のモジュールは生成前の共通検査が E017 で退ける) |
| `type T = U` | `abbrev Model.A.B.T : Type := U`(参照は展開した型で書く) |
| `record` / `state` | `structure … deriving DecidableEq, Ord, Repr`(`derive eq` → `DecidableEq` + `Ord`、`derive order` → `Ord`。`Repr` は常に。`finite` はまだ何も生成しない。`Ord` は `Set` / `Table` の正規化に使う隠れた全順序で、欄・variant の宣言順の辞書式)。欄名と局所名は常に `«»` で囲む(予約語の一覧に頼らない) |
| `enum` | `inductive`(variant の引数は `a0 a1 …`) |
| `fn` / `observer` | `def`。再帰は `Totality` の測度で `termination_by n` + `decreasing_by`(fuel)/ `termination_by structural p`(構造的)。相互再帰は `mutual … end` |
| `scenario` | `def … : List NaruStd.Observation`。先頭の input 束縛は `let f' : (T → U) := fun («x» : T) => …`、`let` は `let`、`observe e;` は `NaruStd.observe "<ソースの式>" e ::`(observer の戻り型が `List` なら `observeList`)、末尾は `[]`([language.md](language.md)「scenario と observer」) |
| `input f(x: T) -> U` | Lean の宣言にならない。それを(推移的に)使う fn / observer の先頭の引数 `f'`(名前 + `'`)になり、呼出しで引き回す。scenario は束縛した input を同名の `let f'` で与える(束縛していない input は E015 で退ける) |
| 型 | `Nat Int Bool String Unit` はそのまま、`Option<T>` → `Option T`、`List<T>` → `List T`、`Result<T, E>` → `NaruStd.Result T E`、`Set<T>` → `NaruStd.Set T`、`Table<K, V>` → `NaruStd.Table K V`、tuple → `×`。引数 0 個の関数型は値として扱う(`f()` は `f`) |
| `==` `<` 等 | `==` / `!=` はそのまま。`<` 等は `Nat` / `Int` / `String` なら `Decidable.decide (a < b)`、他は `Ord.compare a b == .lt` 等(`Ord` だけで決める)。生成コードが使う Lean の組み込み名は完全修飾し(`Option.some` / `Min.min` …)、naru の局所名に捕獲されない |
| stdlib メソッド | `stdlib/Model/NaruStd/*.lean` の関数(`Set` / `Table` は要素の `Ord` で昇順に正規化した重複なしリスト。`DecidableEq` が集合の等しさに一致する)と Lean core の `List` / `Option` |
| `match` のガード | Lean に無いので、最初のガード付き腕 i の前の腕はそのまま、`\| _ =>` の中で `match (match s with \| p_i => if g then some b else none \| _ => none) with \| some g' => g' \| none => REST`(REST = i 以外の腕の match。`p_i` が必ず一致する形 — `_` / 変数 / `()` / variant 1 つだけの enum — なら `\| _ => none` は出さない)。REST は `p_i` の腕の外に置くので、`p_i` の束縛はその腕のガードと本体だけで有効で、REST の同名の外側の束縛(仮引数・`let`・scrutinee の中の名前)を捕捉しない(C34)。再帰 fn の `Nat` の match にガードがあれば `if _h' : v == k && g then … else …` の連鎖 |
| 再帰 fn の `if` と `Nat` の `match` | `if _h' : c then`(事実を証明に残す。`_h'` は naru で書けない名前)。`Nat` の局所変数 v の match は `match _hm' : v with`(等式を証明に残す)にし、bind / `_` の腕は `_ + m`(m = 先行するガード無しリテラル腕が 0 から覆った値の次。m = 0 なら `_`)+ `let k : Nat := v`(束縛名は match の変数にせず別名にする)。ガード付きの束縛の腕 `k if g => b` の `if` の連鎖では、別名はその腕の中にだけ置く: `if _h' : (let k := v; g) then let k := v; b else REST`(`let` を `if` の前に出すと REST で `k` が外側の同名の束縛を隠す: C34。`decreasing_by` の `simp_all` が `_h'` の `let` を展開する) |

scenario の生成例: `def Model.A.B.basic : List NaruStd.Observation := let proposer' := fun («slot» : Nat) => …; let «v0» := …;
NaruStd.observe "readsAt(…)" (Model.A.B.readsAt committee' proposer' … «s» «rho» «v0» 30) :: (… :: ([]))`。束縛した input は
本体の先頭の `let f'`(fn の引数名 `f'` と同じ名前)になり、呼出しがそれを引き回す。`NaruStd.Observation` / `observe` / `observeList` / `runScenario` は
`stdlib/Model/NaruStd/Observe.lean`。

### 生成ファイルのヘッダと決定性

生成ファイルの先頭 5 行はコメント: `naru-compiler: <版> sha256:<compiler/**/*.lean の hash>`、`naru-stdlib: <版> sha256:<stdlib 全ファイルの hash>`、
`naru-source: <ファイル> sha256:<そのファイルの hash>`、`naru-unit: sha256:<全ソースの hash>`。
`naru-source:` のパスはソースルートからの相対パス(`Consensus/Objects/Time.naru`。`specs/consensus/` を含まない)。
同じソースと stdlib からは同じバイト列を生成する(表の反復順・時刻・環境に依存しない)。stdlib / コンパイラの hash はリポジトリのルート(ホーム。
実行ファイル `<ルート>/.lake/build/bin/naru` の場所から求める)相対のパスで計算するので、cwd にも依らない。

生成先と Lake: 生成先は `naru.toml` の `generated`(既定 `generated/`)で、`naru compile` / `naru simulate` は書き終えた生成先への symlink を
`<ルート>/.lake/naru/generated` に置く。`lakefile.toml` の lean_lib `Model` / `Statements` の `srcDir` はこの link なので、`lake build Model` /
`lake build Statements` / `naru_simulate` は現在の設定の生成先を読む(C24。[cli.md](cli.md) の naru.toml)。

既知の制限(backend): naru は enum / Option / Bool / tuple の match の網羅性を検査しないので、網羅していない match は
Lean が拒否する(E018 が最後の腕のガードと Nat / Int / String の穴を塞ぐので、生成コードの `panic!` は到達しない位置にだけある)。
到達しない腕(先行する腕が必ず一致する)は Lean の「redundant alternative」で拒否される。ガード 1 つにつき残りの腕が
2 回生成される。ヘッダとコメントにはソースのパスがソースルートからの相対パス(`compile` の引数のファイルは渡された文字列のまま)で入る。

## Statements backend(`generated/Statements`)

Statements backend(`Backend/Statements.lean`)は spec 宣言だけを Lean に落とす。naru モジュール `A.B` に spec 宣言があれば
ファイル `generated/Statements/A/B.lean`(Lean モジュール `Statements.A.B`)になり、ルート `generated/Statements.lean` がそれらを import する。
生成 Statements が import するのは `NaruStd`・生成 Model(`Model.A.B`)・他の生成 Statements(`Statements.X.Y`。循環は生成前の共通検査が E017 で退ける)だけで、
Proofs は決して import しない(IDEAL.md「不変条件」の依存方向 Model ← Statements ← Proofs。C8 の検査は `lake exe naru_test statements`、[testing.md](testing.md))。
`lake build Statements` でビルドする。

| naru | 生成 Lean |
|---|---|
| `predicate` / `condition` / `regime` / `property` / `claim` | `def Statements.A.B.name (params) : Prop := …`。本体は Bool の式を Prop に読み替える(下)。再帰(`Totality` が受理した明示 fuel / 構造的再帰)は Model と同じ `if _h' :`・`match _hm' :` と `_ + m`・`termination_by` / `decreasing_by`(ガード付きの `Nat` の match を fuel に使う形(Model の `if` の連鎖)はまだ出さない) |
| `claim bundle C { a, b: claimX, nested: D }` | `structure Statements.A.B.C : Prop where` の欄 `a : ∀ (params of a), Statements.A.B.a params`(仮引数が無ければ `Statements.A.B.a`)、`b : ∀ …, Statements.A.B.claimX …`、`nested : Statements.A.B.D`。欄名は項目のラベル(claim surface。C9 はこの欄名を数える) |
| `input` | Model と同じく Lean の宣言にならない。それを(推移的に)使う spec 宣言は先頭に引数 `name'` を持ち、呼出しで引き回す。claim bundle は項目が使う input の和を引数に持つ(`structure Consensus (awake' : …) (proposer' : …) : Prop`) |
| `&&` `\|\|` `!` `implies` | `∧` `∨` `¬` `→` |
| `==` `!=` | `a = b` / `a ≠ b`。どちらかが Prop(量化・spec 宣言の呼出し・Prop に束ねた局所名を含む)なら `↔` / `¬ (… ↔ …)` |
| `<` `<=` `>` `>=` | `Nat` / `Int` / `String` は `<` `≤` `>` `≥`、他の `order` 型は `Ord.compare a b = Ordering.lt` / `≠ Ordering.gt` / `= Ordering.gt` / `≠ Ordering.lt`(Model と同じく `Ord` だけで決める) |
| `forall x: T { … }` / `exists x: T { … }` | `∀ («x» : T), …` / `∃ («x» : T), …` |
| `true` / `false` | `True` / `False` |
| spec 宣言の呼出し `P(x)` | `Statements.A.B.P x`(Prop) |
| それ以外の Bool の値(fn の呼出し、stdlib の `all` / `any` / `contains` / `isEmpty` …、欄、局所名、Bool の `let`) | `(e) = true`(`e` は Model backend と同じ Lean) |
| `if c { a } else { b }` | 条件が Bool の値なら `if c = true then a else b`(再帰する宣言では `if _h' : c = true then`)、条件が Prop なら `(c → a) ∧ (¬ c → b)` |
| `let x = e; body` | `let «x» : T := e`(値)。型が Bool で `e` が Prop を含むなら `let «x» : Prop := e` とし、以後 `x` は Prop として読む |
| `match` | 腕の本体を Prop にする。ガードは Model と同じ構造: 最初のガード付き腕 i より前の腕はそのまま、`\| _ =>` の中で `(match s with \| p_i => g → b \| _ => True) ∧ (¬ (match s with \| p_i => g \| _ => False) → REST)`(REST = i 以外の腕の match。`p_i` が必ず一致する形なら `\| _ => …` は出さない)。REST はどの腕の中にも置かないので、`p_i` の束縛はその腕のガードと本体だけで有効で、REST の同名の外側の束縛(仮引数・`let`・scrutinee の中の名前)を捕捉しない(C34。検体は `tests/accept/guard_shadow.naru`、検査は `lake exe naru_test regression`)。scrutinee とガードが 2 回現れ、到達しない腕は Lean が拒否する(Model と同じ既知の制限) |
| 値の位置(fn / メソッドの実引数・欄・コレクションの要素・lambda の本体・scrutinee・算術 / 比較の被演算子 …)の式 | Model backend と同じ Lean(`emitE`)。Prop(量化・spec 宣言の呼出し・Prop に束ねた局所名)はここに届かない: 型検査が E014 で退ける([language.md](language.md)「Prop と Bool」。C35。Prop は Bool に戻せず、`(∀ …) = true` は Lean が拒否する。量化の実行も classical な判定も naru に無い)。Prop の条件 / ガードで Bool 以外の値を選ぶ式も同じく E014 |

受理例は `tests/accept/statements.naru`(量化・`let`・`if`・`match`・比較・input・入れ子の bundle・再帰)と `tests/accept/prop_bool.naru`(Prop と Bool の
境界で受理される形。`naru_test regression` が戻り値と命題の真偽を照合する)。生成 Lean の型検査は、生成 Model の olean を
`--out` のディレクトリに作ってから(knowledge「生成コードの回帰」)。

### verified-consensus の Statements の移植

移植は `specs/consensus/Consensus/Spec/`(module 宣言は `Consensus.Spec.*`、生成モジュールは `Statements.Consensus.Spec.*` / `Model.Consensus.Spec.*`。
8 ファイル。手書きの Generic + Instantiation の構成に沿う: `Execution`(run の
観測述語 `Emits` / `Processes` / `Handles` / `Carries` / `HandlesAt` / `AcceptsAt` / `BlockInRun` / `NamedRootCollisionFree`)、`Accountability`(`SlashableBetween` /
`HasSlashableWeightBetween` / `RootInjectiveOnAncestors` / `NamedFinalizedAt`)、`Interface`(enum `Output` と `outputAt` / `proposedBlock` / `envAwake` の
fn、`Opening` / `Finalizes` / `CollisionFree` / `Evidence` / `InRun` / `Idealization` / `Slashes`)、`Constants`(定数の fn と `ConstantsValid`)、
`Properties`、`Conditions`(`SetupWellFormed` / `RunDomain` を含む)、`Regimes`、`Claims`(13 の claim と `claim bundle Consensus`))。手書き側は `third_party/verified-consensus`。書き方の約束:
手書きの型引数 `P` / `I : Interface P` / `C : Constants` / `E : Env V` は instantiation が 1 つなので `s: Setup` の引数に、関数欄の record(`Interface` /
`Constants`)は `Setup` を取る fn / spec 宣言に、`structure … : Prop`(欄が複数)と `extends` は `&&` に、`∀ x ∈ S, …` は `forall x: T { S.contains(x) implies … }`
に、Prop の `Preceq` / `Compatible` / `Slashable` は Model の Bool の fn に、noncomputable な `Finset.filter`(`awakeIn`)と `∃ S : Finset V` は
`exists members: List<T> { let w = members.toSet(); … }`(`toSet()` が正規形を作るので、下の既知の制限に当たらない)に写す。手書きの型が暗黙に
保証すること — `Setup` の証明の欄(Δ > 0、R ≥ 3 …)、`Finset` の正規形(量化される `rho.honest` / `committee(k)` / electorate の鍵。下の既知の制限に当たる
ので `xs == sort(xs, by = …).toSet()` で要求する)、validator の型が electorate そのものであること(proposer / committee / honest の所属)— は naru の
record に無いので、condition `SetupWellFormed(s)` と `RunDomain(s, rho)` を各 claim の premise に足す(claim の形は
`SetupWellFormed(s) && RunDomain(s, rho) && <regime> implies <結論>`。`RecoveredBy` が量化する `source` にも `RunDomain`)。

既知の制限: `∀` / `∃` は Lean の型の全要素を回る。`NaruStd.Set` / `NaruStd.Table` は昇順・重複なしのリストだが、その不変条件は型に
入っていないので、`Set` / `Table` を含む型(`Run` の `honest` など)の量化は正規化されていない表現(重複・未整列)も含み、そこでは `size` や
`==` が naru の集合の意味からずれる(手書き Model の `Finset` は不変条件を型に持つ)。移植の claim が集合の濃度や等しさに依存するなら、
stdlib の `Set` / `Table` に不変条件の証明欄を足すか、量化に整形性の前提を付ける(どちらも naru の表現力は変えない)。
