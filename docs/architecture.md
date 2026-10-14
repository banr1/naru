# naru コンパイラの構成

コンパイラのパイプライン、Typed Core IR、Model backend と Statements backend の対応表、生成ファイルのヘッダと決定性。
文法は [language.md](language.md)、診断は [diagnostics.md](diagnostics.md)、コマンドは [cli.md](cli.md)。

## パイプライン

```
Parser → Surface AST
  → 同名のモジュール            (Modules.lean:   E017)
  → 名前解決・phase 検査        (Resolve.lean:   E001, E011〜E013。解決した参照の索引 `Resolve.Ref`(書かれた経路と参照先)も作り、`Checked.refs` に残す: E017 の位置と `naru lsp` の定義ジャンプ(C30)・ホバー(C29)・宣言名のリネーム(C32)が引く)
  → 型・capability 検査 + Core IR への elaboration
                                (Typecheck.lean: E003〜E006, E014〜E016, E018, E019。解決した欄・stdlib メソッドの参照の索引 `Typecheck.MemberRef`(位置・record / 受け手の型・確定した型。欄は式の中の読み `r.f` と record literal の初期化 `R { f: … }`(`init`)の両方)と、欄 / メソッドのアクセスごとの受け手の型の索引 `Typecheck.AccessRef`(名前が解決できなくても残る)も作り、`Checked.members` / `Checked.accesses` に残す: `naru lsp` のホバー(C29)と欄名の定義ジャンプ、`.` の後の補完(C31)、欄名のリネーム(C32)が引く)
  → Core の健全性               (Driver.lean:    E014「internal」。C35)
  → モジュールの循環            (Modules.lean:   E017。生成 Model / Statements の import グラフ)
  → 停止性検査                  (Totality.lean:  E002)
  → Model backend               (Backend/Model.lean)
  → Statements backend          (Backend/Statements.lean)
```

前の段に誤りがあれば次の段には進まない。診断が 1 つでもあれば backend には進まず、`generated/` は書き換えない。
入口は `compiler/Naru/Driver.lean` の `compileFiles`(指定ファイル)/ `compileSources`(ソースルート。`naru lsp` はバッファの内容でこれを呼ぶ)。
`naru lsp` の整形(C33、`compiler/Naru/Format.lean`)だけは段を通らず、字句解析(`Lexer.lean`)の字句列と字句の間のコメントから正規形を印字し直す
(字句列を変えないので、整形は生成 Lean の本文に影響しない。規則は [cli.md](cli.md)「言語サーバー」)。
すべての診断は backend より前の共通の検査が出すので、CLI の `compile`(出力指定あり / なし)と言語サーバーは同じ入力・コンパイル単位に同じ診断を
同じ行・列に出す(C18)。
型検査を診断なしに通った Core には、推論用のメタ変数・誤りの波及を抑える「不明」の型・エラー用ノードが残ってはならない(型検査は誤りを診断してから
それらを作る)。`compileSources` は停止性検査の前に Core の全宣言を再帰的に走査し(`Core.Decl.unsound`)、残っていればコンパイラの不変条件の破れとして
E014 を出して backend に渡さない(C35。`naru_test regression` は全受理例と移植ソースの Core で 0 件を確かめる)。
モジュール構造(`Modules.lean`): 同名のモジュールは構文解析の直後に各ファイルの `module` 行へ、循環は Core と参照の索引から、生成 Model の import グラフ
(`Backend.Model.modelGraph`: 出力する runtime 宣言が参照する他のモジュール)と生成 Statements の import グラフ(`Backend.Statements.specGraph`: spec 宣言が
参照する他のモジュールの spec 宣言)のそれぞれで、循環に関与する辺ごとに参照元の宣言の中の参照先モジュールへの最初の参照の行・列へ E017 を出す
(参照が構文上その宣言に現れない依存 — 推論された型(欄の参照の record・呼出しの結果の型)や使う input の署名を通したもの — は宣言の名前の位置)。
グラフは backend が import を書くのと同じ関数で計算する(生成の規則を変えれば検査も揃う)。Model の辺を作るのは出力される宣言への参照だけで、input への
参照は辺にならない(input の宣言元のモジュールは import しない: C38)。backend に残る同名・循環の検査は安全網で、届かない。
`naru compile` のソースルートが複数のときは、全ルートの module を束ねて同じ同名検査に掛ける(`compiler/Main.lean` の `compileAll`。生成の省略で生成パスが
衝突しない組も E017)。

## Core IR と Model backend

型検査(`Typecheck.lean`)は検査と同時に Surface AST を Typed Core IR(`Core.lean`)に elaborate する。名前は解決済み、
UFCS と名前付き引数は展開済み、ブロックは `let` の入れ子、型が要る位置には解決済みの型を持つ。backend は Core だけを読む。

Model backend(`Backend/Model.lean`)は runtime 宣言だけを Lean に落とす(spec 宣言は下の「Statements backend」)。

| naru | 生成 Lean |
|---|---|
| `module A.B` | ファイル `generated/Model/A/B.lean`、Lean モジュール `Model.A.B`。宣言は `Model.A.B.name` と完全修飾で参照。他モジュールの参照は `import`(循環と同名のモジュールは生成前の共通検査が E017 で退ける)。Model ファイルを出すのは Lean の runtime 宣言(type / record / state / enum / fn / observer / scenario)を実際に出力するモジュールだけ(C38): spec 宣言だけ・input だけ・宣言の無いモジュールからはコメントと import だけのファイルを作らず、ルート `generated/Model.lean`(集約ファイルの例外。宣言が無くても生成する)は存在する Model モジュールだけを import する。`import` は出力される宣言への参照からだけ数える(input の宣言元のモジュールは import せず、input の署名が参照する型のモジュールを import する) |
| `type T = U` | `abbrev Model.A.B.T : Type := U`(参照は展開した型で書く) |
| `record` / `state` | `structure … deriving DecidableEq, Ord, Repr`(`derive eq` → `DecidableEq` + `Ord`、`derive order` → `Ord`。`Repr` は常に。`finite` はまだ何も生成しない。`Ord` は `Set` / `Table` の正規化に使う隠れた全順序で、欄・variant の宣言順の辞書式)。欄名と局所名は常に `«»` で囲む(予約語の一覧に頼らない) |
| `enum` | `inductive`(variant の引数は `a0 a1 …`) |
| 再帰する型の `Ord` | variant の引数に自分を直接持つ enum(`Block` / `NamedBlock` / `Tree`)と `mutual` の成分(`Rose` / `Forest`)は、deriving 句から `Ord` を外し、派生と同じ辞書式順序(異なる構築子は宣言順で前が `.lt`、同じ構築子は引数の宣言順の `(compare a b).then (…)` の連鎖で末尾が `Ordering.eq`)を構造的再帰で明示的に定義した `def <型>.naruCompare («x» «y» : <型>) : Ordering … termination_by structural «x»`(成分なら `mutual … end`)と `instance <型>.naruOrd : Ord <型> := ⟨<型>.naruCompare⟩` を出す。Lean 4.34 の `deriving Ord` は再帰型の `compare` を `partial` で定義するので、そのままでは `compare` が証明から見て不透明(`rfl` / `decide` / 等式補題のどれも効かない)になり、`Set` / `Table` の所属(store の tree / bodies / sigma)に関わるプロトコル証明(`proofs/`、C71)が原理的に閉じない。値の順序は派生と同じなので実行の挙動(golden)は変わらない。コンテナ越しの再帰は E019 が退けるので、再帰はこの直接の形だけ |
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
証明義務の一覧 `obligations.json`(C69。「Proofs」)も同じ決定性を持つ: 先頭のフィールド `naru-compiler` / `naru-compiler-sha256` / `naru-stdlib` / `naru-stdlib-sha256` /
`sources`(ソースルートからの相対パスと sha256。パス順)に C1 のヘッダと同じ 3 値を持ち、正規形の JSON(`Deps.J.render`。「依存グラフ」)で、`naru compile` が生成先に書き直す。

生成先と Lake: 生成先は `naru.toml` の `generated`(既定 `generated/`)で、`naru compile` / `naru simulate` は書き終えた生成先への symlink を
`<ルート>/.lake/naru/generated` に置く。`lakefile.toml` の lean_lib `Model` / `Statements` の `srcDir` はこの link なので、`lake build Model` /
`lake build Statements` / `naru_simulate` は現在の設定の生成先を読む(C24。[cli.md](cli.md) の naru.toml)。

既知の制限(backend): naru は enum / Option / Bool / tuple の match の網羅性を検査しないので、網羅していない match は
Lean が拒否する(E018 が最後の腕のガードと Nat / Int / String の穴を塞ぐので、生成コードの `panic!` は到達しない位置にだけある)。
到達しない腕(先行する腕が必ず一致する)は Lean の「redundant alternative」で拒否される。ガード 1 つにつき残りの腕が
2 回生成される。ヘッダとコメントにはソースのパスがソースルートからの相対パス(`compile` の引数のファイルは渡された文字列のまま)で入る。

## Statements backend(`generated/Statements`)

Statements backend(`Backend/Statements.lean`)は spec 宣言だけを Lean に落とす。naru モジュール `A.B` に spec 宣言があれば
ファイル `generated/Statements/A/B.lean`(Lean モジュール `Statements.A.B`)になり、ルート `generated/Statements.lean`(集約ファイルの例外。spec 宣言の
あるモジュールが無くても生成する)がそれらだけを import する。
生成 Statements が import するのは `NaruStd`・生成 Model(`Model.A.B`。出力される runtime 宣言への参照があるモジュールだけ。input の宣言元は import せず、
input の署名が参照する型のモジュールを import する: C38)・他の生成 Statements(`Statements.X.Y`。循環は生成前の共通検査が E017 で退ける)だけで、
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

宣言コメント(IDEAL.md 用語「宣言コメント」、C60 / C61): `specs/consensus/` 配下(`scenarios/` を含む)の各宣言(type / record / state / enum /
input / fn / protocol / observer / scenario / predicate / condition / regime / property / claim / claim bundle。module / import / derive と scenario
の中の `input` 文は宣言でない)の直上に、空行を挟まず `//` の連続ブロックの日本語の説明を置く。1 行目はその宣言の主張または役割の要旨 1 文、
2 行目以降が説明(何を表すか、引数と戻り値、プロトコル上の役割と他の宣言との関係、前提がある理由、手書きの対応する定義名と写し方の差)で、
fn は 2 行以上、それ以外は 5 行以上(上限は 10 行前後の目安)。手書きの対応物は「手書き `名前`」の形で挙げ(ファイル名を添えてよい。
`/` で並べて複数挙げられる)、名前は `third_party/verified-consensus` の Lean の定義名(`namespace` 付きの完全名のどの後置列でもよい。
structure の欄・inductive の構築子は `型名.名前`)に限る。式や変数付きの参照(`st.F`、`WithBot Time`)は「手書き側の `…`」「手書きでは `…`」
と書き、「手書き `…`」/「手書きの `…`」の直後のバッククォートには置かない(`naru_test repo` が名前の実在を検査する)。対応物が無い naru
側だけの補助は「手書きに直接の対応物は無い」と書く。コメントは字句解析で捨てられ、生成 Lean には写らない(C1 のヘッダの hash だけが変わる)。
形と名前の実在は `naru_test repo` が検査する([testing.md](testing.md))。

既知の制限: `∀` / `∃` は Lean の型の全要素を回る。`NaruStd.Set` / `NaruStd.Table` は昇順・重複なしのリストだが、その不変条件は型に
入っていないので、`Set` / `Table` を含む型(`Run` の `honest` など)の量化は正規化されていない表現(重複・未整列)も含み、そこでは `size` や
`==` が naru の集合の意味からずれる(手書き Model の `Finset` は不変条件を型に持つ)。移植の claim が集合の濃度や等しさに依存するなら、
stdlib の `Set` / `Table` に不変条件の証明欄を足すか、量化に整形性の前提を付ける(どちらも naru の表現力は変えない)。

## 依存グラフ(`naru deps`、`compiler/Naru/Deps.lean`・`DepsTemplate.lean`。C63〜C67)

`lake exe naru deps` は `naru.toml` のソースルートを `naru compile` と同じ共通の検査(`Driver.compileFiles`: 構文解析・同名モジュール・名前解決・型検査・Core の健全性・
循環・停止性と、ルートをまたぐ同名モジュール)に通してから、宣言単位とファイル単位の参照のグラフを `deps.json`(正規形の JSON)と閲覧用の単一ファイル `index.html` に
書く(出力先は `naru.toml` の `deps`、`--out <dir>` で上書き。[cli.md](cli.md)「依存グラフ」)。閲覧と理解のための派生物で、検証の根拠にはしない(IDEAL.md「不変条件」:
生成 Model / Statements の import の正しさ(C8 / C18 / C38)や意味保存(C39〜C59)の証拠に流用しない)。

- **依存の定義**: 宣言の依存は、名前解決の参照の索引 `Resolve.Ref`(値の位置の名前・修飾名・record literal の型名・パターンの構築子・UFCS のメソッド名・型の位置の名前
  — 仮引数・戻り型・欄・variant の引数・型別名の右辺 —・claim bundle の項目・scenario の `input … = …;` の束縛。定義ジャンプ C30 と同じ索引)に記録された、宣言の本体・
  署名から他の宣言への**構文上の**参照。推論された依存(欄アクセスの record、呼出し結果の型、input の署名を通したもの)は含めない。自己参照は辺にせず宣言の属性 `selfRef`。
  ファイルの依存はファイルを跨ぐ宣言の依存の集約(辺ごとに宣言の辺の本数と、参照元の `import` 行に参照先があるか)。
- **import 行・生成 Lean の import グラフとの違い**: `import` 行は受理されるだけで意味を持たない(名前解決は単位の 1 つの大域表)ので、import 行に無い参照と参照の無い import
  がありうる。グラフはそれを差として報告する(`fileEdges[].imported` / `unusedImports`)が、import 行を書き換えることはしない。生成 Model の import グラフ
  (`Backend.Model.modelGraph`: 出力される runtime 宣言の参照だけ。input への参照は辺にならない)と生成 Statements の import グラフ(`specGraph`: spec → spec だけ)は生成の
  都合で引いた別のグラフで、E017 の循環検査はそちら(上の「パイプライン」)。参照のグラフには、spec → runtime と spec → spec の参照が 2 つのファイルの間で逆向きに走る循環
  (強連結成分)がありうるが、生成 Lean の import は循環しないので生成は失敗しない(検体 `tests/deps/sample/` の `Sample.Loop.A` / `Sample.Loop.B`)。
- **層と強連結成分**: ファイルの辺のグラフの強連結成分(Kosaraju)を 1 つの節点に縮約した DAG で、他の成分に依存しない成分が層 0、各成分は依存先の最大の層 + 1。同じ成分
  (循環)のファイルは同じ層。consensus では `Consensus.Objects.Identifiers` が層 0(最上段)、`Consensus.Spec.Claims` が最大の層(最下段)。
- **推移簡約**: 縮約した DAG で到達関係を変えない最小の辺集合。成分の辺 `A → B` は、`A` の他の依存先から `B` へ到達できなければ残す(DAG の推移簡約は一意)。残す成分の辺は
  それを作るファイルの辺のうち並びで最初の 1 つで代表し、成分の中(循環)の辺はすべて残す。
- **決定性**(C64): 並び順はすべてソースから決まる — モジュールはソースルートからの相対パス順、宣言はソース中の出現順、辺は(参照元, 参照先)の宣言 / モジュールの順、
  出現位置は(ファイル, 行, 列)の順。ハッシュ表の走査順・時刻・絶対パス・環境変数・乱数に依存しない。JSON は独自の印字(`Deps.J.render`)で正規形: キーは書いた順で固定、
  2 空白の字下げ(スカラーだけの配列 / オブジェクトは 1 行)、UTF-8、LF、末尾改行あり、浮動小数なし。`<` `>` `&` は `<` 等(バックスラッシュ + `u003c`)に逃がすので、同じバイト列を HTML の
  `<script type="application/json">` にそのまま埋め込める。先頭のフィールド `naru-compiler` / `naru-compiler-sha256`(`compiler/**/*.lean` の hash。C1 のヘッダと同じ計算)と
  `sources`(ソースルートからの相対パスと sha256。パス順)。HTML は先頭のコメントに同じ値を書く。
- **JSON の内容**: `modules`(名前・相対パス・グループ = 名前から最後の要素を除いた経路(要素が 1 つなら空)・import 行・層・成分の添字)、`decls`(修飾名・モジュール・種類
  (`DeclKind.describe`)・phase・protocol の中なら `owner`・行・列(名前のトークン)・`Naru.declComment` と同じ規則で読んだ宣言コメントの 1 行目 `summary`・`selfRef`)、
  `declEdges`(`from` → `to` と `sites`: 出現位置ごとの相対パス・行・列・書かれた経路。重複なし)、`fileEdges`(`from` → `to`、`count`、`imported`)、`unusedImports`
  (モジュールと import 行のモジュール名)、`components`(全成分。各成分はモジュール名の列)、`reducedEdges`、`stats`(ファイル数・宣言数・宣言間の辺・うちファイルを跨ぐもの・
  ファイル間の辺・推移簡約後の辺・層の数)。
- **閲覧用 HTML**(C65 / C67): `compiler/Naru/DepsTemplate.lean` の固定のテンプレート(HTML / CSS / JavaScript。IDEAL.md「前提」の技術スタックの例外)に JSON を埋め込んだ
  単一ファイル。外部への読み込み(CDN・Web フォント・`fetch`)を持たず `file://` で開ける。乱数・時刻を使わない。`prefers-color-scheme` でライトとダーク。データ(宣言・辺・
  層・推移簡約・import との差・統計)はすべて Lean の生成側が作り、テンプレートは描画(層の中の並び = モジュールの順、座標)だけを決定的に行う。ファイル単位タブは縦向きの
  層状グラフ(上ほど層の番号が小さい。既定は推移簡約の辺、切替で全辺、ファイルを選ぶと使う側 / 使われる側の辺を色分けで強調して横のパネルに宣言数(種類別)・使う / 使われる
  ファイルと辺の本数・辺ごとの「宣言 → 宣言」・import 行に無い参照の印・参照の無い import を出す。色はグループ別)、宣言単位タブは名前・種類で絞る一覧(ファイルごと)と、
  選んだ宣言の種類・モジュール・`ファイル:行`・要旨、使う / 使われる(直接 / 推移的。推移的は距離 2 以上を区別)。URL の `#file=<モジュール名>` /
  `#decl=<修飾名>` / `#tab=decls` / `#all=1` / `#transitive=1`(`&` 区切り)で選択状態を開ける(共有と観測のため)。索引に無い参照は捨てず数え(`Graph.dropped`)、
  0 でなければ `naru deps` は内部エラー(exit 1)にする。出力先が有効な生成先かその配下なら拒否する(exit 2)。
- **鮮度**(C66): 追跡対象の `docs/deps/` は機械生成専用(`.gitattributes` で `linguist-generated`)。移植ソース(宣言コメントを含む: 要旨が JSON に入る)・コンパイラ・
  テンプレートを変えたら `lake exe naru deps` で再生成する。`naru_test deps` が一時ディレクトリへの再生成と byte 単位で照合する(古ければ FAIL)。検査の全体は
  [testing.md](testing.md) の `deps` 群。

## Proofs — プロトコル証明の分離基盤(`proofs/`、`compiler/Naru/Obligations.lean`、`naru proofs`。C68〜C72)

**役割**: プロトコルが公開する保証(生成 Statements の claim / claim bundle)を手書きで証明する層を、生成物とコンパイラから分けて置く。生成 Statements の命題を **義務**
として機械的に一覧し(`obligations.json`)、`proofs/` の theorem がどの義務のどの版の型に対するものかを **束縛 hash** で結び、`naru proofs` が義務ごとの **証明状況**
を判定する。基盤は consensus を特別扱いせず、任意の有効な `naru.toml` の単位に同じ規則で動く(検体 `tests/proofs/sample/`)。使い方は `proofs/README.md`、コマンドは [cli.md](cli.md)「証明状況」。

**依存方向**: Model ← Statements ← Proofs。
- `Proofs` が import してよいのは生成 Model / Statements(`Model.*` / `Statements.*`)・`NaruStd`・Lean 本体(`Init` / `Lean` / `Std`)・mathlib(`Mathlib.*` とその依存パッケージ)だけ。
  基準の手書きライブラリ `DecoupledConsensus*`・`NaruSem`・コンパイラ(`Naru.*`)・`NaruTest` は import しない。
- 逆に、生成 Model / Statements・`NaruStd`・`NaruSem`・コンパイラは `Proofs` を import しない。`naru compile` / `simulate` / `lsp` / `deps` は `proofs/` を読まず、
  証明の有無・成否で成否も出力も変えない(`naru proofs` だけが読む)。mathlib を import するのは `Proofs` だけ。
- `NaruSem`(コンパイラの意味保存)とは別の層: `naru proofs` は生成 Statements に対する theorem の状況だけを報告し、最後の行 `layer: protocol guarantees (…). The compiler's
  semantics preservation (lake build NaruSem / naru_test semantics, C45) is a separate layer and is not reported here.` でそれを明示する。

**Lake の配線**(`lakefile.toml` / `lake-manifest.json`):
- lean_lib `Proofs`: `srcDir = ".lake/naru/proofs-src"`(`naru.toml` の `proofs` が指すディレクトリへの symlink。追跡対象外。`naru proofs` が置く。Model / Statements の
  `.lake/naru/generated` と同じ運び)、`globs = ["Proofs.*"]`(`proofs/Proofs.lean` と `proofs/Proofs/**.lean` を、ルートが import しなくてもビルドする)。
  `lake build Proofs` の前に一度 `lake exe naru proofs` が要る。
- mathlib(v4.34.1。基準コミットの verified-consensus と同じ版)とその依存パッケージ(batteries / Qq / aesop / proofwidgets / Cli / importGraph / LeanSearchClient / plausible)を、
  submodule `third_party/verified-consensus/.lake/packages/` のビルド済みのものへの **path 依存**(`[[require]] name = … path = …`)で使い回す。複製も取得もせず、ネットワークは要らない。
  mathlib の依存パッケージは mathlib より先に書く(Lake は同名の依存を最初に解決したもので揃える)。`lake-manifest.json` は手で同じ path の項目にしてある。
  **`lake update` は走らせない**: mathlib の `post_update` フックがネットワークでキャッシュを取ろうとするため。

**義務の一覧**(`obligations.json`。`compiler/Naru/Obligations.lean`): `naru compile` が有効な生成先(`--out <dir> <files>` なら `<dir>`)に Model / Statements と一緒に書き(`writeGenerated` が
書き直すので古いものは残らない)、`lsp` / `deps` / `proofs` は書かない。正規形の JSON は `Deps.J.render`(キーは書いた順で固定、2 空白の字下げ、UTF-8、LF、末尾改行あり、浮動小数なし。`<` `>` `&` は
`<` 等(バックスラッシュ + `u003c`)に逃がす)。
- 先頭のフィールド: `naru-compiler` / `naru-compiler-sha256` / `naru-stdlib` / `naru-stdlib-sha256` / `sources`(C1 の 3 値。各 Lean ファイルのヘッダのコメントと同じ値)。
- `obligations`: コンパイル単位のすべての `claim` と `claim bundle`(入れ子の bundle を含む)。並びはモジュールのソースルートからの相対パス順・ソース中の出現順。claim の無い単位では `[]`。
  各要素は `name`(naru の修飾名)/ `kind`(`"claim"` / `"claim bundle"`)/ `module` / `lean`(生成 Statements の宣言名)/ `theorem`(`lean` の先頭 `Statements.` を `Proofs.` に替えたもの)/
  `type`(義務の型)/ `sha256`(束縛 hash)/ `summary`(宣言コメントの 1 行目。`Naru.declComment` と同じ規則)/ `bundles`(それを項目に持つ claim bundle の修飾名の配列。無ければ `[]`)。
- 義務の型は生成側が決め、証明側は変えない。claim は生成 Statements の宣言を input の引数と仮引数で全量化した命題 `∀ (input の引数…) (仮引数…), Statements.A.B.claim input… 仮引数…`
  (どちらも無ければ `Statements.A.B.claim` そのもの)、claim bundle は構造体の命題そのもの `∀ (input の引数…), Statements.A.B.Bundle input…`。引数の書き方は Statements backend と同じ
  (例 `∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) («s» : Model.Consensus.Execution.Setup.Setup), Statements.Consensus.Spec.Claims.constants committee' proposer' «s»`)。

**束縛 hash**: 義務の宣言が属する生成 Statements モジュール(`Statements.A.B`)の import 閉包(生成ファイルの `import` 行を辿る。生成 Model / Statements のモジュールだけ。`NaruStd` は辿らず stdlib の hash で代表)の
各モジュールについて、本文(C1 のヘッダ 5 行 — `-- Generated by …` / `naru-compiler` / `naru-stdlib` / `naru-source` / `naru-unit` — を除いたもの)の sha256 を取り、
`sha256("naru-stdlib\n<stdlib の sha256>\n" ++ 閉包の各モジュール(名前順)について "<モジュール名>\n<本文の sha256>\n")`。
- 依存しないもの: 時刻・絶対パス・コンパイラ版・単位 hash・宣言コメントの文言(ヘッダ行を除くため)。同じ Statements モジュールの義務は同じ hash を持つ(consensus の 14 件はすべて `Consensus.Spec.Claims` なので同じ値)。
- 変わるもの: claim が依存する fn の本体を変えると変わる。閉包の外のモジュールを変えても変わらない(検体で `inc` の本体 / `far` の本体を変えた複製で確かめる)。

**証明状況の判定**(`naru proofs`。`compiler/Main.lean` の `runProofs`):
- 前提の検査: `obligations.json` の `sources` が現在のソースルートのファイル(相対パスと sha256)と一致すること(古ければ exit 2。古い一覧に対して判定しない)、証明ディレクトリに
  ルート `Proofs.lean` があること(無ければ exit 2)。
- 束縛行 `-- naru-obligation: <naru の修飾名> sha256:<束縛 hash(64 桁の 16 進)>` を証明ディレクトリの `Proofs.lean` / `Proofs/**/*.lean` から集め、`lake build Statements Proofs` の
  後に、検査ファイル `.lake/naru/proofs/Check.lean`(追跡対象外。`set_option autoImplicit false`)へ義務ごとに 4 行を書いて `lake env lean --json` で走らせる:
  `example : <義務の型> := sorry`(型が elaboration できる = 生成先が古くない)、`#check @Proofs.<名>`(theorem の存在)、
  `theorem NaruProofsCheck.obligation<i> : <義務の型> := Proofs.<名>`(型の一致を kernel が検査)、`#print axioms NaruProofsCheck.obligation<i>`(公理監査。検査用の theorem に
  対して行うので、elaboration が補った coercion の公理も閉包に入り、別の型の theorem を coercion で義務の型に見せかける証明は不正になる)。
- 状況と判定の順: `missing`(theorem が無い)→ `invalid`(型が義務の型と違う / `propext` `Classical.choice` `Quot.sound` 以外の公理に依存。`sorryAx` より先に見るので `sorry` の
  下書きが独自の公理を隠さない)→ `sorry`(`sorryAx` に依存)→ `stale`(束縛行が無い / hash が現在の一覧と違う / 同じ義務の束縛行が食い違う)→ `proved`。一覧に無い修飾名の
  束縛行・形の崩れた束縛行・`set_option debug.skipKernelTC` の行(kernel の検査を飛ばす)も `invalid` として数える。
  失効した証明は Lean で通っていても証明済みにせず、現在の hash を表示して書き手の再束縛に委ねる(義務の型を人間が見直す機会を残す)。
- exit: ビルドの失敗・検査が走らない・`invalid` が 1 件でもあれば 1、`missing` / `sorry` / `stale` だけなら 0、前提(`proofs` / 一覧 / 鮮度 / ルート)が崩れていれば 2。生成先と証明
  ディレクトリには何も書かない。信頼する前提: 証明モジュールが義務の型の意味を変える notation / macro / instance を定義しないこと(検査ファイルは証明モジュールを import した
  環境で義務の型を読む)。

**consensus の 14 件**: 13 claims(`constants` / `nested` / `certificatesAccountable` / `finalizedAccountable` / `finalizedMonotone` / `honestNeverSlashed` / `finalizedSafe` / `available` /
`confirmedLive` / `stableLive` / `stableIncludedFast` / `finalized` / `stableAsynchronyResilient`。claim surface の順)と claim bundle `Consensus.Spec.Claims.Consensus`。
theorem の入口は `proofs/Proofs/Consensus/Spec/Claims.lean`(`import Statements.Consensus.Spec.Claims` と `import Mathlib.Tactic`)、補題は `proofs/Proofs/Consensus/` 配下に分ける。
いまは `constants`(補題 `proofs/Proofs/Consensus/Constants.lean`: 定数を Δ・R・η_SG の多項式に開く。`outageStart < expiry` だけ `Int.fdiv` と Nat の除算を通る)と
`nested`(補題 `Nested.lean` / `Blocks.lean`: `getStable` / `getConfirmed` の分岐と `preceq` の反射律。run への前提は使わない)、
`finalizedMonotone`(補題 `FinalizedMonotone.lean`: `RunWellFormed` の中の `EventsSorted` だけを使う。`Stores.lean` が「`f` を変えるのは `updateFinality` の
`prec st.f σ.f` を条件にした分岐だけ」から全ハンドラ(`nodeTick` / `nodeProcess`)が store の `f` を縮めないことを、`Runs.lean` が時刻で非減少な event 列の
`filter (≤ t)` が `filter (≤ t2)` の接頭辞であることと `worldAt (Table.insert …)` の読みを、`Tables.lean` が stdlib の `Table.getOr` / `insert` と `ValidatorId` の
派生 `Ord` の補題を、`Blocks.lean` が `preceq` の推移律を与え、`List.foldl_append` で結ぶ)、
`certificatesAccountable`(補題 `CertificatesAccountable.lean`: run の前提は無く、`SetupWellFormed` からは `normalizedValidators` だけを使う。
`Derivation.lean` が名前付き導出 `deriveNamed` の不変条件 — 高さの順序 `hF ≤ hJ < h`、`f` / `j` / `tH` が `eraseBlock B` の接頭辞、
`hF = 0 → f = Genesis`、3 つの署名者集合が chain 上の行で裏付けられること、finality の証明書(`hF ≠ 0` なら `finalityPair = some ⟨hF, root f⟩` の
定足数)、高さの横断(`1 ≤ h₀ < h` なら祖先 `X` と `matchesEntry … h₀ (root X)` の定足数)— を 1 つの構造体 `Inv` にまとめて `B` の構造帰納法で示し、
`Sets.lean` / `Orders.lean` が stdlib `Set` の所属(`compare` が `.eq ↔ =` の型)と `ValidatorId` の集合の整列・`Finset.sum` への橋を、`Weights.lean` が
定足数の交わりの重み `2q ≤ W + weight (QF ∩ QP)`(mathlib `Finset.sum_union_inter`)を、`NamedBlocks.lean` が消去と `chainAttestations` の所属を、
`Slashing.lean` が E1 の slashable と `slashable` の対称性を与え、手書き `namedChainAccountableSafety` の筋 — 低い方の高さ `h₁` が 0 なら genesis で互換、
さもなければ証明書 `QF` と横断 `QP` を取り、`root X = root target` なら `CollisionFree` から `X = target` で互換、さもなければ `QF ∩ QP` の各署名者の
2 つの行が E1 で slashable — で結ぶ)、
`finalizedAccountable` / `finalizedSafe`(補題 `FinalizedAccountable.lean` / `Carrier.lean`: store の不変条件 — bodies の各名前付きブロック `D` の消去が
`tree` にあり、chain 状態の表 `sigma` のその鍵の値が名前付き導出 `deriveNamed D` に等しく、finalized `f` はどれかの bodies の `D` の導出の `f`(finality carrier)—
を `Store` → `NamedStore` → `nodeTick` / `nodeProcess` → world の順に全ハンドラで保ち(`f` / `tree` / `sigma` / `bodies` を書くのは `onBlockUsing` の受理の経路だけで、
そこで書く `post` は親の不変条件から `deriveNamed B`)、`readAt t` が `EventsSorted` の下で `stateBefore i` であることから carrier を run の中のブロック(`BlockInRun`)にし、
`Idealization = NamedRootCollisionFree` を消去した祖先の持ち上げ(`erased_ancestor_lift`)で `RootInjectiveOnAncestors` にして `certificatesAccountable` の本体 `oriented` を
両向きに当て、`Evidence`(2 本の chain の attestation の間の slashable な重み)を `chainAttestations (eraseBlock D) ⊆ storeAttestations core`
(`storeAttestations = flatMap tree chainAttestations`)で `SlashableStates` に持ち上げる(`finalizedAccountable`)か `SlashableBound` で退ける(`finalizedSafe`)。
`Set Block` / `Set NamedBlock` / `Table Block _`(tree / bodies / sigma)の所属の言い換えには `Orders.lean` の `block_compare_eq_iff` / `nb_compare_eq_iff` が要り、
これは backend が再帰する型に `deriving Ord` の代わりに出す明示的な `naruCompare`(上の「再帰する型の `Ord`」)で初めて書ける。手書き
`storeAccountableSafety_stateBefore` / `wholeRunAccountableFinalitySafety` / `wholeRunFinalitySafety` の筋)、
`honestNeverSlashed`(補題 `HonestNeverSlashed.lean` / `Attribution.lean` / `EmissionSafety.lean` / `Signing.lean` / `Records.lean`: 前提のうち使うのは
`UnforgeableRun` の `UnforgeableSignatures`(carried)と `EventsSorted` だけ。`Records.lean` が validator client の記録 `Record` の性質 — `target` は書き込み 1 回、
`lock` は finality pair の高さに書かれて既にある値は変わらない、`timeout` は増えるだけ、`LockCompatible`(lock のある高さは timeout でなく target は空かその lock)と
`FinalitySafeAt`(finality pair を出した高さは timeout でなく lock がその target)が `createAttestation` で保たれ、既に target / lock のある高さに出す target はその値 — を、
`Signing.lean` が記録を書くのは自分の tick の `namedCreate` だけで tick は attestation を高々 1 つ出すこと(`stateBefore (i + 1)` は添字 `i` の event だけを畳んだもの)を、
`EmissionSafety.lean` が同じ validator の 2 つの発行は同じ高さに同じ target を名指し finality pair と timeout は両立しないので `slashable` でないことを、
`Attribution.lean` が store の honest な署名の attestation は署名者の tick が実際に出した行の消去であること(store の不変条件に tree の各ブロックが bodies の消去であることと
bodies が親について閉じていることを足し、bodies の genesis でないブロックはそのノードが処理したブロックで、`UnforgeableSignatures` の carried で発行に帰着)を与え、
手書き `validatorVoteSafety`(`attributedVoteSafety` / `emissionVoteSafety` / `honestNoDoubleTarget` / `no_timeout_against_finality` /
`carriedByHonest_of_storeAt`)の筋)の 7 件が証明済みで、
`naru proofs` は残り 7 件を `missing` と表示する(C71 が残る。[roadmap.md](roadmap.md))。残りの liveness 系の claim に向けた共有の足場
(theorem はまだ無い): `Liveness.lean`(包含 `IncludedFrom` + 単調 `MonotoneFrom` + 未来の提案の不在 `NoFutureRead` + 再発 → 活性 `LiveFrom`
の generic な補題と、`confirmedLive` / `stableLive` の結論を claim `available` の結論 `AvailableAt` に、`finalized` の活性を finalized の包含に
還元する補題)、`NoFutureRead.lean`(時刻 `t` の読みに提案時刻が `t` より後の honest な提案は入らない。`ExecutionValid` と Δ > 0 だけから
3 出力すべてについて)、`Clocks.lean`(store の時計 `t` / `s` を書くのは tick の冒頭だけで `s = slotOf e t`、時計は event の時刻以下)、
`TreeInv.lean`(`f` / `j` / `latestConfirmed` / `latestStable` は常に tree の要素なので、どの出力の読みも tree の要素)。
claim `available` の結論 `SafeFrom`(一致 ∧ 単調)に向けた足場(theorem はまだ無い): `ConfirmationRecords.lean`(確認・stable の記録
`latestConfirmed` / `latestStable` を書くのは `updateConfirmationWith` だけで、`advanceConfirmed` / `floorOnStable` は古い記録の接頭辞を、新しい記録と互換なら
新しい記録の接頭辞のまま保つ(`Keeps`)。他のハンドラは記録を変えず、1 tick は高々 1 回の更新)、`RecordGrowth.lean`(run に沿って: 記録が変わるのは自分の
tick の添字だけ、時刻 `t` の読みは `filter (≤ t)` の長さの `stateBefore`、tick の直後の記録は同じ時刻の読みの記録、記録の時刻をまたぐ一致 → 単調
`record_mono_of_compatible`)、`Outputs.lean`(出力 `getStable` / `getConfirmed` の単調性と一致を、欄 `f` / 記録の事実と、確認の出力では
`StableBelowConfirmed`(stable の記録 ⪯ 確認の記録)に還元する `safeFrom_stable_of_fields` / `safeFrom_confirmed_of_fields`)、
`RecordOrder.lean`(`StableBelowConfirmed` は regime の事実ではなく store の不変条件: `updateConfirmationWith` は `latestConfirmed := floorOnStable stable …`
と書き、`floorOnStable` はどの分岐でも `stable` を延ばす。他のハンドラは記録を変えないので、run のどの読みでも前提なしに成り立つ `stableBelowConfirmedFrom`。
stable の記録についての欄の事実(一致・finalized との交差の互換)は確認の記録のそれから従う `recordAgreeFrom_stable_of_confirmed` /
`crossAgreeFrom_stable_of_confirmed` ので、2 つの出力の `SafeFrom` はどちらも確認の記録の一致・交差の互換・finalized の一致の 3 つだけに還元される
`safeFrom_confirmed_of_records` / `safeFrom_stable_of_records`)、`Available.lean`(`AvailableAt t0` を残る 5 つの事実 — 確認の記録の一致と finalized との
交差の互換、finalized の一致、2 つの包含 — から組み立てる `availableAt_of_records`(前提は `EventsSorted` / `EventsNodup` だけ)と `SleepyRegime` 版
`availableAt_of_fields`。`t0 ≠ 0` なら `RecoveredBy` は回復の枝に限られ `SlashableBound` を持つので、finalized の一致は `finalizedSafe` の本体から従う
`agreeFrom_finalized_of_recovered`。GST-zero の枝(`t0 = 0`)の finalized の一致と `IncludedFrom` は未証明)、`Goldfish.lean`(確認の候補を書く fork choice と
得点の最初の層: `ghost anchor tree score eligible` は anchor から適格な子のうち得点最大の一意なものへ降りる歩みで、結果は anchor を延ばし `ghost_preceq`、
anchor そのものか適格な tree の要素 `ghost_eligible`。降下補題 `ghost_reaches`(途中のブロックが tree にあり、各ブロックで次の一歩が `target` の祖先で、`target` に
適格な子が無ければ結果は `target`。燃料 `size tree` が足りることは途中のブロックの深さが相異なることから `path_card`)、親について閉じた tree では結果に適格な子は
無い `ghost_terminal`。Goldfish の得点は祖先ほど大きく `goldfishScore_mono`、支持者は投票の参加者 `rawSupporters_size_le`。`updateConfirmationWith` の `let` を
名前つきの定義(`supportVotes` / `lateCount` / `score` / `eligible` / `sgRoot` / `head` / `candidate` …)に開いて `updateConfirmationWith_eq`(`rfl`)で結び、
新しい確認の記録は 元の記録 / stable の記録 / 過半の支持 `lateCount < 2 · score` を持ち SG root を延ばす head / grade の候補 `frameSgCandidate` のどれか
`latestConfirmed_shape`)、`Votes.lean`(投票の pool `storePool` に投票を入れるのは `onGoldfishVote` だけで、必ず `onGoldfishVoteChecked` の守り
`vote.valIndex ∈ committee' vote.slot` を通る。pool の不変条件 `PoolInv`(鍵 `k` の投票は slot `k` で committee の投票)と拡張 `PoolExt`(元の投票は残り、
増えた投票は適格)を全ハンドラ → tick / deliver → world → run の読みに積み上げ、`storeAt_pool` / `stateBefore_pool`(前提なし)と `storeAt_poolExt`
(`EventsSorted` の下で同じノードの pool は時刻について増えるだけ)。自分の投票の形 `goldfishVoteWith_some`)、`Majority.lean`(確認の門
`lateCount < 2 · score` と honest 過半。手書き `Confirmation.lean` の `Numerator` / `HonestSupport` の筋: 支持の投票は遅い投票 `supportVotes_sub_lateVotes`
なので `noSecondVoteIn` の絞り込みから支持の投票は投票者ごとに 1 つ `supportVotes_unique`、equivocator は無く `supportVotes_no_equivocation`(`NaruStd.Set` の
整列 `SortedLt` と `GoldfishVote` の辞書式順序から重複なし)、得点は支持者の数 `score_eq_supporters`。参加者は committee の要素 `participants_sub_committee`
(`PoolInv`)。数え上げの核 `exists_honest_of_majority`(`Finset`: equivocator と支持者は遅い投票の参加者に含まれ互いに素、参加者は committee に含まれ、
honest な committee の要素はすべて参加者、`HonestCommittees` の不等式、門から honest な要素)から、門を通るブロックには honest な支持者がいる
`exists_honest_supporter`(honest な支持者とその投票(slot `s`、`b` 以下を指す))/ `_of_head` / `_of_run`(`SetupWellFormed` と `HonestCommittees` から
run の読みについて)。`HonestSupport`(手書きの形から `vote` を「`B` 以下を指す」に弱めたもの: committee は honest 過半、honest な committee の要素はみな
支持の投票に `B` 以下を指す投票を持つ)から `B` とその祖先は門を通る `HonestSupport.eligible` / `eligible_of_preceq`、門を通るどのブロックも `B` と互換
`HonestSupport.compatible_of_eligible`。`Voting.lean`(honest な投票の発行。tick の投票の務め `namedGoldfishVoteWith` は `voting`(`0 < s`、`t = voteTime e s`)のときだけ走り、提案の務めの後の
store `voteStore` を読む。tick が出す投票は投票の時刻の tick の務めの出力で、投票者は自分・slot は `slotOf e t`・投票者は committee の要素
`tick_gfVote_shape` / `tick_gfVote_fields` / `emits_gfVote_shape`(手書き `gfVote_emitted_shape` / `emits_gfVote_shape`)、1 つの tick が出す投票は 1 つ
`tick_gfVote_unique`、どの投票者も slot ごとに発行する投票は 1 つ `emits_gfVote_unique`(`ScheduleWellFormed` の event の重複なし。手書き `emits_gfVote_unique`)、
投票の時刻の tick で committee の要素なら必ず投票を出す `tick_gfVote_of_duty`(務めは `awake'` を見ない)、`ScheduleWellFormed` は honest なノードの公開時刻の
tick を horizon まで run に入れるので honest な committee の要素は各 slot `k > 0`(`voteTime e k ≤ horizon`)で投票を発行する `honest_emits_gfVote`
(`slotOf_voteTime`(手書き `slotOf_vote_time`)/ `publicTime_voteTime`)、投票の時刻は提案の時刻と違う(Δ > 0)ので投票の務めが読む store は時計を合わせただけ
`voteStore_of_voteTime` で、発行された投票の head は `Emits` の添字 `i` の `stateBefore i` の発行者の store に時計を合わせたもの `clocked` の fork choice の head `voteHead`(cache は `onPhaseTick` で進めたもの。
`tick_gfVote_head` / `emits_gfVote_head` / `honest_emits_gfVote_head`))。`Delivery.lean`(投票の配送の層の入口。投票は `excludes` が偽なので
`PartialSynchrony` から honest な受信者が締切 `max t tGST + Δ` より前に扱う `partialSynchrony_gfVote`、`HandlesAt` の投票の経路は自分の tick の発行・配送・
運ぶブロックの受理の 3 つ `handlesAt_gfVote_cases`、配送された投票は投票者が committee の要素・受信者の slot が `u.slot` か `u.slot + 1`(`InWindow`)・
同じ投票者の投票が pool にまだ 2 つ無いときに受信者の pool に入り以後も残る `mem_receiptProcess_gfVote` / `deliver_gfVote_mem` / `deliver_gfVote_mem_of_lt`)。`Window.lean`(受信の直前の slot の窓。
時計は添字について単調 `clock_mono` で、slot の開始時刻は公開時刻なので honest な受信者への時刻 `t2` の配送の直前の slot は `proposalTime k < t2` なら `k` 以上・
`t2 < proposalTime (k + 1)` なら `k` 以下 `slot_ge_of_deliver` / `slot_le_of_deliver`、GST 以後に発行された投票の発行の時刻 `t` 以後で締切 `t + Δ` より前の配送では受信の直前の slot がちょうど `u.slot` で
`InWindow` `inWindow_of_deliver_gfVote`)。残るのは `SleepyRegime` の下で `HonestSupport` の `vote`(honest な committee の要素は `voteTime` に投票を発行し — 投票者・slot まで `Voting.lean` —、その投票の head は
`stateBefore i` の発行者の store に時計を合わせたものの fork choice の head で(済み)、その head が honest な提案 `B` を延ばして slot が `s` 以下で、`ExecutionValid` / `PartialSynchrony` で投票とブロック `B` が `supportCutoff` までに
届く)を示すことと、2 つの honest なノードの読みの間の正準性(手書きの
`eligible_compatible`: 一方の支持の投票が他方の遅い投票に入る `CrossView` の下で同じ slot に両ノードで門を通る 2 ブロックは互換)で確認の記録の一致・finalized との
交差の互換・GST-zero の枝の finalized の一致(stable の記録と grade の候補の分岐についても同じ)を結ぶこと、honest な提案が適格な子の一意な最大になって
`ghost_reaches` で選ばれること(包含))。
検査は [testing.md](testing.md) の `proofs` 群。

## コンパイラ意味論保存(`semantics/NaruSem`、C39〜C47、C48〜C53、C54〜C59)

生成 Lean が Core の意味を保つことを、backend から独立した意味論と Lean の定理で保証する(限定範囲)。lean_lib `NaruSem`(`semantics/`)。
検査入口と走らせ方は [testing.md](testing.md)「コンパイラ意味論保存」。プロトコルの Proofs(`proofs/`。「Proofs」)とは別の役割(別の層)で、Core・コンパイラ・独立意味論・
生成宣言を参照してよいが、生成 Model / Statements からここへの逆依存は無い(不変条件の依存方向)。
Core IR の意味論(C39〜C47。下の各節)に加えて、構文解析の出力 Surface AST の独立した意味論と適格性(C48。「Surface AST の意味論と適格性」)と、
runtime の Surface AST → Core の変換と値の対応、spec の Surface AST → Core の変換と命題の双方向の同値、それぞれの実際の frontend と生成 Lean への接続
(C49 / C50 / C51。「Surface AST → Core の対応」)がある。関数・input の保存対象(非再帰の fn / spec 宣言の呼出しと input。C54〜C59)は
「関数・input の保存対象の意味論」の段階(C54: Core と Surface AST それぞれの独立した意味論・適格性と、適格な式・宣言群に意味が定まること、
実際の宣言群の引用と適格性の検査)と、runtime の Core → 実生成 Model の層(C55〜C57 の runtime 側: 呼出しを含む生成 Lean の読み、一般定理
`Call.denote_sound`、宣言群の意味と実生成定数の一致 `Call.interp_agree`(呼出し先の証拠の呼出し側への合成)、実際の宣言群の実生成 Model への接続と
負の検体)が揃っている。spec の式には読みと一般双方向同値 `Call.Sem_denote`、現在の10宣言の実生成 Statements と読みの接続がある。
宣言群の spec 環境との一致も `Call.interp_prop_agree` で接続証拠から合成する。呼出しを含む Surface AST → Core → 実生成 Lean の対応は `SurfaceCallProg.lean`(宣言群の意味の対応 `Surf.Call.interp_lower_agree` と合成 `spec_sem_denote`。「Surface / Core の宣言群の意味の対応」)と検査プログラム `SurfaceCallStatementsCheck.lean` が与える。input のみの別モジュールと、別モジュールのfn/spec呼出し先への実生成接続は検査する。保証の境界と未対応は「信頼する部分・方式・未対応」。

### 対象(用語「今回の保存対象」)と範囲の判定(`NaruSem/Scope.lean`)

| 項目 | 定義 |
|---|---|
| 対象の constructor | `Core.Expr` の `.lit`(Nat / Bool)、`.var`、`.let_`、`.ite`、`.binop`、`.unop`(`!`)、`.method`(Nat の `min` / `max`)、`.match_`(`Core.Arm.mk`、パターン `Core.Pat` の `.lit` / `.bind` / `.wild`)。spec では加えて `.quant`(forall / exists、束縛型 Nat / Bool) |
| 対象の演算 | `BinOp.ofString?`: Nat の算術 `+` `-` `*` `/` `%`(`ArithOp`)、比較 `<` `<=` `>` `>=`(`CmpOp`。Nat と Bool)、等値 `==` `!=`(`EqOp`)、論理 `&&` `\|\|` `implies`(`LogicOp`)。`NatMethod.ofString?`: `min` / `max`。写らない演算子は対象外 |
| 型 | `Ty`(nat / bool)。spec の束縛文脈は `STy`(`.val Ty` = 値、`.prop` = 命題)で値と命題を区別する |
| runtime の適格性 | `wtR Γ e = some t`(`Γ : Ctx` = 名前 → 型): 対象の構文だけから成り、スコープ内の名前だけを参照し、型が合い、`match` が網羅的(`exhaustive`: ガード無しの `_` / 変数の腕、または Bool の `true` と `false` のガード無しリテラル腕)。腕は `wtArmsR` / `wtArmR`、パターンは `wtPat` |
| spec の適格性 | `wtS Γ e = some τ`(`Γ : SCtx`): 論理の位置の式は `.val .bool`(Bool の値)か `.prop`(量化・命題に束ねた名前を含む)。値を要求する位置(算術・比較・Nat の等値の被演算子、`min` / `max`、scrutinee、Nat の `let` の値)は `wtR Γ.vals`(命題に束ねた名前はスコープ外)で判定し、命題を戻さない。Bool の `let` は値が命題(`proppyS`: コンパイラの `proppy` と同じ構文的な区分)なら名前を `.prop` に、そうでなければ `.val .bool` に束ねる |
| 対象外 | 上記以外(呼出し・input・record / enum・コレクション・lambda・文字列・Int・Option …)は `wtR` / `wtS` が `none`。保証の対象にならず、言語の受理範囲とは別 |

### 意味(`NaruSem/Eval.lean`、`NaruSem/Sem.lean`)

- runtime は表示的意味論 `eval ρ e : Option Val`(`ρ : Env` = 名前 → 値)。`none` は行き詰まり(スコープ外の名前、型の合わない演算、対象外の構文、
  どの腕も一致しない `match`)で、既定値・panic の値で埋めない。演算の意味は Lean の `Nat` / `Bool` の演算で明示する: `-` は 0 で切り詰め、`/ 0 = 0`、
  `% 0 = a`、Bool の順序は `false < true`、`implies` は `!a || b`、`==` / `!=` は値の等しさ。`match` は腕を前から試し、パターンの束縛はその腕のガードと本体だけで
  有効(ガード不成立なら外側の環境で次の腕へ)。
- spec は評価関係 `Sem ρ e P`(`ρ : SEnv` = 名前 → 値か命題、`P : Prop`)。Bool の値は「true である」という命題に写し(`lit` / `varVal`)、論理演算は `∧` / `∨` /
  `→` / `¬`、Nat の比較・等値は `<` 等 / `=` / `≠`、Bool の比較は `evalBool = true`、論理の位置の `==` / `!=` は `↔` / `¬ (… ↔ …)`、`if` は `(C → P) ∧ (¬ C → Q)`、
  `match` は腕を 1 つずつ剥がし(`matchSkip` / `matchHit` / `matchGuard`)、ガード付きの腕は `(G → B) ∧ (¬ G → R)`(R は外側の環境で解釈する残りの腕)、
  量化は束縛ごとの意味を `∀ a` / `∃ a`(`Ty.carrier`: Nat / Bool の全要素)で束ねる。値の位置は `eval ρ.vals`。命題を実行可能な Bool に戻す規則は無い。
  関係にしたのは量化の本体の意味が定まらない場合を `True` / `False` で埋めないため(導出が無い = 意味が定まらない)。

### 一般定理(`NaruSem/Totality.lean`、`NaruSem/SemTotality.lean`)

| 定理 | 内容 | 仮定 |
|---|---|---|
| `eval_total` | `wtR Γ e = some t` で `Γ = ρ.ty`(各名前の値の型が文脈の型)なら `∃ v, eval ρ e = some v ∧ v.ty = t` | 適格性(型付け・スコープ・網羅性) |
| `Eval_unique` | `Eval ρ e v`(= `eval ρ e = some v`)の `v` は一意 | — |
| `Sem_exists` | `wtS Γ e = some τ`、`τ` が論理の位置の型、`Γ = ρ.ctx` なら `∃ P, Sem ρ e P` | 適格性。値の位置は `eval_total` |
| `Sem_unique` | `Sem ρ e P` と `Sem ρ e Q` なら `P = Q`(量化は関数外延性・命題外延性) | — |
| `denote_sound`(`preserve_nat` / `preserve_bool`) | **Model の保存(C40 / C41)**: `wtR Γ e = some t`(基礎の構文と非再帰の Nat / Bool の `match`)、`Γ = ρ.ty` なら `eval ρ e = some (denoteV ρ t e)` — 独立意味論の結果が生成 Lean の読み(下)の値に一致する。`wtR.mutual_induct` で式・腕の列・腕を同時に示す(`denote_sound_all`) | 適格性(型付け・スコープ・網羅性)。任意の式・任意の対応する環境 |
| `denoteArms_sound` / `denoteArm_sound` | **腕の列・腕の保存(C41)**: 適格で網羅的な腕の列(`wtArmsR Γ ts arms = some t`、`exhaustive ts arms`)と型の合う scrutinee の値 `v` について `evalArms ρ v arms = some (denoteArmsV ρ t v arms)`。一致した腕のガードと本体は束縛を足した環境で読みの値 | 同上。任意の腕の列・環境・値 |
| `denoteArmsV_hit` / `denoteArmsV_miss` / `denoteArmsV_guard_true` / `denoteArmsV_guard_false` | 腕の選択と束縛の形: 一致したガード無しの腕は束縛 `bs` を足した環境の本体、一致しない腕は飛ばす、ガードが真なら同じ環境の本体、ガードが偽なら残りの腕を **外側の環境** で(束縛は次の腕に漏れない) | — |
| `check_sound_nat` / `check_sound_bool` | **接続検査の健全性(C44)**: 仮引数の値の列 `xs` について、その型の文脈で適格な式 `e` と、値 `v = denoteN (Env.ofList xs) e`(各実生成宣言の接続検査が確かめる等式)から `eval (Env.ofList xs) e = some (.nat v)` | 同上 + 接続検査の成功 |
| `CmpOp.leanBool_eq` / `EqOp.leanNat_eq` / `EqOp.leanBool_eq` | 異なる表現の対応関係: 生成 Lean の Bool の比較(`Ord.compare a b == .lt` …)と `==` / `!=`(`BEq`)は独立意味論の `evalBool` / `decide (a = b)` と一致する(Bool の全要素 / `decide` の場合分け) | — |
| `Sem_denote`(`Sem_denoteP`) | **Statements の保存(C42 / C43)**: `wtS Γ e = some τ`(リテラル・局所名(値 / 命題)・Bool / 命題の `let` と shadowing・Bool / 命題の条件の `if`・論理・比較・等値(値の `==` と命題の `↔`)・`!`・Nat / Bool の `forall` / `exists`・非再帰の Nat / Bool のガード付き `match`)、`Γ = ρ.ctx`(命題に束ねた名前も可)なら `Sem ρ e P → (P ↔ denoteP ρ e)` — 独立意味論の命題と生成 Lean の読み(下)の命題が **同値**(両方向)。`Sem_denoteP`: 加えて `τ` が論理の位置の型なら `Sem ρ e (denoteP ρ e)`(読みは意味そのもの。`Sem_exists` + 命題外延性)。`Sem` の導出の帰納法(`Sem_denote_all`。仮定は網羅性と量化の束縛の非空を要求しない型付け `wtSNoExh`: `match` の残りの腕(それだけでは網羅的でない)と量化の束縛の末尾(空)にも帰納法の仮定を使うため。`wtS` で適格なら `wtSNoExh` でも同じ型(`wtS_noExh`)。値の位置は `denote_sound`、Bool の値の条件・両辺が値の `==` は境界(下)、命題の `let` は命題外延性で環境を揃え、`match` は腕の選択と束縛の形、量化は束縛ごとの同値(`forall_congr'` / `exists_congr`)) | 適格性(型付け・スコープ・網羅性)。任意の式・任意の対応する環境・任意の意味 |
| `Sem_denote_basic` | 基礎段階(C42)の形: 加えて `e` が基礎の構文(`basic`)で `Γ` に命題の束縛が無い(`SCtx.NoProp`)場合。一般定理の系(段階の記録) | — |
| `denoteP_iff_denoteB_noProp`(`denoteP_iff_denoteB_all`) | **値 / 命題の境界(C42 / C43)**: 命題でしか表せない部分(量化・命題に束ねた局所名: `proppyS Γ e = false`。`let` / `if` / `match` を含んでよい)を含まない式を任意の環境で読むと、命題の読みは Bool の読み(Model の読み)が `true` であることと同値: `denoteP ρ e ↔ denoteB ρ.vals e = true`。生成 Statements が値の形で出す所(`if c = true`、両辺が値の `a = b`)と意味の側の `(C → P) ∧ (¬ C → Q)` / `P ↔ Q` を結ぶ。`denoteP.mutual_induct`(式と腕の列を同時に)。`denoteP_iff_denoteB` は基礎段階の形(系) | `proppyS` が偽。任意の環境 |
| `proppyS_congr` / `proppyArms_congr` | `proppyS`(命題でしか表せない式の構文的な区分)は文脈のどの名前が命題に束ねられているか(`SCtx.isProp`)だけで決まり、値の型は見ない(`proppyS` は `let` の束縛と変数パターンを値の型を知らずに `.val .nat` で足す。Bool の `let` と Bool の値のパターン束縛の帰納法でこの合同が要る) | — |
| `denoteArmsP_hit` / `denoteArmsP_miss` / `denoteArmsP_guard` / `denoteArmsP_guard_true` / `denoteArmsP_guard_false` | 腕の選択と束縛の形(命題、C43): 一致したガード無しの腕は束縛 `bs` を足した環境の本体、一致しない腕は飛ばす、一致したガード付きの腕は `(G → B) ∧ (¬ G → R)` でガード `G`(Bool の値でも命題でも)と本体 `B` は束縛を足した環境、残りの腕 `R` は **外側の環境**(束縛は次の腕に漏れない)。ガードが成り立てば本体、成り立たなければ残りの腕 | — |
| `denoteQuant_forall_cons` / `denoteQuant_exists_cons` / `denoteQuant_nil` | 量化の読みの形(C43): `forall x: T { … }` / `exists x: T { … }` は `T`(`Ty.carrier`: Nat / Bool の全要素)の `∀ a` / `∃ a` で、束縛を足した環境の続き | — |
| `denoteP_let_prop` / `denoteP_let_bool` / `denoteP_ite_prop` / `denoteP_ite_bool` / `denoteP_eq_prop` / `denoteP_eq_bool` | 局所束縛・条件・`==` の読みの形(C43): 命題の `let` は名前を命題に束ね(以後の値の `let` / 量化 / パターンの同名の束縛が隠す)、Bool の値の `let` は値に束ねる。命題の条件の `if` は `(C → P) ∧ (¬ C → Q)`、Bool の値の条件は `if c = true then …`。命題を含む両辺の `==` / `!=` は `↔` とその否定、両辺が値なら値の等値 `a = b` / `a ≠ b` | — |
| `check_sound_prop` | **接続検査の健全性(命題、C44)**: 仮引数の値の列 `xs` について、その型の文脈で適格な spec の式 `e` と、命題 `Q = denoteP (SEnv.ofList …) e`(各実生成宣言の接続検査が確かめる `Prop` の等式)から `Sem (SEnv.ofList …) e Q`(実生成宣言の命題は意味そのもの) | 適格性 + 接続検査の成功 |
| `EqOp.propIff_bool` / `CmpOp.leanBoolProp_iff` / `EqOp.propBool_iff` / `LogicOp.prop_iff` / `CmpOp.propNat_iff` / `EqOp.propNat_iff` | **値の等値と命題の同値の区別**(C42): 論理の位置の `==` / `!=` の意味 `(a = true) ↔ (b = true)` / その否定は、両辺が Bool の値なら生成 Statements の値の等値 `a = b` / `a ≠ b` と同値(Bool の全要素)。生成 Statements の Bool の比較 `Ord.compare a b = .lt` …(`CmpOp.leanBoolProp`)は `evalBool = true` と同値、論理 `∧` / `∨` / `→` は `&&` / `\|\|` / `implies` が `true` と同値、Nat の比較・等値の命題は `decide` が `true` と同値 | — |
| `Surf.eval_total` / `Surf.Eval_unique` | **Surface AST の runtime の全域性と一意性(C48)**: `Surf.wtR Γ e = some t`(AST の型付け・スコープ・網羅性)で `Γ = ρ.ty` なら `∃ v, Surf.eval ρ e = some v ∧ v.ty = t`、値は一意。`Surf.wtR.mutual_induct` で式・`let` の列・腕の列・腕を同時に示す(`Surf.wtR_total_all`) | AST の適格性 |
| `Surf.Sem_exists` / `Surf.Sem_unique` | **Surface AST の spec の意味の存在と一意性(C48)**: `Surf.wtS Γ e = some τ`、`τ` が論理の位置の型、`Γ = ρ.ctx` なら `∃ P, Surf.Sem ρ e P`、意味は一意。注釈の無い `==` / `!=` の 2 規則(値の等しさ `eqNat` / 命題の同値 `eqForm`)の排他性は `Surf.Sem_not_nat` | AST の適格性。値の位置は `Surf.eval_total` |
| `Surf.eval_mono` / `Surf.Sem_not_nat` | 評価の単調性(環境を広げても定まっていた値は変わらない)と、**論理の位置の式(`Surf.Sem` の導出のある式)は Nat の値に評価されない**(対応する評価の環境 `Agree` のすべてについて) | — |
| `Surf.lower_sound`(`Surf.lower_total` / `Surf.lower_wt` / `Surf.lower_eval`) | **Surface AST → Core の対応(C49)**: `Surf.wtR Γ e = some t` なら `∃ c, Surf.lower Γ e = some c ∧ wtR Γ c = some t ∧ ∀ ρ, Surf.eval ρ e = eval ρ c` — 適格な runtime の AST には frontend から独立の変換 `Surf.lower` が定まり(`lower_total`)、その Core は同じ文脈で適格で(`lower_wt`)、任意の環境で AST の意味と Core の意味が一致する(`lower_eval`。値の対応は等式)。`Surf.wtR.mutual_induct` で式・`let` の列・腕の列・腕を同時に示す(`Surf.lower_sound_all`。腕の列では網羅性の走査も変わらない) | AST の適格性。任意の AST・任意の環境 |
| `Surf.preserve_nat` / `Surf.preserve_bool` | **AST の意味 = 生成 Lean の読み(C49)**: `Surf.wtR Γ e = some .nat`、`Surf.lower Γ e = some c`、`Γ = ρ.ty` なら `Surf.eval ρ e = some (.nat (denoteN ρ c))`(`lower_sound` と C40 / C41 の `denote_sound` の合成) | AST の適格性 + 変換結果 |
| `Surf.check_sound_nat` / `Surf.check_sound_bool` | **接続検査の健全性(AST、C49 / C51)**: 仮引数の値の列 `xs` について、その型の文脈で適格な AST `e`、変換結果 `c`(`low_<f>` が実際の Core と一致することを確かめる)、値 `v = denoteN (Env.ofList xs) c`(`conn_<f>` が実生成宣言について確かめる)から `Surf.eval (Env.ofList xs) e = some (.nat v)` | 同上 + 接続検査の成功 |
| `Surf.wtR_mkLets` / `Surf.eval_mkLets` / `Surf.wtPat_lower` / `Surf.matchPat_lower` / `Surf.binopResult_result` | 変換の部品の対応: ブロックの束縛の列を `let_` の入れ子にする `Surf.mkLets`(コンパイラの `mkLets` と同じ畳み込み)の型付けと評価、パターンの型付けと照合は変換で変わらない、注釈の無い二項演算の型付けは被演算子の型を注釈にした Core の型付けと同じ | — |
| `Surf.lowerS_sound`(`Surf.lowerS_total` / `Surf.lowerS_wt` / `Surf.lowerS_Sem`) | **spec の Surface AST → Core の対応(C50)**: `Surf.wtS Γ e = some τ` なら `∃ c, Surf.lowerS Γ e = some c ∧ wtS Γ c = some τ ∧ ∀ ρ, Γ = ρ.ctx → ∀ P, Surf.Sem ρ e P → Sem ρ c P` — 適格な spec の AST には frontend から独立の変換 `Surf.lowerS` が定まり(`lowerS_total`)、その Core は同じ文脈で適格で(`lowerS_wt`)、対応する任意の環境で AST の意味は Core の意味(`lowerS_Sem`)。`Surf.wtS.mutual_induct` で式・`let` の列・腕の列・腕を同時に示す(`Surf.lowerS_sound_all`。腕の列では網羅性の走査も変わらず、`proppyS` の一致も同時に) | AST の適格性。任意の AST・任意の対応する環境・任意の意味 |
| `Surf.Sem_lowerS_iff` | **双方向の同値(C50)**: 加えて `τ` が論理の位置の型なら、任意の命題 `P` について `Surf.Sem ρ e P ↔ Sem ρ c P`(AST の意味の存在 `Surf.Sem_exists` と Core の意味の一意性 `Sem_unique` から。一方向の含意ではない) | 同上 |
| `Surf.proppyS_lowerS` / `Surf.proppyS_lower` | 命題の区分 `proppyS`(Bool の `let` を命題に束ねるか値に束ねるか)は変換で変わらない: 任意の文脈 `Γ₀` で `proppyS Γ₀ c = Surf.proppyS Γ₀ e`(runtime の変換 `lower` は `lower.mutual_induct` の `proppyS_lower_all`) | 変換が定まること |
| `Surf.preserve_prop` | **AST の意味 ↔ 生成 Lean の読み(C50)**: `Surf.wtS Γ e = some τ`、`Surf.lowerS Γ e = some c`、`Γ = ρ.ctx`、`Surf.Sem ρ e P` なら `P ↔ denoteP ρ c`(`lowerS_sound` と C42 / C43 の `Sem_denote` の合成) | AST の適格性 + 変換結果 |
| `Surf.check_sound_prop` | **接続検査の健全性(AST、命題、C50 / C51)**: 仮引数の値の列 `xs` について、その型の文脈で適格な AST `e`、変換結果 `c`(`lows_<f>` が実際の Core と一致することを確かめる)、命題 `Q = denoteP (SEnv.ofList xs) c`(`conn_<f>` が実生成宣言について確かめる)から `Surf.Sem (SEnv.ofList xs) e Q`(実生成宣言の命題は AST の意味そのもの) | 同上 + 接続検査の成功 |
| `Surf.quant_sound` / `Surf.lowerBinders_sound` / `Surf.exhaustiveFrom_lowerPat_cons` / `Surf.proppyArms_lowerPat_cons` | 変換の部品の対応(spec): 量化の束縛の列(注釈の型 → `(名前, 型)`)が同じ文脈を作り、束縛を 1 つずつ剥がす `forallCons` / `existsCons` が Core の同じ規則に写る、腕のパターンとガードの有無が対応していれば網羅性の走査と `proppyArms` は変わらない | — |
| `Call.eval_total` / `Call.Eval_unique` / `Call.evalArgs_total` | **関数・input を含む Core の runtime の全域性と一意性(C54)**: `Call.wtR Δ Γ e = some t`(署名の文脈 `Δ` と局所の文脈 `Γ` で適格: 呼出し先が fn / input の署名を持ち実引数の数と型が合う)、`Γ = ρ.ty`、`Φ.Respects Δ`(関数環境が署名を守る: fn / input の鍵に型の合う実引数に型の合う結果を返す関数)なら `∃ v, Call.eval Φ ρ e = some v ∧ v.ty = t`、値は一意。実引数の列も同じ(`evalArgs_total`)。`Call.wtR.mutual_induct` で式・腕の列・腕・実引数の列を同時に示す(`Call.wtR_total_all`) | 適格性 + 署名を守る関数環境 |
| `Call.Sem_exists` / `Call.Sem_unique` | **関数・input を含む Core の spec の意味の存在と一意性(C54)**: `Call.wtS Δ Γ e = some τ`、`τ` が論理の位置の型、`Γ = ρ.ctx`、`Φ.Respects Δ`、`Ψ.Defined Δ`(spec 宣言の環境が署名のある鍵に定義されている)なら `∃ P, Call.Sem Δ Φ Ψ ρ e P`、意味は一意(fn / input の呼出しの規則 `callVal` と spec 宣言の呼出しの規則 `callSpec` は署名の phase で排他: `Call.not_value_and_spec`) | 同上 + spec 宣言の環境 |
| `Call.interp_respects` / `Call.interp_defined` / `Call.fn_total` / `Call.spec_defined` | **宣言群の意味は署名を守る(C54)**: 適格な宣言群(`Call.wtProg SigEnv.empty P = some Δ`: 依存順・鍵の重複なし・各本体がそれより前の署名だけで適格)と input の署名を守る任意の解釈 `I`(`FEnv.RespectsInputs`)について、宣言群の意味 `Call.interp I P` の関数環境は `Δ` を守り(各 fn は型の合う任意の実引数に型の合う値を返す: `fn_total`)、各 spec 宣言の意味は定義されている(`spec_defined`)。宣言群の帰納法(`Call.Interp.step_inv` / `Call.interpFrom_inv`) | 宣言群の適格性 + input の解釈が署名を守る |
| `Call.spec_meaning` | **spec 宣言の意味は本体の意味(C54)**: 適格な宣言群の spec 宣言 `k` の意味 `F` は、型の合う任意の実引数 `vs` について、実引数を束ねた環境での本体の(それより前の宣言の意味の下の)意味 `Q` と同値(`F vs ↔ Q`)。`Interp.step` の `∃ P, Sem … P ∧ P` は、本体の意味が存在して一意なので既定値や `False` ではなく本体の意味そのもの | 同上 |
| `Call.wtProg_fresh` / `Call.wtProg_sig` / `Call.wtProg_mono` | 宣言群の適格性の補題: 各宣言の鍵は始めの文脈に無く(重複しない)、各宣言の署名は結果の文脈にあり、始めの署名は保たれる | — |
| `Surf.Call.eval_total` / `Surf.Call.Eval_unique` / `Surf.Call.evalArgs_total` | **関数・input を含む Surface AST の runtime の全域性と一意性(C54)**: `Surf.Call.wtR T Γ e = some t`(宣言表 `T` と束縛文脈 `Γ : SCtx` で適格: 呼出し先の経路が局所名に隠されず表の fn / input に解決し、実引数(位置 / 名前付き)の型が `arrange` で仮引数の順に並べ替えられて一致する。UFCS は受け手を先頭の位置引数に)、`Γ = ρ.ctx`、`Φ.Respects T.Δ`(関数環境が表の署名を守る)なら `∃ v, Surf.Call.eval T Φ ρ e = some v ∧ v.ty = t`、値は一意。実引数の列(構文解析の順、名前付きは名前つき)も同じ(`evalArgs_total`)。`Surf.Call.wtR.mutual_induct` で式・`let` の列・腕の列・腕・実引数の列を同時に示す(`Surf.Call.wtR_total_all`)。局所名による隠蔽は文脈と環境で一致する(`headBound_ctx` / `ufcs_ctx`) | 適格性 + 署名を守る関数環境 |
| `Surf.Call.arrange_map` / `Surf.Call.arrange_vals` | **名前付き引数の並べ替えは payload の写像と可換**: `arrange ps (args.map (mapArg f)) = (arrange ps args).map (List.map f)`(`assign` は名前だけを見る)。したがって実引数の値の列の型の列が仮引数の順に並べ替えられて仮引数の型に一致するなら、値の列も同じ順に並べ替えられて型が合う(`arrange_vals`: 型付けの並べ替えと評価の並べ替えが一致する) | — |
| `Surf.Call.Sem_exists` / `Surf.Call.Sem_unique` | **関数・input を含む Surface AST の spec の意味の存在と一意性(C54)**: `Surf.Call.wtS T Γ e = some τ`、`τ` が論理の位置の型、`Γ = ρ.ctx`、`Φ.Respects T.Δ`、`Ψ.Defined T.Δ` なら `∃ P, Surf.Call.Sem T Φ Ψ ρ e P`、意味は一意(fn / input の呼出しの規則 `callVal` / `ufcsVal` と spec 宣言の呼出しの規則 `callSpec` / `ufcsSpec` は表の署名で排他、注釈の無い `==` の `eqNat` / `eqForm` は `Surf.Call.Sem_not_nat` で排他)。`Surf.Call.wtS.mutual_induct` で式・`let` の列・腕の列・腕を同時に示す(`Surf.Call.Sem_exists_all`) | 同上 + spec 宣言の環境 |
| `Surf.Call.Sem_not_nat` / `Surf.Call.eval_mono` | 論理の位置の式(`Sem` の導出のある式)は対応する評価の環境(`Agree`: 値の束縛と束縛の有無を保ち、命題に束ねた名前に Nat の値を与えない)で Nat の値に評価されない。評価の単調性 `eval_mono`: 値の束縛と束縛の有無(局所名が大域名を隠すこと)を保つ環境の拡張 `SEnv.Sub` は定まっていた値を変えない(呼出しの評価は実引数の値と隠蔽だけに依る。`Surf.Call.eval.mutual_induct` の `eval_mono_all`) | — |
| `Surf.Call.interp_respects` / `Surf.Call.interp_defined` / `Surf.Call.fn_total` / `Surf.Call.spec_defined` | **Surface AST の宣言群の意味は署名を守る(C54)**: 適格な宣言群(`Surf.Call.wtProg P = true`: 依存順・鍵と単純名の重複なし・各本体がそれより前の宣言の表 `tableOf P seen` で適格)と input の署名を守る任意の解釈 `I`(`Surf.Call.RespectsInputs I P`)について、宣言群の意味 `Surf.Call.interp I P` の関数環境は宣言群全体の表 `tableOf P P` の署名を守り(各 fn / input は型の合う任意の実引数に型の合う値を返す: `fn_total`)、各 spec 宣言の意味は定義されている(`spec_defined`)。宣言群の帰納法(`Surf.Call.Interp.step_inv` / `interpFrom_inv`)で、表の署名は宣言を 1 つ足すごとにその宣言の鍵だけで伸びる(`Δ_append_self` / `Δ_append_ne`: 鍵の重複なしと各宣言の署名が対象であることから) | 宣言群の適格性 + input の解釈が署名を守る |
| `Surf.Call.spec_meaning` | **spec 宣言の意味は本体の意味(C54、Surface)**: 適格な宣言群の spec 宣言の意味 `F` は、型の合う任意の実引数 `vs` について、実引数を束ねた環境での本体の(それより前の宣言の表 `T'` と意味 `m'` の下の)意味 `Q` と同値(`F vs ↔ Q`)。`Core` 側の `Call.spec_meaning` と同じ構成 | 同上 |
| `Surf.Call.wtProgFrom_fresh` / `Surf.Call.wtProgFrom_sig` / `Surf.Call.wtProg_sig` / `Surf.Call.sigsOf_append_self` / `Surf.Call.sigsOf_append_ne` | 宣言群の適格性の補題(Surface): 残りの各宣言の鍵はそれまでの表に無く(重複しない)、各宣言の署名は宣言群全体の表にあり、宣言を 1 つ足した表の署名はその鍵だけで変わる | — |
| `Call.denote_sound`(`Call.preserve_nat` / `Call.preserve_bool`、`Call.denote_sound_self`) | **関数・input を含む Model の保存(C55)**: `Call.wtR Δ Γ e = some t`、`Γ = ρ.ty`、読みの署名 `Δ'` が `Δ` の fn / input の署名を含み(`SigEnv.SubV Δ Δ'`)、読みの関数環境 `Φ'` が `Δ'` を守り(`Respects`)、評価の関数環境 `Φ` が `Φ'` と署名の鍵で一致する(`FEnv.Agree Φ Φ' Δ`: fn / input の鍵には両方に関数があり、型の合う実引数に同じ結果を返す)なら `Call.eval Φ ρ e = some (Call.denoteV Δ' Φ' ρ t e)` — 独立意味論の結果が、呼出しを含む生成 Lean の読み(下の「関数・input の保存対象の意味論」: 呼出しは署名の仮引数の型で実引数を読んだ値の列を `Φ'` の関数に渡す)の値に一致する。`Call.wtR.mutual_induct` で式・腕の列・腕・実引数の列を同時に示す(`Call.denote_sound_all`)。`Φ = Φ'` の形は系 `Call.denote_sound_self` | 適格性 + 署名の包含 + 読みの環境が署名を守る + 2 つの関数環境の一致。任意の式・任意の対応する環境 |
| `Call.denoteArms_sound` / `Call.denoteArmsV_hit` / `Call.denoteArmsV_miss` / `Call.denoteArmsV_guard_true` / `Call.denoteArmsV_guard_false` | 腕の列の保存と腕の選択と束縛の形(呼出しを含む読みについて。`Denote.lean` の同名の定理と同じ内容) | 同上 |
| `Call.check_sound_nat` / `Call.check_sound_bool` | **接続検査の健全性(呼出しを含む、C57)**: 仮引数の値の列 `xs` について、署名 `Δ` とその型の文脈で適格な式 `e` と、値 `v = Call.denoteN Δ' Φ' (Env.ofList xs) e`(各実生成宣言の接続検査 `conn_<f>` が確かめる等式)から、`Φ'` と署名の鍵で一致する任意の環境 `Φ` で `Call.eval Φ (Env.ofList xs) e = some (.nat v)` | 同上 + 接続検査の成功 |
| `Call.wrap_respects` / `Call.ofGens_respects` | **実生成定数の環境は署名を守る(C56)**: 実生成の fn / input の Lean の関数(カリー化 `Call.Fn ps t`)を値の列の上の関数に包んだ `Call.wrap ps t g` は、型の合う任意の実引数に戻り型の値を返す(input の任意の全域関数の解釈もこの形)。実生成宣言の表 `Call.Gen`(形 `Call.Shape` = 鍵・input か・仮引数の型・戻り型 + 関数)から作った関数環境 `FEnv.ofGens gs` は表の署名 `SigEnv.ofShapes (gs.map Gen.shape)` を守る | — |
| `Call.exists_fn` / `Call.input_representable` / `Call.inputs_representable` | **任意の input 解釈の Lean 表現(C56)**: `CallInputs.lean`。任意の署名を守る `List Val → Option Val` は、型の合う全引数で `wrap ps t g` と一致する Lean の値・全域関数 `g : Fn ps t` を持つ。`input_representable` は宣言の鍵・仮引数・戻り型を保ち、`inputs_representable` は同じ任意解釈の全 input の表現を同時に与える | input の署名遵守。標準 `Classical.choice` は数学的な関数表現の選択に使う。型外の挙動の等式や `SameInputs` は導かない |
| `Call.inputs_generated_agree` / `Call.SameInputs.agree` | **input 表現から生成環境への対応(C56)**: 任意の署名を守る元解釈を同時に Lean 表現へ写し、全 input の鍵・署名でその表現を受け取る生成環境との `InputsAgree` を得る。`InputsAgree` は型の合う全引数での結果の等式だけを要求し、型外の挙動は自由。従来の `SameInputs` はこの前提を含む | input 署名遵守と、生成側の各 input の lookup が選んだ `wrap` である証拠 |
| `Call.interp_inputs_agree` / `Call.interpFrom_inputs_agree` / `Call.fn_value_inputs` | **型内の input 一致から runtime 呼出しを合成(C56)**: 任意の適格な宣言群・input 解釈・対応生成環境について、`InputsAgree` と全 fn の `Evidence` から `FEnv.Agree` と各 fn の値の対応を導く。型外の関数等式を仮定せず、input の step では型内の一致を使い、fn の step では既存の一般保存定理と接続証拠を合成する。従来 API は `SameInputs.agree` を通す系 | 宣言群の適格性、input 署名遵守、生成環境の署名遵守・署名包含、型内の input 一致、全 fn の kernel 検査済み接続 |
| `Call.interp_prop_inputs_agree` / `Call.interpFrom_prop_inputs_agree` | **型内の input 一致から spec 呼出しを合成(C56)**: 同じ前提と依存 prefix ごとの全 spec の `SpecEvidence` から、独立宣言群の命題環境と生成命題環境の `PEnv.Agree` を導く。任意の型の合う引数で双方向同値。runtime 呼出しと spec 呼出しの双方を含む | 全 fn/spec の接続証拠を要求する。呼出しを含む Surface 保存は `SurfaceCallProg.lean` / `SurfaceCallStatementsCheck.lean` が与える(「Surface / Core の宣言群の意味の対応」)。input のみの別モジュールと、別モジュールのfn/spec呼出し先への実生成接続は検査する |
| `Call.typed_only_agree` / `Call.typed_only_not_same` | **型外の保証境界の対照(C56)**: 型外でも 7 を返す元解釈と、型外では `none` となる Lean 関数の `wrap` は `InputsAgree` を満たすが `SameInputs` は満たさない | 型内の一致を関数全体の等式へ強化しない。両定理を kernel 検査・公理監査する |
| `Call.illtyped_total` / `Call.illtyped_not_equal` | **保証範囲の対照**: 型外の引数でも値を返す解釈は署名遵守を満たすが、型外で `none` を返す `wrap` と全引数で等しくはならない | 型の合う引数だけで一致させる必要を kernel 検査 |
| `Call.Sem_denote`(`Call.Sem_denote_all` / `Call.Sem_denoteP` / `Call.check_sound_prop`) | **呼出しを含む spec 式の一般同値(C55)**: `wtS Δ Γ e = some τ`、対応局所環境、読みの値環境の署名遵守、値環境の `FEnv.Agree` と命題環境の `PEnv.Agree`(型の合う任意の実引数で双方向同値)から、`Sem Δ Φ Ψ ρ e P` の命題は `denoteP Δ Φ' Ψ' ρ e` と同値。値呼出しの Bool 境界、spec 呼出し、論理・比較・等値・量化・let・if・ガード付き match を扱う。`Sem_denoteP` は適格な式の意味の存在と合わせて読みが意味であること、`check_sound_prop` は実生成命題と読みの同値から意味を導く | 任意の適格式・対応環境。環境一致は呼出し先の意味の一致という明示的な条件。宣言群では `interp_prop_agree` が接続証拠からこの条件を導く |
| `Call.interp_agree`(`Call.interpFrom_agree`) | **宣言群の意味と実生成定数の一致(C55 / C56 / C57)**: 適格な宣言群 `P`(`Call.wtProg SigEnv.empty P = some Δ`)、input の署名を守る任意の解釈 `I`、署名 `Δ'`(`SigEnv.SubV Δ Δ'`)を守る実生成定数の環境 `Φ'` について、input の鍵で `I` と `Φ'` が同じ(`Call.SameInputs I Φ' P`: 同じ input 解釈)で、各 fn に接続の証拠(`Call.Evidence Δ' Φ' P`: 各 fn に `Call.FnConn` — 型の合う任意の実引数で `Φ'` の関数の値 = 仮引数に実引数を束ねた環境での本体の読み)があれば `FEnv.Agree (Call.interp I P).Φ Φ' Δ` — 宣言群の意味(呼出し先の本体を評価する閉包)は実生成定数の環境と署名の鍵で一致する。宣言群の帰納法で、各 fn の本体の評価を、それより前の宣言についての一致(帰納法の仮定)と `Call.denote_sound` で実生成定数の値に結ぶ = 呼出し先の証拠の呼出し側への合成 | 宣言群の適格性 + input の解釈が署名を守る + 同じ input 解釈 + 各 fn の接続の証拠 |
| `Call.interp_prop_agree`(`Call.interpFrom_prop_agree` / `Call.specConn_of_curried` / `Call.curried_wrapP`) | **spec 宣言群の合成(C55)**: 適格な宣言群、同じ任意 input 解釈、全 fn の `Evidence` と全 spec の `SpecEvidence` から `PEnv.Agree (interp I P).Ψ Ψ' Δ` を導く。`SpecConn` は任意の型の合う実引数で、その宣言より前の署名での本体の読みと実生成命題を接続する。依存 prefix の値一致と命題同値を帰納的に更新し、独立意味論の `∃ Q, Sem … Q ∧ Q` を読みと双方向同値にする。カリー化の接続を `specConn_of_curried` で証拠へ写す | 宣言群の適格性 + input 署名遵守 + 同じ input 解釈 + 全 fn/spec の kernel 検査済み接続。Surface からの合成は `Surf.Call.interp_lower_agree` / `spec_sem_denote`。input のみの別モジュールと、別モジュールのfn/spec呼出し先への実生成接続は検査する |
| `Call.fn_value` | **fn の意味は実生成定数の値(系)**: 宣言群の各 fn `k` について、`Φ'` の関数 `f'` が型の合う実引数 `vs` に `v` を返すなら、`(Call.interp I P).Φ k = some f` で `f vs = some v` | 同上 |
| `Call.SubV_of_cover` / `Call.fnConn_of_curried` | 検査プログラムの形との結び: 宣言群の各 fn / input の署名が表にあれば(`decide` で確かめる)`wtProg` の署名は表の署名に含まれる(`Call.wtProg_keys`: 署名の鍵は始めの文脈か宣言群の宣言のもの)。接続検査 `conn_<f>`(カリー化の形 `Call.Curried`: 仮引数ごとに量化し、実生成の関数に実引数を渡した値 = 実引数を束ねた環境での本体の読み)と、`Φ'` の鍵がその関数を包んだものであることから接続の証拠 `FnConn`(`Call.curried_wrap`) | — |
| `Surf.Call.interp_lower_agree`(`Surf.Call.interpFrom_lower_agree`) | **Surface / Core の宣言群の意味の対応(C55 / C57)**: 適格な Surface の宣言群 `P`(`Surf.Call.wtProg P = true`)と適格な Core の宣言群 `C`(`Call.wtProg SigEnv.empty C = some Δ`)が宣言ごとに対応し(`Surf.Call.ProgLower P C`: `Surf.Call.DeclLower` の列 — 鍵と署名(仮引数の名前と型・戻り型)が同じで、fn の本体はその宣言より前の宣言の表 `tableOf P seen` での独立 lowering `Surf.Call.lower`、spec 宣言の本体は `Surf.Call.lowerS` の実出力、input は本体なし)、`I` が input の署名を守る任意の解釈なら、同じ `I` の下の宣言群の意味は署名の鍵で一致する: `FEnv.Agree (Surf.Call.interp I P).Φ (Call.interp I C).Φ Δ`(fn / input は型の合う任意の実引数で同じ値)と `PEnv.Agree (Surf.Call.interp I P).Ψ (Call.interp I C).Ψ Δ`(spec 宣言は型の合う任意の実引数で双方向同値)、および `(tableOf P P).Δ = Δ`。宣言群の帰納法で、fn の段は `Surf.Call.lower_eval_agree`、spec 宣言の段は `lowerS_denote` / `lowerS_denoteP` と `Call.Sem_denote_self` / `Call.Sem_denoteP`(読み `Call.denoteP` を経由した全 spec 式の一般双方向同値)、input の段は同じ解釈(残りの input の鍵で両者が同じ)を運ぶ | 両宣言群の適格性 + 宣言ごとの対応(鍵・署名・独立 lowering の実出力)+ input の解釈が署名を守る。翻訳の正しさ・呼出し先の正しさは仮定しない |
| `Surf.Call.spec_sem_denote` | **Surface の宣言群の意味の下での spec 本体と実生成環境での読み(C55 / C57)**: 上の対応と、Core の宣言群の意味と実生成環境の対応(`Call.interp_agree` / `Call.interp_prop_agree` の結論 `FEnv.Agree (Call.interp I C).Φ Φ' Δ` / `PEnv.Agree (Call.interp I C).Ψ Ψ' Δ`)を推移(`Call.FEnv.Agree.trans` / `Call.PEnv.Agree.trans`、prefix への単調 `.mono`)で結び、prefix の表 `tableOf P (P.take i)` で論理の位置で適格な Surface の式 `e` と独立 lowering の実出力 `c` について、`Surf.Call.Sem (tableOf P (P.take i)) (Surf.Call.interp I P).Φ (Surf.Call.interp I P).Ψ ρ e (Call.denoteP … Φ' Ψ' ρ c)`(読み自体が意味)と、任意の意味 `Q` について `Q ↔ Call.denoteP … Φ' Ψ' ρ c` を与える。検査プログラムはこれに各 spec 宣言の実生成 Statements と読みの接続 `read_*` を合わせて、Surface AST → 実生成 Statements 宣言の同値証拠(`sstmt_*` / `sstmt_iff_*`)を書き、runtime は `Surf.Call.lower_denote_sound`(`sread_*`)に同じ対応を与えて実生成 Model の値への等式(`sfn_*`)を書く | 同上 + 実生成環境の署名遵守・署名の包含 + 全 fn / spec の kernel 検査済み接続 |
| `Surf.Call.Δ_take_eq` / `Surf.Call.Δ_full_eq` / `Surf.Call.Δ_take_subV` / `Surf.Call.Δ_take_sub` / `Surf.Call.Δ_step_of_lower` / `Surf.Call.Δ_take_of_lower` / `Surf.Call.tableOf_nil_Δ` / `Surf.Call.sigsOf_append_of_some` | 対応する宣言群の表の署名: prefix の表の署名は Core の prefix の署名の畳み込み(`SigEnv.ext` の `foldl`。検査プログラムの `Δprefix_*` との結び `ssΔ_*`)に等しく、宣言群全体の表の署名は Core の署名(`Call.wtProg_foldl`)、prefix の表の署名は全体の署名に含まれる(fn / input と spec 宣言の両方) | 宣言群の適格性 + 対応 |
| `Surf.Call.respectsInputs_of_lower` / `Surf.Call.DeclLower.key` / `Surf.Call.DeclLower.sig` / `Surf.Call.ProgLowerFrom.length` / `Call.FEnv.Agree.trans` / `Call.FEnv.Agree.mono` / `Call.PEnv.Agree.trans` / `Call.PEnv.Agree.mono` / `Call.Interp.step_Ψ_spec` / `Call.wtProg_foldl` / `SEnv.vals_ofList` | 対応の補題: Core の input の署名を守る解釈は対応する Surface の宣言群の input の署名も守る、対応する宣言は同じ鍵と署名、対応する宣言群は同じ長さ、署名の鍵での一致の推移と小さい署名への単調、Core の spec 宣言の意味の形、値だけを束ねた環境の値の部分 | — |
| `Surf.Call.lowerCallS_eq` / `Surf.Call.lowerCallS_spec_wt` / `Surf.Call.lowerCallS_spec_Sem` / `Surf.Call.lowerCallS_value_Sem` | spec位置の呼出しの局所合成。名前解決・署名・実引数の並べ替えからCoreの形を決め、引数ごとの型/評価対応から命題型または同じ命題の意味を合成する。Bool結果はtrueである命題に写す | 引数の対応は明示的な前提。全spec式の双方向同値は `Surf.Call.lowerS_sem_all` |
| `Surf.Call.SpecLetsBridge.sem_iff` / `Surf.Call.lowerStmtsS_sem_iff` | 子spec式と末尾の双方向意味対応から、任意の値・命題let列をCoreの入れ子のletへ合成する局所保存 | 明示的な `SpecLetsBridge`、同じ局所環境、署名を守る関数/input環境。公開入口はlet列の適格性と独立lowering出力も照合する。全spec式の一般帰納保存ではない |
| `Surf.Call.SpecArmsBridge.lower` / `Surf.Call.SpecArmsBridge.sem_iff` / `Surf.Call.lowerS_match_sem_iff` | 各腕のガード・本体の双方向対応から、任意のガード付きmatchの腕列を実lowerS出力へ合成する局所保存 | 明示的な `SpecArmsBridge`、同じ局所環境・任意spec解釈。scrutineeは適格な値で、関数/inputは署名を守る。意味の存在・全spec帰納保存・宣言群保存は結論にしない |
| `Surf.Call.lowerBinders_sem_iff` / `Surf.Call.lowerS_quant_equiv` / `Surf.Call.lowerS_quant_sem_iff` | 拡張後の任意環境における本体の双方向対応から、任意長のNat/Bool束縛列のforall/existsを実lowerS出力へ合成する局所保存。名前・順序・量化範囲と同名shadowingを保持する | 本体の `SpecSemEquiv`、束縛注釈と文脈の対応、同じ関数/input/spec解釈。公開入口は本体の適格性と実lowering出力も照合する。意味の存在・全spec帰納保存・宣言群保存は含めない |
| `Surf.Call.lowerS_cmp_equiv` / `Surf.Call.lowerS_cmp_sem_iff` / `Surf.Call.lowerS_eqNat_equiv` / `Surf.Call.lowerS_eqNat_sem_iff` / `Surf.Call.lowerS_eqForm_equiv` / `Surf.Call.lowerS_eqForm_sem_iff` | 値比較・Nat等値・Bool/Prop等値の局所双方向対応と実lowering出力の接続 | 値子式の型/独立lowering、署名を守る関数/input環境。命題等値は子SpecSemEquivと左辺の非Nat評価を要求する。全式/宣言群の保存は含めない |
| `Surf.Call.lowerS_logic_equiv` / `Surf.Call.lowerS_not_equiv` / `Surf.Call.lowerS_ite_equiv` / `Surf.Call.lowerS_logic_sem_iff` / `Surf.Call.lowerS_not_sem_iff` / `Surf.Call.lowerS_ite_sem_iff` | 子式の双方向対応から論理演算・否定・ifの意味証人を合成し、独立loweringの実出力へ接続する局所保存 | 子式の `SpecSemEquiv`、同じ環境と解釈。ifは両分岐の意味を要求し、意味不在を補わない。全spec帰納保存・宣言群保存は含めない |
| `Surf.Call.lowerS_typed_all` / `Surf.Call.lowerS_typed` / `Surf.Call.lowerS_total` / `Surf.Call.lowerS_wt` | 呼出しを含むspecの独立loweringの全域性と型保存。式・let列・腕列・腕の相互帰納から変換先の存在とCoreの同じ型を導く。命題の同値・宣言群の意味合成は含めない | 任意の宣言表・文脈・適格なspec式と型。実Coreとの一致は別途kernel検査 |
| `Surf.Call.lowerS_sem_all` / `Surf.Call.lowerS_equiv` / `Surf.Call.lowerS_sem_iff` / `Surf.Call.lowerS_Sem` / `Surf.Call.Sem_lowerS` / `Surf.Call.lowerS_sem_exists_iff` / `Surf.Call.lowerStmtsS_bridge` / `Surf.Call.lowerArmsS_bridge` / `Surf.Call.eval_not_nat_of_wtS` / `Surf.Call.lowerS_denote` / `Surf.Call.lowerS_denoteP` | 呼出しを含む全spec式の一般双方向同値。式・let列・腕列・腕の相互帰納で、let列 / 腕列 / 量化 / 論理 / 比較 / 等値 / 呼出し葉の局所合成を子式の帰納結果で結び、同じ命題がSurfaceの意味であることとCoreの意味であることの同値と意味の存在の一致を導く。命題等値の左子式がNatを評価しないことは `eval_not_nat_of_wtS`。`lowerS_denote` はCore→実生成Leanの読みまで合成する。宣言群からのcallee環境の対応は含めない | 任意の宣言表・文脈・適格なspec式、独立 `lowerS` の実出力、署名を守る任意の関数/input解釈、任意のspec解釈(不在を含む)、型付け文脈と一致する任意の環境。読みへの合成は `FEnv.Agree` / `PEnv.Agree` を前提 |

証明は型付けの関数帰納法(`wtR.mutual_induct` / `wtS.mutual_induct`。腕の列では網羅性の走査の状態を不変条件に持つ)と `Sem` の導出の帰納法。
翻訳の正しさは仮定しない(backend の出力はこれらの定義・定理に現れない)。検体(`NaruSem/Examples.lean`): 対象範囲は空でない、境界の挙動、
不適格な Core(スコープ外・型の不一致・対象外の構文・網羅しない `match`・値の位置の命題)は `none`、行き詰まりは `none` / 導出なし、読みの境界の挙動と
基礎段階の範囲(`basic`。`match` は C41 の段階)、`match` の読み(ガード不成立からの継続は外側の環境、Bool のリテラルの腕)、Statements の読み(値の `let` と
Bool の条件の生成形は任意の引数で `rfl`、論理の位置の `a == b` の意味 `(a = true) ↔ (b = true)` と読み `a = b` の同値、命題の `let` を隠すパターン束縛
(ガードと本体の `p` は値、残りの腕の `p` は外側の命題)、Bool の全要素の `exists`、命題の束縛のある環境での境界の一般形)— すべて `decide` / `rfl` または
導出の場合分けで kernel が検査する。実際の compiler 経路の検体は `tests/accept/sem_core.naru`(`naru_test semantics` が引用して `wtR` / `wtS` を検査し、
runtime 宣言と spec 宣言のすべてについて実生成宣言への接続も検査する)。

### Model の保存と実生成宣言への接続(`NaruSem/Denote.lean`、C40 / C41 / C44)

生成 Model の意味を、backend の文字列とは独立に Core から直接定めた **Lean での読み** `denoteN` / `denoteB`(Nat / Bool の総関数。対象外・不適格な
部分は既定値で、一般定理は適格な式にだけ対応を主張する)と腕の列の読み `denoteArmsN` / `denoteArmsB` で表す。読みは `Backend.Model.emitE` が書く Lean と
同じ演算・同じ形で書く:

| Core | 生成 Lean(`emitE`) | 読み | 独立意味論(`eval`) |
|---|---|---|---|
| Nat の `+ - * / %`、`min` / `max` | `a + b` …、`Min.min a b` / `Max.max a b` | `ArithOp.eval` / `NatMethod.eval`(同じ Lean の `Nat` の演算: `-` は 0 で切り詰め、`/ 0 = 0`、`% 0 = a`) | 同じ(等式) |
| Nat の `< <= > >=` | `Decidable.decide (a < b)` … | `CmpOp.evalNat`(`decide`) | 同じ(等式) |
| Bool の `< <= > >=` | `Ord.compare a b == .lt` / `!= .gt` / `== .gt` / `!= .lt` | `CmpOp.leanBool`(同じ形) | `CmpOp.evalBool`(`!a && b` …)— `CmpOp.leanBool_eq` |
| `==` / `!=` | `a == b` / `a != b`(`BEq`。Nat / Bool とも `instBEqOfDecidableEq`) | `EqOp.leanNat` / `EqOp.leanBool`(同じ形) | `decide (a = b)` / `decide (a ≠ b)` — `EqOp.leanNat_eq` / `EqOp.leanBool_eq` |
| `&&` / `\|\|` / `implies` / `!` | `a && b` / `a \|\| b` / `!a \|\| b` / `!a` | `LogicOp.eval` / `!` | 同じ(等式) |
| リテラル / 局所名 / `let` / `if` | `(n : Nat)` / `x` / `let x : T := v; b` / `if c then t else e` | `n` / 環境の参照 / 環境の拡張 / `if` | 同じ |
| `match`(非再帰、C41) | `emitMatchGuarded`: ガード無しの先頭の腕は `match s with \| p => b …`、最初のガード付きの腕 `p if g => b` は `\| _ =>` の中で `match (match s with \| p => if g then some b else none \| _ => none) with \| some g' => g' \| none => REST`(REST は先頭の腕を再び含む残りの腕の同じ形) | `denoteArmsN` / `denoteArmsB`: 腕を前から `matchPat` で試し、ガード無しの腕は束縛を足した環境の本体、ガード付きの腕は同じ `match (if g then some b else none) with \| some g' => g' \| none => rest`(`rest` は外側の環境: 束縛はその腕のガードと本体だけ) | `evalArms`(同じ腕の選択。適格で網羅的なら等しい: `denoteArms_sound`) |

採用方式(IDEAL.md「コンパイラ意味論保存の保証方式」): **汎用翻訳方式(一般定理)+ 生成物ごとの接続検査**。

1. 一般定理 `denote_sound`: 任意の適格な式(基礎の構文と非再帰の Nat / Bool の `match`)と任意の対応する環境について、独立意味論の結果 = 読みの値。
   腕の列・腕は `denoteArms_sound` / `denoteArm_sound`、腕の選択と束縛の形は `denoteArmsV_hit` / `_miss` / `_guard_true` / `_guard_false`。
2. 接続(生成物ごと、`lake exe naru_test semantics` の `ModelCheck.lean`): 検体 `tests/accept/sem_core.naru` を実際の CLI で生成した `Model/Sem/Core.lean` を
   そのまま Lean のモジュールとして import し、各 runtime 宣言 `f` について `conn_f : ∀ args, Model.Sem.Core.f args = denoteN (Env.ofList [(x, .nat x), …]) core_f`
   を kernel の定義的等しさで検査する。`match` の無い宣言(と変数・`_` のパターンだけの `match`)は `rfl` の項。リテラルパターンの `match` は Lean が
   scrutinee の場合分け(`dite (x = k)` / `Bool.casesOn`)に展開して自由変数のままでは読み(`matchPat` の `if`)と定義的に等しくないので、ドライバ
   (`NaruTest/Semantics.lean` の `proofOf`)が Core から scrutinee に現れる局所名と場合分けの深さ(Nat はパターンのリテラルの最大値 + 1、Bool は 1)を
   読み取り、`by intro …; cases x with | zero => rfl | succ x => …` の tactic を出す(場合分けの後は両辺が同じ形に簡約する。生成形の REST に再び現れる
   先頭の腕もそこで消える)。`core_f` は compiler の Core の引用で、`Quote.checkDecls` が実際の Core との一致を照合する(誤出力に合わせて期待側を変えない)。
   `pres_f : ∀ args, eval (Env.ofList …) core_f = some (.nat (Model.Sem.Core.f args))` は `check_sound_nat` が `wt_f`(適格性、`decide`)・`conn_f` から導く。
   `conn_f` / `pres_f` は公理監査に載る(`cases` の証明項も kernel が検査する)。
3. 負の検体(C46、`ModelWrong.lean`): 実生成文字列から作った誤翻訳 5 つ(`&&` と `||` を取り違えた `Wrong.logic`、2 つ目の束縛を取り違えた `Wrong.letShadow`、
   `true` / `false` の腕を入れ替えた `Wrong.matchBool`、ガードを否定した `Wrong.matchNat`、腕の束縛が後続の腕に漏れた形(`n == x` → `x == x`)の `Wrong.matchShadow`)
   は Lean の型検査を通るが、同じ正しい入力 Core への接続検査だけが失敗し(誤りはそれぞれの接続の定理の行にだけ出る)、正しい出力の対照は同じファイルで
   成功する。生成先は追跡対象外(`.lake/naru/test/semantics/`)で、追跡された `generated/` と実コードは壊さない。

保証の境界: 保証は「接続検査に成功した実生成宣言」に対するもので、検査しなかった宣言・対象外の構文・接続に失敗した出力は検証済みにならない
(コンパイラの全入力への無条件の保存ではない)。読みの定義が `emitE` と食い違えば接続検査が失敗する(読みを信頼する必要はない)。
基礎段階の範囲 `basic`(リテラル・局所名・`let`・`if`・二項演算・`!`・`min` / `max`)は段階の記録で、一般定理の前提ではない。`match` の保証は非再帰の
Nat / Bool の `match`(`emitMatchGuarded` の形)に限り、再帰 fn の中の `Nat` の `match`(`emitNatChain` の `if` の連鎖)・Option / record / enum のパターンは
対象外(C34 の回帰が別に守る)。Statements(`emitProp`)は次の節。

### Statements の保存と実生成宣言への接続(`NaruSem/DenoteProp.lean`、C42 / C43 / C44)

生成 Statements の意味を、backend の文字列とは独立に Core から直接定めた **命題の読み** `denoteP : SEnv → Core.Expr → Prop`(値の位置は Model の読み
`denoteN` / `denoteB` を `ρ.vals`(命題に束ねた名前はスコープ外)で読む。対象外・不適格な部分は `False` で、一般定理は適格な式にだけ対応を主張する)で表す。
読みは `Backend.Statements.emitProp` が書く Lean と同じ形で書き、`emitProp` と同じく `if` の条件と `==` / `!=` の両辺は `proppyS`(コンパイラの `proppy` と同じ
構文的な区分)が真なら命題として、偽なら値として読む:

| Core | 生成 Lean(`emitProp`) | 読み(`denoteP`) | 独立意味論(`Sem`) |
|---|---|---|---|
| `true` / `false` | `True` / `False` | `True` / `False` | `b = true`(`lit`) |
| Bool の値の局所名 | `x = true` | 環境の値 `b` で `b = true`(命題に束ねた名前はその命題) | `b = true`(`varVal`)/ 命題(`varProp`) |
| `&&` / `\|\|` / `implies` / `!` | `∧` / `∨` / `→` / `¬` | `LogicOp.prop` / `¬` | 同じ |
| Nat の `< <= > >=`、`==` / `!=` | `a < b` …、`a = b` / `a ≠ b`(被演算子は `emitE`) | `CmpOp.propNat` / `EqOp.propNat`(被演算子は `denoteN`) | 同じ(値は `eval`) |
| Bool の `< <= > >=` | `Ord.compare a b = Ordering.lt` / `≠ .gt` / `= .gt` / `≠ .lt` | `CmpOp.leanBoolProp`(同じ形) | `CmpOp.evalBool a b = true` — `CmpOp.leanBoolProp_iff` |
| 論理の位置の `==` / `!=`、両辺が値 | `a = b` / `a ≠ b` | `EqOp.propBool` | `(P ↔ Q)` / `¬ (P ↔ Q)` — `EqOp.propIff_bool`(値の等値と命題の同値の区別) |
| 同じく、どちらかが命題(C43) | `P ↔ Q` / `¬ (P ↔ Q)` | `EqOp.propIff` | 同じ |
| `if`(条件が Bool の値) | `if c = true then P else Q` | `if denoteB c = true then … else …` | `(C → P) ∧ (¬ C → Q)` — `denoteP_iff_denoteB_noProp` で結ぶ |
| `if`(条件が命題、C43) | `(C → P) ∧ (¬ C → Q)` | 同じ形 | 同じ |
| 値の `let` | `let x : Nat := v; P` / `let x : Bool := v; P` | 環境の拡張(値。同名の命題の束縛を隠す) | 同じ |
| 命題の `let`(C43) | `let x : Prop := P; Q` | 環境の拡張(命題) | 同じ |
| `match`(非再帰、C43) | `emitMatchGuardedProp`: ガード付きの腕は `(match s with \| p => g → b \| _ => True) ∧ (¬ (match s with \| p => g \| _ => False) → REST)`(ガードは Bool の値 `b = true` でも命題でも) | `denoteArmsP`: 腕を前から `matchPat` で試し、同じ形(`rest` は外側の環境: 束縛はその腕のガードと本体だけ) | `matchSkip` / `matchHit` / `matchGuard` |
| `forall` / `exists`(C43) | `∀ (x : T), …` / `∃ (x : T), …` | `denoteQuant`(`Ty.carrier`: Nat / Bool の全要素) | `forallCons` / `existsCons` |

採用方式は Model と同じ **汎用翻訳方式(一般定理)+ 生成物ごとの接続検査**。

1. 一般定理 `Sem_denote`(C42 / C43): 任意の適格な spec の式(`wtS`: リテラル・局所名(値 / 命題)・Bool / 命題の `let` と shadowing・Bool / 命題の条件の `if`・
   論理・比較・等値(値の `==` と命題の `↔`)・`!`・`min` / `max`・Nat / Bool の `forall` / `exists`・非再帰の Nat / Bool のガード付き `match`)と、任意の対応する環境
   (命題に束ねた名前も可)について、`Sem ρ e P → (P ↔ denoteP ρ e)`(両方向の同値。一方向の含意ではない)。`Sem_denoteP` は存在と合わせて
   `Sem ρ e (denoteP ρ e)`。証明は `Sem` の導出の帰納法(`Sem_denote_all`): 値の位置は Model の保存(`preserve_nat` / `preserve_bool` / `denote_sound`)で読みの値に、
   Bool の値の条件と両辺が値の `==` は境界 `denoteP_iff_denoteB_noProp`(`proppyS` が偽の式すべて。`proppyS` の文脈の合同 `proppyS_congr` を使う)で、命題の
   `let` は値の意味と読みの同値を命題外延性で環境に写し、`match` は腕の選択と束縛の形(`denoteArmsP_hit` / `_miss` / `_guard`)、量化は束縛ごとの同値を
   `forall_congr'` / `exists_congr` で束ねる。帰納法の仮定の型付けは `wtSNoExh`(`wtS` から `match` の網羅性と量化の束縛の非空の要求を除いたもの。残りの腕は
   それだけでは網羅的でなく、量化の束縛の末尾は空になる)で、保証の前提は `wtS`(`wtS_noExh`)。基礎段階の `basic` / `SCtx.NoProp` は段階の記録(`Sem_denote_basic` /
   `denoteP_iff_denoteB` は系)。
2. 接続(生成物ごと、`lake exe naru_test semantics` の `StatementsCheck.lean`): 同じ検体を実際の CLI で生成した `Statements/Sem/Core.lean` をそのまま Lean の
   モジュールとして import し、各 spec 宣言 `f`(基礎段階 `c42Decls` と C43 の段階 `c43Decls`)について
   `conn_f : ∀ args, Statements.Sem.Core.f args = denoteP (SEnv.ofList [(x, .val (.nat x)), …]) core_f`(`Prop` の等式)を kernel の定義的等しさで検査する。
   生成形 `True` / `x = true` / `a = b` / `Ord.compare a b = .lt` / `if b = true then` / `let x : T := v` / `let x : Prop := P`(zeta)/ `∀ (x : T), …` / `∃ (x : T), …` /
   `(C → P) ∧ (¬ C → Q)` / `P ↔ Q` / 変数・`_` のパターンだけの `match`(beta)/ ガード付きの腕の `(match … | p => g → b | _ => True) ∧ (¬ (…) → REST)` は読みと
   定義的に等しいので `rfl` の項。リテラルパターンの `match` は Model と同じくドライバの `proofOf` が scrutinee の局所名の `cases` を出してから `rfl`。
   `core_f` は compiler の Core の引用で、`Quote.checkDecls` が実際の Core との一致を照合する。`stage_f : basic core_f = true / false`(`decide`)は段階の記録。
   `pres_f : ∀ args, Sem (SEnv.ofList …) core_f (Statements.Sem.Core.f args)` は `check_sound_prop` が `wt_f`(適格性)・`form_f`(論理の位置の型)・`conn_f` から
   導く。`conn_f` / `stage_f` / `pres_f` は公理監査に載る。
3. 負の検体(C46、`StatementsWrong.lean`): 実生成文字列から作った誤翻訳 10(`∧` と `∨` を取り違えた `Wrong.specLogic`、含意の向きを反転した `Wrong.specCmp`
   (同値が一方向の誤りを退ける)、Bool の値を `= false` に写した境界の誤り `Wrong.specVar`、`if` の分岐を入れ替えた `Wrong.specIfBool`、`∀` を `∃` にした
   `Wrong.specForall`(`∀ n, n ≥ x` は x = 0 でだけ真、`∃` は常に真)、命題の `let` の束縛を取り違えた(`q` の代わりに `p` を参照する)`Wrong.specLetProp`、
   ガードを否定した `Wrong.specMatch`、`↔` を一方向の `→` にした `Wrong.specIffProp`、命題のガードの `∃` を `∀` にした `Wrong.specGuardProp`、腕の束縛が後続の腕に
   漏れた形(`n = x` → `x = x`)の `Wrong.specMatchShadow`。どれも正しい形と意味の異なる命題)は Lean の型検査を通るが、同じ正しい入力 Core への接続検査だけが
   失敗し、正しい出力の対照は同じファイルで成功する。

保証の境界: 保証は「接続検査に成功した実生成 spec 宣言」に対するもので、対象は `wtS` の範囲(基礎段階と、Nat / Bool の量化・命題の `let` と shadowing・命題の
条件の `if`・非再帰の Nat / Bool のガード付き `match`・命題を含む両辺の `==` / `!=`)。検体の宣言はすべて接続する(`c42Decls` + `c43Decls`)。spec 宣言の呼出し・
input・コレクション・record / enum・再帰は対象外(C35 の受理 / 拒否と C34 の回帰が別に守る)。命題を実行可能な Bool に戻す経路は意味論にも読みにも無い。

### Surface AST の意味論と適格性(`NaruSem/Surface.lean`・`SurfaceEval.lean`・`SurfaceTotality.lean`、C48)

構文解析の出力 `Naru.Expr`(`compiler/Naru/Ast.lean`)のうち、用語「Surface AST の保存対象」(Nat / Bool の Core 構文・演算に対応する式: リテラル、
局所変数、算術・比較・等値・論理と Nat の `min` / `max`、ブロックの `let`(型注釈は任意)と末尾式、`if`、`_` / 変数 / Nat・Bool のリテラルのパターンを持つ
ガード付き `match`、spec の Nat / Bool の `forall` / `exists`、Bool / 命題の局所束縛)を、frontend(`Typecheck.lean` の elaboration)から独立に定める。

| 項目 | 定義 |
|---|---|
| 対象の構文 | `Surf.Expr`(`.lit` / `.var` / `.method`(位置引数)/ `.binop` / `.unop` / `.ite` / `.matchE` / `.block`(`let` の列 `Surf.Stmt.letS` と末尾式)/ `.quant`)、`Surf.Arm`、`Surf.Pat`(`_` / 変数 / リテラル)、`Surf.Ty`(注釈。対象は `Nat` / `Bool`)、`Surf.Binder`。構文解析の出力の部分集合で、位置情報 `Span` もそのまま持つ。`Expr.toAst` が構築子ごとに `Naru.Expr` へ埋め込む(情報を落とさない)。対象外の構築子(呼出し・欄・record / list / tuple のリテラル・lambda・名前付き引数・`e;` 文)は写らない(`SurfaceQuote.ofAst?` が `none`)。リテラルは文字列・`()` も写るが `wtR` / `wtS` が対象外にする |
| 最小の宣言の包装 | `Surf.Decl`(種別 `DeclKind`、名前、位置、仮引数 `Surf.Param`(名前・型注釈・位置)、runtime の戻り型の注釈、本体)。`Decl.toAst` が `Naru.Decl` へ埋め込む(fn / spec 宣言が使わない欄は既定値)。適格性 `Surf.wtDecl d = some (.runtime ctx t)` / `some (.spec ctx τ)`: 仮引数の注釈がすべて Nat / Bool(`paramsCtx` が文脈)、runtime は種別 `fn` で戻り型の注釈が Nat / Bool かつ本体がその型(`wtR`)、spec は phase が spec の宣言(predicate / condition / regime / property / claim)で戻り型の注釈が無く本体が論理の位置の型(`wtS`、`isForm`)。observer・input・注釈が対象外の宣言は `none` |
| runtime の適格性 | `Surf.wtR Γ e = some t`: 対象の構文だけ、スコープ内の名前だけ、型が合う(注釈の無い二項演算は被演算子の型だけから `binopResult`)、`match` が網羅的(`Surf.exhaustive`: Core と同じ規則)。ブロックは `let` を前から型付けして文脈を伸ばし(`wtStmtsR`。注釈があれば値の型と一致 `annot`)、末尾式の型。末尾式の無いブロックと runtime の量化は対象外 |
| spec の適格性 | `Surf.wtS Γ e = some τ`: Core の `wtS` と同じ区分(論理の位置は `.val .bool` か `.prop`、値を要求する位置は `wtR Γ.vals`)。ブロックの `let` は値が命題(`Surf.proppyS`: コンパイラの `proppy` / Core の `proppyS` と同じ構文的区分。注釈は無いか `Bool`)なら名前を `.prop` に、そうでなければ値の型(注釈があれば一致)に束ねる(`wtStmtsS`)。注釈の無い `==` / `!=` は両辺が Nat の値なら `.val .bool`、そうでなければ論理の位置の結び |
| 意味(runtime) | 表示的意味論 `Surf.eval ρ e : Option Val`(`evalStmts` が `let` を前から評価して環境を伸ばす。`none` は行き詰まりで、既定値で埋めない)。値・環境・演算の意味(`Val` / `Env`、`ArithOp.eval` …)は Core の意味論と共有する — それらは言語の意味([language.md](language.md)「式」)であって変換結果ではない |
| 意味(spec) | 評価関係 `Surf.Sem ρ e P`(Core の `Sem` と同じ読み方。ブロックの `let` は `blockLetVal` / `blockLetProp`、注釈の無い `==` / `!=` は両辺が Nat の値なら値の等しさ `eqNat`、そうでなければ両辺の命題の同値 `eqForm`)。命題を Bool に戻す規則は無い |
| 意味が定まる | 上の表の `Surf.eval_total` / `Surf.Eval_unique` / `Surf.Sem_exists` / `Surf.Sem_unique`。`eqNat` / `eqForm` の排他性(論理の位置の式は Nat の値に評価されない `Surf.Sem_not_nat`。評価の単調性 `Surf.eval_mono` を使う) |
| 検体 | `NaruSem/SurfaceExamples.lean`(`decide`): 対象範囲は空でない(ブロック・型注釈・ガード付き `match`・`min` / `max`・量化・命題の `let`・注釈の無い `==`、fn / predicate の包装)、不適格な AST(スコープ外・型不一致・注釈の不一致・対象外の構文・網羅しない `match`(runtime / spec)・値の位置の命題・束縛型の無い量化、戻り型の合わない fn・戻り型のある spec 宣言・observer)は `none`、行き詰まりは `none` / 導出なし。実際の構文解析の出力の検体は `tests/accept/sem_core.naru`(`lake exe naru_test semantics` が各宣言(包装と本体)を引用し、`Surf.wtDecl` と `Surf.wtR` / `Surf.wtS` を `decide` で検査し、埋め込み `Decl.toAst` が構文解析の出力と `==` で一致することを照合する。これらの検体の宣言については、AST の型付けの結果が Core の型付けの結果と一致することもドライバが確かめる — 検体についての照合であって一般定理ではない) |

Core の意味を AST の意味と定義しない(`Surface*.lean` は Core の意味 `eval` / `Sem` も Core の型付け `wtR` / `wtS` も参照しない。値・環境・演算の意味
(`Val` / `Env` / `SEnv`、`ArithOp.eval` / `CmpOp.propNat` …)は言語の意味として共有する)。意味論が見ない前提: Surface AST は大域の宣言表を持たないので
`x.min(y)` / `x.max(y)` を常に Nat のメソッドとして読む(frontend は同名のユーザ宣言の fn があれば UFCS の呼出しに落とす。その場合は Core が `.call` になり、
AST → Core の接続検査が一致しない)。量化の束縛は型注釈のあるものだけが対象(frontend は注釈の無い束縛を推論で補うが、対象外として扱う)。
runtime と spec の AST → Core の対応と実際の frontend への接続は次の節(C49 / C50 / C51)。

### Surface AST → Core の対応(`NaruSem/Lower.lean`・`LowerExamples.lean`・`LowerSpec.lean`・`LowerSpecExamples.lean`、C49 / C50 / C51 / C52)

frontend(`Typecheck.lean` の `infer` / `check` / `inferStmts` / `checkPat` / `mkLets`)が Surface AST を Core に elaborate する変換のうち、用語
「Surface AST の保存対象」の部分を、frontend から独立に Lean の関数 `Surf.lower : Ctx → Surf.Expr → Option Core.Expr`(runtime)と
`Surf.lowerS : SCtx → Surf.Expr → Option Core.Expr`(spec)として定める(汎用翻訳方式、「コンパイラ意味論保存の保証方式」)。変換は型に導かれる: Core の
注釈(二項演算の被演算子の型、`let_` の型、`match_` の scrutinee の型、量化の束縛の型)を AST の型付け `Surf.wtR` / `Surf.wtS` から補う(frontend の推論・
単一化は参照しない)。

| AST(`Surf.Expr`) | 変換結果(`Core.Expr`) |
|---|---|
| リテラル / 局所名 | `.lit l .nat` / `.lit l .bool` / `.var x` |
| `l op r` | `.binop op (lower l) (lower r) tl.toTyV`(`tl` = `Surf.wtR Γ l`。論理は Bool、比較・等値は被演算子の型、算術は Nat) |
| `!a` / `x.min(y)` | `.unop "!" (lower a)` / `.method "Nat" "min" (lower x) [lower y] .nat` |
| `if c { t } else { e }` | `.ite (lower c) (lower t) (lower e)`(分岐のブロックは末尾式そのもの) |
| `match s { p if g => b, … }` | `.match_ (lower s) ts.toTyV [ .mk (lowerPat p) (lower g) (lower b), … ]`(`ts` = scrutinee の型。腕のガードと本体はパターンの束縛を足した文脈で。パターンは位置情報を落とすだけ) |
| `{ let x[: T] = v; …; e }` | `Surf.mkLets [(x, tv.toTyV, lower v), …] (lower e)` = `.let_ x tv.toTyV (lower v) (… (lower e))`(`tv` = 値の型。コンパイラの `Typecheck.mkLets` と同じ畳み込み。末尾式の無いブロックは対象外) |
| 量化・修飾名・対象外のメソッド・型の定まらない式 | `none` |

- 一般定理(上の表): `Surf.lower_sound` — 任意の適格な AST に変換が定まり、その Core は同じ文脈で適格で、任意の環境で AST の意味と Core の意味が一致する。
  翻訳の正しさは仮定しない(frontend の実装はこの定義・定理に現れない)。C40 / C41 と合成した `Surf.preserve_nat` / `Surf.preserve_bool` と、接続検査の健全性
  `Surf.check_sound_nat` / `Surf.check_sound_bool` が AST → Core → 生成 Lean をつなぐ。
- 実際の frontend への接続(C51、runtime): `lake exe naru_test semantics` が、実際に構文解析された各 runtime 宣言の AST(`ast_<f>`。埋め込みの一致を
  `Surf.Quote.checkDecls` が照合する)の `Surf.lower` が実際に出力された Core(`core_<f>`。`Quote.checkDecls` が一致を照合する)に等しいことを kernel の
  定義的等しさで確かめ(`low_<f> : Surf.lower actx_<f> ast_<f> = some core_<f> := rfl`。ドライバも `==` で先に照合する)、実生成宣言の接続 `conn_<f>` と合成した
  `apres_<f> : ∀ args, Surf.eval (Env.ofList …) ast_<f> = some (.nat (Model.Sem.Core.f args))`(`Surf.check_sound_nat` / `_bool`)を `#audit_axioms` で監査する。
  保証は「`low_<f>` と `conn_<f>` に成功した宣言」に対するもので、frontend の全入力への無条件の保存ではない。`x.min(y)` に同名のユーザ宣言 `min` があると
  frontend は UFCS の呼出し(`.call`)に落とすので `low_<f>` が一致しない(意味論が見ない前提。上)。
- 負の検体(C52、runtime): `LowerExamples.lean`(`&&` を `||` に取り違えた Core、2 つ目の束縛を改名した Core は適格だが変換結果でない。`neg_lower_swapped` /
  `neg_lower_let_shadow`)と、`naru_test semantics` の `SurfaceWrong.lean`(実際の Core の値から作った `WrongCore.logic`(最外の `||` → `&&`)/
  `WrongCore.letShadow`(2 つ目の `let_` の改名)/ `WrongCore.matchNat`(ガードの否定)は `wtR` を通り、AST の意味と食い違う具体環境がある(`diff_*`、`decide`)が、
  正しい AST の変換との一致 `conn_wrong_*` だけが失敗する。負の検体は意味の異なる Core にする(式全体で `&&` / `||` を入れ替えた `logic` は `a || b` と同値になる)。
  [testing.md](testing.md))。forall / exists の取り違えは spec の負の検体(下)で、`&&` / `||` の取り違えはこの runtime の検体が覆う(C52 の要求は runtime と spec の
  検体を合わせて満たす)。

spec の式(spec 宣言の本体)の変換 `Surf.lowerS`(`LowerSpec.lean`)は AST の spec の型付け `Surf.wtS` に導かれる。論理の位置(論理演算・命題の同値の `==` / `!=`・
`!`・`if`・`match` の腕・量化の本体・命題の `let` の値)は `lowerS` 自身で、値を要求する位置(算術・比較・Nat の等値の被演算子、`min` / `max`、scrutinee、値の `let` の値)は
runtime の変換 `Surf.lower` を値の文脈 `Γ.vals` で使う。

| AST(`Surf.Expr`、spec) | 変換結果(`Core.Expr`) |
|---|---|
| リテラル / 局所名(値・命題) | `.lit l .nat` / `.lit l .bool` / `.var x` |
| `l && r`(`\|\|` / `implies`) | `.binop op (lowerS l) (lowerS r) .bool` |
| `l == r` / `l != r` | 両辺が Nat の値(`wtR Γ.vals`)なら `.binop op (lower l) (lower r) .nat`(値の等値)、そうでなければ `.binop op (lowerS l) (lowerS r) .bool`(Bool の値の等値か命題の同値。frontend と同じ注釈) |
| `l < r` 等 / 算術 / `x.min(y)` | `.binop op (lower l) (lower r) tl.toTyV`(`tl` = 被演算子の型)/ `.binop op (lower l) (lower r) .nat` / `.method "Nat" "min" … .nat`(値の位置は runtime の変換) |
| `!a` / `if c { t } else { e }` | `.unop "!" (lowerS a)` / `.ite (lowerS c) (lowerS t) (lowerS e)` |
| `match s { p if g => b, … }` | `.match_ (lower s) ts.toTyV [ .mk (lowerPat p) (lowerS g) (lowerS b), … ]`(ガードと本体は束縛を値として足した文脈で) |
| `{ let x[: Bool] = v; …; e }` | `Surf.mkLets [(x, ty, cv), …] (lowerS e)`: 値 `v` が命題(`Surf.proppyS`)なら `cv = lowerS v` で注釈 `.bool`(frontend の命題の `let` と同じ)、そうでなければ `cv = lower v` で注釈は値の型 |
| `forall x: T { b }` / `exists` | `.quant q [(x, T.toTyV), …] (lowerS b)`(束縛は注釈の型。注釈の無い束縛は対象外) |
| 修飾名・対象外のメソッド・末尾式の無いブロック・型の定まらない式 | `none` |

- 一般定理(上の表): `Surf.lowerS_sound` — 任意の適格な spec の AST に変換が定まり、その Core は同じ文脈で適格で、対応する任意の環境で AST の意味は Core の意味。
  `Surf.Sem_lowerS_iff` — 任意の命題について AST の意味であることと Core の意味であることは同値(双方向。AST の意味の存在と Core の意味の一意性から)。
  命題の区分 `proppyS` は変換で変わらない(`Surf.proppyS_lowerS` / `Surf.proppyS_lower`)。量化範囲(`Ty.carrier` の全要素)・前提・結論は AST と Core の意味論が
  同じ規則で読み、命題を実行可能な Bool に戻す規則はどちらにも無い。翻訳の正しさは仮定しない。C42 / C43 と合成した `Surf.preserve_prop`(AST の意味 ↔ 生成 Lean の
  読み `denoteP`)と、接続検査の健全性 `Surf.check_sound_prop` が AST → Core → 生成 Lean をつなぐ。
- 実際の frontend への接続(C51、spec): `lake exe naru_test semantics` が、実際に構文解析された各 spec 宣言の AST(`ast_<f>`)の `Surf.lowerS` が実際に出力された
  Core(`core_<f>`)に等しいことを kernel の定義的等しさで確かめ(`lows_<f> : Surf.lowerS actx_<f> ast_<f> = some core_<f> := rfl`。ドライバも `==` で先に照合する)、
  実生成 Statements 宣言の接続 `conn_<f>` と合成した `apres_<f> : ∀ args, Surf.Sem (SEnv.ofList …) ast_<f> (Statements.Sem.Core.f args)`(`Surf.check_sound_prop`)を
  `#audit_axioms` で監査する。宣言の包装(識別・phase・仮引数と型・本体と環境の対応)は `wtd_<f>` / `actx_<f>_decl` が検査する(前節)。保証は「`lows_<f>` と `conn_<f>` に
  成功した宣言」に対するもので、frontend の全入力への無条件の保存ではない。
- 負の検体(C52、spec): `LowerSpecExamples.lean`(`forall` を `exists` に取り違えた Core、命題の `let` の束縛を取り違えた Core は適格だが変換結果でない。
  `neg_lowerS_swapped_quant` / `neg_lowerS_let_prop_wrong`)と、`naru_test semantics` の `SurfaceSpecWrong.lean`(実際の Core の値から作った
  `WrongCore.specForall`(`∀` → `∃`)/ `WrongCore.specExists`(`∃` → `∀`)/ `WrongCore.specLetProp`(命題の `let` の束縛の取り違え)/ `WrongCore.specMatch`(ガードの否定)は
  `wtS` を通り、正しい Core の読みと意味の食い違う具体環境がある(`diff_*`: 読みの非同値 `¬ (denoteP ρ WrongCore.f ↔ denoteP ρ core_f)` を明示の命題と証明で
  kernel に検査させる。`Sem_denote` により読みは意味そのもの)が、正しい AST の変換との一致 `conn_wrong_*` だけが失敗する。

### 関数・input の保存対象の意味論(`NaruSem/Call.lean`・`CallTotality.lean`・`CallExamples.lean`・`SurfaceCall.lean`・`SurfaceCallTotality.lean`・`CallQuote.lean`、C54。`CallDenote.lean`、C55〜C57 の runtime)

用語「関数・input の保存対象」(C39〜C53 の Nat / Bool の式・演算・束縛・ガード付き `match`・spec の量化を土台に、有限で非循環の宣言群に対する大域名で静的に識別できる
非再帰の fn / spec 宣言の呼出しと input の呼出しを加えたもの)の独立した意味論と適格性。既存の `Scope.lean` / `Eval.lean` / `Sem.lean` / `Surface*.lean` の定義は
変えず(C39〜C53 の条件はこの追加で拡大しない)、呼出しを含む式・宣言群のための定義を名前空間 `NaruSem.Call`(Core)/ `NaruSem.Surf.Call`(Surface AST)に並置する。
backend の出力・frontend の変換結果を意味と定義しない。

| 項目 | 定義 |
|---|---|
| 署名と環境(Core) | `Call.Sig`(fn / input: 仮引数の型と Nat / Bool の戻り型、spec 宣言: 仮引数の型。`Sig.phase`)、`Call.SigEnv`(修飾名 → 署名: 型付けの文脈)、`Call.FEnv`(修飾名 → 値の列 → 値: fn の意味と input の解釈)、`Call.PEnv`(修飾名 → 値の列 → 命題: spec 宣言の意味)。`valueSig?` / `specSig?` / `isValueKey` / `isSpecKey` |
| Core の適格性 | `Call.wtR Δ Γ e = some t`: `wtR` に `.call k args`(`valueSig? Δ k = some (ps, t)` で `wtArgs Δ Γ args ps`: 実引数の数と型が仮引数に一致。spec 宣言は runtime から呼べない)を加えたもの。`Call.wtS Δ Γ e = some τ`: fn / input の呼出しは値 `.val t`、spec 宣言の呼出しは `.prop`、実引数は値の位置(`wtR Δ Γ.vals`: 命題を渡さない)。`Call.proppyS` は spec 宣言の呼出しを命題でしか表せない式に数える(コンパイラの `proppy` と同じ) |
| Core の意味 | `Call.eval Φ ρ e`: `.call k args` は実引数を順に評価し(`evalArgs`)環境の関数 `Φ k` に渡す(鍵が無い・実引数が評価できない・関数が値を返さないときは `none`: 既定値で埋めない)。`Call.Sem Δ Φ Ψ ρ e P`: fn / input の呼出しの Bool の結果を「true である」という命題に写し(`callVal`)、spec 宣言の呼出しを `Ψ k vs`(`callSpec`)にする。`Δ` は `let` の値が命題か(`proppyS`)と呼出し先の phase の判定に使う。命題を Bool に戻す規則は無い |
| 宣言群(Core) | `Call.Decl`(`.fn key params ret body` / `.spec key params body` / `.input key params ret`)の列 `Call.Prog`(**依存順**: 呼出し先が前)。`Call.wtProg Δ₀ P = some Δ`: 前から順に、鍵が未使用で(重複なし)、本体がそれまでの署名だけで適格(`wtDecl`: fn は本体が戻り型の型、spec 宣言は本体が論理の位置の型、input は署名だけ)なら署名を足す。自己再帰・相互再帰・依存順でない・未解決の呼出し先・phase の誤り・引数の数と型の不一致・重複は `none`(保証対象でない) |
| 宣言群の意味(Core) | `Call.interp I P : Interp`(`Δ` / `Φ` / `Ψ`): input の解釈 `I : FEnv` から始めて(`Interp.init`)、宣言ごとに `Interp.step` が fn の意味(実引数を仮引数に束ね(`bindParams`: 数と型が合えば環境)本体をそれまでの環境で評価する関数)と spec 宣言の意味(実引数を束ねた環境での本体の意味 `∃ P, Sem … P ∧ P`)を足す。input は署名だけ(解釈は `I`)。`FEnv.Respects Δ` / `PEnv.Defined Δ` / `FEnv.RespectsInputs P`(input の解釈が署名を守る: 型の合う実引数に型の合う結果を返す任意の全域関数。特定の scenario の束縛ではない) |
| 意味が定まる(Core) | 上の表の `Call.eval_total` / `Call.Eval_unique` / `Call.evalArgs_total` / `Call.Sem_exists` / `Call.Sem_unique`、宣言群の `Call.interp_respects` / `interp_defined` / `fn_total` / `spec_defined` / `spec_meaning`(`CallTotality.lean`) |
| 宣言表(Surface) | `Surf.Call.Table`: 名前の経路の解決 `resolve`(修飾名そのもの、または宣言の単純名。コンパイル単位で一意)と修飾名の署名 `sig`(`DeclSig`: 仮引数の **名前** と型、fn / input の戻り型)。`tableOf all seen`: 解決は宣言群全体の名前で、署名は依存順でそれより前の宣言だけ。局所名は大域名を隠す(`headBound`: 呼出し先の経路の頭が束ねられていれば対象外。UFCS も局所名 `f` があれば適用しない。コンパイラの名前解決と同じ規則) |
| 実引数の順序(Surface) | `Surf.Call.arrange ps args`: 位置引数は仮引数の先頭から順に、名前付き引数は仮引数の名前で(`assign` の枡)。名前付きの後の位置引数・無い名前・二重の指定・不足・過剰は `none`(コンパイラの `matchArgs` と同じ規則)。実引数は構文解析の順に型付け・評価してから並べ替える(構造的再帰のため。評価は純粋なので順序は意味に関与しない) |
| Surface の構文 | `Surf.Call.Expr`(`Surf.Expr` に `.call`(呼出し先の式と実引数 `Surf.Call.Arg` = `.pos e` / `.named n e`)を加え、`.method` の実引数を名前付きも許す列にしたもの)/ `Arm` / `Stmt`、`Expr.toAst`(`Naru.Expr` への埋め込み)。宣言 `Surf.Call.Decl`(モジュール名・種別・名前・位置・仮引数・戻り型の注釈・本体(input は無し))、`Decl.key`(修飾名)、`Decl.sig?`、`Decl.toAst` |
| Surface の適格性 | `Surf.Call.wtR T Γ e` / `Surf.Call.wtS T Γ e`: この層では runtime の式も束縛文脈 `SCtx` の上で読む(runtime の式は値の束縛だけを参照し、命題の束縛名も局所名として大域名を隠す。fn の本体の文脈は仮引数 = すべて値)。`.call sp (.var _ path) args`: 頭が局所名でなく、実引数の型(構文解析の順。`wtArgs`)を `arrange` で仮引数の順にできて一致すれば fn / input は値、spec 宣言は命題(`callTy` / `callTyS`)。`.method sp r m args`: `ufcs T Γ m`(`m` が局所名でなく宣言に解決)なら受け手を先頭の位置引数にした呼出し、そうでなければ Nat の `min` / `max`(位置引数 1 つ)。`Surf.Call.proppyS` も spec 宣言の呼出し(UFCS を含む)を数える |
| Surface の意味 | `Surf.Call.eval T Φ ρ e`(`ρ : SEnv`。`.call` / UFCS は実引数を評価し `callVal` が `arrange` で並べて `Φ k` に渡す)、`Surf.Call.Sem T Φ Ψ ρ e P`(`callVal` / `callSpec` / `ufcsVal` / `ufcsSpec`: 呼出し先の署名・解決・局所名による隠蔽・並べ替えを前提に持つ)。`Φ` / `Ψ` は Core と共有(鍵 → 値の列 → 値 / 命題) |
| 宣言群(Surface) | `Surf.Call.Prog`(`Decl` の列、依存順)。`Surf.Call.wtProg P`: 前から順に鍵も単純名も未使用で、各宣言が `wtDecl (tableOf P seen)` で適格。`Surf.Call.interp I P`: `Call.interp` と同じ構成(本体はそれより前の宣言の表と環境で読む)。`Surf.Call.RespectsInputs` |
| 意味が定まる(Surface) | 上の表の `Surf.Call.eval_total` / `Eval_unique` / `evalArgs_total` / `Sem_exists` / `Sem_unique`(前提は `Γ = ρ.ctx`・`Φ.Respects T.Δ`・`Ψ.Defined T.Δ`。`T.Δ` は表の署名から仮引数の名前を落とした Core 側の署名の文脈)、名前付き引数の並べ替えの可換性 `arrange_map` / `arrange_vals`、評価の単調性 `eval_mono` と `Sem_not_nat`、宣言群の `Surf.Call.interp_respects` / `interp_defined` / `fn_total` / `spec_defined` / `spec_meaning`(`SurfaceCallTotality.lean`) |
| 生成 Model の読み(呼出しを含む。C55) | `Call.denoteN Δ Φ ρ e` / `Call.denoteB`(`CallDenote.lean`。`Denote.lean` の読みに `.call k args` を加えたもの: 署名 `Δ` の仮引数の型で実引数を読んだ値の列 `Call.denoteArgs` を関数環境 `Φ` の鍵 `k` の関数に渡し、Nat / Bool の結果を取り出す(無ければ既定値。一般定理は適格な式にだけ対応を主張する)。腕の列は `Call.denoteArmsN` / `denoteArmsB`)。実生成 Model の呼出し `Model.M.g <input の引数> args`(呼出し先の定数への適用)と input の参照 `name'` は、実生成定数の環境(下)の下でこの読みと定義的に等しい(接続検査) |
| 実生成定数の環境(C56) | `Call.Fn ps t`(実生成の fn / input の Lean の型、カリー化: `Fn [Nat, Bool] Nat = Nat → Bool → Nat`)、`Call.wrap ps t g`(値の列の上の関数に包む: 型の合う実引数には結果の値、合わなければ `none`。`wrap_respects`)、実生成宣言の表 `Call.Shape`(鍵・input か・仮引数の型・戻り型)/ `Call.Gen`(形 + 関数。fn は生成定数に(推移的に)使う input の引数を名前順に適用したもの、input はその解釈の Lean の値 — 署名に従う任意の全域関数)、`SigEnv.ofShapes` / `FEnv.ofGens`(`ofGens_respects`: 表から作った環境は表の署名を守る) |
| 宣言群の意味と実生成定数の一致(C55 / C56 / C57) | `Call.FEnv.Agree Φ Φ' Δ`(2 つの関数環境が署名の鍵で一致)、`Call.SigEnv.SubV`(署名の包含)、`Call.SameInputs I Φ' P`(同じ input 解釈: 宣言群の各 input の鍵で同じ)、`Call.FnConn` / `Call.DeclConn` / `Call.Evidence`(各 fn の接続の証拠)、`Call.Curried`(接続検査 `conn_<f>` の形)。上の表の `Call.denote_sound`(独立意味論の結果 = 読み。評価の環境は読みの環境と一致すればよい)/ `Call.interp_agree`(宣言群の意味 = 実生成定数の環境。呼出し先の証拠の呼出し側への合成)/ `Call.fn_value` / `Call.SubV_of_cover` / `Call.fnConn_of_curried` |
| 実生成 Model への接続(C55 / C56 / C57 / C58) | `lake exe naru_test semantics` が検体を実際の CLI で生成し、生成 Model `Model.Sem.Call`(fn は input の引数 `name'` を名前順に先頭に取る Lean の定義、ゼロ引数の fn は定数、呼出しは呼出し先の定数への適用)をそのまま Lean のモジュールにして `CallModelCheck.lean` を kernel に検査させる: 表 `shapes_call` / `gens_call <inputs>` から作った `Δgen_call` / `Φgen_call <inputs>`(input の Lean の値 `bias'` / `flag'` / `otherBias'` / `seed'` で量化)が表の署名を守る(`Φgen_call_respects`)、宣言群の各 fn / input の署名が表にある(`cover_call`、`decide`)、各 fn の接続 `conn_<f> <inputs> : ∀ args, Model.Sem.Call.<f> <fn の input 引数> args = Call.denoteN Δgen_call (Φgen_call <inputs>) (Env.ofList …) ccore_<f>`(kernel の定義的等しさ `rfl`。リテラルパターンの `match` は scrutinee の仮引数の `cases` の後に `rfl`。`ccore_<f>` は `CallScope.lean` の実際の Core の引用で `checkProg` が再コンパイルして一致を照合)と接続の証拠 `evid_<f>`(`fnConn_of_curried`)、宣言群全体の証拠 `cevid_call`、宣言群の意味と実生成定数の一致 `cgen_call`(`interp_agree`: 任意の input 解釈 `I` が `Φgen_call` と input の鍵で同じなら `interp I cprog_call` の fn / input は `Φgen_call` と署名の鍵で一致)、各 fn の値 `cval_<f>`(`fn_value`: 宣言群の意味の fn は型の合う任意の実引数で実生成定数の値)。負の検体 `CallModelWrong.lean`(実生成文字列から作る: `twoStep` が同じ署名の `base` を `callBase` の代わりに呼ぶ、`callNamed` の名前付き実引数の取り違え、`ufcs` の UFCS の受け手の誤対応、`useInputArg` の input `seed` の誤配線、`sharedInputs` の同型inputの交換)は型検査を通るが接続検査だけが失敗する(対照は成功)。検体の `match` の scrutinee は仮引数(呼出しの scrutinee のリテラル腕の接続は scrutinee の場合分けが要り、検査プログラムの `cases` は仮引数にだけ掛ける。一般定理は呼出しの scrutinee も扱う) |
| 検体 | `NaruSem/CallExamples.lean`(Core。`decide` / 構成): 対象範囲は空でない(fn / input / spec 宣言の呼出し、値の位置の呼出し、命題の `let`)、不適格な Core(未解決・引数の数と型・phase・値の位置の spec 宣言・命題の実引数・関数の値としての参照)、宣言群(適格な 2 段の呼出しと input、自己再帰・相互再帰・依存順でない・重複・input の引数の不一致は `none`)、input の解釈による値(同じ宣言群を別の解釈で読めば別の値)、署名に合わない解釈は行き詰まり(`none`)で `RespectsInputs` を満たさない、`fn_total` / `spec_defined` の実例、`callVal` / `callSpec` の実例、行き詰まり。実際の compiler 経路の検体は `tests/units/accept/sem_calls/`(下) |
| 実際の宣言群の引用 | `NaruSem/CallQuote.lean`: `Call.Quote.declOf?`(Core の fn / input / spec 宣言 → `Call.Decl`)/ `declWith` / `checkProg`(同じソースを再びコンパイルし、引用した各宣言が実際の宣言(鍵・種別・仮引数の名前と型・戻り型・本体)と一致し、実際の fn / input / spec 宣言がすべて引用されている — 宣言群全体)、`Surf.Call.Quote.ofAst?` / `ofDeclAst?`(構文解析の宣言 → `Surf.Call.Decl`。モジュール名つき)/ `expr` / `declWith` / `checkProg`(再構文解析と `Decl.toAst` の `==`)。`lake exe naru_test semantics` が検体 `tests/units/accept/sem_calls/`(input 4・fn 17・spec 宣言 10: 位置 / 名前付き引数・UFCS・ゼロ引数・2 段の呼出し・input の推移的な依存と共有・spec から runtime / spec の呼出し)の宣言群を依存順に引用した `CallScope.lean` / `SurfaceCallScope.lean` を書き、`Call.wtProg` / `Surf.Call.wtProg` と各宣言の署名を kernel の `decide` で、負の検体(実際の Core / AST から作る: 依存順の反転・違う呼出し先・phase・循環・重複・引数の数と型・未解決の名前・名前付き引数の名前 / 順序 / 二重指定)が不適格であること、input の解釈の下の fn の値と署名に合わない解釈の行き詰まりも kernel に検査させる([testing.md](testing.md)) |

言語の意味(呼出しは実引数を仮引数に束ねて本体を読む、名前付き引数は仮引数の名前で、UFCS は受け手を先頭の引数に、input は環境からの入力。[language.md](language.md)「式」
「scenario と observer」)はこの定義のために変えていない。この段階で保証するのは、「意味が定まる」こと(Core と Surface AST の両方: 適格な式・宣言群と対応する環境、
署名を守る任意の input の解釈について、runtime の値が存在して一意で、spec の意味が存在して一意で、各 fn は全域で各 spec 宣言の意味は本体の意味)と適格性の明示(C54)、
そして runtime の Core → 実生成 Model の保存(C55〜C57 の runtime 側: 任意の適格な宣言群・同じ input 解釈・型の合う任意の実引数について、宣言群の意味の fn の値 =
実生成定数の値。呼出し先の一般保存定理と kernel 検査済みの接続証拠を呼出し側へ合成する `Call.interp_agree`)である。

spec の式の一般同値は `CallDenoteProp.lean` の `Call.Sem_denote`。型付け署名 `Δ` を読みの呼出しと値/命題分類にも使い、より大きい署名 `Δ'` は値環境の署名遵守の前提に使う。
`PEnv.Agree` は各 spec 鍵に命題関数が存在し、型の合う任意の実引数で同値であること。Bool の if と等値を常に命題の形で読むため、backend の Bool の if / 値の等値とは定義的に異なる場合があり、接続は `↔` を使う。
`CallModelCheck.lean` は現在の Core の4 input(`seed`・`bias`・`otherBias`・`flag`)について `irepr_*` と全体の `ireprs_call` を kernel 検査・公理監査する。任意の `RespectsInputs` 解釈からゼロ引数の値と引数ありの関数を同時に表現できる。表現した関数と元解釈の一致は型の合う引数の範囲であり、関数全体の等式 `SameInputs` は導かない。`inputs_generated_agree` と `CallModelCheck.lean` の `cinputs_generated` はその表現を現在の実生成 input 引数へ渡す。同じ選んだ値・関数について、`cgen_inputs_call` と `CallStatementsReadCheck.lean` の `cprops_inputs_call` を `cinputs_connect` が合成し、任意の元解釈に対する runtime の全値対応と spec の双方向同値を同時に kernel 検査・公理監査する。input のみの別モジュール `Sem.Inputs` から `Sem.Call` の runtime / spec への実生成接続も検査する。呼出しを含む Surface 保存は `SurfaceCallProg.lean` / `SurfaceCallStatementsCheck.lean` が与える(「Surface / Core の宣言群の意味の対応」)。

同型inputの `bias` / `otherBias` (Nat → Nat) は別の鍵と別の生成引数を持つ。`inputPair` と `sharedInputs`、`specSharedInputs` の実Core・実生成宣言への接続と、同じ任意解釈を用いる宣言群の合成を検査する。二つのcalleeが共有する `bias` / `seed` の推移依存は一度ずつ名前順で渡し、期待input列との一致も検査する。runtimeの一方のcalleeだけで二解釈を交換する `Wrong.sharedInputs` と specの受け渡しで交換する `Wrong.specSharedInputs` は型が合っても正しい入力への接続が失敗する。対照と意味の差の反例 `different_sharedInputs` / `different_specSharedInputs` を kernel 検査・公理監査し、監査欠落を拒否する。この検体はCoreから生成Leanの接続であり、呼出しを含むSurface保存は `SurfaceCallStatementsCheck.lean` が別に検査する。

`CallStatementsReadCheck.lean` は同じ現在のソースから実際に生成・elaboration した10個の Statements 宣言について、任意の input 解釈・仮引数で命題が現在の引用 Core の読みと同値であることを検査・公理監査する。
命題環境の表 `Ψgen_call` は実生成 spec 定数を型に沿って包み、値環境には既存の `Φgen_call`、署名には同じ `cprog_call` の各宣言より前の有限 prefix を使う。引用の同一性は `CallScope` の再コンパイルで確認する。
`CallStatementsReadWrong.lean` は実生成文字列から6件の型の合う隔離出力を作る。`specCallSpec` の `∧`→`∨`、`specTwoStep` の spec 呼出し先を input 適用後に同じ Nat→Prop 署名の `specCallSpec` へ置換、`specNamed` の同型の名前付き引数の交換、`specUfcs` の受け手と引数の交換、`specBoolCall` が runtime の `boolCall` 経由で input に渡す解釈を `flag'` から `fun v => flag' (!v)` へ変更する。`specSharedInputs` は同型の `bias` / `otherBias` を spec→runtime の受け渡しで交換する。6件とも同じ正しい Core への接続定理の行だけが失敗し、正しい対照は任意の input 解釈・仮引数で成功する。
各誤出力には閉じた非同値の反例 `different_*` もある(順に `x=10`、`seed'=0,x=10`、`a=0,b=1`、`a=0,b=1`、`flag'=id,b=false`、`bias'=fun n => n*10,otherBias'=fun _ => 1,seed'=0,x=1`)。kernel 検査と公理監査を要求して、定義的等しさの相違だけを意味の違いと誤認しない。反例は一般保存定理と任意引数の接続証拠を補助するもので、代用ではない。
`CallComposeProp.lean` の `SpecEvidence` は宣言順に prefix 署名を更新して各 `SpecConn` を束ねる。検査は各 `read_*` を `spevid_*` に写し、全宣言の `spevid_call` と `cprops_call` を kernel 検査・公理監査する。`cprops_call` は任意の署名を守る input 解釈で、同じ input を渡す独立宣言群の命題環境と実生成 `Ψgen_call` の双方向同値を示す。全 fn の接続も必要で、証拠欠落を仮定で埋めない。呼出しを含む Surface AST → Core の値/命題対応は `SurfaceCallLowerSound.lean` / `SurfaceCallLowerSpecSemAll.lean`、宣言群の合成は `SurfaceCallProg.lean` が与える。input のみの別モジュールからの接続はこの検査に含む。
証拠は宣言と本体に結び付いている。`CallEvidenceCheck.lean` / `CallEvidenceWrong.lean` は、同じ署名の別宣言・変更前の Core の証拠と、呼出し先の証拠が欠けた束による runtime 合成を拒否する(C57)。
spec の `CallSpecEvidenceCheck.lean` / `CallSpecEvidenceWrong.lean` も、別宣言・変更前の Core の証拠の流用と、呼出し先の証拠欠落による全体の命題同値の合成を拒否する。
正しい対照では、同型で意味が異なる変更後 Core、全体の合成、呼出し先 `posBase` の証拠だけを含まない suffix の証拠を kernel 検査・公理監査する。
suffix は元の prefix 署名を保持し `specCallSpec` の接続を証明できるが、署名に `posBase` があることはその接続証拠の代用にならず、全体の `SpecEvidence` としては使えない。
失敗は3件の不正な証拠使用の行の型不一致に限定し、構文/import/未証明の穴による失敗を成功扱いしない。
有限の負の検体は拒否理由を確かめるもので、一般保存定理の代わりにはしない。
`lake exe naru_test semantics` の `CallScope.lean` / `SurfaceCallScope.lean` は、実際の宣言群に一般定理が適用できること(前提 `wtProg` の成立から
`cresp_call` / `cdef_call` / `sresp_call` / `sdef_call`: 署名を守る任意の解釈の下で宣言群の意味が署名を守り spec 宣言の意味が定義される)も kernel に検査させ、公理監査に載せる。
保証は「接続検査に成功した実生成宣言」の宣言群に対するもので、呼出し先を含む必要な証拠(`Evidence`)が欠けた宣言や対象外の宣言は検証済みにならず、コンパイラの全入力への
無条件の保存とは呼ばない。

### 信頼する部分・方式・未対応

- 信頼する部分: Lean kernel と elaborator、`Naru.compileFiles`(型検査・名前解決・Core への elaboration)の一般的な正しさは境界の外(IDEAL.md「対象外」)。
  ただし検体の宣言については、構文解析の出力 AST → 実際の Core の対応を成果物ごとに kernel が検査する(`low_<f>` / `lows_<f>`: 独立の変換の結果が実際の Core
  と定義的に等しい)ので、それらの宣言の AST → Core → 生成 Lean は型検査器を信頼せずに検証済みになる(`apres_<f>` は「実生成宣言の値 / 命題は AST の意味」で、
  意味の一意性 `Surf.Eval_unique` / `Surf.Sem_unique` により AST の唯一の意味)。
  Core の引用(`NaruSem/Quote.lean`)は、検査プログラムの中で同じソースを再びコンパイルして構造の等しさで照合する。Surface AST の引用
  (`NaruSem/SurfaceQuote.lean`)は、同じソースを再び構文解析して埋め込み `Expr.toAst` と `==`(`Naru.Expr` の構造の等しさ)で照合する。生成 Model の Lean への
  elaboration(`import Model.Sem.Core`)は Lean の elaborator に委ねる(接続検査はその結果の定数に対して行う)。
- 採用方式: 上の「Model の保存と実生成宣言への接続」と「Statements の保存と実生成宣言への接続」。Model は基礎段階(C40)と非再帰の Nat / Bool の `match`
  (C41)まで(接続はリテラルパターンの scrutinee の場合分け + `rfl`)。Statements は基礎段階(C42)と、Nat / Bool の量化・Bool / 命題の `let` と shadowing・
  Bool / 命題の条件の `if`・非再帰の Nat / Bool のガード付き `match`・命題を含む両辺の `==` / `!=`(C43)まで(接続は `rfl`、リテラルパターンの `match` は
  場合分け + `rfl`)。Surface AST → Core(C49 / C50)は汎用翻訳方式(runtime は `Surf.lower` + `Surf.lower_sound`、spec は `Surf.lowerS` + `Surf.lowerS_sound` /
  `Surf.Sem_lowerS_iff`)で、実際の AST と Core への接続は `rfl`(`low_<f>` / `lows_<f>`)、実生成宣言への合成は `apres_<f>`。
  関数・input(C55〜C57、runtime)は汎用翻訳方式(一般定理 `Call.denote_sound` と宣言群の帰納法 `Call.interp_agree`)+ 生成物ごとの接続検査(`conn_<f>`、`rfl`)で、
  呼出し先の証拠は `Call.Evidence` として呼出し側へ合成する(上の「関数・input の保存対象の意味論」)。
- 公理監査: `NaruSem/Audit.lean` の `#audit_axioms`。許容は `propext` / `Classical.choice` / `Quot.sound`(理由は同ファイル)。
- 未対応: 関数呼出しと input の **保存** のうち、spec(Statements)の読みと双方向の同値、呼出し・名前付き引数・UFCS を含む Surface AST → Core の変換と
  値 / 命題の対応、それらの実生成 Statements への接続と負の検体(C55〜C58 の残り。runtime の Core → 実生成 Model の層と実際の宣言群の接続・負の検体は上の
  「関数・input の保存対象の意味論」)、lambda・高階値、再帰、record / enum、Set / Table / List、モジュール全体・claim bundle 全体(IDEAL.md「延期」)。
  C49 / C50 の Surface AST → Core の対応は「Surface AST の保存対象」の式と最小の fn / spec 宣言の包装に限る(上の「Surface AST → Core の対応」)。ソース文字列からの保証
  (構文解析の正しさ)・型検査器全体の健全性・consensus 全体と基準実装の同値・プロトコルの Safety / Liveness・レビュー面は境界の外で、達成済みと呼ばない。
  `Set` / `Table` の生のリスト表現と数学的な集合 / 写像の区別は上の「Statements backend」の既知の制限のとおりで、後続拡張の設計判断は次の節。
- 文書との照合: `lake exe naru_test semantics` は、この文書の「一般定理」の表の第 1 列に挙げた定理名がすべて公理監査(`audit ok:`)に現れることと、
  [testing.md](testing.md)「コンパイラ意味論保存」に記載した検査のコマンドが実際に走らせるものと一致することを検査する(C47)。

### 後続拡張の設計判断(Set / Table・input・量化範囲。C47)

今回の保存対象は Nat / Bool の式と命題に限る(上)。言語の意味はこの証明のために変えていない(`docs/language.md` の意味 — Nat の演算の境界、Bool の順序、
`match` の束縛の範囲、Prop と Bool の境界、量化が型の全要素を回ること — がそのまま `NaruSem` の定義)。次の段階(IDEAL.md「延期」の展望: 非再帰の式 →
関数と input → 再帰とコレクション → 状態機械の一ステップ → 実行列と observer の対応 → Surface AST → Core)に進むときの設計判断と、保証への影響:

- **現状の `Set` / `Table`**: `NaruStd.Set` / `NaruStd.Table` は昇順・重複なしのリストだが、その不変条件は Lean の型に入っていない(上の「Statements backend」
  の既知の制限)。したがって生成 Statements の `∀ (s : Set T), …` / `∃ …` は Lean の型 `NaruStd.Set T` の全要素、すなわち未整列・重複ありの表現も回り、
  そこでは `size` / `==` / `subset` が naru の集合の意味(数学的な有限集合)からずれる。数学的な集合 / 写像と生のリスト表現は別物で、現状の一般定理はこの
  区別に触れない(`Ty` に `Set` / `Table` は無い)。
- **選んだ方針: 不変条件を型に持たせる**。`Set` / `Table` を保存対象に入れるときは、stdlib の表現を「整列・重複なしの証明欄を持つ構造」(部分型)に変え、
  生成 Model / Statements の型もそれにする。理由: (1) 生成 Statements の量化の形 `∀ (s : Set T), …` を変えずに、量化範囲が正規形 = 数学的な有限集合と
  一対一になる(`Ty.carrier` が「型の全要素」のままで `denoteQuant` と `Sem` の `forallCons` / `existsCons` の対応が保てる)。(2) Model の `==` / `size` /
  `subset` が構成によって数学的な意味と一致し、手書き Model の `Finset`(golden の基準)と同じ性質を型で持つ。(3) 独立意味論の値 `Val` に集合の値を足す
  とき、Lean の値との対応関係を等式(同じ表現)にでき、環境・引数の整形性の前提が増えない。退けた方針は「生の表現のまま、値の対応関係・環境・量化範囲に
  整形性を要求する」(意味論の `Val` を数学的な集合にし、対応関係 `Val ~ Lean の値` で Lean 側が正規形であることを要求し、量化は `∀ s, WF s → …` に制限する):
  生成 Statements の量化の形が変わる(既存の移植 claim の形が変わる)か、`Set` を含む量化が保証の外に残るかのどちらかになり、整形性の前提が環境と
  量化範囲のすべてに波及するため。
- **将来の証明義務**(今回は証明していない。保証の範囲に含めない): (i) 順序と等値の整合性 — 要素 / 鍵の型の `Ord` と `DecidableEq` が整合する
  (`compare a b = .eq ↔ a = b`。naru の `order` capability の約束で、`derive order` した record / enum にも及ぶ)。(ii) 構築・操作による不変条件保存 —
  `Set.empty` / `singleton` / `of` / `insert` / `remove` / `union` / `inter` / `diff` / `filter` / `map` / `flatMap`、`Table` の `insert` / `remove` / `mapValues`、
  `List.toSet`、`sort` がすべて整列・重複なしを保つ(stdlib の各操作の定理)。(iii) `forall` / `exists` の量化範囲の対応 — 正規形の型の全要素が数学的な
  有限集合 / 写像とちょうど対応し、独立意味論の量化範囲と一致する。これらが揃ってはじめて `Set` / `Table` を含む式の一般定理を主張できる。
- **input の将来の対応**: input は Lean の宣言にならず、それを使う Model の fn / spec 宣言の引数 `name'` として引き回される(上の各 backend の表)。
  保存定理は、特定の scenario の束縛ではなく、**同じ input 解釈(input の名前 → 値)を与えた任意の環境** を扱う形にする: 独立意味論の環境に input の
  解釈を足し、生成 Model の引数と生成 Statements の引数に同じ値を渡した任意の呼出しについて対応を示す(Core の input の署名と Lean の引数の対応は
  宣言ごとに固定)。scenario はその一例にすぎない。
- **関数呼出しの将来の対応**: 呼出し先の fn / spec 宣言の保存定理を前提に(宣言ごとの接続検査の成功を条件に)呼出し側を示す形で、モジュール全体の
  保証は宣言ごとの証拠の合成になる(無条件の保存ではない)。再帰は `Totality` が受理する構造的再帰 / fuel に限り、意味論側も同じ尺度で定める。

これらは段階的な展望であり、今回の限定範囲の保証(上の「保証の境界」)と混同しない。最終の文書・記録はこの範囲で既存資産(`docs/language.md`、stdlib、
移植ソース、golden の基準)と整合している。

`tests/units/accept/sem_calls/` は `src/Sem/Inputs.naru` に4 input、`src/Sem/Callees.naru` に基礎の3 fn(`base`・`zero`・`addTo`)と1 spec(`posBase`)、`src/Sem/Call.naru` に呼出し側を置く。runtime→runtime・spec→runtime・spec→spec の別モジュール呼出し、修飾参照・位置/名前付き引数・UFCS・ゼロ引数を実生成 `Model.Sem.Callees` / `Statements.Sem.Callees` と呼出し側へ接続する。単一ファイルの受理例 `tests/accept/sem_call.naru` も維持する。`Call.Quote.checkProg` / `Surf.Call.Quote.checkProg` は同じ3ファイルを再コンパイルし、引用の識別・署名・本体と全31宣言の網羅を照合する。検体の宣言一覧を安定した依存順へ並べ、適格性をkernel検査する。`checkOmission` はinput元のModel/Statements不在、生成宣言の網羅、集約importと全依存の解決を検査する。任意解釈の接続・同型input交換のruntime/spec負検体はこの複数ファイル単位でkernel検査・公理監査する。モジュール全体の保存やSurface/Core宣言群の意味合成はこの接続では保証しない。

別モジュール呼出しの接続も同じ `semantics` / `regression` 入口で再検査する。実際のCoreの呼出し辺と生成Model/Statementsのimportを照合し、calleeの生成モジュールを先にLeanとしてビルドする。全17fn/10specの任意引数の接続・宣言群の合成証拠、公理監査、別宣言/古いCore/callee証拠欠落のruntime/spec各3件、Model5件/spec6件の型が合う誤出力検査は維持する。Surface/Core宣言群の意味合成は後述の `SurfaceCallProg.lean` が与えた(spec側のSurface保存は後述の `SurfaceCallLowerSpecSemAll.lean` が与えた)。

呼出しを含む runtime の構造的対応は `SurfaceCallLower.lean` の `Surf.Call.lower T Γ` で検査する。
`T` は宣言群全体の名前と各宣言の前までの署名、`Γ : SCtx` は実際の仮引数の文脈である。
`lowerArgs` は構文解析順で変換し、`lowerCall` は名前解決・値の署名を検査して `arrange` で仮引数順に並べる。
UFCS は受け手を先頭の位置引数にし、局所の命題束縛も大域名を隠す。ブロック・let・if・ガード付きmatch・算術等も変換する。
`SurfaceCallLowerCheck.lean` は現在の全17 fnの宣言包装・仮引数・本体・適格性・実Coreとの一致 `slow_*` を kernel 検査し、公理監査する。
`lowerCall_eq` は呼出し先・署名・並べ替えの対応から Core の呼出しの形を導く補題であり、意味保存定理ではない。
lowering の成功だけから型・スコープ・網羅性の成立は導かず、独立した適格性検査も要求する。
runtime式の値対応は以下の一般定理で検査する。宣言群の Surface / Core の意味の合成は後述の `SurfaceCallProg.lean` が与えた(spec の lowering の一般保存と双方向同値は後述の `SurfaceCallLowerSpecSound.lean` / `SurfaceCallLowerSpecSemAll.lean` が与えた)。

呼出しの局所的な合成は `Surf.Call.arrange_eval` / `arrange_wt` が担う。
名前を保った子引数ごとの評価・型の対応から、仮引数順のCore引数の評価と型を導く。
`lowerCall_eval` / `lowerCall_wt` は名前解決・値の署名・並べ替えの成功を使い、
`lower_call_eval` / `lower_ufcs_eval` はその結果を通常のSurface呼出しとUFCSに合成する。
環境・子式・値は任意で、calleeが存在しない場合や `none` を返す場合も同じ結果を保つ。
これらの局所補題では子式の対応、局所名による隠蔽、UFCSの判定を前提とする。全式の評価保存は以下の帰納定理でそれらを導く。
`SurfaceCallLowerExamples.lean` の名前付き引数・UFCS・ゼロ引数の引数評価・型対応・同型の値の交換対照をkernel検査・公理監査する。
具体的な対照は一般補題を補うもので、宣言群の合成保存や実生成LeanへのSurfaceからの接続を証明済みとはしない。


ブロックの局所合成では、呼出しの署名を受け取る `Surf.Call.wtBinds` と同じ関数・input環境を使う
`evalBinds` が、Coreの束縛列を前から読む。`wtR_mkLets` / `eval_mkLets` は任意の束縛列・環境・末尾式について、
その読みと `Surf.mkLets` による入れ子のletの型・部分評価を結ぶ。束縛は順序通りに上書きし、失敗した値を後続のletで埋めない。
`lowerStmts_cons_eval` は値の子式と後続列の対応を一つのletへ合成し、`lower_block_eval` は列と末尾式の対応を
実際の独立loweringのブロックへ合成する。Surfaceの局所環境は値・命題を区別するSEnvのままで、Coreへの対応は `.vals` で取る。
この局所補題では子式・列・末尾式の対応を合成前提とする。全式のruntime評価保存は以下の帰納定理で導き、宣言群の合成とspecのloweringは残る。
新しい4補題と7検体は公理監査と必須定理の欠落検査の対象である。

matchの局所合成は `Surf.Call.exhaustiveFrom_lowerArm` / `exhaustiveFrom_lowerArms` が
loweringに成功した腕のパターン・ガードの有無から網羅性の走査の一致を示す。
`lowerArm_eval` はパターン照合後の束縛環境での本体・ガードの対応と、元の環境での後続腕の対応を要求する。
`ArmsEval` は各腕の継続の証拠を同じ長さ・順序で束ね、`lowerArms_eval` が任意の長さの列の評価を合成する。
`lower_match_eval` はscrutineeと腕列の評価の対応を実際の独立loweringのmatchへ合成する。
`lower_match_wt` はCore子式の型とASTの網羅性からCoreのmatchの型を導く。
ガードfalseの後はパターン束縛を次の腕へ漏らさず、不在・失敗・Bool以外のガードは後続で成功にしない。
修飾名のゼロ引数inputを使う任意の関数・局所環境の検体、Boolの二つのリテラル腕、
ガードだけでは網羅しない対照、束縛漏れで生じる値と正しい結果の不一致をkernel検査する。
全6補題と13検体を公理監査・欠落検査するが、照合後の子式の対応は合成前提である。
全式のruntime評価保存は以下の帰納定理で検査する。Surface/Core宣言群の合成は後述の `SurfaceCallProg.lean` が与えた(specのloweringの一般保存は後述の `SurfaceCallLowerSpecSound.lean` / `SurfaceCallLowerSpecSemAll.lean` が与えた)。

runtimeのloweringの全域性と型保存は `SurfaceCallLowerSound.lean` で独立に検査する。
`Surf.Call.lower_typed` は任意の宣言表・束縛文脈・適格なruntime式に対し、変換先が存在し、
Coreの型がASTの型と一致することを示す。式・実引数・let列・腕列・腕の同時帰納で、
名前付き引数の印を保ったまま仮引数順へ並べ、局所命題の大域名の隠蔽、UFCS、
letの型注釈、matchの網羅性とガードを扱う。型付けと変換結果の正しさを同じ前提にせず、
前提は独立したASTの適格性だけである。`lower_total` と `lower_wt` はその系で、
現在の17 fnのAST/実Core一致 `slow_*` と適格性 `stype_*` から `sctyped_*` をkernel検査する。
これは型と変換の存在の保証であり、評価結果の一致は次の定理で別に検査する。specの双方向同値と宣言群の意味合成の証明は残る。

同ファイルの `Surf.Call.lower_eval` は、適格なruntime式とそのloweringについて、
同じ任意の関数・input環境 `Φ` の下で `Surf.Call.eval T Φ ρ e = Call.eval Φ ρ.vals c` を示す。
前提は `wtR T Γ e = some t`、`lower T Γ e = some c`、`Γ = ρ.ctx`、`Φ.Respects T.Δ`。
局所束縛の値・命題の区分と型、callee/inputの署名遵守を要求し、子式の対応は帰納法で導く。
式・let列・腕列・腕・実引数列を同時に扱い、名前付き引数・UFCS・ゼロ引数、
letのshadowingとガードfalse後の元の環境への継続を保つ。
`lower_eval_all` は5つの構文群を同時に証明し、`lowerStmts_eval` / `lowerArgs_eval` /
`lowerArms_eval_wt` / `lowerArm_eval_wt` は対応する列・腕への適用である。
現在の全17 fnの適格性と実Core一致から、任意の対応環境での `seval_*` をkernel検査・公理監査する。
`Surf.Call.lower_eval_agree` は、署名に合う引数で呼出し結果が一致する別々の環境 `Φ` / `Φ'` に拡張する。
前提はASTの適格性・実Coreとの一致・対応文脈に加えて、`Φ'.Respects T.Δ` と `Call.FEnv.Agree Φ Φ' T.Δ`。
`Call.eval_agree` は既存のCoreの一般保存定理から両評価を同じ読みへ結び、型外の入力での閉包の等式は要求しない。
`Surf.Call.lower_denote_sound` は拡張署名 `Δ'` への `SigEnv.SubV` を使い、同じ対応証拠から `Call.denoteV Δ' Φ' ρ.vals t c` まで合成する。
現在17 fnの `seval_agree_*` / `sread_*` も任意の対応環境について検査し、全153証拠の欠落を拒否する。
型内でのみ一致するinput閉包は任意のNat引数で同じ結果を返し、Boolの型外引数では異なることをkernel検査する。
これらの定理は環境対応の証拠を前提にする。SurfaceとCoreの宣言群からその対応を導くこと、
specのloweringの双方向同値は後述の `SurfaceCallLowerSpecSemAll.lean` が、Surfaceから実生成Leanまでの宣言群の合成は後述の `SurfaceCallProg.lean` が与えた。

呼出しを含む spec の独立変換 `Surf.Call.lowerS` は `SurfaceCallLowerSpec.lean` にある。
現在の10 specのAST・prefix宣言表・包装・仮引数・本体と実Coreの一致を `SurfaceCallLowerSpecCheck.lean` の100証拠(一般双方向同値の適用 `sssem_*` を含む)でkernel検査・公理監査する。
論理の位置はspec変換、値の位置と実引数はruntime変換を使い、命題のlet・Bool値・量化・ガードを区別する。
`lowerCallS_eq` / `lowerCallS_spec_wt` / `lowerCallS_spec_Sem` / `lowerCallS_value_Sem` は、解決・署名と引数の型または評価の対応から呼出しの形・命題型・意味を局所的に合成する。
`SurfaceCallLowerSpecWrong.lean` の5件はspec呼出し先・名前付き引数・UFCS受け手・同型input・命題letの型が合う誤対応を作り、正しい対照を成功させ、一致の5行だけで失敗させる。
`SurfaceCallLowerSpecSound.lean` の `Surf.Call.lowerS_typed` は任意の宣言表 `T`・文脈 `Γ`・適格なspec式 `e`・型 `τ` に対し、`wtS T Γ e = some τ` から変換先の存在とCoreの同じ型を示す。
`lowerS_typed_all` は式・let列・腕列・腕を同時に帰納し、値の位置と実引数にはruntimeの型保存を使う。`lowerS_total` / `lowerS_wt` はその系である。
命題専用の構文区分も `proppyS_lowerS` で同じ文脈のAST/Core間で保存する。`proppyS_lowerS_view` は名前の可視性を保ち、命題束縛を増やさない `ScopeView Γ Γ₀` を前提に構文走査文脈へ拡張する。
`SurfaceCallProppy.lean` のruntime命題除外補題を使い、Propを実行可能なBoolへ戻さない。これらの公開補題も必須監査に含める。
現在10宣言の具体的なAST型 `sswtype_*` と実Core一致 `sslower_*` から一般定理を適用した `ssctyped_*` を検査・公理監査し、100証拠と一般定理の欠落を拒否する。
この型保存と変換の存在はspecの双方向同値を保証しない。一般のspec loweringの双方向同値は後述の `SurfaceCallLowerSpecSemAll.lean` が与えた。Surface/Core宣言群からの環境対応とSurface宣言群から実生成Model/Statementsへの接続は後述の `SurfaceCallProg.lean` が与えた。

`SurfaceCallLowerSpecSem.lean` の `Surf.Call.SpecLetsBridge.sem_iff` / `lowerStmtsS_sem_iff` は、呼出しspecの値と命題のlet列をCoreの入れ子のletへ合成する局所証明である。
`SpecSemEquiv.iff` は同値な意味の証人を移し、`SpecLetsBridge.lower` は証明書の束縛列と独立lowering出力の一致を示す。5補題と境界検体は公理監査と必須一覧の欠落検査に含め、`lake exe naru_test semantics` と同じ回帰入口から実行する。
子spec式と末尾式の双方向の意味対応を明示した証明書を前提に、値の束縛にはruntimeの一般評価保存を使い、命題の同値には命題外延性を使って束縛環境を揃える。
同じ名前の値・命題を再束縛する場合も扱う。この局所合成は子式の対応を全spec式の帰納法から導く一般定理ではない(それは後述の `SurfaceCallLowerSpecSemAll.lean` が与える)。Surface/Core宣言群からの環境対応と実生成Model/StatementsへのSurfaceからの接続は後述の `SurfaceCallProg.lean` が与えた。

`lowerS_block_sem_iff` は末尾の型と独立変換の一致も照合して、実際の `lowerS` が出力したブロック全体へこの局所合成を適用する。子式の双方向対応は引き続き証明書の前提である。

`SurfaceCallLowerSpecSemExamples.lean` の11検体は、ゼロ引数のBool inputを値として `q` へ束縛し、spec呼出しを命題として同じ `q` へ再束縛する。任意解釈の双方向対応と、spec解釈の存在を明示した意味の証人を検査する。閉じたinput=false / spec=Trueの正対照に対し、命題の子式を否定したCoreは同じ `.prop` 型で適格だが意味が `¬ True` となることと、正しいSurfaceの意味を保存しないことをkernelが検査する。5一般補題・11検体の監査欠落は失敗になる。

`SurfaceCallLowerSpecSem.lean` の `Surf.Call.SpecArmsBridge.sem_iff` は、各腕のガード・本体の `SpecSemEquiv` を前提に、任意の長さのガード付きmatchの腕列をCoreへ双方向に合成する局所証明である。
`SpecArmsBridge.lower` はパターン・順序・束縛型と独立 `lowerArmsS` の出力を照合し、`lowerS_match_sem_iff` は適格な値のscrutineeにruntimeの一般保存を適用して実 `lowerS` 出力へ接続する。関数/inputは署名を守る任意の解釈、specは任意の解釈を扱う。
パターン不一致は元の環境で後続へ進み、成功時の束縛はその腕のガード・本体だけに有効で、後続腕には漏れない。BoolガードとPropガードを命題として扱い、ガードの真偽に応じる前提・結論の両方向を保つ。意味の証人が無いガードや空の腕列にFalseや既定値を補わず、網羅性や意味の存在をこの局所定理の結論にしない。
3一般定理と `SurfaceCallLowerSpecSemExamples.lean` の20検体をroot公理監査と `requiredTheorems` に追加し、`lake exe naru_test semantics` と回帰から欠落を拒否する。任意input/spec解釈のBool検体、任意Natの後続値、Prop/Boolガード、外側の命題qをBoolパターンが隠す検体、falseガード二つから外側の値に戻る検体、specガード不在の両側の意味不在を検査する。正しいSurfaceに対し、Propガードを否定した同じ型のCoreはFalseを意味し保存しないことをkernelが検査する。
子spec式の対応はこの局所定理では明示的な前提であり(全spec式の型付け帰納からそれを導く一般同値は後述の `SurfaceCallLowerSpecSemAll.lean` が与える)、Surface/Core宣言群からの環境対応と現在の実生成StatementsへのSurfaceからの接続は含めない。現在17fnの153証拠と10specの100証拠を維持する。

呼出しspecの論理演算(`&&` / `||` / `implies`)・否定・ifには、子式の双方向対応から親式の意味証人を合成する局所保存がある。公開入口は適格性と独立loweringの実出力を照合する。ifは独立意味論に従い両分岐の意味を要求し、未選択分岐の意味が欠けても成功にしない。子式の対応を一般帰納から導く全spec同値は `SurfaceCallLowerSpecSemAll.lean` が与えた。宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

`SurfaceCallLowerSpecSem.lean` の `SpecSemEquiv.of_iff`、`lowerS_logic_equiv` / `lowerS_not_equiv` / `lowerS_ite_equiv`、`lowerS_logic_sem_iff` / `lowerS_not_sem_iff` / `lowerS_ite_sem_iff` と `SurfaceCallLogicSemExamples.lean` の正負・意味不在の検体を、必須公理監査と `lake exe naru_test semantics` / `lake exe naru_test regression` から検査する。これらは全式の一般同値の代用にはしない。

論理構文の7補題と23公開検体は必須監査に登録する。隔離した `CallLogicControl.lean` は正しい含意の接続と逆含意の命題型・2監査を通し、`CallLogicWrong.lean` は同じ入力への接続1行だけが型不一致になることを要求する。意味の異なる反例自体もkernelで証明し、構文・importの失敗で拒否を代用しない。

呼出しspecのNat/Bool値の比較とNat値の等値には、runtimeの一般評価保存を使う局所双方向対応がある。Bool値と命題を含む等値は、子式の `SpecSemEquiv` と左辺がNatを評価しない局所前提を使い、値の等値と命題の同値を区別する。公開入口は適格性・変換の分岐・独立loweringの実出力を照合する。全spec式の一般同値は `SurfaceCallLowerSpecSemAll.lean` が与えた。Surface/Core宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

`SurfaceCallLowerSpecSem.lean` の7補題と `SurfaceCallCompareSemExamples.lean` の44公開検体をroot公理監査・必須一覧へ登録する。任意のinput解釈、Nat/Boolの全比較・等値演算、Bool値と命題の等値、意味不在、Nat/Bool混合型の拒否をkernel検査する。`checkComparisonConnection` の `CallCompareControl.lean` は正しい接続と同型誤Coreの型・4監査を通し、`CallCompareWrong.lean` は等値と比較を交換した接続2行だけの型不一致を要求する。反例の非保存もkernelが検査し、構文エラーやimport欠落で拒否を代用しない。再実行は `lake build NaruSem` / `lake exe naru_test semantics` / `lake exe naru_test regression`。


呼出し葉の双方向対応は `SurfaceCallCallSem.lean` の `Surf.Call.lowerArgs_arrange_eval` / `lowerS_call_sem_iff` / `lowerS_ufcs_sem_iff` / `lowerS_call_equiv` / `lowerS_ufcs_equiv` が扱う。通常呼出しとUFCSの式全体の適格性・独立loweringの実出力から、引数の一般runtime評価保存と仮引数順の並べ替えを合成する。位置・名前付き・修飾名・ゼロ引数、fn/inputのBool値をtrueへ写す境界、同じ任意のspec解釈を保ち、子SpecSemEquivやspec解釈の存在を仮定しない。spec解釈の不在も両側の意味不在として保持する。関数/input環境は署名を守ること、値/命題の束縛環境は型付け文脈と一致することを前提にする。
`SurfaceCallCallSemExamples.lean` の35公開検体は任意解釈の対応、非空虚な意味証人、名前付き/UFCS引数順、Bool値境界、ゼロ引数、spec解釈不在、同名の局所隠蔽と不正引数の拒否をkernel検査する。同型の引数交換は適格でも意味を保存しない反例を含む。5一般補題と35検体をroot公理監査・`requiredTheorems`へ登録し、欠落を失敗にする。`checkCallLeafConnection` の `CallLeafControl.lean` は正しい接続と交換したCoreの型・4監査を通し、`CallLeafWrong.lean` は名前付き/UFCSの接続2行だけの型不一致を要求する。再実行は `lake build NaruSem` / `lake exe naru_test semantics` / `lake exe naru_test regression`。
これは同じcallee解釈での呼出し葉の保存であり、全spec式の相互帰納保存は `SurfaceCallLowerSpecSemAll.lean` がこれを子式の対応に使って与えた。Surface/Core宣言群からcallee環境の対応を導く証明と、Surfaceから実生成Model/Statementsへの接続は `SurfaceCallProg.lean` が与えた(後述)。手組AST/Coreの検体を実naru/compiler経路の接続や一般保証全体の代用にはしない。


呼出しを含む全spec式の一般双方向同値は `SurfaceCallLowerSpecSemAll.lean` の `Surf.Call.lowerS_sem_all` / `lowerS_equiv` / `lowerS_sem_iff` / `lowerS_Sem` / `Sem_lowerS` / `lowerS_sem_exists_iff` が扱う。`Surf.Call.wtS.mutual_induct` で式・let列・腕列・腕を同時に帰納し、let列 `SpecLetsBridge`(`lowerStmtsS_bridge`)・腕列 `SpecArmsBridge`(`lowerArmsS_bridge`)・量化・論理/否定/if・比較/値等値/命題等値・通常呼出し/UFCSの葉の局所合成を、これまで前提にしていた子式の `SpecSemEquiv` を帰納結果で満たして結ぶ。命題等値の左子式がNatを評価しないことは `eval_not_nat_of_wtS`(spec解釈をすべて補った環境での意味の存在 `Sem_exists` と `Sem_not_nat`。評価はspec解釈に依らない)で導く。任意の宣言表・文脈で論理の位置で適格なspec式と独立 `lowerS` の実出力について、署名を守る任意の関数/input解釈・任意のspec解釈(不在を含む)・型付け文脈と一致する任意の環境で、同じ命題がSurfaceの意味であることとCoreの意味であることは同値であり、意味の存在(不在)も両側で一致する。`lowerS_denote` / `lowerS_denoteP` はC44/C55のCore→実生成Leanの読み `Call.denoteP` まで合成する(読みの環境との対応 `FEnv.Agree` / `PEnv.Agree` は前提)。
`SurfaceCallLowerSpecSemAllExamples.lean` の18公開検体は、命題のlet・Natの量化・呼出しのscrutinee・ガード付きmatch・名前付きspec呼出し・UFCSのinput呼出し・否定・命題等値・論理演算を1式に重ねた合成式について、子式の対応を仮定しない任意解釈の双方向対応、意味の存在の一致、Natに評価されないこと、2つの腕へ進む非空虚な意味証人(すべての値calleeがfalse / trueを返す解釈)とそのCore側・読みへの合成、否定を落とした同型の誤Coreが適格でも正しいloweringでなく意味を保存しないことをkernel検査する。11一般定理と18検体をroot公理監査・`requiredTheorems`へ登録し、欠落を失敗にする。`naru_test semantics` は現在10specの `sssem_*`(`lowerS_sem_iff` を実AST/実Coreへ適用した任意解釈・任意環境の双方向同値)を `SurfaceCallLowerSpecCheck.lean` に加え、計100証拠の監査と欠落検査を行う。再実行は `lake build NaruSem` / `lake exe naru_test semantics` / `lake exe naru_test regression`。
これは式の意味の対応であり、Surface/Core宣言群の意味 `interp` からcallee環境 `Φ` / `Ψ` の対応を導く証明と、現在の実生成Model/Statements宣言へのSurfaceからの接続証拠は `SurfaceCallProg.lean` と `SurfaceCallStatementsCheck.lean` が与えた(後述)。手組AST/Coreの検体を実naru/compiler経路の接続や一般保証全体の代用にはしない。

Surface/Core宣言群の意味の対応と実生成Model/Statementsへの合成は `SurfaceCallProg.lean` の `Surf.Call.interp_lower_agree` / `interpFrom_lower_agree` / `spec_sem_denote` が扱う。宣言ごとの対応 `Surf.Call.DeclLower`(鍵と署名が同じで、fn/spec宣言の本体はその宣言より前の宣言の表での独立lowering `lower` / `lowerS` の実出力、inputは本体なし)の列 `ProgLower` と、適格な両宣言群・inputの署名を守る任意の同じ解釈 `I` から、宣言群の帰納法で `Surf.Call.interp I P` と `Call.interp I C` のcallee環境の一致(`FEnv.Agree`: 型の合う任意の実引数で同じ値、`PEnv.Agree`: 型の合う任意の実引数で双方向同値)を導く。fnの段はruntimeの一般評価保存 `lower_eval_agree`、spec宣言の段は全spec式の一般双方向同値を読み `Call.denoteP` 経由で(`lowerS_denote` / `lowerS_denoteP` と `Call.Sem_denote_self` / `Sem_denoteP`)それまでの対応に合成し、inputの段は同じ解釈を運ぶ。翻訳の正しさや呼出し先の正しさは仮定しない。prefixの表の署名はCoreのprefix署名の畳み込みに等しく(`Δ_take_eq`)、宣言群全体の署名に含まれる(`Δ_full_eq` / `Δ_take_subV`)。`spec_sem_denote` は既存のCore→実生成環境の対応(`Call.interp_agree` / `interp_prop_agree` の結論)と推移(`FEnv.Agree.trans` / `PEnv.Agree.trans`)で結び、Surfaceの宣言群の意味の下でのspec本体の意味が実生成環境での読みと同値であること(読み自体が意味、任意の意味は読みと同値)を与える。`naru_test semantics` は `SurfaceCallStatementsCheck.lean` に、現在31宣言の対応 `splower_call`(鍵・署名は `decide`、本体は `slow_*` / `sslower_*`)、宣言群の意味の一致 `sagree_call` と実生成環境との一致 `sgen_call` / `sinputs_connect`、現在17fnの `sfn_*`(Surfaceの宣言群の意味の下でのfn本体の評価 = 実生成Modelの値)、現在10specの `ssΔ_*`(prefix署名の一致)/ `ssurf_*`(読みが意味)/ `ssiff_*`(任意の意味は読みと同値)/ `sstmt_*`(実生成Statementsの命題がSurface ASTの意味)/ `sstmt_iff_*`(任意の意味は実生成Statementsの命題と同値)を、任意の署名を守るinput解釈(実生成と同じinput)と任意の仮引数について書き、kernel検査・公理監査・欠落検査する。負の検体 `SurfaceCallStatementsWrong.lean` は、違う宣言の実生成Statements(`specUfcs`)を `specNamed` のASTと組み合わせた接続と、同じ署名の別の呼出し先へ置換した型の合うCoreを宣言群の対応に使う検体が、対照の成功の下で接続の2行だけで失敗することを要求する。再実行は `lake build NaruSem` / `lake exe naru_test semantics` / `lake exe naru_test regression`。これは現在の実生成物への接続であり、構文解析・モジュール全体・claim bundle全体の保存、再帰・コレクションは含めない。
