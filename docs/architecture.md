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

既知の制限: `∀` / `∃` は Lean の型の全要素を回る。`NaruStd.Set` / `NaruStd.Table` は昇順・重複なしのリストだが、その不変条件は型に
入っていないので、`Set` / `Table` を含む型(`Run` の `honest` など)の量化は正規化されていない表現(重複・未整列)も含み、そこでは `size` や
`==` が naru の集合の意味からずれる(手書き Model の `Finset` は不変条件を型に持つ)。移植の claim が集合の濃度や等しさに依存するなら、
stdlib の `Set` / `Table` に不変条件の証明欄を足すか、量化に整形性の前提を付ける(どちらも naru の表現力は変えない)。

## コンパイラ意味論保存(`semantics/NaruSem`、C39〜C47、C48〜C53、C54〜C59)

生成 Lean が Core の意味を保つことを、backend から独立した意味論と Lean の定理で保証する(限定範囲)。lean_lib `NaruSem`(`semantics/`)。
検査入口と走らせ方は [testing.md](testing.md)「コンパイラ意味論保存」。プロトコルの Proofs(`proofs/`、空)とは別の役割で、Core・コンパイラ・独立意味論・
生成宣言を参照してよいが、生成 Model / Statements からここへの逆依存は無い(不変条件の依存方向)。
Core IR の意味論(C39〜C47。下の各節)に加えて、構文解析の出力 Surface AST の独立した意味論と適格性(C48。「Surface AST の意味論と適格性」)と、
runtime の Surface AST → Core の変換と値の対応、spec の Surface AST → Core の変換と命題の双方向の同値、それぞれの実際の frontend と生成 Lean への接続
(C49 / C50 / C51。「Surface AST → Core の対応」)がある。関数・input の保存対象(非再帰の fn / spec 宣言の呼出しと input。C54〜C59)は
「関数・input の保存対象の意味論」の段階(C54: Core と Surface AST それぞれの独立した意味論・適格性と、適格な式・宣言群に意味が定まること、
実際の宣言群の引用と適格性の検査)と、runtime の Core → 実生成 Model の層(C55〜C57 の runtime 側: 呼出しを含む生成 Lean の読み、一般定理
`Call.denote_sound`、宣言群の意味と実生成定数の一致 `Call.interp_agree`(呼出し先の証拠の呼出し側への合成)、実際の宣言群の実生成 Model への接続と
負の検体)が揃っており、spec(Statements)の読みと双方向の同値、呼出しを含む Surface AST → Core の変換と対応、それらの実生成 Statements への接続
(C55〜C58 の残り)はまだ無い。保証の境界と未対応は「信頼する部分・方式・未対応」。

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
| `Call.interp_agree`(`Call.interpFrom_agree`) | **宣言群の意味と実生成定数の一致(C55 / C56 / C57)**: 適格な宣言群 `P`(`Call.wtProg SigEnv.empty P = some Δ`)、input の署名を守る任意の解釈 `I`、署名 `Δ'`(`SigEnv.SubV Δ Δ'`)を守る実生成定数の環境 `Φ'` について、input の鍵で `I` と `Φ'` が同じ(`Call.SameInputs I Φ' P`: 同じ input 解釈)で、各 fn に接続の証拠(`Call.Evidence Δ' Φ' P`: 各 fn に `Call.FnConn` — 型の合う任意の実引数で `Φ'` の関数の値 = 仮引数に実引数を束ねた環境での本体の読み)があれば `FEnv.Agree (Call.interp I P).Φ Φ' Δ` — 宣言群の意味(呼出し先の本体を評価する閉包)は実生成定数の環境と署名の鍵で一致する。宣言群の帰納法で、各 fn の本体の評価を、それより前の宣言についての一致(帰納法の仮定)と `Call.denote_sound` で実生成定数の値に結ぶ = 呼出し先の証拠の呼出し側への合成 | 宣言群の適格性 + input の解釈が署名を守る + 同じ input 解釈 + 各 fn の接続の証拠 |
| `Call.fn_value` | **fn の意味は実生成定数の値(系)**: 宣言群の各 fn `k` について、`Φ'` の関数 `f'` が型の合う実引数 `vs` に `v` を返すなら、`(Call.interp I P).Φ k = some f` で `f vs = some v` | 同上 |
| `Call.SubV_of_cover` / `Call.fnConn_of_curried` | 検査プログラムの形との結び: 宣言群の各 fn / input の署名が表にあれば(`decide` で確かめる)`wtProg` の署名は表の署名に含まれる(`Call.wtProg_keys`: 署名の鍵は始めの文脈か宣言群の宣言のもの)。接続検査 `conn_<f>`(カリー化の形 `Call.Curried`: 仮引数ごとに量化し、実生成の関数に実引数を渡した値 = 実引数を束ねた環境での本体の読み)と、`Φ'` の鍵がその関数を包んだものであることから接続の証拠 `FnConn`(`Call.curried_wrap`) | — |

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
| 実生成 Model への接続(C55 / C56 / C57 / C58) | `lake exe naru_test semantics` が検体を実際の CLI で生成し、生成 Model `Model.Sem.Call`(fn は input の引数 `name'` を名前順に先頭に取る Lean の定義、ゼロ引数の fn は定数、呼出しは呼出し先の定数への適用)をそのまま Lean のモジュールにして `CallModelCheck.lean` を kernel に検査させる: 表 `shapes_call` / `gens_call <inputs>` から作った `Δgen_call` / `Φgen_call <inputs>`(input の Lean の値 `bias'` / `flag'` / `seed'` で量化)が表の署名を守る(`Φgen_call_respects`)、宣言群の各 fn / input の署名が表にある(`cover_call`、`decide`)、各 fn の接続 `conn_<f> <inputs> : ∀ args, Model.Sem.Call.<f> <fn の input 引数> args = Call.denoteN Δgen_call (Φgen_call <inputs>) (Env.ofList …) ccore_<f>`(kernel の定義的等しさ `rfl`。リテラルパターンの `match` は scrutinee の仮引数の `cases` の後に `rfl`。`ccore_<f>` は `CallScope.lean` の実際の Core の引用で `checkProg` が再コンパイルして一致を照合)と接続の証拠 `evid_<f>`(`fnConn_of_curried`)、宣言群全体の証拠 `cevid_call`、宣言群の意味と実生成定数の一致 `cgen_call`(`interp_agree`: 任意の input 解釈 `I` が `Φgen_call` と input の鍵で同じなら `interp I cprog_call` の fn / input は `Φgen_call` と署名の鍵で一致)、各 fn の値 `cval_<f>`(`fn_value`: 宣言群の意味の fn は型の合う任意の実引数で実生成定数の値)。負の検体 `CallModelWrong.lean`(実生成文字列から作る: `twoStep` が同じ署名の `base` を `callBase` の代わりに呼ぶ、`callNamed` の名前付き実引数の取り違え、`ufcs` の UFCS の受け手の誤対応、`useInputArg` の input `seed` の誤配線)は型検査を通るが接続検査だけが失敗する(対照は成功)。検体の `match` の scrutinee は仮引数(呼出しの scrutinee のリテラル腕の接続は scrutinee の場合分けが要り、検査プログラムの `cases` は仮引数にだけ掛ける。一般定理は呼出しの scrutinee も扱う) |
| 検体 | `NaruSem/CallExamples.lean`(Core。`decide` / 構成): 対象範囲は空でない(fn / input / spec 宣言の呼出し、値の位置の呼出し、命題の `let`)、不適格な Core(未解決・引数の数と型・phase・値の位置の spec 宣言・命題の実引数・関数の値としての参照)、宣言群(適格な 2 段の呼出しと input、自己再帰・相互再帰・依存順でない・重複・input の引数の不一致は `none`)、input の解釈による値(同じ宣言群を別の解釈で読めば別の値)、署名に合わない解釈は行き詰まり(`none`)で `RespectsInputs` を満たさない、`fn_total` / `spec_defined` の実例、`callVal` / `callSpec` の実例、行き詰まり。実際の compiler 経路の検体は `tests/accept/sem_call.naru`(下) |
| 実際の宣言群の引用 | `NaruSem/CallQuote.lean`: `Call.Quote.declOf?`(Core の fn / input / spec 宣言 → `Call.Decl`)/ `declWith` / `checkProg`(同じソースを再びコンパイルし、引用した各宣言が実際の宣言(鍵・種別・仮引数の名前と型・戻り型・本体)と一致し、実際の fn / input / spec 宣言がすべて引用されている — 宣言群全体)、`Surf.Call.Quote.ofAst?` / `ofDeclAst?`(構文解析の宣言 → `Surf.Call.Decl`。モジュール名つき)/ `expr` / `declWith` / `checkProg`(再構文解析と `Decl.toAst` の `==`)。`lake exe naru_test semantics` が検体 `tests/accept/sem_call.naru`(input 3・fn 16・spec 宣言 9: 位置 / 名前付き引数・UFCS・ゼロ引数・2 段の呼出し・input の推移的な依存と共有・spec から runtime / spec の呼出し)の宣言群を依存順に引用した `CallScope.lean` / `SurfaceCallScope.lean` を書き、`Call.wtProg` / `Surf.Call.wtProg` と各宣言の署名を kernel の `decide` で、負の検体(実際の Core / AST から作る: 依存順の反転・違う呼出し先・phase・循環・重複・引数の数と型・未解決の名前・名前付き引数の名前 / 順序 / 二重指定)が不適格であること、input の解釈の下の fn の値と署名に合わない解釈の行き詰まりも kernel に検査させる([testing.md](testing.md)) |

言語の意味(呼出しは実引数を仮引数に束ねて本体を読む、名前付き引数は仮引数の名前で、UFCS は受け手を先頭の引数に、input は環境からの入力。[language.md](language.md)「式」
「scenario と observer」)はこの定義のために変えていない。この段階で保証するのは、「意味が定まる」こと(Core と Surface AST の両方: 適格な式・宣言群と対応する環境、
署名を守る任意の input の解釈について、runtime の値が存在して一意で、spec の意味が存在して一意で、各 fn は全域で各 spec 宣言の意味は本体の意味)と適格性の明示(C54)、
そして runtime の Core → 実生成 Model の保存(C55〜C57 の runtime 側: 任意の適格な宣言群・同じ input 解釈・型の合う任意の実引数について、宣言群の意味の fn の値 =
実生成定数の値。呼出し先の一般保存定理と kernel 検査済みの接続証拠を呼出し側へ合成する `Call.interp_agree`)までで、spec(Statements)の読みと双方向の同値、
証拠は宣言と本体に結び付いている。`naru_test semantics` の `CallEvidenceCheck.lean` / `CallEvidenceWrong.lean` は、同じ署名の別宣言の証拠と、
本体の変更前の証拠が現在の接続義務を満たさず、呼出し先 `base` を抜いた証拠束では宣言群全体に `Call.interp_agree` を適用できないことを検査する(C57)。
正しい対照と、変更した Core の適格性・意味の差も kernel に検査させ、公理監査する。有限の差の検体は拒否理由を確かめるためであり、一般保存定理の代わりにはしない。
呼出しを含む Surface AST → Core の変換と対応、実生成 Statements への接続は未対応(C55〜C58 の残り)。
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
