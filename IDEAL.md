# IDEAL — naru

## 理想

Lean を知らない分散プロトコルの設計者が、プロトコルを naru で 1 本書くだけで、次の 3 つが同時に成り立っている。

- 書いたプロトコルを実行し、シミュレーションで挙動を確かめられる。
- Safety / Liveness などの定理が AI によって証明され、Lean kernel で検査されている。
- 人間がレビューするのは、生成された仕様のうち短い 3 つの部分 — Model と定理の対応付け(Interface)、定数(Constants)、公開する保証の一覧(Claim Bundle)— だけであり、それで保証を信頼できる。

naru の文法は、Rust / TypeScript / Python / Go を知っている人が想像しやすい形である。

## 実現する状態

### 必須
- **C1** 同じ naru ソースから生成される Lean は byte-for-byte 同一で、各生成ファイルの先頭にコンパイラ版・stdlib 版・ソース hash が入っている — 検証: `lake exe naru compile` を 2 回実行し、`generated/` 配下の全ファイルの sha256 が一致し、各ファイル先頭のコメントに 3 つの値が含まれる
- **C2** runtime 宣言から spec 宣言への依存(phase leak)はコンパイルエラーになる — 検証: 反例ソース `tests/reject/phase_leak.naru` に対し `lake exe naru compile` が exit 非 0 で `E001` を出力する
- **C3** 無条件の選択(choose / pick / set.first / set.toList 等)はコンパイルエラーになる — 検証: 反例 `tests/reject/choose.naru` で exit 非 0、`E003` を出力する
- **C4** 停止性を確認できない再帰はコンパイルエラーになる — 検証: 反例 `tests/reject/non_total.naru` で exit 非 0、`E002` を出力する
- **C5** 順序指定の無い Set → List 変換はコンパイルエラーになる — 検証: 反例 `tests/reject/order_loss.naru` で exit 非 0、`E004` を出力する
- **C6** 生成 Model は Lean としてビルドでき、`noncomputable` / `unsafe` / `axiom` / `sorry` / 無制限の `partial` を含まない — 検証: 生成 Model の lake target のビルドが exit 0 で、`grep -rwE 'noncomputable|unsafe|axiom|sorry|partial' generated/Model` が 0 件
- **C7** 生成 Model は native 実行でき、scenario をシミュレーションして observer の値を表示する — 検証: `lake exe naru simulate dsl/scenarios/basic.naru` が exit 0 で、time / node / confirmed / stable / finalized を出力する
- **C8** 生成 Statements は生成 Model だけを import し(Proofs を import しない)、`sorry` を含まない — 検証: import 閉包の検査スクリプトが exit 0 で、`grep -rw sorry generated/Statements` が 0 件
- **C9** 生成 Statements の公開 claim surface は naru ソースの claim bundle と一致し、verified-consensus の 13 claims と同名である — 検証: surface shape の検査スクリプトが 13 のフィールド名を列挙して exit 0
- **C10** 具体的な fixture 上で、手書き Model(DecoupledConsensusModel)と生成 Model の confirmed / stable / finalized の読みと emitted objects が一致する — 検証: 両者を同一 Lean プログラムで実行する golden test が、verified-consensus の Witnesses の 4 run と、複数ノード・equivocation を含む naru scenario 3 本以上に対し、MISMATCH 0 件で exit 0

### 望ましい
- **C11** naru のユーザーは Lean 固有の概念を扱わない — 検証: naru の予約語一覧・構文エラーメッセージ・`dsl/` の移植ソースに `Fintype` / `DecidableEq` / `Finset` / `Classical` / `termination_by` / `Prop` / `theorem` / `by` が現れない(grep が 0 件)
- **C12** capability の無い型への `==` や `<` はコンパイルエラーになる — 検証: 反例 `tests/reject/missing_capability.naru` で exit 非 0、`E005` を出力する
- **C13** Model 内での無限量化(`forall n : Nat` 等)の結果による分岐はコンパイルエラーになる — 検証: 反例 `tests/reject/infinite_quantification.naru` で exit 非 0、`E006` を出力する
- **C14** runtime の条件が classical な命題の決定に依存するとコンパイルエラーになる — 検証: 反例 `tests/reject/classical_decision.naru` で exit 非 0、`E007` を出力する
- **C15** 人間のレビュー面(Interface・Constants・Claim Bundle)は生成 Statements の 1 ファイルに集約されている — 検証: `generated/Statements/Review.lean` が存在し、interface binding・constants・claim bundle の 3 つの宣言をその 1 ファイルが含む

## 不変条件

- Model 内に任意の Lean を埋め込む抜け道(`lean { ... }` の類)は存在しない。移植で足りない機能が出たら、計算可能性・phase 分離・決定性を保ったまま naru の言語機能か stdlib に加える(この追加は周回の判断で行ってよく、人間への確認は要らない)。検査(E001〜E004、C6 の 0 件)を緩めて通すことはしない。
- `verified-consensus/` 配下の手書き Model・Statements・Proofs・scripts は変更しない。golden test(C10)と claim surface(C9)の基準だからである。
- 依存方向は Model ← Statements ← Proofs のみ。逆依存(Model が Statements や Proofs を import する、Statements が Proofs を import する)は決して入れない。
- `generated/` は機械生成専用で、人間も AI も直接編集しない。生成結果を直したいときは naru ソース・stdlib・コンパイラのどれかを直して再生成する。
- naru の表現力は Lean より小さく保つ。任意の依存型・型クラスプログラミング・quotient・一般公理・任意の classical choice・一般再帰・runtime での proof 消去・暗黙の非決定性・暗黙の集合順序・tactic・metaprogramming・unsafe な外部呼出しは naru ユーザーに公開しない。
- 一度 met になった条件を退行させない。特に C10 の golden test は、言語機能や stdlib を追加するたびに通し直す。
- 衝突の裁定: 移植の進捗(C7〜C10)と保証(C1〜C6・上記の抜け道禁止)が衝突したら、保証が勝つ。保証を保ったまま進める方法が周回に見つからなければ、推測で進めず ask で止まる。

## 前提

- 技術スタック: Lean 4.34.1 + mathlib v4.34.1(`verified-consensus/lean-toolchain` と `lakefile.toml` の pin に合わせる)。コンパイラ・stdlib・golden test・検査スクリプトも Lean で書く(既存の Ruby スクリプトの流用は可)。別言語の interpreter もコンパイラも作らない。「naru を実行する」とは、naru を Lean の Model に変換し、その Lean を実行することである。
- 実行環境: この Mac(arm64 / Darwin)に `lean` / `lake` / `elan` / `ruby` が入っている。verified-consensus のフルビルド(5 ライブラリ)は約 1 時間かかる。golden test に要るのは手書きの Model と Statements のビルドだけで、Proofs はビルドしなくてよい。
- 既存資産: `verified-consensus/`(naru リポジトリに同梱)。手書き Model(29 ファイル)・Statements(12 ファイル、13 claims の `Consensus`)・Witnesses(4 つの具体的 run)が golden test と claim surface の基準。`scripts/check-review-boundary.rb` と `scripts/ReviewSurfaceShape.lean` は C8 / C9 の検査の雛形になる。
- 対象ソース: 必須の条件はすべて、verified-consensus の Model と Statements を移植した naru ソースに対して検証する(反例ソースを除く)。
- 構成: `dsl/`(naru ソースと `scenarios/`)、`compiler/`、`stdlib/`(Model 用・Statements 用)、`generated/`(Model / Statements)、`proofs/`、`tests/reject/`、`lakefile.toml`。
- コンパイラの構造: Parser → Surface AST → 名前解決 → 型・capability 検査 → phase 検査 → 計算可能性検査 → Typed Core IR → Model backend / Statements backend。Surface syntax を直接 Lean に落とさず、必ず小さな Core IR を経由する。
- 言語の意味論: 宣言は phase(runtime / spec)を持ち、runtime → spec の依存は禁止。primitive 型は Bool / Nat / Int / String / Unit / Option / Result / List / Set / Table / Tuple / Record / Enum。Lean の型クラスは露出せず capability(eq / order / finite / repr)で表す。Set は順序を持たず、List 化は `sort(set, by = …)` で順序を明示する。選択は `find?` / `findUnique?` / `minBy?` / `maxBy?` だけ。runtime の条件は Bool、Statements の述語は Prop 相当。再帰は構造的再帰・明示 fuel・有限集合の反復のみ。非決定性は `input` と Trace として明示する。言語 core は一般の state machine を扱い、consensus 固有の `Event` / `ProtocolSpec` / `Run` は stdlib に置く。Event は (time, phase) で順序付け、Tick = 0 / Deliver = 1、同時刻・同 phase は trace 順。emit と deliver は別事象。Byzantine は注入 object で表す。scenario は定理ではなく実行 fixture で、出力は observer を通す。Statements は predicate / condition / regime / claim / claim bundle で書き、Safety / Liveness の一般概念と条件・regime は stdlib に置く。Model と generic statements の接続は interface binding で明示する。
- MVP 構文: module / type / record / enum / derive eq / derive order / input / fn / if / match / let / List / Set / Table / protocol / predicate / condition / regime / claim / claim bundle / scenario / observer。これ以上は移植で必要になってから加える。
- 理想化: 署名の偽造不能・hash の衝突なし・ネットワーク同期・honest 多数・参加・proposer 再帰は Model に実装せず、Statements の premise として表す。BlockId は単なる識別子でよい。
- 崩れたら報告する前提: 移植した naru ソース(`dsl/` 配下、`scenarios/` を除く)の行数が、手書きの Model と Statements の合計(約 6,850 行)の 1.5 倍を超えたら、「Lean より簡単」の前提が崩れた兆候として ask で止まり報告する。
- 期限: なし。
- データと秘密: 扱わない。コードはすべて公開可能(verified-consensus は CC0)。

## 対象外

### 恒久(有用に見えても作らない)
- production Ethereum client の直接生成。
- P2P networking の実装。
- BLS / hashing などの暗号の実装(Model では識別子と premise で代替する)。
- database の実装。
- 性能最適化された実装。
- Rust / TypeScript など Lean 以外への code generation。
- 別言語による naru の interpreter(naru の実行は生成 Lean の実行だけ)。
- naru 内での tactic / proof script の記述。
- AI による Model / Statements の自由な書き換え(AI が触ってよいのは `proofs/` だけ)。
- Model 内の任意 Lean の抜け道(`lean { ... }`)。

### 延期(理想の一部だが今回は追わない)
- AI による証明の再生成(生成 Model + Statements に対する証明を AI が `proofs/` に書き、Lean kernel が検査する)と、それに付随する proof obligation manifest・model / statements hash への bind・hash 変更時の STALE 化(現段階では実施しない。C1〜C10 がすべて met(realized)になったら昇格を検討)。
- Core IR の意味論と Lean への lowering の対応を Lean 自身で証明すること(現段階では実施しない。`proofs/` に AI 生成の証明が置かれ `lake build` が通る状態が観測されたら昇格を検討)。
- verified-consensus 以外のプロトコルの naru による記述(現段階では実施しない。C1〜C10 がすべて met になったら昇格を検討)。

## 用語

- **naru** — この DSL と、そのコンパイラ・stdlib・CLI(`lake exe naru`)の総称。ソースの拡張子は `.naru`。
- **Model** — naru の runtime 宣言から生成される、計算可能・決定的・total な Lean の状態機械。`generated/Model`。
- **Statements** — naru の spec 宣言から生成される、Prop・∀ / ∃・classical 推論を許す Lean の論理仕様。`generated/Statements`。
- **Proofs** — Statements の定理に対する Lean の証明。`proofs/`。今回の周回では空。
- **phase** — すべての naru 宣言が持つ区分。`runtime`(実行に参加: fn / record / enum / state / input / protocol)と `spec`(検証にのみ参加: predicate / condition / regime / property / claim / claim bundle)。
- **phase leak** — runtime 宣言が spec 宣言に依存すること。E001。
- **Interface** — 生成 Model と stdlib の汎用 statements をつなぐ対応付け(confirmed / stable / finalized / proposer / committee などが Model のどの関数を指すか)。verified-consensus の `Instantiation.lean` の binding に相当。
- **Constants** — Statements が参照する時間・閾値などの定数(Δ、GST、K など)。
- **Claim Bundle** — 公開する保証を 1 つにまとめた宣言。verified-consensus の `Consensus`(13 claims)に相当。
- **claim surface** — Claim Bundle が公開するフィールド名の集合。C9 は verified-consensus の 13 名(constants / nested / certificatesAccountable / finalizedAccountable / honestNeverSlashed / finalizedMonotone / finalizedSafe / available / confirmedLive / stableLive / stableIncludedFast / finalized / stableAsynchronyResilient)との一致を求める。
- **手書き Model** — `verified-consensus/DecoupledConsensusModel`。golden test の基準。
- **golden test** — 同一の fixture に対して手書き Model と生成 Model を同じ Lean プログラム内で実行し、観測(confirmed / stable / finalized の読みと emitted objects)を突き合わせる検査。
- **fixture** — golden test や simulation に与える具体的な run(validators・environment・event trace)。verified-consensus の Witnesses の 4 run と、naru の scenario で書いたもの。
- **scenario** — naru の実行 fixture 宣言。定理ではない。`observe` で observer の値を確かめる。
- **observer** — simulation の出力を取り出す宣言(confirmed / stable / finalized / head / currentSlot など)。state を直接 dump しない。
- **capability** — 型に付ける性質の宣言(eq / order / finite / repr)。Lean の型クラス(DecidableEq / Ord / Fintype / Repr)への変換は backend が行う。
- **stdlib** — naru の標準ライブラリ。Model 用(Event / ProtocolSpec / Run / Env)と Statements 用(Safety / Liveness の一般概念・条件・regime)。
- **E001〜E007** — コンパイラの静的検査の番号。E001 phase leak、E002 停止性未確認の再帰、E003 無条件の選択、E004 順序指定なしの Set → List、E005 capability 不足、E006 Model 内の無限量化による分岐、E007 runtime 条件の classical 依存。
- **反例ソース** — `tests/reject/` に置く、意図的に検査に違反する naru ソース。コンパイラが拒否することを確かめるための fixture。
