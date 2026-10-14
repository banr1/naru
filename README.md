# naru

naru は、分散プロトコルを 1 本書くだけで「実行できる」「定理が証明される」「人間が読むべき部分が短い」を同時に成り立たせることを目指す DSL です。
Lean 4 を知らない設計者が、Rust / TypeScript / Python / Go を知っていれば想像できる文法でプロトコルを書くと、

- **実行できる** — naru は計算可能・決定的・total な Lean の状態機械(Model)に変換され、scenario をシミュレーションして observer の値を表示できる。
- **検証できる** — 同じソースから Safety / Liveness などの定理(Statements)が Lean の命題として生成され、証明は Lean kernel で検査される
  (証明の AI 生成は延期項目。`docs/roadmap.md`)。
- **レビューが短い** — 人間が読むのは、生成された仕様のうち Model と定理の対応付け(Interface)・定数(Constants)・公開する保証の一覧(Claim Bundle)だけ。

基準として、Francesco D'Amato の [verified-consensus](https://github.com/fradamt/verified-consensus)(Lean 4 で書かれた decoupled consensus の
モデルと証明)を `third_party/` に同梱し、その Model と Statements を naru に移植した `specs/consensus/` が、生成 Model の golden test と
claim surface の基準になっています。移植ソースの各宣言には日本語の宣言コメント(要旨 1 行と、その下の説明。手書きの対応する定義名を
「手書き `名前`」で挙げる)が付いていて、作者でない人が移植ソースをそのまま読めます(規約は `docs/architecture.md`)。設計の正本は
[IDEAL.md](IDEAL.md)(人間が宣言する「実現する状態」)です。


呼出しspecの値・命題のlet列には、子式と末尾の双方向の意味対応を明示した証明書からCoreのlet列への意味対応を合成する局所証明がある。同名の値・命題の再束縛も検査する。全spec式の一般同値は `SurfaceCallLowerSpecSemAll.lean` が与えた(後述)。宣言群からのcallee環境の対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

呼出しspecのガード付きmatchにも、各腕のガード・本体の双方向意味対応を明示した `SpecArmsBridge` から腕列の意味を合成する局所証明がある。Bool/Propガード、Nat/Boolパターン、同名束縛と後続腕への復帰を保ち、意味のないガードや空の腕列に意味を補わない。全spec式の一般同値は `SurfaceCallLowerSpecSemAll.lean` が与えた(後述)。宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

呼出しspecの量化には、本体の双方向対応を拡張後の任意環境で要求し、任意長のNat/Bool束縛列を同じ全量化範囲で運ぶ局所保存がある。`Surf.Call.lowerS_quant_sem_iff` は束縛の名前・順序・同名shadowingと実lowering出力を照合する。本体の対応と意味の存在をこの局所定理だけから導くものではない(全spec式の一般同値は `SurfaceCallLowerSpecSemAll.lean` が与えた)。宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

呼出しspecの論理演算(`&&` / `||` / `implies`)・否定・ifには、子式の双方向対応から親式の意味証人を合成する局所保存がある。公開入口は適格性と独立loweringの実出力を照合する。ifは独立意味論に従い両分岐の意味を要求し、未選択分岐の意味が欠けても成功にしない。子式の対応を一般帰納から導く全spec同値は `SurfaceCallLowerSpecSemAll.lean` が与えた。宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

呼出しspecのNat/Bool値の比較とNat値の等値には、runtimeの一般評価保存を使う局所双方向対応がある。Bool値と命題を含む等値は、子式の `SpecSemEquiv` と左辺がNatを評価しない局所前提を使い、値の等値と命題の同値を区別する。公開入口は適格性・変換の分岐・独立loweringの実出力を照合する。全spec式の一般同値は `SurfaceCallLowerSpecSemAll.lean` が与えた。Surface/Core宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

## 前提の道具

| 道具 | 版 / 備考 |
|---|---|
| [elan](https://github.com/leanprover/elan) / Lean 4 | `lean-toolchain` の `leanprover/lean4:v4.34.1`(`lake` も同梱)。naru 本体は mathlib に依存しない |
| verified-consensus(golden test に要る) | mathlib v4.34.1。`third_party/verified-consensus/` の submodule を取得して `lake build DecoupledConsensusModel`(mathlib のビルドを含む。初回は約 1 時間) |
| mathlib(証明を書くときだけ import する) | `Proofs` が使う mathlib は上の submodule のビルド済みのもの(`lakefile.toml` の path 依存 `third_party/verified-consensus/.lake/packages/…`)なので追加の取得は要らない。ただし Lake のワークスペースはこの path を常に読むので、**`lake build` の前に submodule 側のビルド(上の行。`.lake/packages/` ができる)が要る**。`lake update` は走らせない |
| エディタ対応(任意) | tree-sitter CLI 0.27 と node 24(`tree-sitter generate`)、rustup の cargo / rustc と `wasm32-wasip2` ターゲット(Zed 拡張のビルド)、Zed 1.23 |

## クイックスタート

```sh
git clone --recursive <このリポジトリ>        # 既に clone してあれば: git submodule update --init
lake build
lake exe naru compile
lake exe naru simulate specs/consensus/scenarios/basic.naru
```

`lake build` が naru コンパイラ(`lake exe naru`)を、`lake exe naru compile` が `specs/consensus/` の移植ソースから `generated/` の Model と Statements を作ります
(追跡済みの `generated/` と byte-for-byte 同じものができます)。`lake exe naru simulate …` は scenario を native 実行し、observer の値を表示します。
期待される出力の抜粋(WeakGenesis に対応する run。node 0 の各時刻の confirmed / stable / finalized の読み):

```text
scenario basic
  trace(s, rho, v0):
    { time := 0, node := { value := 0 }, confirmed := { value := 0 }, stable := { value := 0 }, finalized := { value := 0 } }
    { time := 10, node := { value := 0 }, confirmed := { value := 2 }, stable := { value := 0 }, finalized := { value := 0 } }
    { time := 30, node := { value := 0 }, confirmed := { value := 7 }, stable := { value := 4 }, finalized := { value := 0 } }
  readsAt(s, rho, v0, 30) = { time := 30, node := { value := 0 }, confirmed := { value := 7 }, stable := { value := 4 }, finalized := { value := 0 } }
```

## ディレクトリ構成

| ディレクトリ | 内容 |
|---|---|
| `compiler/` | naru コンパイラ(Lean)。字句・構文解析、名前解決、型・capability・phase・停止性の検査、Core IR、Model / Statements backend、言語サーバー、CLI |
| `stdlib/` | Model 用 stdlib(`stdlib/Model`、Lean の `NaruStd`)。生成 Model が import する |
| `semantics/` | コンパイラ意味論保存(Lean の `NaruSem`): naru の Core IR と Surface AST の独立した意味論と適格性、一般定理、検体、公理監査(関数・input の呼出しを含む宣言群の意味論は `Call.lean` / `SurfaceCall.lean`、呼出しを含む Model の保存と宣言群の意味と実生成定数の一致は `CallDenote.lean`、呼出しを含む spec 式の一般同値は `CallDenoteProp.lean`、Surface / Core の宣言群の意味の対応と実生成 Model / Statements への合成は `SurfaceCallProg.lean`)。`lake build NaruSem` が検査入口(`docs/architecture.md`「コンパイラ意味論保存」) |
| `specs/` | naru ソース。`specs/consensus/` は verified-consensus の Model と Statements の移植(`Consensus/**`。spec 側は `Consensus/Spec/`)と実行 fixture(`scenarios/`)。`naru.toml` のソースルート |
| `generated/` | `naru compile` の決定的な出力(`Model` / `Statements`。Model は runtime 宣言を出力するモジュールにつき 1 ファイル、Statements は spec 宣言のあるモジュールにつき 1 ファイル。証明義務の一覧 `obligations.json` も)。機械生成専用で手では編集しない |
| `proofs/` | プロトコル証明(Lake ライブラリ `Proofs`)。各義務の theorem と補題(`Proofs.lean` / `Proofs/**`)。書き手の案内は `proofs/README.md` |
| `tests/` | 受理例 `accept/`、反例 `reject/`、複数ファイルのコンパイル単位の検体 `units/`、設定変更プロジェクト `config_change/`、golden test `golden/`、検査ドライバ `naru_test`(`NaruTest/`) |
| `docs/` | 文書(下の案内)と、機械生成の依存グラフ `docs/deps/`(`naru deps` の出力。手では編集しない。下の「依存グラフの見方」) |
| `editors/` | エディタ対応: tree-sitter 文法 `tree-sitter-naru/` と Zed 拡張 `zed-naru/` |
| `third_party/` | 同梱する外部の参照物。git submodule `verified-consensus/`(基準コミットと約束は `third_party/README.md`) |
| `.idd/` | Ideal-Driven Development の台帳(`progress.md`)・知見(`knowledge.md`)・周回記録(`cycles/`) |

ルート直下のファイル: `README.md`(この入口)、[IDEAL.md](IDEAL.md)(正本)、`LICENSE`(CC0 1.0)、`naru.toml`(ソースルート・生成先・依存グラフの出力先・証明ディレクトリ)、
`lakefile.toml` / `lake-manifest.json` / `lean-toolchain`(Lake のワークスペース。`Proofs` の mathlib は submodule のビルド済みのものへの path 依存)、`.gitattributes`(linguist の区分)、`.gitmodules`(submodule)。

## 文書

- [docs/language.md](docs/language.md) — 言語リファレンス(字句・宣言・capability・phase・型・式・パターン・stdlib のメソッド表・Set の規則・量化・再帰・scenario / observer)
- [docs/diagnostics.md](docs/diagnostics.md) — 診断 E001〜E019 の一覧と例
- [docs/cli.md](docs/cli.md) — `naru compile` / `simulate` / `check-reject` / `lsp` / `deps` / `proofs` と `naru.toml`
- [docs/architecture.md](docs/architecture.md) — パイプライン・Core IR・Model backend・Statements backend・生成物のヘッダと決定性・依存グラフ・コンパイラ意味論保存(`semantics/`)
- [docs/testing.md](docs/testing.md) — 検査ドライバ `naru_test` の各群と golden test の走らせ方
- [docs/editors.md](docs/editors.md) — tree-sitter 文法と Zed 拡張、`rev` の付け替えの運び
- [docs/roadmap.md](docs/roadmap.md) — まだ無いもの
- [IDEAL.md](IDEAL.md) — 実現する状態(条件 C1〜C72)・不変条件・前提・対象外・用語

## 依存グラフの見方

移植ソースのどのファイルとどの宣言がどれに依存しているかは、`naru deps` がソースから決定的に生成する依存グラフで辿れます。
[docs/deps/index.html](docs/deps/index.html) をブラウザで開く(単一ファイルで、外部への読み込みはありません)と、ファイル単位タブに縦向きの層状グラフ
(層 0 = 他のファイルに依存しないものが最上段。既定は推移簡約した辺だけ、切替で全辺。ファイルを選ぶと使う側 / 使われる側の辺を色分けし、横のパネルに宣言数・
使う / 使われるファイルと「宣言 → 宣言」の内訳・import 行との差)、宣言単位タブに宣言名と種類で絞れる一覧と、選んだ宣言の要旨・使う / 使われる宣言(直接 / 推移的)が出ます。
データは [docs/deps/deps.json](docs/deps/deps.json)(import 行ではなく実際の参照に基づく宣言単位・ファイル単位の辺、層、強連結成分、推移簡約、import との差)。
`docs/deps/` は機械生成で、ソース・コンパイラ・テンプレートを変えたら `lake exe naru deps` で作り直します(`docs/cli.md`「依存グラフ」、`docs/architecture.md`「依存グラフ」)。

## 証明状況の見方

`lake exe naru proofs`(先に `lake exe naru compile`)は、14 件の証明義務(consensus の 13 claims と claim bundle)それぞれの状況 — 証明済み / 未証明(theorem が無い・`sorry`)/ 失効 / 不正 — を
表示します(`--json` で正規形 JSON)。いまは 14 件のうち 6 件(`constants` / `nested` / `finalizedMonotone` / `certificatesAccountable` / `finalizedAccountable` / `finalizedSafe`)が証明済みで、残り 8 件は `missing`(未証明)です。義務の一覧は `generated/obligations.json`(`naru compile` が書く)、
証明の書き方は [proofs/README.md](proofs/README.md)、判定の定義は [docs/cli.md](docs/cli.md)「証明状況」と [docs/architecture.md](docs/architecture.md)「Proofs」にあります。
これはプロトコルの保証の層で、コンパイラの意味保存(`lake build NaruSem`)とは別の層です。

## 検査の走らせ方

```sh
lake exe naru check-reject tests/reject/phase_leak.naru E001   # 反例が期待の診断で拒否される
lake exe naru_test grammar      # tree-sitter 文法(C16)
lake exe naru_test zed          # Zed 拡張(C17)
lake exe naru_test lsp          # 言語サーバー: 診断・ホバー・定義ジャンプ・補完・リネーム・整形(C18 / C29 / C30 / C31 / C32 / C33)
lake exe naru_test statements   # 生成 Statements の import 閉包と claim surface、移植ソースの所在とモジュール名(C8 / C9 / C37)
lake exe naru_test repo         # README・submodule・docs(C21 / C23 / C25)
lake exe naru_test deps         # 依存グラフ `naru deps`: 生成・決定性・手書きの期待 JSON の検体・移植ソースの独立検査・HTML の自己完結・docs/deps/ の鮮度(C63 / C64 / C65 / C66)。約 10 秒
lake exe naru_test proofs       # 証明基盤: obligations.json・束縛 hash・依存方向・naru proofs の状況・書き手の案内(C68 / C69 / C70 / C72)。約 1 分
lake exe naru_test semantics    # コンパイラ意味論保存: `lake build NaruSem`(意味論・一般定理・公理監査)、実際の AST / Core の適格性、AST → Core の変換の一致(runtime / spec)、実生成 Model / Statements の接続・保存と AST → 生成 Lean の合成(C39〜C45、C48〜C52)、関数・input の呼出しを含む宣言群の適格性(C54)と実生成 Model への接続・宣言群の意味との合成(C55〜C57 の runtime)、呼出しを含む spec 式の一般同値と10宣言の prefix 読みへの接続・宣言群の命題同値の合成(C55 の進展、inputのみの別モジュールからの任意解釈と別モジュールのfn/spec呼出し先への接続、runtime17関数のAST→Coreの構造的一致・評価保存とspec10宣言の独立lowering/実Core一致・一般の全域性/型保存も検査、Surface の宣言群の意味の対応から実生成 Model / Statements への合成 `sfn_*` / `sstmt_*`(C55 / C57)も検査)。約 1 分
lake exe naru_test golden       # 手書き Model との golden test(C10)。約 9 分
lake exe naru_test regression   # 上の全部 + 受理例・反例・生成 Lean の意味(C34)・決定性(C1)・simulate(C7)・設定(C24)を 1 コマンドで(C36。`deps` の次に `proofs` 群も走らせる)。約 14 分
```

`naru_test golden` は verified-consensus の手書き Model(mathlib)を interpreter で走らせるので、引数なし(FinalityLiveness の horizon 100)で約 9 分かかります。
短い予行は `lake exe naru_test golden --finality-horizon 40`(約 30 秒)、比較器の検体だけなら `lake exe naru_test golden --comparator`(約 10 秒)。
`naru_test regression` はコードを変えたときの最終検証で、`/tmp` のスクリプトや
過去の出力に頼らず全項目を走らせます。`naru_test zed-install`(C19)は起動中の Zed を操作して Dev Extension を
入れ直すので、普段の回帰には含めません。詳しくは [docs/testing.md](docs/testing.md)。

## Zed 拡張について

`editors/zed-naru/` の `extension.toml` は、文法をこのリポジトリの `file://` の絶対パス(`/Users/banriyanahama/workspace/naru`)とコミット SHA(`rev`)で
取るので、**この機械専用**です。他の機械で使うには `repository` のパスを自分の clone に変え、Zed の `zed: install dev extension` でこのディレクトリを選びます
([docs/editors.md](docs/editors.md))。

## ライセンスと出典

naru は [CC0 1.0 Universal](LICENSE)(パブリックドメイン相当)です。

同梱する verified-consensus も CC0 1.0 で、出典は次のとおりです(`third_party/verified-consensus/CITATION.cff`):
D'Amato, Francesco. *verified-consensus: a Lean 4 formalization of the decoupled consensus protocol*. https://github.com/fradamt/verified-consensus (2026)。

呼出し葉は通常・UFCSの双方向保存を一般runtime評価保存から合成し、名前付き引数・Bool値境界・spec解釈不在を検査する。全spec式の帰納同値は `SurfaceCallLowerSpecSemAll.lean` が与えた。Surface/Core宣言群からのcallee環境の対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。詳しくは[アーキテクチャ](docs/architecture.md)と[検査手順](docs/testing.md)を参照。


呼出しを含む全spec式の一般双方向同値(`lowerS_sem_iff`)を `wtS` の相互帰納で証明し、現在10specの実AST/実Coreへ適用した(`sssem_*`、計100証拠)。Surface/Core宣言群からのcallee環境の対応と、実生成Model/StatementsへのSurfaceからの接続証拠も `SurfaceCallProg.lean` / `SurfaceCallStatementsCheck.lean` が与えた(周回 111)。詳しくは[アーキテクチャ](docs/architecture.md)と[検査手順](docs/testing.md)を参照。
