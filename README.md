# naru

naru は、分散プロトコルを 1 本書くだけで「実行できる」「定理が証明される」「人間が読むべき部分が短い」を同時に成り立たせることを目指す DSL です。
Lean 4 を知らない設計者が、Rust / TypeScript / Python / Go を知っていれば想像できる文法でプロトコルを書くと、

- **実行できる** — naru は計算可能・決定的・total な Lean の状態機械(Model)に変換され、scenario をシミュレーションして observer の値を表示できる。
- **検証できる** — 同じソースから Safety / Liveness などの定理(Statements)が Lean の命題として生成され、証明は Lean kernel で検査される
  (証明の AI 生成は延期項目。`docs/roadmap.md`)。
- **レビューが短い** — 人間が読むのは、生成された仕様のうち Model と定理の対応付け(Interface)・定数(Constants)・公開する保証の一覧(Claim Bundle)だけ。

基準として、Francesco D'Amato の [verified-consensus](https://github.com/fradamt/verified-consensus)(Lean 4 で書かれた decoupled consensus の
モデルと証明)を `third_party/` に同梱し、その Model と Statements を naru に移植した `specs/consensus/` が、生成 Model の golden test と
claim surface の基準になっています。設計の正本は [IDEAL.md](IDEAL.md)(人間が宣言する「実現する状態」)です。


呼出しspecの値・命題のlet列には、子式と末尾の双方向の意味対応を明示した証明書からCoreのlet列への意味対応を合成する局所証明がある。同名の値・命題の再束縛も検査する。全spec式の一般同値と宣言群から実生成LeanまでのSurface合成は未完了である。

呼出しspecのガード付きmatchにも、各腕のガード・本体の双方向意味対応を明示した `SpecArmsBridge` から腕列の意味を合成する局所証明がある。Bool/Propガード、Nat/Boolパターン、同名束縛と後続腕への復帰を保ち、意味のないガードや空の腕列に意味を補わない。全spec式の一般同値、宣言群の環境対応、Surfaceから実生成Leanへの合成は未完了である。

呼出しspecの量化には、本体の双方向対応を拡張後の任意環境で要求し、任意長のNat/Bool束縛列を同じ全量化範囲で運ぶ局所保存がある。`Surf.Call.lowerS_quant_sem_iff` は束縛の名前・順序・同名shadowingと実lowering出力を照合する。本体の対応と意味の存在をこの局所定理だけから導くものではなく、全spec式の一般同値・宣言群の環境対応・Surfaceから実生成Leanへの合成は未完了である。

## 前提の道具

| 道具 | 版 / 備考 |
|---|---|
| [elan](https://github.com/leanprover/elan) / Lean 4 | `lean-toolchain` の `leanprover/lean4:v4.34.1`(`lake` も同梱)。naru 本体は mathlib に依存しない |
| verified-consensus(golden test に要る) | mathlib v4.34.1。`third_party/verified-consensus/` の submodule を取得して `lake build DecoupledConsensusModel`(mathlib のビルドを含む。初回は約 1 時間) |
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
| `semantics/` | コンパイラ意味論保存(Lean の `NaruSem`): naru の Core IR と Surface AST の独立した意味論と適格性、一般定理、検体、公理監査(関数・input の呼出しを含む宣言群の意味論は `Call.lean` / `SurfaceCall.lean`、呼出しを含む Model の保存と宣言群の意味と実生成定数の一致は `CallDenote.lean`、呼出しを含む spec 式の一般同値は `CallDenoteProp.lean`)。`lake build NaruSem` が検査入口(`docs/architecture.md`「コンパイラ意味論保存」) |
| `specs/` | naru ソース。`specs/consensus/` は verified-consensus の Model と Statements の移植(`Consensus/**`。spec 側は `Consensus/Spec/`)と実行 fixture(`scenarios/`)。`naru.toml` のソースルート |
| `generated/` | `naru compile` の決定的な出力(`Model` / `Statements`。Model は runtime 宣言を出力するモジュールにつき 1 ファイル、Statements は spec 宣言のあるモジュールにつき 1 ファイル)。機械生成専用で手では編集しない |
| `tests/` | 受理例 `accept/`、反例 `reject/`、複数ファイルのコンパイル単位の検体 `units/`、設定変更プロジェクト `config_change/`、golden test `golden/`、検査ドライバ `naru_test`(`NaruTest/`) |
| `docs/` | 文書(下の案内) |
| `editors/` | エディタ対応: tree-sitter 文法 `tree-sitter-naru/` と Zed 拡張 `zed-naru/` |
| `third_party/` | 同梱する外部の参照物。git submodule `verified-consensus/`(基準コミットと約束は `third_party/README.md`) |
| `.idd/` | Ideal-Driven Development の台帳(`progress.md`)・知見(`knowledge.md`)・周回記録(`cycles/`) |

ルート直下のファイル: `README.md`(この入口)、[IDEAL.md](IDEAL.md)(正本)、`LICENSE`(CC0 1.0)、`naru.toml`(ソースルートと生成先)、
`lakefile.toml` / `lake-manifest.json` / `lean-toolchain`(Lake のワークスペース)、`.gitattributes`(linguist の区分)、`.gitmodules`(submodule)。

## 文書

- [docs/language.md](docs/language.md) — 言語リファレンス(字句・宣言・capability・phase・型・式・パターン・stdlib のメソッド表・Set の規則・量化・再帰・scenario / observer)
- [docs/diagnostics.md](docs/diagnostics.md) — 診断 E001〜E019 の一覧と例
- [docs/cli.md](docs/cli.md) — `naru compile` / `simulate` / `check-reject` / `lsp` と `naru.toml`
- [docs/architecture.md](docs/architecture.md) — パイプライン・Core IR・Model backend・Statements backend・生成物のヘッダと決定性・コンパイラ意味論保存(`semantics/`)
- [docs/testing.md](docs/testing.md) — 検査ドライバ `naru_test` の各群と golden test の走らせ方
- [docs/editors.md](docs/editors.md) — tree-sitter 文法と Zed 拡張、`rev` の付け替えの運び
- [docs/roadmap.md](docs/roadmap.md) — まだ無いもの
- [IDEAL.md](IDEAL.md) — 実現する状態(条件 C1〜C33)・不変条件・前提・対象外・用語

## 検査の走らせ方

```sh
lake exe naru check-reject tests/reject/phase_leak.naru E001   # 反例が期待の診断で拒否される
lake exe naru_test grammar      # tree-sitter 文法(C16)
lake exe naru_test zed          # Zed 拡張(C17)
lake exe naru_test lsp          # 言語サーバー(C18)
lake exe naru_test statements   # 生成 Statements の import 閉包と claim surface、移植ソースの所在とモジュール名(C8 / C9 / C37)
lake exe naru_test repo         # README・submodule・docs(C21 / C23 / C25)
lake exe naru_test semantics    # コンパイラ意味論保存: `lake build NaruSem`(意味論・一般定理・公理監査)、実際の AST / Core の適格性、AST → Core の変換の一致(runtime / spec)、実生成 Model / Statements の接続・保存と AST → 生成 Lean の合成(C39〜C45、C48〜C52)、関数・input の呼出しを含む宣言群の適格性(C54)と実生成 Model への接続・宣言群の意味との合成(C55〜C57 の runtime)、呼出しを含む spec 式の一般同値と10宣言の prefix 読みへの接続・宣言群の命題同値の合成(C55 の進展、inputのみの別モジュールからの任意解釈と別モジュールのfn/spec呼出し先への接続、runtime17関数のAST→Coreの構造的一致・評価保存とspec10宣言の独立lowering/実Core一致・一般の全域性/型保存も検査、Surface 保存は未完了)。約 1 分
lake exe naru_test golden       # 手書き Model との golden test(C10)。約 9 分
lake exe naru_test regression   # 上の全部 + 受理例・反例・生成 Lean の意味(C34)・決定性(C1)・simulate(C7)・設定(C24)を 1 コマンドで(C36)。約 12 分
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
