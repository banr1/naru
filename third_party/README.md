# third_party — 同梱する外部の参照物

naru 本体ではない、基準として同梱する外部のリポジトリの置き場。いまは `verified-consensus/` だけ。

## verified-consensus(git submodule)

- 上流: https://github.com/fradamt/verified-consensus
- 基準コミット: `b241081d344555797205f8718eeb23a8a0e3eb4c`(2026-09-28「Migrate to Lean and Mathlib v4.34.1」)。submodule が指すコミットはこれ(IDEAL.md の前提「基準コミット」と同じ)。
- ライセンス: CC0 1.0 Universal(`verified-consensus/LICENSE`。naru の `LICENSE` も同じ全文)。
- 引用: `verified-consensus/CITATION.cff` — D'Amato, Francesco. "verified-consensus: a Lean 4 formalization of the decoupled consensus protocol". https://github.com/fradamt/verified-consensus (CC0-1.0, 2026-09-23)。
- 役割: 手書きの Model(`DecoupledConsensusModel`、29 ファイル)・Statements(`DecoupledConsensusStatements`、13 claims の `Consensus`)・Witnesses(4 つの具体的 run)が、
  naru の golden test(IDEAL.md C10)と claim surface(C9)の基準。`scripts/` の検査の雛形も参照する。

### 約束

- **この submodule の中身は変更しない。** 指すコミットは IDEAL.md の前提「基準コミット」で、変えるのは `idd refine` だけ。周回が自分の判断で進めたり戻したりしない。
- 内側の `.github/`(上流の CI)は naru では動かない。
- 手書き側のビルド成果物(mathlib と手書き Model の olean、約 17 GB)は `verified-consensus/.lake/`(追跡対象外)にある。golden test に要るのは
  `DecoupledConsensusModel`(と Statements の `Instantiation`)のビルドだけで、Proofs はビルドしなくてよい(フルビルドは約 1 時間)。

### 取得

clone の直後は空のディレクトリなので、取得が要る(GitHub への接続が要る):

```sh
git submodule update --init
cd third_party/verified-consensus && lake build DecoupledConsensusModel
```

### 上流に新しい版が出たかの確かめ方と更新の運び

```sh
git ls-remote https://github.com/fradamt/verified-consensus HEAD
```

の SHA を基準コミットと比べる。違えば上流に新しい版がある。取り込むと決めたら、専用のスクリプトは作らず、`idd refine` で IDEAL.md の基準コミットを
書き換える(上流の差分の要点 — claim の名前・数、Model の挙動、Lean / mathlib の版 — も伝える)。周回は IDEAL.md の基準コミットと submodule が指す
コミットの食い違いを見つけたら、submodule の中で基準コミットを取り、手書き側をビルドし直し、移植(`specs/consensus/`)を追従させ、C9 / C10 の証拠を
取り直す(IDEAL.md「基準コミットの更新の運び」)。
