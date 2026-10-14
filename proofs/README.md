# proofs/ — プロトコル証明の書き方

`proofs/` は、naru が生成した Statements(プロトコルが公開する保証の命題)を **手書きで証明する** Lake ライブラリ `Proofs` です。
どのプロトコルにも同じ手順で使えます(consensus は 1 つの例にすぎません)。証明すべき命題の一覧は `naru compile` が機械的に作る
**義務** の一覧 `generated/obligations.json` で、証明が一覧のどれに対応し、いまも有効かは `naru proofs` が検査して報告します。

## 1. 義務一覧の見方

`lake exe naru compile` は `generated/obligations.json`(正規形の JSON。機械生成専用で手では編集しない)を Model / Statements と一緒に書きます。
コンパイル単位のすべての `claim` と `claim bundle`(入れ子の bundle を含む)が 1 件ずつ義務になります。`claim` の無い単位では `"obligations": []`。

先頭のフィールド `naru-compiler` / `naru-compiler-sha256` / `naru-stdlib` / `naru-stdlib-sha256` / `sources` は生成 Lean のヘッダと同じ値です。
`obligations` の各要素:

| フィールド | 意味 |
|---|---|
| `name` | naru の修飾名(`Consensus.Spec.Claims.finalizedSafe`)。束縛行にはこの名前を書く |
| `kind` | `"claim"` か `"claim bundle"` |
| `module` | naru のモジュール名 |
| `lean` | 生成 Statements の宣言名(`Statements.Consensus.Spec.Claims.finalizedSafe`) |
| `theorem` | 付ける theorem の名前(`lean` の先頭 `Statements.` を `Proofs.` に替えたもの) |
| `type` | **証明すべき命題**(義務の型)。Lean の式としてそのまま読める |
| `sha256` | 束縛 hash(下の 3)。束縛行に書く値 |
| `summary` | 宣言コメントの 1 行目(何を保証するかの要旨) |
| `bundles` | この claim を項目に持つ claim bundle の修飾名の配列(無ければ `[]`) |

`type` は、claim なら生成 Statements の宣言を input の引数と仮引数で全量化したもの(`∀ (input の引数…) (仮引数…), Statements.A.B.claim input… 仮引数…`)、
claim bundle なら構造体の命題そのもの(`∀ (input の引数…), Statements.A.B.Bundle input…`)です。義務の型は生成側が決め、証明側は変えません。

## 2. 証明の置き場と命名規則

- `proofs/Proofs.lean` がルートです(theorem は持たず、各モジュールを import するだけ。無いと `naru proofs` は exit 2。別のプロトコルで証明を始めるときは、
  まず何も import しないルートを置く)。証明は `proofs/Proofs/**.lean` に置きます。Lake ライブラリ `Proofs` が読むのはこの 2 か所だけで、それ以外の `.lean` は
  ビルドにも `naru proofs` にも入りません。
- theorem の名前は義務の `theorem` フィールドそのもの(`Proofs.Consensus.Spec.Claims.finalizedSafe`)。`Proofs.` の後は生成 Statements の宣言名の `Statements.` の後と同じです。
  名前空間はファイルのモジュール名と一致させる必要はありません(`namespace Proofs.Consensus.Spec.Claims` の中の `theorem finalizedSafe` でも、完全名を書いても同じ)。
- 型は義務の `type` を **そのまま** 書きます(明示の binder。implicit な binder に変えたり、別の形に書き換えたりすると、`naru proofs` の型の一致の検査で不正になります)。
- claim bundle の theorem は構造体の値を作ります(`fun inputs => { item1 := …, item2 := … }`)。項目は個々の claim の theorem を再利用してよい。
- 証明は `generated/` の Model / Statements の宣言に対して直接書きます。補題は別のモジュール(`proofs/Proofs/Consensus/` 配下など)に分け、theorem の入口のモジュールから
  import してかまいません。補題には義務の束縛行は要りません。
- import してよいもの: 生成 Model / Statements(`Model.*` / `Statements.*`)、`NaruStd`、Lean 本体(`Init` / `Lean` / `Std`)、mathlib(`Mathlib.*` とその依存パッケージ)。

## 3. 束縛行

証明が **どの義務の、どの版の型** に対するものかを、証明ファイルのコメント行で結びます。

```lean
-- naru-obligation: Consensus.Spec.Claims.finalizedSafe sha256:<obligations.json の sha256 の値>
theorem Proofs.Consensus.Spec.Claims.finalizedSafe : <obligations.json の type の値> := …
```

- 形: `-- naru-obligation: <naru の修飾名> sha256:<束縛 hash>`。名前は `name` フィールド、hash は同じ要素の `sha256` フィールドの値(64 桁の 16 進。桁が違えば形の崩れた束縛行として不正)。
- 置き場: `proofs/Proofs.lean` と `proofs/Proofs/**.lean` のどこでもよい(ファイルのどこにあっても読まれます。1 ファイルに複数書いてよい)。
  theorem の直前に置くと読みやすい。同じ義務の束縛行は 1 本にする(食い違う束縛行が複数あると失効)。
- 束縛 hash は、その義務の宣言が属する生成 Statements モジュールの import 閉包(生成 Model / Statements だけ)の本文と stdlib の hash から決まります。
  時刻・パス・コンパイラ版・宣言コメントの文言には依存せず、claim が依存する fn の本体や型が変わると変わります。同じ Statements モジュールの義務は同じ hash を持ちます。
- 束縛行の無い theorem、一覧に無い名前の束縛行、形の崩れた束縛行は、下の状況でそれぞれ `stale` / `invalid` になります。

## 4. 下書きは `sorry`

証明の途中は `sorry` を置いて構いません(下書きとして許されます)。`naru proofs` は `sorry`(未証明)と表示し、exit code には影響しません。
`sorry` が残る theorem は証明済みになりません。完成させたら `sorry` を消します(`proofs/` に `sorry` / `admit` が残らない状態が目標です)。

## 5. 失効(`stale`)したとき

生成 Statements / Model / stdlib が変わって義務の型が変わりうるとき、束縛 hash が変わり、古い束縛行の証明は **失効** と表示されます。
証明が Lean で通っていても証明済みにはせず、現在の hash を示します。手順:

1. `lake exe naru compile` で `generated/` を最新にし、`lake exe naru proofs` で `stale` の義務と現在の hash を確かめる。
2. `generated/obligations.json` のその義務の `type` を読み、**意図した命題のままか** を確かめる(何が変わったかは `git diff generated/` で見える)。
3. 命題が意図どおりなら、束縛行の hash を現在の値(`sha256`)に書き換える(再束縛)。型が変わっていたら、まず証明を直す(その上で再束縛)。
4. `lake exe naru proofs` で `proved` になることを確かめる。

hash の書き換えは「この型を見て、これが保証したい命題だと確認した」という人間の確認の印なので、確認せずに機械的に書き換えないでください。

## 6. mathlib の使い方

証明では mathlib を使えます(`import Mathlib.Tactic` など)。mathlib(Lean と同じ版)とその依存パッケージは、submodule `third_party/verified-consensus/.lake/packages/`
のビルド済みのものを Lake の path 依存で使い回します。複製も取得も要らず、ネットワークも使いません。**`lake update` は走らせないでください**
(mathlib のフック `post_update` がネットワークでキャッシュを取ろうとします。`lake-manifest.json` は path 依存に手で揃えてあります)。
mathlib を import するのは `Proofs` だけで、生成 Model / Statements・`NaruStd`・コンパイラなどは mathlib に依存しません。

## 7. 禁止事項

- `generated/` と `third_party/` の編集(`generated/` は `naru compile` の出力、`third_party/` は基準の参照物)。
- 義務の型の変更(`obligations.json` の `type` を書き換える・証明側で別の命題にすり替える)。命題を変えたいときは naru のソース(claim)を直して `naru compile` し直す。
- 公理の追加(`axiom`)。`propext` / `Classical.choice` / `Quot.sound` 以外の公理に依存する theorem は `invalid`(不正)。`sorry` と一緒でも不正が先。
- `set_option debug.skipKernelTC`(kernel の検査を飛ばす)。書いた行があれば不正。
- 義務の型の意味を変える notation / macro / coercion(`Coe` の instance)の定義。`naru proofs` の検査は証明モジュールを import した環境で義務の型を読むので、
  これらは判定を狂わせる(coercion で別の型の theorem を義務の型に見せかけても、検査用の theorem の公理監査が coercion の公理を捕まえて不正になる)。
- 手書きライブラリ `DecoupledConsensus*`・`NaruSem`・コンパイラ(`Naru.*`)・`NaruTest` の import。`Proofs` が依存してよい向きは上の 2 の一覧だけで、
  逆に生成 Model / Statements・`NaruStd`・`NaruSem`・コンパイラは `Proofs` を import しません。
- `compile` / `simulate` / `lsp` / `deps` は `proofs/` を読みません。証明の有無・成否でプロトコルの実行や生成物は変わりません。

## 8. 検査の走らせ方

```sh
lake exe naru compile              # 義務の一覧 generated/obligations.json を最新にする
lake exe naru proofs               # 証明状況の一覧(--json で正規形 JSON)
lake build Proofs                  # naru proofs を一度走らせた後(Lake が読む link を置くため)
lake exe naru_test proofs          # 証明基盤の検査(C68 / C69 / C70 / C72)。約 1 分
```

`naru proofs` は、`obligations.json` が現在のソースから作られたもの(`sources` の sha256 が一致)であることと `proofs/Proofs.lean` があることを確かめてから
`lake build Statements Proofs` を走らせ、義務ごとに theorem の存在・型の一致(kernel: `theorem NaruProofsCheck.obligation<i> : <義務の型> := Proofs.<名>`)・その検査用の theorem の
公理を検査して、義務ごとに 1 行 `<修飾名>  <状況>  <理由>` を表示します。

| 状況 | 意味 |
|---|---|
| `proved` | 証明済み。theorem があり、型が義務と一致し、許された公理だけに依存し、束縛行の hash が現在と一致する |
| `missing` | 未証明。theorem が無い |
| `sorry` | 未証明。`sorry`(`sorryAx`)に依存している(下書き) |
| `stale` | 失効。束縛行の hash が現在と違う、または theorem はあるが束縛行が無い |
| `invalid` | 不正。theorem の型が義務の型と違う、または許された公理(`propext` / `Classical.choice` / `Quot.sound`)以外に依存する。一覧に無い名前や形の崩れた束縛行も不正として数える |

判定の順は `missing` → `invalid` → `sorry` → `stale` → `proved` です。exit code: `lake build` の失敗・検査が走らない・`invalid` が 1 件でもあれば 1、
`missing` / `sorry` / `stale` だけなら 0(証明が未完了でも実行・シミュレーションを許す)、`naru.toml` の `proofs` が無い・`obligations.json` が無い・一覧が古い(ソースを変えて
`lake exe naru compile` していない)・`proofs/Proofs.lean` が無いなら 2。
`naru proofs` が書くのは `.lake/naru/` の link と検査ファイルだけで、`generated/` と `proofs/` には何も書きません。
最後の行 `layer: …` が示すとおり、これはプロトコルの保証(生成 Statements に対する theorem)の層で、コンパイラの意味保存(`lake build NaruSem`)は別の層です。

`naru_test proofs` は、`obligations.json` の決定性・束縛 hash の独立な再計算・検体 `tests/proofs/` での 5 つの状況・Lake の依存方向(`Proofs` の import 閉包に手書きライブラリ等が無いこと、逆依存が無いこと)・
`proofs/` に `sorry` / `admit` が残らないこと・この README の内容を検査します。

## 9. consensus の義務

このリポジトリの consensus(`specs/consensus/`)の義務は 14 件(13 claims と claim bundle `Consensus.Spec.Claims.Consensus`)で、
theorem の入口は `proofs/Proofs/Consensus/Spec/Claims.lean`、補題は `proofs/Proofs/Consensus/` 配下のモジュールに分けて置きます。
基準の verified-consensus の手書き証明(`third_party/verified-consensus/`)は **読んで参照してよい** ですが、import はしません(上の禁止事項)。
生成 Model / Statements に対して、必要な補題を `Proofs` の側で書き直します。

証明済み(7 件): `constants`(補題 `Proofs/Consensus/Constants.lean`。`period = 4Δ·R` などの時刻の式を Δ・R・η_SG の多項式に開き、
`SetupWellFormed` の数値の前提から `ConstantsValid` の各項を閉じる。手書き `constants_valid` の筋)、`nested`(補題 `Proofs/Consensus/Nested.lean` と
`Blocks.lean`。`getStable` / `getConfirmed` の `if preceq … then … else …` の分岐と `preceq` の反射律だけで閉じ、run への前提は使わない。手書き
`nestedOutputs_holds` の筋)、`finalizedMonotone`(補題 `Proofs/Consensus/FinalizedMonotone.lean`。`Stores.lean`: 生成 Model のハンドラで store の `f` を変えるのは
`updateFinality` の `prec st.f σ.f` を条件にした分岐だけなので、`nodeTick` / `nodeProcess` は `f` を縮めない。`Runs.lean`: `EventsSorted` から event の時刻は非減少で、
`t ≤ t2` なら `readAt` の `filter (≤ t)` は `filter (≤ t2)` の接頭辞。`Tables.lean`: stdlib の `Table.getOr (insert …)` の読みと `ValidatorId` の派生 `Ord` の `.eq`。
`Blocks.lean`: `preceq` の推移律。前提のうち使うのは `RunWellFormed` の `EventsSorted` だけ。手書き `finalized_readAt_mono_of_sorted` の筋)、
`certificatesAccountable`(補題 `Proofs/Consensus/CertificatesAccountable.lean`。run の前提は無く、`SetupWellFormed` からは
`normalizedValidators`(電子集団が正規集合であること)だけを使う。`Derivation.lean`: 名前付き導出 `deriveNamed` の不変条件 `Inv` — 高さの順序
`hF ≤ hJ < h`、`f` / `j` / `tH` が `eraseBlock B` の接頭辞、`hF = 0 → f = Genesis`、`finalize` / `targetParticipation` / `progress` が整列していて各署名者に
chain 上の行があること、finality の証明書(`hF ≠ 0` なら `finalityPair = some ⟨hF, root f⟩` の行を持つ定足数)、高さの横断(`1 ≤ h₀ < h` なら祖先 `X` と
`matchesEntry … h₀ (root X)` の行を持つ定足数)— を `B` の構造帰納法で示す(`processAttestation` → `foldRows` → `processHeightEvents` の順)。
`Orders.lean` / `Sets.lean`: 派生 `Ord` の `.eq ↔ =` と stdlib `Set` の所属の言い換え、`ValidatorId` の集合の整列(`Sorted`)と `Finset.sum` への橋。
`Weights.lean`: どの集合の重みも総重み `W` 以下、`weight (s ∪ t) + weight (s ∩ t) = weight s + weight t`、定足数の交わり `2q ≤ W + weight (s ∩ t)`。
`NamedBlocks.lean`: 名前付き祖先の行の消去が `chainAttestations (eraseBlock B)` に入ること。`Slashing.lean`: 同じ署名者の finality pair と衝突する
height pair は E1 で `slashable`、`slashable` の対称性。手書き `namedAccountableSafety_oriented` / `namedChainAccountableSafety` の筋)、
`finalizedAccountable` / `finalizedSafe`(補題 `Proofs/Consensus/FinalizedAccountable.lean` と `Carrier.lean`。`Carrier.lean`: store の不変条件 `StoreInv` —
bodies の各名前付きブロック `D` の消去が `core.tree` にあり、chain 状態の表 `core.sigma` のその鍵の値が `deriveNamed D` に等しく、`core.f` はどれかの
bodies の `D` の導出の `f`(finality carrier)— を全ハンドラで保つ(`f` / `tree` / `sigma` / `bodies` を書くのは `onBlockUsing` の受理の経路だけ。
そこで書く chain 状態は親の不変条件から `deriveNamed B`)。`FinalizedAccountable.lean`: `EventsSorted` の下で `readAt t` は `stateBefore i`
(`filter (≤ t)` は接頭辞 `take i`)なので carrier は run の中のブロック、`NamedRootCollisionFree` を `erased_ancestor_lift` で
`RootInjectiveOnAncestors` にして `certificatesAccountable` の `oriented` を両向きに当て、`Evidence` を `chainAttestations ⊆ storeAttestations`
で `SlashableStates` に持ち上げる / `SlashableBound` で退ける。`Orders.lean` の `block_compare_eq_iff` / `nb_compare_eq_iff`(`Block` / `NamedBlock` の
`compare` の `.eq ↔ =`)が tree / bodies / sigma の所属の言い換えに要る。手書き `storeAccountableSafety_stateBefore` /
`wholeRunAccountableFinalitySafety` / `wholeRunFinalitySafety` の筋)、
`honestNeverSlashed`(補題 `Proofs/Consensus/HonestNeverSlashed.lean`。前提のうち使うのは `UnforgeableRun` の `UnforgeableSignatures`(carried)と
`EventsSorted` だけ。`Records.lean`: validator client の記録 `Record`(高さごとの `target` / `timeout` / `lock`)について、`createAttestation` が
`target` を書くのは空のときだけ、`lock` は finality pair の高さに書かれて `finalityPair` の検査で既にある値は変わらない、`timeout` は増えるだけ、
`LockCompatible`(lock のある高さは timeout でなく target は空かその lock)と `FinalitySafeAt`(finality pair を出した高さは timeout でなく lock がその target)が
保たれ、既に target / lock のある高さに出す target はその値に等しい。`Signing.lean`: tick が記録を書くのは `attestWith` → `namedCreate` だけで attestation を
高々 1 つ出し、配送の処理は記録に触れず、`stateBefore (i + 1)` は添字 `i` の event だけを `stateBefore i` に畳んだものなので、記録の性質は run のどの添字でも
成り立ち以後も保たれる。`EmissionSafety.lean`: 同じ validator の 2 つの発行は同じ高さに同じ target を名指し(先の発行の target が記録に残り、後の発行はそれに従う。
同じ tick なら同じ行)、finality pair と timeout は両立しないので、消去は `e1Fields` / `e2Fields` とも偽で `slashable` でない。`Attribution.lean`: store の
不変条件(`Carrier.lean` に tree の各ブロックが bodies の消去であること `named` と bodies が親について閉じていること `closed` を足した)から、store の
attestation は bodies の名前付き祖先の行の消去で、bodies の genesis でないブロックはそのノードが処理した(`Processes`)ブロック(bodies が増えるのはブロックの
配送か自分の提案の tick だけ)なので、`UnforgeableSignatures` の carried で署名者の発行(`Emits`)に帰着する。手書き `validatorVoteSafety`
(`attributedVoteSafety` / `emissionVoteSafety` / `honestNoDoubleTarget` / `no_timeout_against_finality` / `carriedByHonest_of_storeAt`)の筋)。
残り 6 claims と bundle `Consensus` は `missing`。`naru_test proofs` は証明済みの件名が `proved` のままであることを検査する
(`tests/NaruTest/Proofs.lean` の `consensusProved`。証明を足したらそこにも足す)。

残りの liveness 系の claim(`available` / `confirmedLive` / `stableLive` / `stableIncludedFast` / `finalized` / `stableAsynchronyResilient`)に向けた
共有の足場は既にある(theorem はまだ無い): `Proofs/Consensus/Liveness.lean` の `liveFrom_of_includedFrom`(property `IncludedFrom`(honest な提案が
期限 `D` 以内に包含される)と `MonotoneFrom`・`NoFutureRead`・`SingleProposerRecurrence` から `LiveFrom … (gap · period + D)`。手書き
`Generic.liveFrom_of_includedFrom` の筋)、`confirmedLive_of_available` / `stableLive_of_available`(claim `available` の結論 `AvailableAt` から
`confirmedLive` / `stableLive` の結論)、`finalizedLive_of_included`(finalized の `IncludedFrom … (t0 + finalityStartup) finalityDeadline` から
claim `finalized` の活性の半分。単調性は `finalizedMonotone` の補題、再発は `StrongMultiProposerRecurrence`)。`NoFutureRead.lean` は
「時刻 `t` の読みに提案時刻が `t` より後の honest な提案は入らない」を `ExecutionValid`(`EventsSorted`・event の時刻が非負)と Δ > 0 だけから
3 出力すべてについて示す: `Clocks.lean`(store の時計 `t` / `s` を書くのは tick の冒頭だけで `s = slotOf e t`、時計は event の時刻以下で非負)、
`TreeInv.lean`(`f` / `j` / `latestConfirmed` / `latestStable` は常に tree の要素。`updateFinality` が書く `σ.f` / `σ.j` は受理したブロックの祖先、
`updateConfirmationWith` が書く値は grade の読み `activePrefix` = filtered tree の `deepest?`・fork choice `ghost`(anchor か tree の子)・
`getFgRoot`(`j` / `f`)か元の値)、受理の守り `¬ (st.s < slot b)`(`onBlockUsing_slot_le`)から tree のブロックの提案時刻は読みの時刻以下
(`tree_block_slot`)、honest な提案 `proposedBlockAt k` は slot `k` のブロック(提案の時計は `proposalTime k`)。残るのは `available`
(回復と GST-zero の保証)、finalized の包含、`stableIncludedFast`、`stableAsynchronyResilient` の本体で、手書きでは `StableCoverageConsumer` 等の
数千行の下流に当たる。

生成 Model の定義に対して補題を書くときの運び(`finalizedMonotone` で使った形): `unfold <関数>` → `dsimp only`(`let` を展開し、pair の `match` を
射影 `.1` / `.2` に落とす)→ `split_ifs`(すべての `if` を割る)→ 各分岐を `rfl` / 既存の補題で閉じる。`exact` の単一化が左辺の `st.f` から先に
`?st := st` と決めて失敗するときは、始点を等式 `hf : st0.f = f0` で与える形の補題(`updateFinality_f'` / `proposeBlockWith_f'`)を使う。
`exact preceq_self _` を大きな項の goal に試すと `whnf` の heartbeat を使い切るので、`first | …` で並べず分岐ごとに書くか、候補を
`with_reducible exact …` にして照合を reducible な展開だけにする(`Carrier.lean` の `tick_inv`: 16 の経路を 16 の候補で閉じる)。
再帰する型(`Block` / `NamedBlock`)の `compare` は backend が構造的再帰で明示的に定義する(`docs/architecture.md`「再帰する型の `Ord`」)ので
`rfl` / 等式補題が効く。Lean の `deriving Ord` のままでは `partial`(不透明)で、`Set` / `Table` の所属の補題が書けない。
tick の出力(`(tick …).2.2`)と記録(`.2.1`)を論じる補題(`Signing.lean` の `tick_attest_shape`、`Attribution.lean` の `tick_bodies`)は、
`unfold tick` → `dsimp only` → `split_ifs`(仮説と goal の両方なら `split_ifs at hD ⊢`)の後に、全経路を同じ tactic 列
(`all_goals first | exact … | …`。出力の `match blockOut with …` に attestation が無いことは `(try split at h) <;> simp at h`)で閉じる。
`cases hm : e with` は goal の `e` だけを置き換え仮説は置き換えないので、仮説には `rw [hm] at h` を足す。
