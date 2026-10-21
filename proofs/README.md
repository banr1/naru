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
大きな義務は、`sorry` を名前付きの穴に閉じ込めた骨格として先に置き、穴を 1 つずつ閉じます(下の 11)。

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
`proofs/` に `admit` が無く `sorry` が下の「11. 骨格と穴」の穴の一覧と一対一に対応すること・義務の theorem の公理監査・この README の内容を検査します。

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
`hF ≤ hJ < h`、`f` / `j` / `tH` が `eraseBlock B` の接頭辞、`hF = 0 → f = Genesis`、`hJ = 0 → j = Genesis`、`finalize` / `targetParticipation` / `progress` が整列していて各署名者に
chain 上の行があること、finality の証明書(`hF ≠ 0` なら `finalityPair = some ⟨hF, root f⟩` の行を持つ定足数)、justification の証明書
(`hJ ≠ 0` なら `matchesEntry … hJ (root j)` の行を持つ定足数。周回 160 で足した)、高さの横断(`1 ≤ h₀ < h` なら祖先 `X` と
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
残りの 6 claims と bundle `Consensus` は骨格(周回 211・212。穴 10 件、`sorry` と表示。下の 12)で、`missing` は 0 件。`naru_test proofs` は証明済みの件名が `proved` のままであることを検査する
(`tests/NaruTest/Proofs.lean` の `consensusProved`。証明を足したらそこにも足す)。

残りの liveness 系の claim(`available` / `confirmedLive` / `stableLive` / `stableIncludedFast` / `finalized` / `stableAsynchronyResilient`)に向けた
共有の足場(周回 212 から骨格の theorem が使う): `Proofs/Consensus/Liveness.lean` の `liveFrom_of_includedFrom`(property `IncludedFrom`(honest な提案が
期限 `D` 以内に包含される)と `MonotoneFrom`・`NoFutureRead`・`SingleProposerRecurrence` から `LiveFrom … (gap · period + D)`。手書き
`Generic.liveFrom_of_includedFrom` の筋)、`confirmedLive_of_available` / `stableLive_of_available`(claim `available` の結論 `AvailableAt` から
`confirmedLive` / `stableLive` の結論)、`finalizedLive_of_included`(finalized の `IncludedFrom … (t0 + finalityStartup) finalityDeadline` から
claim `finalized` の活性の半分。単調性は `finalizedMonotone` の補題、再発は `StrongMultiProposerRecurrence`)。`NoFutureRead.lean` は
「時刻 `t` の読みに提案時刻が `t` より後の honest な提案は入らない」を `ExecutionValid`(`EventsSorted`・event の時刻が非負)と Δ > 0 だけから
3 出力すべてについて示す: `Clocks.lean`(store の時計 `t` / `s` を書くのは tick の冒頭だけで `s = slotOf e t`、時計は event の時刻以下で非負)、
`TreeInv.lean`(`f` / `j` / `latestConfirmed` / `latestStable` と、確認の更新が書く `liveConfirmed`(周回 164 で追加。`ghost` の head か `getFgRoot`)は常に tree の要素。`updateFinality` が書く `σ.f` / `σ.j` は受理したブロックの祖先、
`updateConfirmationWith` が書く値は grade の読み `activePrefix` = filtered tree の `deepest?`・fork choice `ghost`(anchor か tree の子)・
`getFgRoot`(`j` / `f`)か元の値)、受理の守り `¬ (st.s < slot b)`(`onBlockUsing_slot_le`)から tree のブロックの提案時刻は読みの時刻以下
(`tree_block_slot`)、honest な提案 `proposedBlockAt k` は slot `k` のブロック(提案の時計は `proposalTime k`)。残るのは `available`
(回復と GST-zero の保証)、finalized の包含、`stableIncludedFast`、`stableAsynchronyResilient` の本体で、手書きでは `StableCoverageConsumer` 等の
数千行の下流に当たる。

claim `available` の結論 `SafeFrom g t0 = AgreeFrom g t0 ∧ MonotoneFrom g t0`(`g` は Confirmed / Stable)に向けた足場(theorem はまだ無い):
`ConfirmationRecords.lean`(利用者向けの 2 つの記録 `latestConfirmed` / `latestStable` を書くのは `updateConfirmationWith` だけ。その書き方
`advanceConfirmed old cand`(`cand ⪯ old` なら `old`、でなければ `cand`)と `floorOnStable stable cand old` は「古い記録の接頭辞 `B` は、新しい記録と
互換なら新しい記録の接頭辞のまま」(`Keeps`)を満たす(手書き `preceq_floor` / `update_confirmation_with_latest_preserves`)。投票・attestation・ブロックの
受理・finality の更新は記録を変えず(`SameRec`)、1 tick の結果は記録を変えない務めで得た store に更新を高々 1 回掛けた形(`tick_rec_shape`、
`Carrier.tick_inv` と同じ 16 経路))、`RecordGrowth.lean`(run に沿って: ノード `v` の記録 `recAt R v i` が変わるのは `v` 自身の tick の添字だけ
(`recAt_succ`)、添字 `m` の記録の接頭辞は `[m, n)` の各 tick の直後の記録と互換なら添字 `n` でも接頭辞(`prefix_preserved`)、時刻 `t` の読み
`storeAt v t` は `filter (eventTime ≤ t)` の長さ `idx t` の `stateBefore`(`EventsSorted`)、`idx` より前の event の時刻は `t` 以下・以降は `t` より後、
`v` の tick の直後の記録は同じ時刻の読みの記録(`recAt_tick_eq_storeAt`。同じ時刻の後続の event に `v` の tick が無いことに event の重複の無さ
`EventsNodup` が要る)、よって記録の時刻 `t` の値が `t` 以後のどの時刻の値とも
互換なら時刻 `t2 ≥ t` の値の接頭辞(`record_mono_of_compatible`。手書き `latest_confirmed_mono_of_agreement`))、`ShortHorizon.lean`(確認評価の時刻
(`0 < slotOf e t` かつ `t = supportCutoff e (slotOf e t)`)でない tick は 2 つの記録を変えず(`tick_rec_of_noCutoff`)、正の slot の締切は
`confirmationTime e 0` 以後なので、`horizon < confirmationTime e 0` の run ではどの読みでも確認の記録と stable の記録は genesis(`storeAt_rec_short`。
手書き `latestConfirmedAt_eq_genesis_of_short_horizon`)、finalized も genesis(読みの時計の slot は 1 以下で、tree の親の slot の不変条件
`ParentSlot.stateBefore_parentInv` から finality carrier の担い手は genesis か親が genesis のブロック `storeAt_f_short`))、`Outputs.lean`(出力
`getStable st = if f ⪯ latestStable then latestStable else f`、`getConfirmed st = if getStable ⪯ latestConfirmed then latestConfirmed else getStable` の
単調性と一致を、欄の事実 — `f` の単調性(`EventsSorted`)、記録の時刻をまたぐ一致 `RecordAgreeFrom`、記録と finalized の交差の互換 `CrossAgreeFrom`、
finalized の一致 `AgreeFrom … Finalized` — と、確認の出力では `StableBelowConfirmed`(stable の記録 ⪯ 確認の記録)に還元する
`safeFrom_stable_of_fields` / `safeFrom_confirmed_of_fields`。手書き `ConfirmedOutput.lean` の筋)、`RecordOrder.lean`(`StableBelowConfirmed` は regime の事実ではなく
store の不変条件: `updateConfirmationWith` は `latestStable := stable`、`latestConfirmed := floorOnStable stable candidate old` と書き、`floorOnStable` はどの分岐でも
`stable` を延ばす(`stable_preceq_floorOnStable`)。初期 store は両方 `Genesis`、他のハンドラは記録を変えない(`SameRec`)ので、tick / deliver / world / `readAt` /
`stateBefore` / `storeAt` のどの store でも前提なしに成り立つ(`storeAt_sbc` / `stableBelowConfirmedFrom`。手書き `ConfirmationRecordOrigin.lean` の
`update_confirmation_stable_le_confirmed` / `stableBelowConfirmed_storeAt`。手書き `ConfirmedOutput.lean` の「regime の事実」という注記は古い)。
stable の記録についての欄の事実(2 ノードの一致 `RecordAgreeFrom`・finalized との交差の互換 `CrossAgreeFrom`)は、`S ⪯ C` から確認の記録のそれに
従う(`recordAgreeFrom_stable_of_confirmed`: 2 つの確認の記録が互換なら一方が他方の接頭辞で、2 つの stable の記録はともに大きい方の接頭辞 /
`crossAgreeFrom_stable_of_confirmed`: `C ⪯ F` なら `S ⪯ F`、`F ⪯ C` なら `S` と `F` はともに `C` の接頭辞)ので、2 つの出力の `SafeFrom` はどちらも
確認の記録の一致・交差の互換・finalized の一致の 3 つだけに還元される(`safeFrom_confirmed_of_records` / `safeFrom_stable_of_records`)。
`AgreeFrom` / `MonotoneFrom` / `SafeFrom` の開始時刻についての単調性 `*.mono` も置く)、`Available.lean`(claim `available` の結論 `AvailableAt t0` を
残る 5 つの事実 — `latestConfirmed` の `RecordAgreeFrom` と `CrossAgreeFrom`、`AgreeFrom … Finalized t0`、`IncludedFrom … Confirmed t0 confirmationDelay`、
`IncludedFrom … Stable t0 stableInclusionDelay` — から組み立てる `availableAt_of_records`(前提は `EventsSorted` / `EventsNodup` だけで regime に依らない)と
`SleepyRegime` 版 `availableAt_of_fields`。finalized の一致は、`t0 ≠ 0` なら `SleepyRegime` の `RecoveredBy` は回復の枝(`t0 = recoveryEnd …`)に限られ、
その枝は `SlashableBound` を持つので、`ExecutionValid` → `RunWellFormed`(`runWellFormed_of_executionValid`)と `finalizedSafe` の本体を `t0 ≥ 0` の窓に
絞って従う(`agreeFrom_finalized_of_slashableBound` / `agreeFrom_finalized_of_recovered`。残る事実は 4 つ `availableAt_of_fields_recovered`))。
確認の候補を書く fork choice と得点の最初の層(theorem はまだ無い): `Goldfish.lean`(fork choice `ghost anchor tree score eligible` は anchor から適格な子
(`ghostChildren`: tree の要素で親が現在の head、`eligible` が真)のうち得点最大の一意なもの(`argmax?` = `findUnique?`)へ降りる燃料つきの歩み `ghostWalk`。
一歩の結果は現在の head の適格な子(`ghostStep_child`)、適格な子が無ければ止まる(`ghostStep_none`)、結果は anchor を延ばし(`ghost_preceq`)、anchor そのものか
適格な tree の要素(`ghost_eligible`)。降下補題 `ghost_reaches`(手書き `Walk.lean` の `ghost_reaches`): anchor から `target` までの途中のブロックがすべて tree に
あり、各ブロックで歩みの次の一歩が `target` の祖先で、`target` に適格な子が無ければ結果は `target`。燃料 `size tree` が足りること(`path_card`)は、途中の
ブロックが深さの相異なる tree の要素なので `size tree` 個以下であることから(`chainUpTo`: 親を遡る列。`pairwise_chainUpTo` / `chainUpTo_le_size`)。
親について閉じた tree では結果に適格な子は無い(`ghost_terminal`: 燃料を使い切ると深さ `depth anchor + size tree` の tree の要素に達し、その祖先 `size tree + 1`
個が tree にあって矛盾)。Goldfish の得点 `goldfishScore`(`rawEquivocators` の個数 + `rawSupporters` の個数。支持者は slot `s` の投票が `b` の子孫
(`b ⪯ c`)を指す非 equivocator の投票者 `mem_rawSupporters_iff`)は祖先ほど大きく(`goldfishScore_mono`。手書き `supporters_mono`)、支持者は投票の参加者
(`rawSupporters_size_le`。手書き `supporters_subset_participants`)。`updateConfirmationWith` の `let` 束縛を名前つきの定義(`earlyVotes` / `lateVotes` /
`supportVotes` / `lateCount` / `score` / `eligible` / `sgRoot` / `head` / `live` / `stableRec` / `candidate`)に開いて `updateConfirmationWith_eq`(`rfl`)で結び、
新しい確認の記録は 元の記録 / stable の記録 / 過半の支持 `lateCount < 2 · score` を持ち SG root を延ばす fork choice の head / grade の候補
`frameSgCandidate` のどれか(`latestConfirmed_shape`))。
投票の pool と過半の支持の honest な投票者(theorem はまだ無い): `Votes.lean`(投票の pool `storePool st k`(`gfVotes` の鍵 `k` のリストの集合)に投票を
入れるのは `onGoldfishVote` だけで、必ず `onGoldfishVoteChecked` の守り `vote.valIndex ∈ committee' vote.slot` を通る(ブロックの受理が運ぶ投票の `foldl`、
配送された投票 `receiptProcess`、自分の投票 `goldfishVoteWith`)。`onGoldfishVote` は鍵 `vote.slot` のリストの末尾に足し他の鍵は変えない(`poolList_onGoldfishVote`)。
pool の不変条件 `PoolInv committee' st`(鍵 `k` の投票は slot が `k` で投票者は `committee' k` の要素 `Admissible`)と拡張 `PoolExt committee' a b`(`a` の投票は
`b` にも残り、`b` に増えた投票は適格)を全ハンドラ(投票を触らないものは `PoolExt.of_same`)→ tick(`tick_poolExt`: `Carrier.tick_inv` と同じ 16 経路。
`NamedStore` の間の拡張 `NExt` を `abbrev` にして各務めの補題を「出発点からの拡張を 1 段延ばす」形 `*_poolExt'` にすると、`with_reducible exact` の入れ子で閉じる)/
deliver → world → run の読みに積み上げ、`storeAt_pool` / `stateBefore_pool`(前提なし)と `stateBefore_poolExt` / `storeAt_poolExt`(`EventsSorted` の下で同じノードの
pool は添字・時刻について増えるだけ)。自分の投票の形 `goldfishVoteWith_some`: 投票者は自分、slot は store の `s`、head は `getHeadInTreeWith` の結果の root、
自分は slot の committee の要素、store 側は `onGoldfishVoteChecked`)、`Majority.lean`(確認の門 `lateCount < 2 · score` と honest 過半。手書き
`DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean` の `Numerator` / `HonestSupport` の筋。支持の投票は遅い投票
`supportVotes_sub_lateVotes`(解決の印 `storeTau` = 受信の印と head のブロックの受信の印の大きい方 `stampBefore_of_max`、`supportCutoff ≤ confirmationTime`、`0 ≤ Δ`。
手書き `Numerator.subset_late`)なので、`noSecondVoteIn lateVotes` の絞り込みから支持の投票は投票者ごとに 1 つ `supportVotes_unique`(手書き `unique_in_late`)、
equivocator は無く `supportVotes_no_equivocation`(手書き `no_equivocation`。`NaruStd.Set` の要素は整列して重複が無い: 任意の `[Ord α]` で `.lt` が推移的・`.gt` が
逆向きの `.lt` なら stdlib の構築関数が狭義昇順 `SortedLt` を保つ、`GoldfishVote` の派生 `Ord` は (投票者, slot, head) の辞書式 `gv_lt_iff`)、得点は支持者の数そのもの
`score_eq_supporters`。参加者は committee の要素 `participants_sub_committee`(`PoolInv`。手書き `voters_count_le_committee`)、`NaruStd.Set ValidatorId` の大きさは
整列(`Sorted`: `voters` は `Set.map` = `of` で整列、`filter` が保つ)の下で `Finset` の濃度 `size_eq_card`。数え上げの核 `exists_honest_of_majority`(`Finset` の上:
equivocator `E` と支持者 `S` は遅い投票の参加者 `P` に含まれ互いに素、`P ⊆ C`(committee)、honest な committee の要素 `C ∩ H` はすべて参加者、`|C| < 2 |C ∩ H|`
(`HonestCommittees`)、門 `|P| < 2 (|E| + |S|)` なら `E ∪ S` に honest な要素がある。無ければ `E ∪ S ⊆ P \ H` で `2 |P \ H| > |P| ≥ |P \ H| + |C ∩ H|`、一方
`|P \ H| ≤ |C \ H| < |C ∩ H|` で矛盾)から、**門を通るブロックには honest な支持者がいる** `exists_honest_supporter`(honest な `v` とその投票 `u`: slot `s`、`b` 以下を
指す `targetsUnder`。前提は `0 ≤ Δ`・`PoolInv`・committee の整列・`HonestCommittees` の不等式・honest な committee の要素がみな遅い投票の参加者)/
`_of_eligible` / `_of_head`(fork choice の head が SG root から降りていれば head について)/ `_of_run`(`SetupWellFormed`(`committee_sorted`、`0 < Δ`)と
`HonestCommittees`(`honestCommittees_at`)から run の読み `storeAt` の store について)。手書きの `HonestSupport` から `vote` を弱めた **`HonestSupport`**
(`majority`: committee は honest 過半、`vote`: honest な committee の要素はみな支持の投票に `B` 以下を指す slot `s` の投票を持つ。手書きは「`B` にちょうど
解決する」を要求する)から、honest な committee の要素はみな参加者で `B` の支持者(`participants` / `supporters`)、`B` とその祖先は門を通る
`HonestSupport.eligible` / `eligible_of_preceq`(`2 · score B ≥ 2 |C ∩ H| > |C| ≥ lateCount`、得点は祖先ほど大きい)、門を通るどのブロック `C` も `B` と互換
`HonestSupport.compatible_of_eligible`(`C` の honest な支持者の投票は投票者ごとに 1 つなので `B` 以下も指す。手書き `not_eligible`(`B` と競合するブロックは門を
通らない)より弱い形で、`vote` を弱めたので結論は互換まで)。生成 Model の得点と `HonestCommittees` は個数(`Set.size`)なので重みではなく個数で数える)。
`Voting.lean`(honest な投票の発行。tick の投票の務め `namedGoldfishVoteWith` は `voting`(`0 < s`、`t = voteTime e s`)のときだけ走り、提案の務めの後の
store `voteStore` を読む。tick が出す投票は投票の時刻の tick の務めの出力で、投票者は自分・slot は `slotOf e t`・投票者は committee の要素
`tick_gfVote_shape` / `tick_gfVote_fields` / `emits_gfVote_shape`(手書き `gfVote_emitted_shape` / `emits_gfVote_shape`)、1 つの tick が出す投票は 1 つ
`tick_gfVote_unique`、どの投票者も slot ごとに発行する投票は 1 つ `emits_gfVote_unique`(`ScheduleWellFormed` の event の重複なし。手書き `emits_gfVote_unique`)、
投票の時刻の tick で committee の要素なら必ず投票を出す `tick_gfVote_of_duty`(務めは `awake'` を見ない)、`ScheduleWellFormed` は honest なノードの公開時刻の
tick を horizon まで run に入れるので honest な committee の要素は各 slot `k > 0`(`voteTime e k ≤ horizon`)で投票を発行する `honest_emits_gfVote`
(`slotOf_voteTime`(手書き `slotOf_vote_time`)/ `publicTime_voteTime`)。投票の head: 投票の時刻は提案の時刻と違う(Δ > 0)ので投票の務めが読む store は
時計を合わせただけ `voteStore_of_voteTime`(手書き `vote_time_ne_proposal_time` の筋で `voteTime_ne_proposalTime`)、tick が出す投票の head は tick の前の store に時計を
合わせたもの `clocked` の fork choice の head `voteHead`(`tick_gfVote_head`)、run では `Emits` の添字 `i` の `stateBefore i` の発行者の store と `onPhaseTick` で進めた
cache で読む `emits_gfVote_head` / `honest_emits_gfVote_head`)。
`Delivery.lean`(投票の配送の層の入口。投票は `excludes` が偽なので `PartialSynchrony` の第 1 連言から、honest な `v` が時刻 `t` に発行した投票を
honest な `w` が締切 `max t tGST + Δ`(horizon 以内)より前のある添字で扱う `partialSynchrony_gfVote`。`HandlesAt` の投票の経路は `w` 自身の tick の発行
(= `Emits` の添字。投票者は `w`)・`w` への配送・投票を運ぶブロックの新しい受理の 3 つ `handlesAt_gfVote_cases` / `partialSynchrony_gfVote_cases` /
`handlesAt_gfVote_tick_self`。配送された投票が pool に入るのは無条件ではなく、投票者が committee の要素(`voteWellFormed`)・受信者の slot が `u.slot` か
`u.slot + 1`(`InWindow`)・pool の slot `u.slot` に同じ投票者の投票がまだ 2 つ無い(`equivocates` が偽)ときで(`mem_onGoldfishVote` /
`mem_onGoldfishVoteChecked` / `mem_receiptProcess_gfVote`。手書き `on_goldfish_vote_insert` の窓と equivocation の守りに当たる。配送は時計を進めないので、
受信者の slot は受信の前の受信者自身の最後の tick で決まる)、run では配送の添字 `j` の後の
`stateBefore (j + 1)` 以降の受信者の pool に残る `deliver_gfVote_mem` / `gfVote_mem_of_le` / `deliver_gfVote_mem_of_lt`。受信済みの判定は pool の所属
`processed_gfVote_iff`)。
`Window.lean`(受信の直前の slot の窓。配送は時計を進めないので、時計は添字について単調 `clock_succ_ge` / `clock_mono`(手書き `stateBefore_clock_mono`)で、
添字 `j < i` の自分の tick の時刻は `stateBefore i` の時計以下 `tick_le_clock`。event が整列していれば時刻が狭義に早い event は添字も前 `lt_of_time_lt`。
slot の開始時刻 `proposalTime k`(Δ の `4k` 倍)は公開時刻 `publicTime_proposalTime` なので `ScheduleWellFormed` が honest な受信者の tick を run に入れ
(`honest_tick_index`)、honest な `w` への時刻 `t2` の配送の直前の slot は `proposalTime k < t2` なら `k` 以上 `slot_ge_of_deliver`、`t2 < proposalTime (k + 1)` なら
`k` 以下 `slot_le_of_deliver`。`proposalTime u.slot < t2 < proposalTime (u.slot + 2)` なら `InWindow` `inWindow_of_deliver`。投票の時刻は `proposalTime k + Δ`、
slot の長さは `4Δ` なので、GST 以後(`tGST ≤ t`)に時刻 `t` に発行された投票の、発行の時刻 `t` 以後で締切 `t + Δ` より前の配送の直前の slot はちょうど `u.slot` で `InWindow`
`slot_eq_of_deliver_gfVote` / `inWindow_of_deliver_gfVote` — `Delivery.deliver_gfVote_mem` の窓の仮定を満たす)。
`PoolFrom.lean`(pool の投票の由来。pool に投票を入れるのは `onGoldfishVote` だけで、来る投票は配送された投票・受理したブロックが運ぶ投票(`gfVotes (eraseBlock B) = namedGfVotes B`)・
自分の tick の出力(提案したブロックが運ぶ投票と自分の投票)の 3 通り(`onGoldfishVote_from` / `foldl_onGoldfishVoteChecked_from` / `onBlockUsing_from` / `onBlockWith_from` /
`receiptProcess_from` / `proposeBlockWith_from` / `namedGoldfishVoteWith_from` / `tick_from`)。したがって `stateBefore i` のノード `u` の pool の投票は `u` が処理した(`Processes`)投票か、
`u` が処理したブロックが運ぶ投票 `pool_from`(手書き `GfFrom` / `gfFrom_on_goldfish_vote_checked`。store の attestation の真正性の `Attribution.bodies_processed` と同じ運び)。`UnforgeableSignatures` の 2 つの連言から
honest な投票者の pool の投票はその投票者の tick が出した投票 `pool_genuine`、`Voting.emits_gfVote_unique` と合わせて同じ honest な投票者・同じ slot の pool の投票は
どのノード・どの添字でも 1 つ `pool_honest_unique` — `equivocates` が偽であることに向けた層)。
`Equivocation.lean`(honest な投票者は run のどの添字・どのノード・どの鍵の pool でも equivocate しない `pool_no_equivocation`: pool の集合は整列なので `votesBy` の絞り込みに重複は無く、
鍵 `k` の pool の投票の slot は `k`(`Votes.PoolInv`)で、`pool_honest_unique` から同じ honest な投票者の投票はすべて等しく、大きさは 1 以下(`Majority.supportVotes_no_equivocation` と同じ運び)。
発行された投票の投票者は committee の要素 `voteWellFormed_of_emits`。`Delivery.deliver_gfVote_mem` の 3 つの仮定 — committee・窓(`Window.inWindow_of_deliver_gfVote`)・equivocation — を
すべて外し、GST 以後に honest な `v` が発行した投票の honest な `w` への締切 `max t tGST + Δ` より前の配送の後、`w` の鍵 `u.slot` の pool に投票がある
`deliver_honest_gfVote_mem` / `deliver_honest_gfVote_mem_of_lt` — 配送の経路 (2) の完成。経路 (1)(自分の tick)と (3)(ブロックが運ぶ投票)は残り)。
`OwnVote.lean`(tick の投票の務め `namedGoldfishVoteWith` は投票を出すとき store に `onGoldfishVoteChecked` で入れ(`Votes.goldfishVoteWith_some`)、務めの store の slot は投票の slot なので窓は自明、
投票者は committee の要素。Δ > 0 なら投票の時刻に提案の務めは走らず(`Voting.voteStore_of_voteTime`)、確定の更新と attestation の務めは pool を変えないので、tick の前の pool で equivocation が無ければ
tick の後の鍵 `u.slot` の pool に投票がある `tick_gfVote_mem` / `nodeTick_gfVote_mem`。run では honest な `w` の tick が出した投票の投票者は `w` 自身で `pool_no_equivocation` が守りを満たし、
以後 `w` の pool にある `tick_honest_gfVote_mem` / `emits_honest_gfVote_mem_of_lt` — 経路 (1) の完成。`Delivery.handlesAt_gfVote_cases` の経路 (1)(2) をまとめ、GST 以後の honest な投票を honest な `w` が
発行の時刻以後・締切より前の添字 `j` で扱えば `stateBefore (j + 1)` の `w` の pool に投票があるか経路 (3) `handlesAt_honest_gfVote_mem_or_carried`)。
`Carried.lean`(ブロックの受理 `onBlockUsing` は新しいブロックを tree に入れるときだけ受理の分岐を通り、運ばれた投票を `foldl onGoldfishVoteChecked` で入れる。畳み込みの途中の store は時計が元のまま
(`Clocks.onGoldfishVoteChecked_clock`)で pool は最終の pool の部分集合(`Votes.foldl_poolExt`)なので、最終の pool で投票者の投票が 1 つ以下(`UniqueIn`)なら途中の equivocation の守りも通り
(`equivocates_false_of_unique`)、窓・committee の下で運ばれた投票は受理の後の pool にある `foldl_mem` / `onBlockUsing_mem` / `processBlockCore_mem`。tick がブロックを出すのは提案の時刻だけ
`tick_block_time` で、投票の時刻以後・次の slot の提案の時刻より前は提案の時刻ではない `ne_proposalTime_of_vote_window` ので、GST 以後の honest な投票の締切より前の経路 (3) は `w` への配送だけで、
受信の直前の slot はちょうど `u.slot` で、配送の後の pool で honest な投票者の投票は 1 つ以下 `stateBefore_uniqueIn` なので pool に入る `carried_honest_gfVote_mem` — 経路 (3) の完成。
経路 (1)(2)(3) をまとめて `handlesAt_honest_gfVote_mem`(扱った event の直後の pool にある)、`PartialSynchrony` と合わせて締切が horizon 以内なら締切より前のある添字の後で
honest な `w` の pool にある `partialSynchrony_honest_gfVote_mem`)。
`Stamps.lean`(受信の印の表 `timestampVote` を書くのは `onGoldfishVote` だけで、投票を pool に入れるときにその印を時計の時刻 `Stamp.At st.t` にし、既に鍵 `u.slot` の pool にある投票は受理しない
(`onGoldfishVote_cases`)。したがってどのハンドラも時計を変えずに pool の投票の印を保存し新しい投票の印は時計以下(`Step`)、tick は時計を合わせた後の store からの `Step`(`tick_grow`)。
run では時計が添字について単調(`Window.clock_succ_ge`)なので pool の投票の印は時計以下 `stateBefore_stampInv`、添字 `j` の event の後の時計はその event の時刻以下 `clock_succ_le_event` なので
`stateBefore (j + 1)` の pool の投票は以後ずっと pool にあり印は添字 `j` の event の時刻以下 `stamp_le_of_mem`。投票の締切 `voteTime + Δ` は `supportCutoff` と等しいので、GST 以後の honest な投票は
`supportCutoff` が horizon 以内なら honest な `w` の pool に `w` ごとのある添字の後で入り受信の印が `supportCutoff` より前 `partialSynchrony_honest_gfVote_stamped`)。
`BlockStamps.lean`(ブロックの受信の印の表 `timestampBlock` を書くのは `onBlockUsing` の受理の分岐(`storedOf`)だけで、まだ tree に無いブロックを入れるときにその印を時計の時刻にする。
したがってどのハンドラも時計を変えずに tree のブロックとその印を保存し新しいブロックの印は時計以下(`Step`)、tick は `tick_grow`。初期の tree `{Genesis}` の印は `Bottom` なので、
run のどの添字でも tree のブロックの印は `Bottom` か時計以下 `stateBefore_stampInv`、`stateBefore (j + 1)` の tree のブロックは以後ずっと tree にあり印は添字 `j` の event の時刻で抑えられる
`stamp_le_of_mem` / `tree_stamped`。投票の受信の印と、投票の head の root を引いたブロック(slot が投票の slot 以下)の受信の印がどちらも `γ` より前なら解決の印 `storeTau` も `γ` より前
`storeTau_before`。honest な提案のブロックが締切より前に honest な各ノードの tree に入ることは残り)。
`BlockReceipt.lean`(`onBlockUsing` の受理の守りのうち「まだ tree に無い」を除く 5 つ — slot が受信者の slot 以下・親が tree にある・確定のブロック `st.f` の子孫・提案者が `proposer' (slot b)`・親の slot が小さい — を `Admits` にまとめ、
その下で受理の後の tree にブロックがある `onBlockUsing_mem_tree`(既にあれば `Step` の保存、無ければ受理の分岐 `acceptBody` が入れる)。名前付きの処理は名前付きの親が bodies にあることと運ばれた attestation の round の守りも持ち、
その下で処理の後の tree にあり、tree に無かったなら `commitBlock` が bodies に入れる `processBlockCore_mem_tree` / `_bodies`。`admitCarried` は tree を保存し bodies を変えないので受信の処理でも同じ `onBlockWith_mem_tree` / `_bodies`。
run では配送の直前の受信者の store がこれらを満たせば `stateBefore (j + 1)` の tree にある `deliver_block_mem`(tree に無かったなら bodies にもある `deliver_block_mem_bodies`)、配送の時刻が `γ` より前なら以後ずっと tree にあり
受信の印が `γ` より前 `deliver_block_stamped`。条件を run の事実から外すこと — 受信者の slot、親が先に届いていること、honest な提案が `st.f` の子孫であること(`PartialSynchrony` の除外が外れること `¬ excludes` が与えるのは締切の時刻の store での `compatible` で、これより弱い)— は残り)。
`Proposal.lean`(提案の務め `proposalWith` が出すブロックは `Node par st.s (newRoot' v st.s) … (proposalRows par (selectRows …)) v` で、名前付きの親 `par` は提案者の bodies から `parentBody?` で引き消去すると入力の親 `(proposalInput …).parent`(定義では fork choice の head)、
slot は提案者の slot、提案者は自分 `proposalWith_some` / `_parent` / `_slot` / `_proposer`。運ぶ行は `selectRows`(pool の行と bodies の運んだ行。どちらも `inWindow` で絞る)の部分集合(`excludeOnChain` は filter、`capPerSigner` は足すだけ)なので
round は提案者の round 以下で round の守りを通る `proposalWith_admissible`。tick が出すブロックは提案の務めが走った tick の、時計を合わせた store の `proposalWith` の出力 `tick_block_shape` で、slot は `slotOf e t`・
提案者は `proposer' (slot)`・round の守りを通り・名前付きの親は tick の前の bodies にある `tick_block_fields`。run では発行されたブロックは slot の提案の時刻に発行される `emits_block_fields`、honest な受信者への
発行より後の配送の直前の受信者の slot はブロックの slot 以上 `emits_block_slot_le`(`Admits.slot_le`)。親の slot が小さいことは次の `ParentSlot.lean`)。
`ParentSlot.lean`(tree を育てるのは `onBlockUsing` の受理だけで、守り `st.s < slot b` と `slot (parent b) < slot b` を通ったブロックの slot は store の slot 以下で親の slot より大きい `onBlockUsing_step`、他のハンドラは tree と時計を変えず tick は時計を進めてから務めを走らせる
`tick_fresh`、初期の tree `{Genesis}` の slot は 0 で時計の slot は単調 `slot_succ_ge` なので、run のどの添字でも tree のブロックの slot は store の slot 以下 `stateBefore_slotInv`、genesis でない tree のブロックの親の slot はブロックの slot より小さい `stateBefore_parentInv`(前提なし。周回 220)。時計は初期の 0 か前の自分の tick の時刻
`clock_origin` で、`EventsNodup` から同じ tick は 2 度現れないので正の時刻の tick の直前の時計はその時刻より前 `clock_lt_of_tick`、提案の時刻 `proposalTime k`(`0 < k`)の tick の直前の slot は `k` より小さい
`slot_lt_of_tick`。発行されたブロックの名前付きの親は発行の直前の提案者の bodies にあり `emits_block_parent_mem`、その消去は tree にある(`Carrier.StoreInv.tree`)ので親の slot はブロックの slot より小さい
`emits_block_parent_slot`(`Admits.parent_slot`)。親が受信者の tree / bodies にあることは次の `DeliveredBlock.lean`)。
`DeliveredBlock.lean`(run の前提 `DeliveryWellFormed` は配送の直前の受信者の store で依存が揃い(`depsPresent`: 名前付きの親が bodies にある)まだ受理していない(`!processed`: bodies に無い)ことを要求する
`deliver_deps` / `deliver_not_processed`。bodies の消去は tree にある(`Carrier.StoreInv.tree`)ので、消去したブロックの親は受信者の tree にある `deliver_parent_tree`(`Admits.parent_mem`)。
`Proposal.lean` / `ParentSlot.lean` と合わせ、honest な受信者に発行より後に配送された発行されたブロックは `Admits` のうち `extends_f`(`preceq st.f b`)を除く 4 つを setup と run の前提(`ScheduleWellFormed` / `DeliveryWellFormed` / `0 < Δ`)で満たし
`emits_admits_of_extends`(名前付きの親は `deliver_deps`、round の守りは `emits_block_fields`)、`extends_f` の下で配送の後の tree にあり `deliver_emitted_block_mem`、配送の時刻が `γ` より前なら以後ずっと tree にあり受信の印が `γ` より前 `deliver_emitted_block_stamped`、
tree に無かったなら bodies にもある `deliver_emitted_block_mem_bodies`。`Admits` の残りは `extends_f`(finality の事実)だけで、提案者の側は次の `ProposerFinality.lean`)。
`ProposerFinality.lean`(filtered tree は `finalizedDescendants f` で絞るので要素は `f` を延ばす `filtered_extends`。anchor は filtered tree の `activePrefix` か FG root(`j` か `f`)なので `f ⪯ j` の下で `f` を延ばす
`anchor_extends`、head は anchor から `ghost` で辿るので `getHeadWith_extends`、提案されたブロックの親は head なので `proposalWith_extends`。`f ⪯ j`(`FJ`)は `updateFinality` の `j` を変える分岐の守り
`preceq afterMax.f σ.j` と `f` を変える分岐の守り `preceq σ.f afterJustification.j` が保ち(`updateFinality_fj`)、他のハンドラは `f` / `j` を変えないので、run のどの添字・時刻の読みでも前提なしに成り立つ
`stateBefore_fj` / `readAt_fj`。発行されたブロックは発行の tick の直前の提案者の `f` を延ばし `emits_block_extends`、配送の直前の受信者の `f` がその祖先なら配送の後の tree にある
`deliver_emitted_block_mem_of_finalized`。`extends_f` の残りは受信者の側で、次の `ReceiverFinality.lean`)。
`ReceiverFinality.lean`(`f` は run の添字について `preceq` で単調 `stateBefore_f_mono`(各 `worldStep` が `f` を縮めない `FinalizedMonotone.worldStep_f`)、`f ⪯ j` から FG root は `f` を延ばす
`store_fgRoot_extends` ので、後の添字の `f` か FG root がブロックの祖先ならそれ以前のどの添字の `f` も祖先 `stateBefore_f_preceq_of_later` / `_of_root`。時刻 `d` の読みは添字 `idx d` の直前の状態で、
時刻 `d` 以下の event の添字は `idx d` より前 `lt_idx_of_time_le` なので、読みについても同じ `stateBefore_f_preceq_of_storeAt` / `_of_storeAt_root`。発行されたブロックが honest な受信者に
発行より後、時刻 `d` 以下に配送され、時刻 `d` の読みの受信者の `f`(または FG root)がその消去の祖先なら、配送の後の tree にあり tree のブロックは残る(`BlockStamps.stateBefore_keep`)ので
時刻 `d` の読みの tree にある `deliver_emitted_block_mem_storeAt` / `_of_root`(setup と run の前提、event の整列と重複なしの下で)。`storeAt` / `readAt` は時刻 `≤ d` の読みなので、
前提(`PartialSynchrony` など)が使う時刻 `< d` の読み `stateBeforeTime` の版も置く(`stateBeforeTime_eq_stateBefore_idxLt`、配送の時刻は `d` より前:
`stateBefore_f_preceq_of_stateBeforeTime_root` / `deliver_emitted_block_mem_stateBeforeTime_of_root`)。手書き `finalized_preceq_at_prefix_of_storeBeforeRoot_preceq`
(`Execution/ExcludesRefute.lean`。読みは `stateBeforeTime`)と、それで `ProposalFinalizedBelowAtDeliveries` を組み立てる筋。`extends_f` の残りは honest な提案が締切の時刻の受信者の FG root を延ばすこと)。
`BlockSynchrony.lean`(event の整列の鍵 `eventKey` は (時刻, phase) で tick の phase 0 < 配送の phase 1 なので、時刻 `t1 ≤ t2` の tick は時刻 `t2` の配送より添字が前 `tick_lt_deliver`。
これで honest な受信者への配送の直前の slot は `proposalTime k ≤ t2` なら `k` 以上 `slot_ge_of_deliver_le` になり、発行の時刻と等しい時刻の配送でも `Admits` の 4 つの守りが出る
`emits_admits_of_extends_le` / `deliver_emitted_block_mem_le` / `deliver_emitted_block_mem_stateBeforeTime_of_root_le`。tick が出すブロックの提案者は tick のノード自身なので発行者は 1 つ
`emits_block_proposer` / `emits_block_unique`。ブロックの `HandlesAt` の経路は自分の tick の発行か配送 `handlesAt_block_cases` で、`PartialSynchrony` の第 1 連言から、締切 `max t tGST + Δ`
(horizon 以内)の時刻の読み(`stateBeforeTime`)の受信者の `f` がブロックと互換なら締切より前に扱う `partialSynchrony_block`、ブロックの提案者(発行者)でない受信者には配送がある `partialSynchrony_block_deliver`。
FG root は `f` を延ばすので、締切の読みの FG root がブロックの消去の祖先なら `excludes` は偽 `compatible_of_stateBeforeTime_root` で、配送の event と時刻を仮定せずに締切の読みの tree にある
`partialSynchrony_emitted_block_mem`。手書き `proposedBlock_admittedBefore_vote_after_gst_named`(`ProposalAdoptionNamedClosed.lean`)の提案者でない受信者の分岐に当たる(手書きの結論は投票の時刻より前の受理の event、ここは締切の読みの tree への所属)。
残りは提案者自身の受理(手書き `acceptsAt_proposedBlock`)と、honest な提案が締切の時刻の受信者の FG root を延ばすこと)。
`ProposerReceipt.lean`(提案者は配送に頼らず、提案の tick の中で時計を合わせた store に `onBlockWith` で自分のブロックを受理する。`Admits` の 5 つの守りは提案の形と `f ⪯ j` から出て
`proposeBlockWith_mem`、投票・確定の更新・attestation の務めは tree のブロックを保存するので tick の後の tree にある `tick_block_mem`(16 経路のうち提案の務めが走る 8 経路)/ `nodeTick_block_mem`。
run では発行の tick の直後の提案者の tree にあり `emits_block_mem_self`、発行の時刻より後の時刻の読みの tree にもある `emits_block_mem_stateBeforeTime_self`(FG root の事実も配送も要らない)。
締切 `max t tGST + Δ` は `0 < Δ` で発行の時刻より後なので、`BlockSynchrony.partialSynchrony_emitted_block_mem` と合わせ、`w ≠ v` の仮定なしにすべての honest な受信者について
締切の読みの FG root がブロックの祖先なら締切の読みの tree にある `partialSynchrony_emitted_block_mem_honest`。手書き `acceptsAt_proposedBlock`(`Protocol/Handlers/HonestProposalAdmission.lean`)に当たる。
残りは honest な提案が締切の時刻の受信者の FG root を延ばすこと)。
`ProposerRoot.lean`(filtered tree は `viableTree` を `preceq fgRoot` で絞るので、その要素・anchor・head は前提なしに FG root を延ばす `filtered_extends_fgRoot` / `anchor_extends_fgRoot` /
`getHeadWith_extends_fgRoot`。提案されたブロックは提案を作った store の FG root を延ばし `proposalWith_extends_fgRoot`、tick の時計合わせは `f` / `j` / `hJ` / `hMax` を変えないので
tick の直前の store の FG root を延ばす `nodeTick_block_extends_fgRoot`、run では発行の tick の直前の提案者の FG root `emits_block_extends_fgRoot`。
したがって締切の読みの受信者の FG root が発行の tick の直前の提案者の FG root の祖先なら、締切の読みの tree にある `partialSynchrony_emitted_block_mem_of_fgRoot`(`w = v` も可。
受信者の FG root が提案者のものより新しいこともありうるので、この仮定は強すぎる場合がある)。受信者の FG root がブロックの親(提案者の head)の祖先でも同じ `partialSynchrony_emitted_block_mem_of_parent`。
手書き `finalized_preceq_proposedParent`(`ProposalBridge.lean`)の `fgRoot ⪯ anchor ⪯ head` に当たる。残りは honest な読みの FG root を、提案の親の祖先である共通の上界で抑えること。
手書きでは `hreadBound`(`ProposalAdoptionNamedClosed.lean`。すべての honest な読みの FG root ⪯ `E`)がそれで、中身の `fgRoot_preceq_previousHead_through_confirmation_after_GST`
(`Objects/FGSafetyRootNamed.lean`。honest な読みの FG root ⪯ honest な投票の head)は GST 後の `fgSafetyProgressDeadline` 以後の読みについて height の regime と
`MultiProposerRecurrence` / `TimeoutDelayBound` から出る)。
`JustifiedCarrier.lean`(共通の上界への最初の層。store の `(j, hJ)` を書くのは `updateFinality` だけで、値は受理したブロックの chain 状態 `post = deriveNamed B` の `(j, hJ)` なので、
`(j, hJ)` は常に bodies のどれかの導出のもの `JCarrier`(`Carrier.StoreInv` の `carrier` の `j` 版。run のどの読みでも前提なし `stateBefore_jcarrier` / `readAt_jcarrier` / `stateBeforeTime_jcarrier`)。
FG root は `j` か `f` `fgRoot_eq` なので bodies のどれかの導出の `j` か `f` `fgRoot_source`、導出の `j` / `f` はその消去の祖先なので FG root は tree にある bodies の消去の祖先 `fgRoot_preceq_body`
(`stateBefore` / `storeAt` / `stateBeforeTime` の版 `*_fgRoot_source` / `*_fgRoot_preceq_body`)。手書き `HealingSurface.fgRoot_justificationSource_at_read`(`Protocol/ChainState/FGRootWitness.lean`)の 2 つの分岐
(`Proofs.Bridges.storeJustificationOnChain_stateBeforeTime` / `storeFinalizationOnChain_stateBeforeTime`)に当たるが、手書きは finalized の分岐を導出の justified な祖先の `J` に
言い換える(private な `named_finalized_justificationAncestor`)ので、`f` の分岐をそのまま返すここの版はそれより弱い(言い換えは次の `FinalizedSource.lean`)。手書きはその後、justification の証明書の honest な署名者の
checkpoint の witness に結ぶ(同じファイルの `fgRoot_confirmationWitness_at_read`)。その先は残り)。
`FinalizedSource.lean`(周回 159。`f` の分岐の言い換え。`foldRows` は `(j, hJ, f, hF)` を変えず `foldRows_fields`、`processHeightEvents` が `(f, hF)` を書くのは finality の分岐の
`f := j`、`hF := hJ` だけ `processHeightEvents_f` なので、子の導出の `(f, hF)` は親の導出の `(j, hJ)` か `(f, hF)` `deriveNamed_f_node`(手書き `derive_named_F_node_cases`)。
`C` の構造帰納法で、どの `C` にも導出の `(j, hJ)` が `C` の導出の `(f, hF)` に等しい名前付きの祖先がある `finalized_justificationAncestor`(手書き `named_finalized_justificationAncestor`。高さの等式はここで足した)。
`StoreInv.closed` から祖先も bodies にある(`Attribution.ancestor_mem_bodies`)ので、store の FG root は常に bodies のどれかの導出の `j` `fgRoot_justified`、その消去は tree にあり FG root はその祖先
`fgRoot_justified_preceq`。run の読みの版 `stateBefore_fgRoot_justified` / `storeAt_fgRoot_justified` / `stateBeforeTime_fgRoot_justified` / `stateBeforeTime_fgRoot_justified_preceq` は前提なしで、
手書き `fgRoot_justificationSource_at_read`(`AdmissibleCore` を仮定する)の形。次の層の justification の証明書の honest な署名者は次の `JustificationCertificate.lean`)。
`JustificationCertificate.lean`(周回 160。`Derivation.Inv` の欄 `hJ_zero` / `jcert` から、導出の `hJ = 0` なら `j = Genesis` `justified_zero_is_genesis`、`hJ ≠ 0` なら
`matchesEntry heightPair hJ (root j)` の行の定足数 `justification_certificate`(手書き `NamedJustificationCertificates` の 2 つ。手書きは行の flag を `false` に固定するが、ここは
`tp_rows` と同じく flag を見ない)。定足数は重み `⌊(2W + 2) / 3⌋` 以上なので、faulty(`validators \ H`)の重み `w` が `3 · w < W`(`BelowOneThird`)なら `H` の署名者がいる
`exists_honest_of_quorum`(署名者がどれも `H` に無ければ、重みが 0 でない署名者は `validators \ H` にあるので `weightOf_le_diff`)。store と run の版の前提は
「どの定足数にも `H` の署名者がいる」`QuorumHonest` で、`BelowOneThird` からは `quorumHonest_of_belowOneThird`(手書きは `HonestWeightMajority`(faulty の重み < honest の重み)から
`exists_honest_member_of_quorum` で取る。`SleepyRegime` には `BelowOneThird` が無い。周回 162 で、faulty の重みが要素がみな `H` にある集合の重みより小さければ
定足数に `H` の署名者がいる `exists_honest_of_quorum_majority` を足し、`WindowMajority` / `FreshMajority` から `quorumHonest_of_windowMajority` / `_freshMajority`、
regime から `quorumHonest_of_bftRegime` / `_sleepyRegime`(窓の条件を満たす時刻があれば)/ `_outageRegime`(honest の整列を前提に。`RunDomain` から `sorted_honest` で出せる)を出した)。store の FG root は genesis か、bodies の `D` の導出の `j` で、
bodies にある `D` の祖先の行に honest な署名者の `matchesEntry heightPair hJ (root FG root)` のものがある `fgRoot_honestRow`。run では、その祖先は読みの主が処理した(`Processes`)ブロックで
(`Attribution.bodies_processed`)、`UnforgeableSignatures` の carried の半分から、署名者は処理の時刻以前にその行を出した(`Emits`)`stateBefore_fgRoot_honestEmission` /
`stateBeforeTime_fgRoot_honestEmission`(`EventsSorted`)。手書き `processedJustification_confirmationWitness` の前半。周回 161 で、処理の event の添字を追う
`bodies_processed_before`(`Attribution.bodies_processed` に添字 `j < i` を足したもの)と、添字 `idxLt time` より前の event の時刻は `time` より前 `time_lt_of_lt_idxLt` から、
処理の event の添字 `j < i` を返す `stateBefore_fgRoot_honestEmission_before` と、処理の時刻 `t < time` と発行の時刻 `t2 < time`(手書きの `ta < time`)を返す
`stateBeforeTime_fgRoot_honestEmission_lt` を足した。
後半の、その行を出した tick の store の checkpoint の witness に結ぶところは次の `AttestationSource.lean` から)。
`AttestationSource.lean`(周回 163。行の height pair を attestation の務めの FG source に結ぶ: `namedCreate` の行が `Vote h entry nu` なら入力の `fields` は
`some (h, entry, _)` `namedCreate_vote`、務めの `fields` は FG source `q = fgSourceWith …` の chain 状態の `(h, root tH, nj)` なので `(chainStateOf sigma q).h = h`・
`root (chainStateOf sigma q).tH = entry` `attestWith_vote_source`。tick の出力の行は tick の中の store `st3`(時計合わせ・提案・投票・確認の更新の後。`StoreInv` を受け継ぐ)での
`attestWith` の行で、tick の後の store は `attestWith` の後のもの `tick_attest_store` / `tick_vote_source`。run の発行の版 `emits_vote_source` は添字 `i` の `Tick w t` の中の `st3` を返し、
`stateBefore (i + 1)` の `w` の bodies は `st3` の bodies で、`q` は `st3` の tree にあり(周回 164)、bodies に `eraseBlock D = q` の `D` があって `deriveNamed D` の `h` / `tH` の根が行のもの
(`source_named`)。周回 164 で、FG source が tree にあることを示した: `fgSourceWith` は `liveConfirmed` の祖先(`deepestClear` は `chainOf liveConfirmed` から選ぶ。
`mem_chainUp_preceq` / `deepestClear_preceq`)か grade 2 のブロック(filtered tree の `activePrefix`。`grade2BlockWith_mem`)を返すので、`liveConfirmed` が tree にあり
tree が親について閉じていれば tree にある(`fgSourceWith_mem` / `fgSource_mem_tree`)。`TreeInv` に欄 `live`(`liveConfirmed ∈ tree`)を足し、
`tick_attest_store` は `st3` が `TreeInv` も受け継ぐことを返す。手書き `HealingSurface.honestEmittedHeightRow_exactFGSelectorWitness_core` の行と務めの source の結びに当たる。手書きは務めの store を `actionStoreAt`
(`stateBeforeTime (a r)` に確認の更新を掛けたもの)で読み、source が bodies にあること(`NamedActionSources.action_witness`)まで示す。
`EntryHeight.lean`(周回 165。導出の高さの入口: 子の導出の `(h, tH)` は親のものか `(親の h + 1, 子の消去)` `deriveNamed_htH_node`、どの `B` にも消去が `B` の導出の
`tH` で導出の `h` が等しい名前付きの祖先 `K` がある `entry_ancestor_same_height`、`deriveNamed_h_mono` / `node_entry_eq_of_height_eq` / `entry_eq_on_plateau`。
手書き `NamedEntryHeight` に当たる。`entry_geometry_ancestor` は移していない)と `RootEntry.lean`(周回 165。読みの FG root が genesis でなければ、honest な署名者 `w` が時刻 `< time` に出した行は
`Vote hJ (root FG root) nu`(`matchesEntry_vote`)で、`emits_vote_source` の `D'` に `entry_ancestor_same_height` を掛けると、その tick の後の `w` の bodies に
導出の `h` が `hJ` で根が FG root の根の `K` がある `stateBeforeTime_fgRoot_honestEntry`。`D'` はその tick の中の store `st3` の務めの FG source `q` の名前付きブロック(`eraseBlock D' = q`)で、`K` の導出の `tH` は `K` の消去)と `RootWitness.lean`(周回 166。読みの主の bodies に消去が FG root の名前付きブロック `J` がある `stateBeforeTime_fgRoot_named`、
`NamedRootCollisionFree` の下で読みの主が honest なら `J` は `RootEntry` の `K` と同じブロックで、`J` は `w` の bodies にあり `D'` の祖先、導出の `h` が `hJ`・`tH` が `J` の消去、`D'` の導出の `tH` は FG root そのもの `stateBeforeTime_fgRoot_entryWitness`、周回 167 でそれを `StoreInv.sigma` で tick の中の store `st3` の chain 状態に移し、務めの FG source `q` と FG root 自身の `(chainStateOf st3.core.sigma ·).(h, tH)` が `(hJ, FG root)` で FG root が `st3` の tree にある `stateBeforeTime_fgRoot_storeWitness`、周回 168 でその結論に `preceq (FG root) q = true` を足した。周回 171 で `st3` を run の関数 `dutyStoreAt`(`AttestationSource.tickDutyStore`。tick の時計合わせ・提案・投票・確認の更新の後の store で、`tick_attest_store` 以下の補題はこの等式も返す)として定義し、その務めの確認の証人 `fgConfirmationWitnessAt`(手書き `fgConfirmationWitness` に当たる、FG source の chain 状態の `tH`)が `some (FG root)` の `stateBeforeTime_fgRoot_confirmationWitness`)。周回 172 で、時刻の境 `cutTime` の前後で証人の tick を分け、最近の務めの証人と古い証人の 2 つの前提から `compatible (FG root) B` を出す `stateBeforeTime_fgRoot_compatible_of_bootstrap_and_recent`(手書き `fgRoot_compatible_of_bootstrap_and_recentActions_at_read`)を足した。周回 173 で、提案しない tick では務めの store `dutyStoreAt` の FG root が tick の前の store の FG root に等しい `dutyStoreAt_fgRoot_of_not_proposing`(時計合わせ・投票・確認の更新は FG root の読む `hMax` / `hJ` / `j` / `f` を変えない。手書き `fgRoot_confirmationWitness_at_action` の前段)を足した。周回 174 で、行を出した tick は提案しない(Δ > 0 なら action 時刻 `4Δ · (r · R) + 6Δ` は提案時刻 `4Δ · k` と重ならない `actionTime_ne_proposalTime`)ので、行を出した時刻の務めの store の FG root も tick の前の store の FG root に等しい `dutyStoreAt_fgRoot_of_emits` を足した。周回 175 で、添字 `i` の event が `Tick w t` なら `stateBefore i` の `w` の状態は時刻 `< t` の読み `stateBeforeTime t` の `w` の状態に等しい(間の event は `w` のものでない。`EventsSorted` と重複なし)`worldAt_stateBefore_tick_eq_stateBeforeTime` と、それを合わせて行を出した tick の務めの store の FG root が読みの FG root に等しい `dutyStoreAt_fgRoot_eq_stateBeforeTime`(手書き `actionStoreAt_fgRoot_eq_storeBeforeTime`)を足した。周回 176 で、それに `stateBeforeTime_fgRoot_confirmationWitness` を掛け、行を出した tick の務めの store の FG root が genesis か、時刻 `< t` に発行された行の tick の務めの確認の証人である `dutyStoreAt_fgRoot_confirmationWitness`(手書き `fgRoot_confirmationWitness_at_action`)を足した。周回 177 で、その証人の時刻を時刻の境で分け、最近の務めの証人と古い根の 2 つの前提から務めの FG root が `X` の祖先であることを出す `dutyStoreAt_fgRoot_preceq_of_recent_and_legacy`(手書き `actionSources_preceq_of_priorConfirmations_and_historyCut` の帰納の段 `hroots`)を足した。周回 178 で、発行した行の時刻は行の round の action 時刻 `emits_attest_actionTime_round` で、action 時刻は round について狭義単調(Δ > 0、`0 < R`。`actionTime_lt_actionTime_iff`)なので、時刻の境を round `cut` の action 時刻に置くと時刻の境と round の境が同じ行を選ぶ `emits_attest_time_lt_actionTime_iff` を足した。周回 179 で、それらを round の強い帰納で組み、round `cut` 以上の行の tick の務めの FG root と確認の証人が `X` の祖先であることを、古い証人の前提と「前の round の仮定の下で、FG root が `X` の祖先なら確認の証人も」という段の前提から出す `dutyStoreAt_preceq_of_roundInduction` を足した(手書き `actionSources_preceq_of_priorConfirmations_and_historyCut` の帰納の骨組みの第 2 連言)。周回 180 で、それを行ごとの性質 `Q`(手書きの第 1 連言の SG block ⪯ X に当たる)との同時帰納に広げ、round `base` 以上 `cut` 未満の行は `Q` を前提から受け、段の前提が前の round の `Q` と FG root・確認の証人の両方を仮定に受ける `dutyStoreAt_jointRoundInduction` を足した(手書きの段 `hsg` が段の前提の中に届く。周回 179 の定理はその `Q := True` の系にした)。周回 181 で、段の前提に「同じ round の行を出した honest な tick の FG root はどれも `X` の祖先」の仮定を足した(手書きの `hformation` に当たり(行を出した tick に限る)、本体が自分の FG root と同じ導出で出す)。周回 182 で、務めの確認の証人 `T` は務めの FG source `q` の chain 状態の `tH` で、`q` は務めの store の `liveConfirmed` の祖先か grade 2 の候補そのものである `fgConfirmationWitnessAt_source`(`AttestationSource.fgSourceWith_cases`)を足した(手書きの段で確認の証人を `hlive` と窓の SG block に分ける前の場合分け)。周回 183 で、その `q` は務めの store の tree にあって確認の証人 `T` は `q` の祖先(`T ⪯ q`)なので、`T` は `liveConfirmed` の祖先か grade 2 の候補 `q` の祖先である `fgConfirmationWitnessAt_preceq_source`(store の版 `AttestationSource.chainState_tH_preceq`。手書き `derive_named_T_h_preceq`)を足した。周回 184 で、務めの store の `liveConfirmed` は tick の前の store の `liveConfirmed` のままか、務めの store の FG root か、確認の更新の前の段の eligible な head である `dutyStoreAt_live_cases`(`AttestationSource.tickDutyStore_live_cases`。提案・投票は `liveConfirmed` を変えない)を足し、確認の証人を 4 つの枝(前の `liveConfirmed`・FG root・eligible な head・grade 2 の候補)に分ける `fgConfirmationWitnessAt_preceq_cases` と、FG root ⪯ X の下でその枝を閉じる `fgConfirmationWitnessAt_preceq_of_fgRoot` を足した。周回 185 で、行を出した tick の時刻(action 時刻)はその slot の supportCutoff と一致するので務めの store は必ず確認の更新を通ることを示し(`AttestationSource.slotOf_actionTime` / `supportCutoff_actionTime` / `tickDutyStore_live_cases_of_actionTime`)、前の `liveConfirmed` の枝を除いた 2 枝の版 `dutyStoreAt_live_cases_of_emits`(手書き `actionStoreAt_liveConfirmed_genuine_or_fgRoot` に当たる。確認の更新の slot は行の round の opening slot `emits_attest_slotOf_pred`)と、確認の証人の 3 枝の版 `fgConfirmationWitnessAt_preceq_cases_of_emits` / `fgConfirmationWitnessAt_preceq_of_emits_fgRoot` を足した。周回 186 で、手書き `GenuineConfirmationWith` に当たる `GenuineConfirmationAt`(確認の更新の前の段の head で、その slot で eligible)を置き、2 枝を手書きと同じ形にした `dutyStoreAt_live_genuine_or_fgRoot_of_emits`、FG root ⪯ X とこの tick の genuine な確認 ⪯ X から `liveConfirmed ⪯ X` を出す `dutyStoreAt_live_preceq_of_prior`(手書きの `hlive`)、確認の証人を `X` の祖先か grade 2 の候補の祖先に絞る `fgConfirmationWitnessAt_preceq_of_emits_prior` を足した。周回 187 で、務めの grade 2 の候補 `grade2CandidateAt` を置き、genuine な確認 ⪯ X と grade 2 の候補 ⪯ X から確認の証人 ⪯ X を出す `fgConfirmationWitnessAt_preceq_of_prior_grade2` と、round の同時帰納の `hstep` の証人の連言をその 2 つの供給に置き換えた `dutyStoreAt_jointRoundInduction_of_prior` を足した。周回 188 で、新しいモジュール `Grade2Capture.lean` に cache の 1 段(切り詰め `clipGrade` は元の root の祖先、phase tick の後の cache の G2 の結果は tick の前の結果かこの tick で `freezeRoot` が凍結した結果の祖先 `onPhaseTick_g2_cases`、grade 2 の候補はその祖先 `grade2BlockWith_onPhaseTick_cases`)を置き、`RootWitness.lean` に、行を出した tick の時刻は G2 の domain 時刻でない `actionTime_ne_domainTime_G2` と、務めの grade 2 の候補は tick の前の cache の G2 の結果の祖先 `grade2CandidateAt_of_emits`(手書き `q2_capture_at_action_read` の前半)を足した。周回 189 で、`Grade2Capture.lean` に run の帰納(`stateBefore i` の cache の G2 の結果 `some (some b)` は、添字 `j < i` の自分の tick(G2 の domain 時刻)で `stateBefore j` の store の `freezeRoot` が凍結した root の祖先 `stateBefore_g2_origin`。手書き `completed_phase_origin` を祖先の関係に弱めた版)を置き、`RootWitness.lean` に、行を出した tick の務めの grade 2 の候補はその凍結した root の祖先 `grade2CandidateAt_origin_of_emits`(手書き `q2_capture_at_action_read` の全体)を足した。周回 190 で、`Grade2Capture.lean` に凍結した root は grade view の tree にあり `gradeBool` が真 `freezeRoot_mem` を置き、`RootWitness.lean` に、行を出した tick の務めの grade 2 の候補は grade の通った凍結した root の祖先 `grade2CandidateAt_frozen_of_emits` を足した。周回 191 で、`RootWitness.lean` に、その root を G2 の domain 時刻の読みに移した `grade2CandidateAt_graded_of_emits`(手書きの `hrawGrade`)と、grade の通った block の担い手を性質 `P` に抽象した `nodeQ2_preceq_honestWindowCarrier` の版 `grade2CandidateAt_preceq_carrier_of_emits` を足した。周回 193 で、その読みの時刻 `domainTime k G2` が 0 以上 horizon 以下であることを示す `grade2CandidateAt_domainTime_bounds_of_emits`(手書きの `hdomainHor`)と、担い手の前提に手書き `hgrade` の horizon の守りと tree への所属を足した `grade2CandidateAt_preceq_carrier_horizon_of_emits` を足した。周回 194 で、務めの SG block `sgBlockAt`(手書き `actionSGBlockAt`)と、発行した行の `confirmed` がその根であること `emits_confirmed_sgBlockAt`、窓の round の honest な行の SG block `HonestWindowCarrierAt` と手書きと同じ形の `RelativeGradeCarrierAt` を置き、担い手をそれに置いた `grade2CandidateAt_preceq_honestWindowCarrier_of_emits`(手書き `nodeQ2_preceq_honestWindowCarrier` と同じ前提の形)を足した。周回 195 で、担い手の行の `confirmed` が担い手の根であること `honestWindowCarrierAt_confirmed`(重複なしの下)と、grade 2 の候補が窓の round の honest な行の `confirmed` の祖先であること `grade2CandidateAt_preceq_windowConfirmed_of_emits` を足した。周回 196 で、grade の通った block には honest な支持者がいること(手書き `q20_graded_has_honest_supporter`)を `GradeSupporter.lean` に移した: 早い token があれば支持か反対か `supports_or_opposes`、`readyView` の cutoff の単調性 `readyView_mono`、`validators \ H` の重みが早い cutoff で解釈済みの入力を持つ `H` の部分集合 `A` の重みより小さく grade が通れば、honest な `v` の解釈済みの入力 `y` の `confirmed` の head が block を覆う `graded_has_honest_supporter_head` / `phase_graded_has_honest_supporter`。
残るのは `SleepyRegime` の下で `HonestSupport` の `vote` を示すこと(honest な committee の要素は `voteTime` に投票を発行し(投票者・slot まで `Voting.lean`)、その投票の head は
`stateBefore i` の発行者の store に時計を合わせたものの fork choice の head で(`Voting.emits_gfVote_head`)、その head が honest な提案 `B` を延ばして slot が `s` 以下であること(投票者の fork choice `getHeadInTreeWith` / `voterView` が `B` を採る。
手書きでは `B.slot = Σ.s` なので過半なしに適格)、`ExecutionValid` / `PartialSynchrony` で投票とブロック `B` が honest な全ノードに `supportCutoff` までに届くこと
(解決の印 `storeTau` は投票の受信の印と head のブロックの受信の印の大きい方))、2 つの honest なノードの読みの間の正準性(手書きの安全の核 `eligible_compatible`: 一方の
支持の投票が他方の遅い投票に入る `CrossView` の下で、同じ slot に両ノードで門を通る 2 ブロックは互換 — 2 つの支持者の集合は `noSecondVoteIn` で互いに素でどちらも
一方の参加者に収まるので `2(a + b) ≤ count_v + count_w < 2a + 2b`)で確認の記録の一致・確認の記録と finalized の交差の互換・GST-zero の枝(`t0 = 0`)の finalized の
一致(stable の記録と grade の候補 `frameSgCandidate` の分岐についても同じ)を結ぶこと、honest な提案が適格な子の一意な最大になって `ghost_reaches` で選ばれること
(`IncludedFrom` ×2)を Goldfish の投票と確認の本体から示すこと。

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

## 10. 有界検査(実行テストの篩。IDEAL.md C73 / C74)

残りの claim と証明の途中の中間命題が生成 Model で本当に成り立つかを、証明に取り組む前に実行で安く確かめる篩が `tests/properties/`
(Lake の lean_lib `Properties`、実行ファイル `lake exe naru_properties`、ドライバ `lake exe naru_test properties`。走らせ方と設定は
[docs/testing.md](../docs/testing.md)「有界検査」)にある。生成 Model と `NaruStd` だけを import し、`Proofs` からは import しない(逆も)。
**実行テストの結果は証明の代用にせず、`naru proofs` の証明状況の表示は変えない。** 違反が出たら、期待値の書き換えや検査器の弱化で通さず、
用語「反例の分類」(検査器の誤り / 前提の判定の誤り / 移植の不一致)で原因を分ける。

どの命題が実行テストでどこまで確かめられているか(最終実行は周回 210、固定設定 10 run。表の件数は各検査器を足した周回のもの。詳しい件数は docs/testing.md):

| 命題 | 検査器 | 判定 / 前提不成立 / 判定外 / 違反 | 備考 |
|---|---|---|---|
| 中間命題 `hreadBound`(honest な読みの FG root ⪯ honest な投票の head・提案の親。手書き `fgRoot_preceq_previousHead_through_confirmation_after_GST`、`fgSafetyProgressDeadline` 以後。`proofs/Proofs/Consensus/ProposerRoot.lean` が残りとして挙げる上界) | `hreadBound`(強い形) | 1015 / 168 / 1055 / 0 | 手書きの期限 `a(D)`(3858〜9564)は固定設定の horizon を越えるので、用語「強い形」(GST 以後のすべての honest な読みで FG root ⪯ honest な投票の head・提案の親)で判定し、期限付きの形は判定外として併せて数える。強い形の違反 0(「期限の前の正常な挙動」に分けたもの 0)なので、round の帰納を強い形で回す筋は固定設定の run では反例が無い |
| `IncludedFrom(s, rho, Output.Confirmed, 0, confirmationDelay)`(claim `available` の結論の項目。`Liveness.lean` の `liveFrom_of_includedFrom` の前提) | `includedFrom(confirmed)` | 71 / 45 / 16 / 0 | 前提は `SleepyRegime` の本来の形(`WindowMajority` の窓の欄と `RecoveredBy` の genesis / 回復の枝)の有界版で判定。sleepy の run は判定に入り、`tGST > 0` の 3 run は回復の枝の `recoveryEnd(s, tGST, 0)`(3513〜7002)が horizon を越えてどの証人でも成り立たないので前提不成立 |
| `IncludedFrom(s, rho, Output.Stable, 0, stableInclusionDelay)`(同) | `includedFrom(stable)` | 25 / 45 / 62 / 0 | 同上。stable の期限が長いので判定外が多い |
| claim `available`(前提 `SetupWellFormed` ∧ `RunDomain` ∧ `SleepyRegime(t0)`、結論 `AvailableAt(t0)` = confirmed / stable の `SafeFrom` と `IncludedFrom`。手書き `available_confirmedSafe` / `available_confirmedIncluded` / `available_stableSafe` / `available_stableIncluded_any`) | `available` | 136 / 114 / 78 / 0 | 前提は `includedFrom` と同じ `SleepyRegime` の本来の形の有界版。`SafeFrom`(`AgreeFrom` ∧ `MonotoneFrom`)は述語自身が `[t0, horizon]` と honest に切っているので有界版は本物と同じ範囲。前提不成立は `tGST > 0` の 3 run |
| claim `confirmedLive` / `stableLive`(前提 `SetupWellFormed` ∧ `RunDomain` ∧ `LiveSleepyRegime(t0, gap)` = `SleepyRegime(t0)` ∧ `SingleProposerRecurrence(t0, gap)`、結論 `LiveFrom(confirmed, t0, growthDelay(gap))` / `LiveFrom(stable, t0, stableGrowthDelay(gap))`。手書き `Generic.liveFrom_of_includedFrom`、naru 側 `confirmedLive_of_available` / `stableLive_of_available`) | `confirmedLive` / `stableLive` | 866 / 255 / 1542 / 0 と 220 / 255 / 2188 / 0 | `t0` は `sleepyCandidates`、`gap` は `[1, (horizon - t0) / period]` を列挙し前提が成り立つ組をすべて判定。`SingleProposerRecurrence` は厳密。`LiveFrom` の存在量化の `b` は `maxSlot(horizon)` までの honest な提案で探す(違反を報告する側にしか働かない)。前提不成立は `tGST > 0` の 3 run |
| claim `stableIncludedFast`(前提 `SetupWellFormed` ∧ `RunDomain` ∧ `FreshSleepyRegime(t0)` = `SleepyRegime(t0)` ∧ `FreshMajority`、結論 `IncludedFrom(stable, t0, fastStableInclusionDelay)`。手書き `stableIncludedFast_concrete`、`Bridge/StableIncludedFresh.lean`) | `stableIncludedFast` | 34 / 58 / 40 / 0 | `FreshMajority` は窓の集合が `AwakeInExactly` で一意に決まるので厳密。前提不成立は `tGST > 0` の 3 run と、`FreshMajority` が破れる sleepy の run |
| claim `stableAsynchronyResilient`(前提 `SetupWellFormed` ∧ `RunDomain` ∧ `OutageRegime(tRead, b0, b1)`、結論 `PersistsFrom(stable, tRead, b0)`。手書き `outage_stablePersists`) | `stableAsynchronyResilient` | 3012 / 2628 / 2100 / 0 | `HealthyPrefixDelivery(b0)` は破れた要求の最小の期限で厳密に判定、`FreshMajority` / `SlashableBound` も厳密。`tRead` は `[0, horizon]`、`b0` は窓の位置の範囲の public time、`b1` は最小の `max(b0, tGST)`。`PersistsFrom` は `b = r` に帰着して厳密。前提不成立は GST 前の遅延で `HealthyPrefixDelivery` が破れる 2 run と sleepy の run |

| claim `finalized`(前提 `SetupWellFormed` ∧ `RunDomain` ∧ `FinalityRegime(t0, gap)` = `BFTRegime(t0)` ∧ `StrongMultiProposerRecurrence(tGST, gap)` ∧ `gap + 2 <= maxGap` ∧ `t0 + finalityStartup(gap) <= horizon`、結論 `FinalizedAt(t0 + finalityStartup(gap), gap)` = finalized の `IncludedFrom` と `LiveFrom`。手書き `finalized_included` / `finalized_growth`、naru 側 `finalizedLive_of_included`) | `finalized`(強い形) | 16 / 1995 / 122 / 0 | `StrongMultiProposerRecurrence` は厳密。`finalityStartup` は前提を満たしうる最小の設定(gap 3、`k = 5`、`r = 1`)でも 2279、固定設定で 6159〜7863 で horizon に届かないので、周回 210 から用語「強い形」(GST 以後の honest な提案は `4 · period` 以内に honest 全員の finalized の読みに入り、同じ期限で `LiveFrom`)で判定し、期限付きの形は判定外として併せて数える。判定は `h4-k5-honest-proposers` の包含 3・伸長 13。強い形の違反 0(「期限の前の正常な挙動」に分けたもの 0) |

`HealthyPrefixDelivery` は周回 207 から、`FreshMajority` は周回 205 から、`WindowMajority` / `SlashableBound` / `RecoveredBy` は周回 201 から判定する。
他の中間命題(round の帰納の段の主張)、
C74 の `検査器 = true ↔ 述語` の theorem は後続の周回。

## 11. 骨格と穴

大きな義務は、いきなり完成した証明を書くのではなく、**骨格** — 義務の theorem を名前付きの中間補題に分解し、Lean の型検査を通した証明の計画 — を先に置き、
まだ証明の無い中間補題(**穴**)を 1 つずつ閉じて上から下へ進めます。手書き証明を持たないプロトコルでも同じ手順です。

1. 義務の theorem を置き、束縛行を付ける(義務の型・前提・結論は変えない)。本体は中間補題を組み立てるだけにする。
2. 中間補題を、手書き証明があればその構成(入口の定理と主要補題の分割)に沿って切る。無ければ義務の結論の項目と前提の枝で切り、残る依存を docstring に書く。
3. 証明できない中間補題は穴として残す: 本体は `sorry` の 1 行だけ、docstring に対応する手書きの宣言名とファイル(無ければ「なし」と、代わりの根拠)と
   「閉じるのに要る」依存の要点を書き、下の一覧に 1 行ずつ載せる。`sorry` の語を穴の本体以外(コメント・docstring を含む)に書かない。
4. 穴を閉じる(証明を完成させて `sorry` を消す)か、細分する(残りを新しい穴に切り出し、理由を周回記録に書く)。一覧の行も合わせて直す。
5. `naru proofs` では穴に依存する義務は `sorry` と表示され、証明済みにならない。穴が 0 になった義務は `proved` になる。

骨格は手で書きます(コンパイラや `naru proofs` に雛形の生成はありません)。`naru_test proofs` は、`grep -rnw sorry` の一致箇所とこの一覧の行が一対一に対応すること、
一覧の手書きの宣言名がそのファイルに実在すること、穴の docstring の形、義務の theorem の `#print axioms` が `propext` / `Classical.choice` / `Quot.sound` / `sorryAx` の
部分集合であること、HEAD の一覧との差を検査・表示します。consensus の骨格を置く義務は 7 件(`available` / `confirmedLive` / `stableLive` / `stableIncludedFast` /
`finalized` / `stableAsynchronyResilient` と bundle `Consensus`)で、穴はこの 7 件の経路にだけ置き、証明済みの 7 件が依存する補題には置きません。

骨格の運び(consensus): `available`(周回 211)は入口 `Proofs/Consensus/AvailableHoles.lean` の `availableAt` が `t0 = 0`(`RecoveredBy` の genesis)か否かで
finalized の一致の出どころを分け(`t0 ≠ 0` は証明済みの `agreeFrom_finalized_of_recovered`、`t0 = 0` は確認の出力の一致 `confirmedAgree_genesis` から
証明済みの `agreeFrom_finalized_of_confirmed` で下ろす。周回 214)、`Available.lean` の `availableAt_of_fields` の残りの事実を取ります。GST-zero の枝の
確認の記録の一致・交差の互換・確認の出力の一致は、どれも `commonUpper_genesis`(2 つの読みの finalized と確認の記録の共通の上界 `CommonUpperFrom`)から
証明済みの `recordAgreeFrom_of_commonUpper` / `crossAgreeFrom_of_commonUpper` / `agreeFrom_confirmed_of_commonUpper` で出します。`commonUpper_genesis` は
最初の確認の時刻 `confirmationTime e 0` が `horizon` 以下なら `commonUpper_genesis_long`、より前に run が終わるなら確認の記録は genesis(証明済みの
`ShortHorizon.storeAt_rec_short`)で finalized も genesis(証明済みの `ShortHorizon.storeAt_f_short`。tree の親の slot の不変条件
`ParentSlot.stateBefore_parentInv` を使う)なので上界は genesis です(枝の分け方は周回 218、finalized の側は周回 220)。`commonUpper_genesis_long` は、
確認の記録と finalized がそれぞれある slot 以後の投票の務めの head `voteDutyHeadAt`(手書き `voterHeadAt`)の祖先であることを言う
`recordAt_preceq_laterVoteHead` / `finalizedAt_preceq_laterVoteHead` から、4 つの slot の最大で上界を揃えて証明します(周回 222)。
`finalizedAt_preceq_laterVoteHead`(穴ではない。周回 248)は手書きと同じく、時刻 `t` の読みを時刻 `< t + 1` の読みに移して finalized ⪯ FG root
(`ReceiverFinality.store_fgRoot_extends`)とし、FG root を `RootWitness.stateBeforeTime_fgRoot_confirmationWitness` で genesis(`first = 0`)か honest な行の
務めの確認の証人に分け、後者は行の時刻が行の round の action 時刻 = opening slot の確認の時刻なので `first` を opening slot にとり、
`fgWitness_preceq_laterVoteHead` に渡します。`fgWitness_preceq_laterVoteHead`(穴ではない。周回 250)は手書き
`actionSources_preceq_voteDutyHead_of_gstZero` と同じく、round の同時帰納 `RootWitness.dutyStoreAt_jointRoundInduction_of_prior`(手書き
`WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut`)を `base = cut = 0`・行の時刻 `< voteTime (d + 1)`・行ごとの性質 SG block ⪯ head で掛け、
段の genuine な確認(行を出した tick は確認評価の tick で slot は `d` 未満。`emits_confTick` / `emits_slot_lt_of_lt_nextVote`)を
`genuineConf_preceq_laterVoteHead`(手書き `protectedVoteSlots_of_gstZero_v2` の `heads`。周回 270 から穴ではない。その段の保存の穴
`protectedVoteSlot_preserve` は周回 297 に閉じた: 読みの voter view での `B` の支持者の過半を `voteDutyStore_supporterMajority_of_heads` で出し、
`B` の名前付きブロックの導出の高さが band に届くかで `voteDutyHead_passes_supporter_majority_of_bandNamed` / `_of_belowBand` に分ける。
新しい確認の段 `protectedVoteSlot_succ_of_genuineConf` は周回 298 に、`C` の honest な支持者 `y` の slot `d` の head を上界に同じ 2 枝で閉じ、
読みの voter view での `C` の支持者の過半を `genuineConf_supporterMajority` に切り出した。これは周回 299 に手書き `AdoptionTransport` の
数え上げ(`Majority.AdoptionTransport.supporterMajority_of_eligible`。手書き `confirmation_adoption`)で閉じ、確認の store から読みの voter view への
移送の境界を穴 `genuineConf_adoptionTransport`(手書き `adoptionTransport_B_after_gst`)に切り出した。その穴の `forward` / `backward` に共通の中継の層は周回 300 に `Settled.lean` に証明した: honest なノードが窓の中で扱った投票は pool に入るか投票者の equivocation が pool に残り(`handlesAt_gfVote_settled`。手書き `weakct_actual_gfVote_settled_before_deadline`)、受理された投票は中継で honest な各ノードにそうなり(`acceptsAt_gfVote_settled`)、後の読みの印の付いた pool に移る(`settled_stamped`)。pool の投票はある添字で受理されている(`pool_accepted`)。周回 301 に、受理の時刻は投票の slot の提案の時刻以後(`PoolSlot.acceptsAt_gfVote_slot_le`。pool に入る守り `st.s < vote.slot` の run の不変条件)を足して、読み手の pool の投票は確認の遅い投票に落ち着く(`AvailableHoles.pool_lateSettled`)ことを証明し、`genuineConf_adoptionTransport` を組んだ。残りは `forward`(穴 `genuineConf_adoptionForward`)と、`backward` の carried の部分(読みの tree の slot `d + 1` のブロックが運ぶ投票。手書き `targetCarrierVote_settledInPool`)だった。周回 302 に後者を閉じた: tree のブロックは genesis か、ある添字で tree に新しく入り(`AvailableHoles.tree_entered`)、新しく入ったブロックの運ぶ投票は、自分の提案なら既に pool にあり、配送なら受理の守り `slot b ≤ st.s` と配送の時刻の上限で窓の中なので pool に入るか投票者の equivocation が pool に残る(`treeEntry_gfVote_settled`)。あとは pooled の部分と同じく `pool_lateSettled` か `nonUnique_lateEquivocates` で遅い投票に移す(`genuineConf_backwardCarried`)。周回 303 に `forward` を組んだ: 配送で pool に新しく入った投票の印はその時の時計で、honest なノードの時計は配送の時刻以下の最大の公開時刻以上なので、印が支持の締切より前の投票は支持の締切より前に受理されている(新しいモジュール `StampExact.lean` の `pool_acceptedBeforeCutoff`)。中継で読み手に `viewFreeze d` より前に届き、読みの印の付いた pool に入るか投票者の異なる 2 つの投票が残る(`AvailableHoles.supportVote_readSettled`)。head の解決先が読みの tree で見えることは穴 `genuineConf_supportHeadVisible`(手書き `supportingTarget_visibleAtVoteDuty_after_gst`)に切り出し、周回 304 に閉じた: 解決の印が支持の締切より前なので head のブロックの受信の印も前で、tree のブロックの印は tick ならその時刻以上、配送なら配送の前の時計なので、そのブロックは支持の締切より前の event で評価者の tree に入っている(`AvailableHoles.tree_enteredBeforeCutoff`)。読み手の finalized ⪯ FG root ⪯ `C` ⪯ head で互換なので、中継 `bodiesBlock_stamped` で `viewFreeze d` より前の印で読みの tree に入る)から、SG block と grade 2 の候補を
`fgStep_preceq_laterVoteHead`(穴ではない。周回 251)から供給します。これは務めの store の round で分け、round 0 は `fgStep_round_zero`(round 0 の frame に
G1 / G2 の root は無いので grade 2 の候補は空、anchor は FG root で、SG block は `liveConfirmed` の祖先か FG root。手書き `WeakGenesis.actionSGBlock_eq_genesis_zero`)
で閉じ、正の round は `fgStep_preceq_laterVoteHead_positive`(穴ではない。周回 252)に渡します。これは SG block を `sgBlockAt_preceq_of_candidate_anchor`
(`currentSGVote` の 4 つの枝: `deepestClear` の結果は `liveConfirmed` の祖先、grade 2 の候補、rawG2 なら FG root、それ以外は anchor)で grade 2 の候補と
務めの round の frame の anchor に下ろします。anchor は `frameAnchor_preceq_of_g1Prefix`(周回 253)で FG root と G1 の root の active prefix に下ろし、
G1 の root の active prefix は `fgStep_g1Prefix_positive`(周回 255。手書き `actionGradeFormationAt_of_awakeWindowMajority` の anchor の枝)で、G1 の domain 時刻の tick で
凍結した root(`confCache_phase_origin`)の grade の担い手を通して前の round の SG block の前提で閉じます。grade 2 の候補は
`fgStep_candidate_positive`(周回 254)で窓の round の honest な行の SG block の祖先に下ろし(`RootWitness.grade2CandidateAt_preceq_honestWindowCarrier_of_emits`。
窓の round は務めの round より小さい `lt_of_mem_latestWindow`)、前の round の SG block の前提で閉じます。grade の担い手 `fgStep_gradeCarrier_positive`(周回 257 に閉じた)と確認の側の担い手 `confG1Carrier_positive`(周回 257 に閉じた)は、共通の上界 `D` が窓の round の honest な行の SG block と phase の読みのすべての honest なノードの finalized の上にあれば担い手がある、という共通の構成 `relativeGradeCarrierAt_of_commonUpper`(手書き `WeakJoint.relativeGradeCarrierAt_of_awakeWindowHistory_gstZero`)から証明します。finalized の側は `stateBeforeTime_f_preceq_of_witnesses` で読みより前の honest な行の確認の証人に下ろします。共通の構成は周回 258 に手書き `relativeGradeCarrierAt_of_awakeWindowMajority`(`RelativeOneChain.lean`)の運びで証明しました: 早い cutoff に解釈済みの入力を持つ honest な多数派(`honestInterpretedMajority_of_commonUpper`。周回 260 に閉じた: 多数派は `SleepyRegime` の `WindowMajority` を round の action 時刻で使った窓の awake な honest の集合(手書き `windowMajority_of_generic`)で、窓の時刻の action round は round の窓にある(`actionRound_mem_latestWindow`)。各元が解釈済みの入力を持つことは `awakeWindowVote_interpreted_of_commonUpper`(手書き `relativeGradeCarrierAt_of_awakeWindowHistory_gstZero` が供給する `htransport`。周回 261 に閉じた: 元は round の action 時刻に行を出し(`awake_emits_actionRow`。手書き `honest_emits_exact_actionAttestationAt_of_awake`)、行の SG block と読み手の finalized はどちらも共通の上界の祖先なので互換で、その行の SG 票と SG block が早い cutoff より前の印で読み手の store に入ることは `honestActionRow_delivered`(手書き `honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible` の配送の段)。その行の側は周回 262 に証明しました: `PartialSynchrony` の第 1 連言で読み手は `t + Δ` より前に行を扱い、扱いの後の行の attestation(`honestActionRow_handled_row`。手書き `honest_row_after_call`)の印は扱いの時刻以下で読みまで残ります(新しい SG 票の印の不変条件 `SgStamps.stateBefore_sgStampInv` と `SgStamps.sg_stamp_le_of_mem`)。扱いの後の行の attestation は周回 263 に `SgAdmit.lean`(sorry なし)で閉じました: `HandlesAt` の 3 つの経路(自分の tick の `attestWith`・配送の `admitRow`・受理したブロックが運ぶ行の `admitRows`。自分の提案は提案の時刻にだけ起き、扱いの時刻は提案の時刻ではない)で、`onSgVote` の受理の窓は扱いの時点の slot `k · R + 1` の round で通り(`mem_rows_onSgVote` / `admitRows_mem`)、大きさ 2 の守りは honest な送り手の行の `confirmed` がどの store でも 1 通りであること(`honest_rows_confirmed_eq`: `SgFrom.sg_genuine`、行の時刻は round の action 時刻、同じ時刻の tick の行は 1 つ)で外れます。SG block の側 `honestActionRow_sgBlock_delivered`(手書き `compatible_carrier_body_at_read_after_gst`)は周回 264 に、SG block が読み手の tree に初期から、または `t + Δ` より前の event の後に入れば、印が `t + Δ` より前(`BlockStamps.tree_stamped`)で root の解決が SG block 自身(`findRoot?_of_mem`)であることと、読み手が行の送り手自身なら tick の後の tree にあること(`honestActionRow_sgBlock_entered`)で証明しました。送り手でない読み手の tree に入ること(`honestActionRow_sgBlock_held`)は周回 265 に証明しました: SG block は tick の後の送り手の bodies の名前付きブロックの消去なので genesis か送り手がある添字で受理したブロック(`bodies_accepted_before`)で、後者は `PartialSynchrony` の中継の連言(締切は受理の時刻 + Δ ≤ `t + Δ`。除外は読みの finalized との互換を finalized の単調性で締切の読みへ移して外す)で、読み手が受理の直後に既に持つか締切より前に扱います。扱ったブロックが扱いの後の読み手の tree にあること(`acceptedBlock_handled_held`。手書き `NamedRelayGuards.handled_block_held_of_finalized_prefix`)は周回 266 に証明しました: 読み手の tick の出力なら発行の tick の後の tree にあり、配送なら直前の tree に既にあるか、受理の守りを外して入ります。提案者・親の slot・運ばれた attestation の守りと slot の提案の時刻は送り手の受理から(`acceptedBlock_static`。配送の受理は `processBlockCore_guards`)、`extends_f` は読みの finalized との互換を扱いの直前へ移し、`X ⪯ f` の向きは finalized の祖先が tree にあるので除かれます。SG block の root の解決は SG block 自身(`sgBlockAt_findRoot_eq`)で、SG 票は生の入力で `bodyReady`))から grade の honest な支持者の入力を取り(`GradeSupporter.phase_graded_has_honest_supporter`)、それを送り手が実際に出した行の消去に戻し(新しい `SgFrom.sg_genuine`: SG 票の行の attestation は処理した行か処理したブロックが運ぶ行の消去で、`UnforgeableSignatures` から honest な送り手の行は真正。手書き `honest_rawInput_is_own_round_vote`)、その `confirmed`(行の SG block の root)の tree での解決を行の SG block と同一視します(`sgBlockAt_findRoot_eq`。手書きの `hhead` の段)。これは周回 259 に閉じました: SG block は務めの store の tree の要素(`sgBlockAt_mem_dutyTree`。`currentSGVote` の 4 つの枝)で、務めの store の bodies は行を出した tick の後の bodies(`stateBefore_succ_bodies_of_emits`)なので、解決した head と SG block はどちらも run の中のブロックの消去で、run に root の衝突が無い(`FinalizedAccountable.rootInjective_of_collisionFree`)ので等しくなります。
`recordAt_preceq_laterVoteHead` は確認の記録の由来(`ConfirmedOrigin.lean` の `storeAt_confirmed_origin`: genesis か、確認評価の tick の確認の walk か
grade の stable root。手書き `ConfirmationOrigin.stateBefore_latest_confirmed_origin`)で分け、`confWalk_preceq_laterVoteHead`(walk ⪯ 後の投票の head。穴ではない。
手書きと同じく walk が anchor のままか filtered tree の適格な要素か(`Goldfish.head_cases`)で分け、anchor は g1 の frame の raw の active prefix か FG root なので
`confG1Raw_preceq_laterVoteHead`(round 0 は凍結が空なので g1 の frame に root が無く矛盾(`confCache_g1_round_zero`: `FrameCapture.freezeRoot_zero` / `FrameCapture.stateBefore_phase_zero`。手書き `confirmationRead_g1_round_zero_no_root`)、正の round は `confG1Raw_preceq_laterVoteHead_positive`。周回 246。これは raw を G1 の domain 時刻の tick で凍結した root に下ろし(`confCache_phase_origin`)、その grade の担い手(`confG1Carrier_positive`。手書き `relativeGradeCarrierAt_of_awakeWindowMajority`)の窓の round の honest な行の SG block を `sgBlock_preceq_laterVoteHead`(`fgWitness_preceq_laterVoteHead` と同じ round の同時帰納 `laterVoteHead_rowSources` の SG block の連言。手書き `actionSources_preceq_voteDutyHead_of_gstZero` の第 1 の結論)で閉じる。周回 256)と `confFgRoot_preceq_laterVoteHead`(穴ではない。FG root を tick の時刻の読みの FG root に移し(`confPreUpdate_fgRoot`: 確認の締切は提案時刻ではない)、証明済みの `RootWitness.stateBeforeTime_fgRoot_confirmationWitness`(手書き `WeakFG.fgRoot_confirmationWitness_at_read`)で genesis か honest な行の務めの確認の証人に分け、後者は `fgWitness_preceq_laterVoteHead`(手書き `actionSources_preceq_voteDutyHead_of_gstZero` の FG の証人の結論)から。周回 247)から `confAnchor_preceq_laterVoteHead` で、動いた walk は `confEligibleWalk_preceq_laterVoteHead`(walk は genuine な確認なので穴 `genuineConf_preceq_laterVoteHead` から。周回 250)から。周回 245)と
`confStableRoot_preceq_confWalk`(stable root ⪯ walk。穴ではない)から証明します(周回 224)。`confStableRoot_preceq_confWalk` は stable root が FG root に戻る枝を
FG root ⪯ SG root ⪯ head(`ProposerRoot.getSgRootWith_extends_fgRoot` / `Goldfish.sgRoot_preceq_head`)で閉じ、g2 の frame の root がある枝を
`confFrameRoot_preceq_confWalk`(穴ではない)に渡します(周回 226)。`confFrameRoot_preceq_confWalk` は確認の更新の前の段の store の round で分け、round 0 は
g2 の frame に root が無いので矛盾(`confCache_g2_round_zero`: G2 の round 0 の domain 時刻は `-Δ` で、凍結の出どころ `Grade2Capture.stateBefore_g2_origin` の
tick の時刻は 0 以上。手書き `confirmationRead_g2_round_zero_no_root`)、正の round は `confFrameRoot_preceq_confWalk_positive`(穴ではない)に渡します(周回 228)。`confFrameRoot_preceq_confWalk_positive` は
手書きの `hfinish` と同じく、g1 の frame の anchor が fork choice の SG root(`getSgRootWith` は `frameGradeRead` の `anchor`)で walk はそこから歩く
(`Goldfish.sgRoot_preceq_head`)ので、`confFrameRoot_preceq_anchor_positive`(g2 の frame の root の active prefix ⪯ g1 の anchor。穴ではない)から証明します(周回 230)。
`confFrameRoot_preceq_anchor_positive` は手書きと同じく、g2 の root の active prefix `g`(filtered tree にあり g2 の root の祖先)から穴 `confFrameG2_g1Root_positive`
(手書き `q10_g1_slot_of_g2_slot`。穴ではない)で g1 の root `root1`(`g ⪯ root1`)を取り、証明済みの `activePrefix_exists` / `activePrefix_dominates`(手書き `q10_activePrefix_dominates`)で
anchor = `activePrefix … root1` が `g` を延ばすことを示します。naru の `activePrefix` は `Set` の表現のリストの `findUnique?` なので、存在には tree の要素の重複なし
(`preUpdateTree_nodup`。手書きの tree は `Finset` なので要らない)が要ります(周回 232)。これは `TreeInv` の欄 `nodup`(受理はまだ tree に無いブロックだけを
`insertSorted` で入れるので重複が生じない)から出します(周回 233 に閉じた)。`confFrameG2_g1Root_positive` は手書きと同じく、g2 の root の出どころ
(`confCache_g2_origin`: G2 の domain 時刻の tick で凍結した root。`Grade2Capture.stateBefore_g2_origin`)、`confFrameG1_slot_positive`(読みの G1 の欄は
G1 の domain 時刻の tick の凍結の切り詰め。手書き `frame_phase_completed_in_round`。周回 243 に、欄が閉じていることを穴 `confFrameG1_closed_positive` に切り出し(周回 244 に閉じた: G1 の domain 時刻の tick が `ScheduleWellFormed` の tick の網羅性で確認評価の tick より前にあり、その間の tick の時計の round は同じなので欄が残る。`FrameCapture.stateBefore_closed` / `FrameCapture.onPhaseTick_closed`)、
値を証明済みの `FrameCapture.onPhaseTick_phase_some` / `FrameCapture.stateBefore_phase_origin`(完了した phase の結果は domain の tick の凍結を
いまの finalized で切り詰めたもの。手書き `completed_phase_before_read`)と切り詰めの合成 `FrameCapture.clipGrade_clipGrade` で出した)、`g1Freeze_of_g2Freeze_positive`(G2 の凍結の root 以上の G1 の凍結。
手書き `q10_g1_of_g2_freeze`。穴ではない)と、切り詰めが finalized と互換な祖先を保つこと(`preceq_clipGrade_of_compatible`)から証明します(周回 234)。
`g1Freeze_of_g2Freeze_positive` は手書きと同じく、G2 の凍結の root を `g1Grade_of_g2Grade_positive`(G1 の grade への持ち越し。手書き `q10_grade_cross`)と
`g1Tree_of_g2Tree`(G1 の tick の tree への持ち越し。手書き `q10_tree_fwd`。G2 の domain 時刻は G1 より前なので添字も前で、tree のブロックは残る。周回 236 に閉じた)で G1 の tick に運び、証明済みの `freezeRoot_of_graded`(grade の通った要素は互いに互換
`GradeSupporter.graded_compatible` なので最も深い要素が支配する。手書き `q10_freeze_of_graded`)で G1 の凍結に移します(周回 235)。`g1Grade_of_g2Grade_positive` は手書きと同じく、抽象的な持ち越し `GradeTransport.gradeBool_transport`(支持は持ち越し反対は戻る。手書き `q10_gradeBool_transport`)に、G1 の early / late 時刻が G2 の domain 時刻以下であることと、2 つの tick の間の包含 `g1RawInputs_back` / `g1Interpreted_back`(G1 の tick の入力は `cut`(G2 の domain 時刻以下)より前に受信したので G2 の tick にもある。手書き `q10_rawInputs_back` / `q10_interpreted_back`。G2 の tick より後に入った SG 票とブロックの受信の印はその tick の時刻以上(新しい `SgStamps.stateBefore_sgFresh` / `BlockStamps.stateBefore_fresh`。新しい印はその時点の時計で、時計は戻らない)、finalized は添字について祖先へ戻らない。周回 242 に閉じた)・`g1LocalCovers_fwd`(覆いは tree が育っても残る。手書き `q10_localCovers_fwd`。tree のブロックは残り、run に root の衝突が無いので root の解決も変わらない。周回 240 に閉じた)・`g1InterpretedCover_fwd`(`b` を覆う入力は G1 の tick に運べる。手書き `q10_interpreted_fwd_cover`。SG 票の行と受信の印は run の添字について残り(新しい `SgStamps.stateBefore_sgKeep`。手書き `strict_sg_row_carry`)、本体の head も tree に残って印と root の解決が変わらない。周回 241 に閉じた)を渡して証明します(周回 238)。回復の枝は穴
`recordAgree_recovered` / `crossAgree_recovered` から取ります(周回 216 に穴 `recordAgree` / `crossAgree` / `confirmedAgree_genesis` をこの形に替えた)。
周回 304 で GST-zero の枝の一致の側(`commonUpper_genesis` から下)は sorry に依存しなくなりました(`#print axioms` で確かめた)。
確認の出力への包含 `confirmedIncluded` は周回 305 に `RecoveredBy` の 2 枝に分けました: GST-zero の枝 `confirmedIncluded_genesis`(穴ではない)は、
`IncludedFrom` の期限の時刻 `proposalTime e k + confirmationDelay` が確認の時刻 `confirmationTime e k` そのものなので、その読みの確認の記録が
提案の消去に等しいこと(`latestAtProposal_genesis`。手書き `latestAtProposalField_of_weakGenesis`)と交差の互換 `crossAgree` から
`preceq_getConfirmed_of_latest` で出します(手書き `userProposalsConfirmedAfter_of_weakGenesis_named` の筋。手書きは確認の時刻より後の読みにも
単調性で広げますが、naru の `IncludedFrom` は期限の時刻の 1 点なので要りません)。回復の枝は穴 `confirmedIncluded_recovered` です。
`latestAtProposal_genesis` は周回 306 に手書き `update_confirmation_latest_eq_of_duty` の運びで組みました: 確認の時刻の honest なノードの tick は
確認評価の tick で、読みの記録はその tick の確認の更新の結果(`confRead_eq_update`)。walk が提案で eligible なこと(`genuineConf_proposal_genesis`。周回 314 まで穴。
手書き `genuineConfirmation_of_dutyExecution` を `canonicalProposalDuty_positive_of_gstZero_named` の務めに当てたもの)、stable の書き込みが
元の記録を walk に進めたものの祖先であること(穴 `confHeadExtendsStable_genesis`)、元の記録が slot `k` の投票の務めの head の祖先で、その head が
提案であること(`voteDutyHead_proposal_genesis`。周回 306 に穴として置いた。元の記録の側は証明済みの `confWalk_preceq_laterVoteHead`)、提案のブロックがあること
(穴 `proposedBlockAt_isSome_genesis`)の 4 つの穴に分けました。
周回 307 に `voteDutyHead_proposal_genesis` の等号を祖先の側に弱めました: 投票の務めの head は投票時刻の読みの tree のブロックで slot が `k` 以下、
tree は親について閉じて(bodies の親閉包)親の slot は小さいので、tree の真の子孫は slot が大きく(`tree_slot_lt_of_preceq`)、slot `k` の提案が
head の祖先なら head そのもの(`voteDutyHead_eq_of_preceq`)。残りは提案が head の祖先であること(`proposal_preceq_voteDutyHead_genesis`)です。
周回 308 にそれを手書きと同じく slot 1 と `k ≥ 2` の枝に分けました: honest な提案者の発行したブロックはその slot の提案で(`emits_block_proposedBlockAt`。
tick の前の状態はその時刻の読みで、`preparedCache` / `setClock` は tick の式と同じ)、受理されたブロックは slot の提案者が honest なら
`UnforgeableSignatures` から提案(`acceptedBlock_proposedBlockAt` / `bodies_proposedBlockAt`)なので、slot 1 の投票時刻の tree は genesis と提案だけ
(`voteTreeOne_cases`)。head はその tree のブロックなので、slot 1 の枝は head が genesis でないことに、
`k ≥ 2` の枝は穴 `proposal_preceq_voteDutyHead_succ_genesis` に残ります。
周回 309 に slot 1 の枝を組みました(`proposal_preceq_voteDutyHead_one`): 投票の務めの anchor は投票時刻の tree のブロックなので genesis か提案で、
提案なら head はその子孫。genesis なら walk の tree(投票者の絞り込んだ tree)で genesis の子は提案だけで、提案は現在の slot なので適格、
walk は提案に降ります(`preceq_ghost_of_unique_child`)。提案が絞り込んだ tree にあること(`proposal_mem_voterTreeOne_genesis`。手書きの `hcandidate`)は、
FG root が anchor の祖先で finalized が FG root の祖先なことから組み、提案が投票時刻の tree にあること(穴 `proposal_mem_voteTreeOne_genesis`。
手書きの `hadmit` / `hBT`)と提案の高さが viable の証人になること(穴 `proposal_frontier_voteTreeOne_genesis`。手書きの `hfrontier`)を残しました。
周回 310 に提案が投票時刻の tree にあること(`proposal_mem_voteTreeOne_genesis`)を組みました: honest なノードは horizon 以内の公開の時刻すべてで
tick するので、提案者 `p 1` は提案の時刻に提案を発行し(`proposedBlockAt_emits`。`tick_block_of_proposalWith` は `Proposal.tick_block_shape` の逆向き)、
`tGST ≤ 0` なので配送の締切は投票の時刻そのもの。受信者の FG root は tree にあって genesis か提案なので、genesis なら提案の親の祖先で
`ProposerRoot.partialSynchrony_emitted_block_mem_of_parent` から、提案ならそのまま tree にあります。
周回 311 に提案の高さが viable の証人になること(`proposal_frontier_voteTreeOne_genesis`)を組みました: 読みの `hMax` は bodies のブロック `W` の
導出の高さで、`W` の消去は tree にあり `sigma` のその値は `W` の導出(`MaxCarrier.stateBeforeTime_maxCarrier`)。tree は genesis と提案だけなので、
`W` が genesis なら `hMax` は 1、そうでなければ提案の状態の高さが `hMax` そのものです。
周回 312 に提案のブロックがあること(穴 `proposedBlockAt_isSome_genesis`)を前提なしの `AvailableHoles.proposedBlockAt_isSome` にしました:
提案の親は fork choice の head で読みの tree にあり、tree のブロックは bodies の消去で、run のどの store でも bodies は重複が無く消去が単射
(新しいモジュール `BodiesUnique.lean`。bodies に `b` を足すのは消去が前の tree に無いときだけ)なので、`parentBody?`(`findUnique?`)は
その body を返します(手書き `runtime_proposal_some`)。
周回 313 に stable の書き込みが元の確認の記録を walk に進めたものの祖先であること(穴 `confHeadExtendsStable_genesis`)を証明しました(手書き
`stableWrite_preceq_advanceWalk_of_gstZero_of_carrierWindow` の運び): tick の slot を `q` とすると、walk は slot `q + 1` の投票の務めの head の祖先
(`confWalk_preceq_laterVoteHead`)、元の確認の記録も genesis か、より前の確認評価の tick の walk か stable root なので同じ head の祖先で、
2 つは一方が他方の祖先(`Blocks.preceq_linear`。手書き `latestConfirmed_compatible_confWalk_of_gstZero`)。stable の書き込みは元の stable の記録
(元の確認の記録の祖先 `RecordOrder.stateBefore_sbc`)か grade の stable root(walk の祖先 `confStableRoot_preceq_confWalk`)なので、
`advanceConfirmed` の 2 枝で閉じます。
周回 314 に walk が提案で eligible なこと(穴 `genuineConf_proposal_genesis`)を手書き `genuineConfirmation_of_dutyExecution` の運びで組みました:
確認の更新の前の段の store で、slot `k` の committee の honest な要素がみな root が提案に解決する支持の投票を持てば、門を通るブロックは
honest な支持者の投票(投票者ごとに 1 つ)から提案の祖先で(`Majority.preceq_of_eligible_exactSupport`。手書き `HonestSupport.not_eligible`)、
anchor から提案までの途中で門を通る子は提案に向かう子だけ、提案の子は門を通らないので、walk は提案で止まり提案は門を通ります
(`Majority.head_eq_of_exactSupport`。手書き `confWalkWith_eq_of_support`)。前提の pool の不変条件・committee の整列・honest 過半・tree の重複の無さは
証明済みの補題から出し、手書き `CanonicalProposalDutyAt` の欄に当たる 3 つに分けました。支持の投票(`confSupport_proposal_genesis`。欄
`votes` / `counted` / `resolve`)は同じ周回に証明しました: honest な委員の投票は支持の締切より前の受信の印で pool に入り
(`Stamps.partialSynchrony_honest_gfVote_stamped`)、その head は提案(`voteDutyHead_proposal_genesis`)で、読み手の締切の読みの finalized が提案の
祖先なので提案は締切より前の印で読み手の tree に入り(`bodiesBlock_stamped`)、遅い投票に同じ投票者の別の投票は無い(`PoolFrom.pool_honest_unique`)。
anchor が提案の祖先なこと(`confAnchor_preceq_proposal_genesis`。欄 `anchor`)は周回 315 に証明しました: 手書きは同じ slot の投票者の head についての
`_same_of_gstZero` の補題で、naru では anchor の補題の連鎖(`confAnchor_preceq_laterVoteHead` / `confFgRoot_preceq_laterVoteHead` /
`confG1Raw_preceq_laterVoteHead` から下)の slot の仮定を `q < d` から `1 ≤ d`・`q ≤ d` に弱めました。tick の時刻 `t` そのものは slot `q + 1` の
投票時刻より後ですが、使っていたのは `t` より前の時刻だけです: FG root の確認の証人の行の時刻は `t` より前の確認の時刻なので opening slot が `q` より前
(`attest_lt_nextVote_of_lt_confTick`)、窓の行の round の opening slot は `r ≥ 3` で `q` より前、G1 の domain 時刻は slot `q + 1` の提案時刻以下です。
anchor から提案までの途中が filtered tree にあること(`confPath_proposal_genesis`。欄 `path`)は周回 316 に、手書き
`proposedBlock_confirmationBandAndCandidate_of_gstZero_of_pins` と同じ運びで証明しました: 提案は tick の前の tree に支持の締切より前の印で入り
(`proposal_stamped_confTick_genesis`。`confSupport_proposal_genesis` の途中から切り出しました)、tree は祖先について閉じているので途中のブロックも
tree にあります。viable の証人は提案そのもので、その高さが `hMax - 1` 以上なこと(`confBand_proposal_genesis`)は、最大の高さの横断の honest な行
(`MaxCrossing.stateBeforeTime_maxCrossing_honestEmission_lt`)を出した tick の務めの確認の証人 `K`(高さ `hMax - 1`)が、行の時刻が slot `k + 1` の
投票時刻より前なので提案(slot `k` の投票の務めの head)の祖先で、root の衝突なしで高さが単調なことから出します。finalized ⪯ FG root ⪯ anchor ⪯ 途中のブロックです。
GST-zero の枝で残る穴は、提案が slot `k ≥ 2` の投票の務めの head の祖先なこと(`proposal_preceq_voteDutyHead_succ_genesis`)だけです。
周回 318 にそれを降下補題 `Goldfish.ghost_reaches` の 4 つの前提に分けました。投票の務めの head は anchor から歩みの tree・得点・適格さで辿る
`ghost` の結果です(`voteDutyHeadAt_eq_ghost`。定義を開いただけ)。walk が提案で止まること(`voteStop_proposal`。前提 `hstop`)は証明しました:
歩みの tree は store の tree の部分集合で、提案の子は slot が `k` より大きいのに、投票時刻の tree のブロックの slot は `k` 以下です。
残りは 3 つの穴でした。anchor ⪯ 提案(`voteAnchor_preceq_proposal_succ_genesis`。前提 `hpre`、手書きの `hcompat`)、途中のブロックが歩みの tree にあること
(`votePath_proposal_succ_genesis`。前提 `hpath`、手書きの `hcandidate`)、途中の各ブロックで提案の祖先へ一歩進むこと(`voteStep_proposal_succ_genesis`。
前提 `hstep`、手書きの pivot と凍結した suffix の帯の前提 hexists / hfrozen / hsuffix / htarget / hscore)です。
周回 320 に、はじめの 2 つを 1 つの穴に寄せて証明しました。寄せた先は、slot `k - 1` で保護されたブロック(`ProtectedVoteSlot`)が提案の親の祖先なこと
(`protected_preceq_proposalParent_succ_genesis`。手書き `protected_preceq_proposedParent_of_gstZero_named`)です。anchor は honest な各ノードの
slot `k - 1` の head の祖先(`voteDutyAnchor_preceq_prevHead`)なので保護されます。途中の tree は手書き `proposedBlock_voterCandidate_of_gstZero_named` と同じ運びです:
提案は配送の締切(投票時刻)までに tree に入ります(FG root ⪯ anchor ⪯ 提案の親。`ProposerRoot.partialSynchrony_emitted_block_mem_of_parent`)。
高さの帯(`voteBand_proposal_succ_genesis`)は `confBand_proposal_genesis` と同じ形で、最大の高さの横断の行の確認の証人が slot `k - 1` で保護されることから出します。
周回 321 に、寄せた先を提案者の walk の層で組みました。提案の親は提案者の読み(`proposalDutyStoreAt`)の `getHeadWith` です(`proposalParent_eq_head`)。
保護されたブロック `P` が読みの anchor の祖先なら、anchor ⪯ 提案の親で済みます。そうでなければ、過半の支持で walk が `P` を通ります
(`proposalParent_passes_supporter_majority`。重複なしと「支持 ⊆ 投票」は証明済み)。途中のブロックは、歩みの tree の証人 `X` の祖先として
tree に入ります(`proposalDutyTree_mem_of_preceq`)。残りは 2 つの穴です。証人 `X`(`proposerCandidate_protected_succ_genesis`。手書きの `hXcandidate` と `hanchorX`)と、
提案者の view での過半(`proposerSupporterMajority_protected_succ_genesis`。手書きの `supporterMajority_of_cone`)です。
周回 322 に、過半の穴を閉じました。前提に anchor ⪯ `P` を足しました(呼び出し側の枝にあります)。提案者の view は pool のバケツ `d` そのもので、
凍結の絞り込みがありません。参加者は pool の不変条件で committee に収まり(`proposalDutyStore_participants_committee`)、honest な委員は
equivocate しません(`proposalDutyStore_no_honest_equivocation`)。slot `d` の honest な委員の投票(`voteConeSlot_of_heads`)は、支持の締切
`supportCutoff d ≤ proposalTime (d + 1)` より前に提案者の pool に入ります。その head は提案者の読みの tree にあります(`voteDutyHead_mem_proposalDutyTree`。
互換は finalized ⪯ FG root ⪯ anchor ⪯ `P` ⪯ head)。そこで投票は支持の view で `P` 以下を指します(`proposalDutyStore_supportVote_of_pool`)。
手書きはどの穴も `RecoveredBy` の 2 枝(`gstZeroGuarantees_of_weakGenesis` / `recoveryProducesHealedState` の位相の保証)で分けるので、細分はその 2 枝から切ります。
`confirmedLive` / `stableLive`(周回 212)は固有の穴を持たず、`LiveSleepyRegime` の `SleepyRegime` で `availableAt` を当て、証明済みの
`Liveness.lean` の `confirmedLive_of_available` / `stableLive_of_available` で活性に移します(`available` の穴を閉じれば一緒に閉じる)。
`stableIncludedFast`(周回 212)は入口 `StableIncludedFastHoles.lean` の `stableIncludedFastAt` が `FreshSleepyRegime` を `SleepyRegime` と新鮮な過半に分け、
確認の出力への包含を `available` の `confirmedIncluded`(周回 305 から穴ではなく、GST-zero の枝は周回 306 に `latestAtProposal_genesis` から分けた 4 つの穴、回復の枝は穴 `confirmedIncluded_recovered` に依る)から取り(手書き `available_stableIncluded_fresh` と同じ依存)、`t0 = 0` か否かで stable の書き込みの
穴 `stableWriteFresh_genesis` / `stableWriteFresh_recovered` に渡します。`finalized`(周回 212)は入口 `FinalizedHoles.lean` の `finalizedAt` が包含を穴 `finalizedIncluded` から取り、活性を
証明済みの `finalizedLive_of_included` で包含から出します。`stableAsynchronyResilient`(周回 212)は入口 `PersistsHoles.lean` の `persistsFrom` が
`PersistsFrom` の量化を開いてブロック・時刻ごとの穴 `stableInBy` に渡します。bundle `Consensus`(周回 212)は 13 件の theorem を項目に置き、固有の穴を持ちません。

### 穴の一覧

手書きのファイルは `third_party/verified-consensus/` からの相対パスです。

| 穴(theorem) | 義務 | 手書きの宣言 | 手書きのファイル | 置いた周回 |
|---|---|---|---|---|
| `Proofs.Consensus.AvailableHoles.recordAgree_recovered` | `Consensus.Spec.Claims.available` | `available_confirmedSafe` | `DecoupledConsensusProofs/Bridge/StandardVocabulary.lean` | 216 |
| `Proofs.Consensus.AvailableHoles.crossAgree_recovered` | `Consensus.Spec.Claims.available` | `latest_compatible_finalized_core` | `DecoupledConsensusProofs/Execution/PreparedV4LatestFinalizedCompatibilityClosed.lean` | 216 |
| `Proofs.Consensus.AvailableHoles.proposerCandidate_protected_succ_genesis` | `Consensus.Spec.Claims.available` | `protected_preceq_proposedParent_of_gstZero_named` | `DecoupledConsensusProofs/Protocol/ForkChoice/Views/WeakProposalHeadNamed.lean` | 321 |
| `Proofs.Consensus.AvailableHoles.voteStep_proposal_succ_genesis` | `Consensus.Spec.Claims.available` | `namedProposalWalkTransferred_of_frozenCompatiblePivot_core` | `DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/ProposalPivot.lean` | 318 |
| `Proofs.Consensus.AvailableHoles.confirmedIncluded_recovered` | `Consensus.Spec.Claims.available` | `available_confirmedIncluded` | `DecoupledConsensusProofs/Bridge/StandardVocabulary.lean` | 305 |
| `Proofs.Consensus.AvailableHoles.stableIncluded` | `Consensus.Spec.Claims.available` | `available_stableIncluded_any` | `DecoupledConsensusProofs/Bridge/StableIncludedAnySlot.lean` | 211 |
| `Proofs.Consensus.StableIncludedFastHoles.stableWriteFresh_genesis` | `Consensus.Spec.Claims.stableIncludedFast` | `stableWrite_anySlot_fresh_gstZero` | `DecoupledConsensusProofs/Bridge/StableIncludedFresh.lean` | 212 |
| `Proofs.Consensus.StableIncludedFastHoles.stableWriteFresh_recovered` | `Consensus.Spec.Claims.stableIncludedFast` | `stableWrite_anySlot_fresh_afterGST` | `DecoupledConsensusProofs/Bridge/StableIncludedFresh.lean` | 212 |
| `Proofs.Consensus.FinalizedHoles.finalizedIncluded` | `Consensus.Spec.Claims.finalized` | `finalized_included` | `DecoupledConsensusProofs/Bridge/StandardVocabulary.lean` | 212 |
| `Proofs.Consensus.PersistsHoles.stableInBy` | `Consensus.Spec.Claims.stableAsynchronyResilient` | `outage_stablePersists` | `DecoupledConsensusProofs/Bridge/StandardVocabulary.lean` | 212 |
