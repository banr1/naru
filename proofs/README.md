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
互換なら時刻 `t2 ≥ t` の値の接頭辞(`record_mono_of_compatible`。手書き `latest_confirmed_mono_of_agreement`))、`Outputs.lean`(出力
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
`supportCutoff` が horizon 以内なら honest な `w` の pool に `w` ごとのある添字の後で入り受信の印が `supportCutoff` より前 `partialSynchrony_honest_gfVote_stamped`。`storeTau` の head のブロックの受信の印の側は残り)。
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
