-- naru-obligation: Consensus.Spec.Claims.constants sha256:9c0ca8f2de33f19fdf9e07c4d0df7b6e63a7cd67fb03e279ae0a17035426fe66
-- naru-obligation: Consensus.Spec.Claims.nested sha256:9c0ca8f2de33f19fdf9e07c4d0df7b6e63a7cd67fb03e279ae0a17035426fe66
-- naru-obligation: Consensus.Spec.Claims.finalizedMonotone sha256:9c0ca8f2de33f19fdf9e07c4d0df7b6e63a7cd67fb03e279ae0a17035426fe66
-- naru-obligation: Consensus.Spec.Claims.certificatesAccountable sha256:9c0ca8f2de33f19fdf9e07c4d0df7b6e63a7cd67fb03e279ae0a17035426fe66
-- naru-obligation: Consensus.Spec.Claims.finalizedAccountable sha256:9c0ca8f2de33f19fdf9e07c4d0df7b6e63a7cd67fb03e279ae0a17035426fe66
-- naru-obligation: Consensus.Spec.Claims.finalizedSafe sha256:9c0ca8f2de33f19fdf9e07c4d0df7b6e63a7cd67fb03e279ae0a17035426fe66
-- naru-obligation: Consensus.Spec.Claims.honestNeverSlashed sha256:9c0ca8f2de33f19fdf9e07c4d0df7b6e63a7cd67fb03e279ae0a17035426fe66
import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Constants
import Proofs.Consensus.Nested
import Proofs.Consensus.FinalizedMonotone
import Proofs.Consensus.CertificatesAccountable
import Proofs.Consensus.FinalizedAccountable
import Proofs.Consensus.HonestNeverSlashed
import Proofs.Consensus.Liveness
import Proofs.Consensus.Outputs
import Proofs.Consensus.RecordOrder
import Proofs.Consensus.Available
import Proofs.Consensus.Goldfish
import Proofs.Consensus.Votes
import Proofs.Consensus.Majority
import Proofs.Consensus.Voting
import Proofs.Consensus.Delivery
import Proofs.Consensus.Window
import Proofs.Consensus.PoolFrom
import Proofs.Consensus.Equivocation
import Proofs.Consensus.OwnVote
import Proofs.Consensus.Carried
import Proofs.Consensus.Stamps
import Proofs.Consensus.BlockStamps
import Proofs.Consensus.BlockReceipt
import Proofs.Consensus.Proposal
import Proofs.Consensus.ParentSlot
import Proofs.Consensus.DeliveredBlock
import Proofs.Consensus.ProposerFinality
import Proofs.Consensus.ReceiverFinality
import Mathlib.Tactic

/-!
# consensus の証明義務の入口(IDEAL.md C71)

`generated/obligations.json` の 14 件 — claim bundle `Consensus.Spec.Claims.Consensus` と 13 claims(`constants` / `nested` /
`certificatesAccountable` / `finalizedAccountable` / `finalizedMonotone` / `honestNeverSlashed` / `finalizedSafe` / `available` /
`confirmedLive` / `stableLive` / `stableIncludedFast` / `finalized` / `stableAsynchronyResilient`)— の theorem
`Proofs.Consensus.Spec.Claims.<名前> : <義務の型>` をここに置き、補題は `Proofs/Consensus/` 配下のモジュールに分けてここから import する。
各 theorem の束縛行 `-- naru-obligation: Consensus.Spec.Claims.<名前> sha256:<束縛 hash>` はこのファイルの先頭に並べる(`proofs/README.md`)。

証明済み(束縛行あり): `constants`(補題 `Proofs/Consensus/Constants.lean`: 定数を Δ・R・η_SG の多項式に開く)、
`nested`(補題 `Proofs/Consensus/Nested.lean`: `getStable` / `getConfirmed` の分岐と `preceq` の反射律。run への前提は要らない)、
`finalizedMonotone`(補題 `Proofs/Consensus/FinalizedMonotone.lean`: 全ハンドラが store の `f` を縮めないこと(`Stores.lean`)と、
`EventsSorted` の下で `filter (≤ t)` が `filter (≤ t2)` の接頭辞であること(`Runs.lean` / `Tables.lean`)から、`preceq` の推移律(`Blocks.lean`)で結ぶ)、
`certificatesAccountable`(補題 `Proofs/Consensus/CertificatesAccountable.lean`: 名前付き導出 `deriveNamed` の不変条件
(`Derivation.lean`: finality の証明書と高さの横断の定足数)、定足数の交わりの重み `2q − W`(`Weights.lean` / `Sets.lean`)、
E1 の slashable(`Slashing.lean`)、消去と `chainAttestations` の所属(`NamedBlocks.lean` / `Orders.lean`)から、手書きの
`namedChainAccountableSafety` の筋で結ぶ)、
`finalizedAccountable` / `finalizedSafe`(補題 `Proofs/Consensus/FinalizedAccountable.lean`: store の不変条件(`Carrier.lean`: bodies の各
名前付きブロックの消去が tree にあり chain 状態の表 `sigma` の値がその名前付き導出で、finalized `f` はどれかの bodies の導出の `f`)から
2 つの読みの finality carrier `D₁` / `D₂` を取り、`EventsSorted` の下で `readAt t` が `stateBefore i` であることから run の中のブロックにし、
`Idealization = NamedRootCollisionFree` を消去した祖先の持ち上げで `RootInjectiveOnAncestors` にして `certificatesAccountable` の本体 `oriented` を
両向きに当て、`Evidence` を `chainAttestations ⊆ storeAttestations` で `SlashableStates` に持ち上げる(`finalizedAccountable`)か
`SlashableBound` で退ける(`finalizedSafe`)。`Set Block` / `Set NamedBlock` / `Table Block _` の所属は `Orders.lean` の
`block_compare_eq_iff` / `nb_compare_eq_iff`(backend が再帰する型に出す明示的な `naruCompare` の `.eq ↔ =`)で言い換える)、
`honestNeverSlashed`(補題 `Proofs/Consensus/HonestNeverSlashed.lean`: store の `v` の署名の attestation は `v` の tick が実際に出した
行の消去(`Attribution.lean`: store の不変条件の `named` / `closed`、bodies のブロックは処理されたブロック、`UnforgeableSignatures` の
carried)で、`v` の 2 つの発行の消去は slashable でない(`EmissionSafety.lean`: validator client の記録 `Record` の性質
(`Records.lean`: target は書き込み 1 回、lock / timeout は増えるだけ、`LockCompatible` / `FinalitySafeAt`)と、記録を書くのは自分の tick の
`namedCreate` だけであること(`Signing.lean`)から、同じ高さに名指す target は等しく finality pair と timeout は両立しない))。
残りの 6 claims と bundle `Consensus` は未証明(`lake exe naru proofs` が `missing` と表示する)。手書き証明
(`third_party/verified-consensus/DecoupledConsensusProofs`、基準コミット)は構成・補題の分割・証明の筋を読んで参照するが import しない。
liveness 系の claim の共有の足場(周回 127。theorem はまだ無い): `Proofs/Consensus/Liveness.lean` の `liveFrom_of_includedFrom`
(包含 `IncludedFrom` + 単調 `MonotoneFrom` + 未来の提案の不在 `NoFutureRead` + 再発 → 活性 `LiveFrom`)と、
`confirmedLive_of_available` / `stableLive_of_available`(claim `available` の結論 `AvailableAt` から `confirmedLive` / `stableLive` の結論)、
`finalizedLive_of_included`(finalized の包含から `finalized` の活性)。`NoFutureRead.lean`(時刻 `t` の読みに提案時刻が `t` より後の
honest な提案は入らない: `Clocks.lean` の時計の不変条件 `s = slotOf e t`・時計は event の時刻以下、`TreeInv.lean` の出力のブロックが tree にあること、
受理の守り `¬ (st.s < slot b)`)は `ExecutionValid` と Δ > 0 だけから 3 出力すべてについて成り立つ。
claim `available` の結論 `SafeFrom`(一致 `AgreeFrom` ∧ 単調 `MonotoneFrom`)に向けた足場(周回 130。theorem はまだ無い):
`ConfirmationRecords.lean`(確認・stable の記録 `latestConfirmed` / `latestStable` を書くのは `updateConfirmationWith` だけで、
`advanceConfirmed` / `floorOnStable` は「古い記録の接頭辞は、新しい記録と互換なら新しい記録の接頭辞」(`Keeps`)を満たし、他のハンドラは
記録を変えず、1 tick は記録を変えない務めに高々 1 回の更新を掛けた形 `tick_rec_shape`)、`RecordGrowth.lean`(run に沿って: ノードの記録が
変わるのは自分の tick の添字だけ `recAt_succ`、添字の区間の接頭辞保存 `prefix_preserved`、時刻 `t` の読みは `filter (≤ t)` の長さ `idx t` の
`stateBefore`、tick の直後の記録は同じ時刻の読みの記録 `recAt_tick_eq_storeAt`、記録の時刻をまたぐ一致 → 単調 `record_mono_of_compatible`)、
`Outputs.lean`(出力 `getStable` / `getConfirmed` の単調性と一致を欄 `f` / 記録の事実と、確認の出力では `StableBelowConfirmed`
(stable の記録 ⪯ 確認の記録)に還元する `safeFrom_stable_of_fields` / `safeFrom_confirmed_of_fields`)。
周回 132 の足場(claim の theorem はまだ無い): `RecordOrder.lean`(`StableBelowConfirmed` は regime の事実ではなく store の不変条件:
`updateConfirmationWith` は `latestConfirmed := floorOnStable stable …` と書き、`floorOnStable` はどの分岐でも `stable` を延ばすので、
run のどの読みでも前提なしに成り立つ `stableBelowConfirmedFrom`。stable の記録についての欄の事実(一致・finalized との交差の互換)は
確認の記録のそれから従う `recordAgreeFrom_stable_of_confirmed` / `crossAgreeFrom_stable_of_confirmed` ので、2 つの出力の `SafeFrom` は
どちらも確認の記録の一致・交差の互換・finalized の一致の 3 つだけに還元される `safeFrom_confirmed_of_records` / `safeFrom_stable_of_records`。
`AgreeFrom` / `MonotoneFrom` / `SafeFrom` の開始時刻についての単調性 `*.mono`)、`Available.lean`(`AvailableAt t0` を残る 5 つの事実 —
確認の記録の一致と finalized との交差の互換、finalized の一致、2 つの包含 — から組み立てる `availableAt_of_records`(前提は `EventsSorted` /
`EventsNodup` だけ)と `SleepyRegime` 版 `availableAt_of_fields`。`t0 ≠ 0` なら `RecoveredBy` は回復の枝に限られ `SlashableBound` を持つので、
finalized の一致は `finalizedSafe` の本体から従う `agreeFrom_finalized_of_recovered`(残る事実は 4 つ `availableAt_of_fields_recovered`))。
周回 133 の足場(claim の theorem はまだ無い): `Goldfish.lean`(確認の候補を書く fork choice と得点の最初の層。`ghost anchor tree score eligible` は
anchor から適格な子のうち得点最大の一意なものへ降りる歩みで、結果は anchor を延ばし `ghost_preceq`、anchor そのものか適格な tree の要素
`ghost_eligible`。降下補題 `ghost_reaches`: anchor から `target` までの途中のブロックが tree にあり、各ブロックで次の一歩が `target` の祖先で、
`target` に適格な子が無ければ結果は `target`(燃料 `size tree` が足りること `path_card` は途中のブロックの深さが相異なることから)。
親について閉じた tree では結果に適格な子は無い `ghost_terminal`。Goldfish の得点は祖先ほど大きく `goldfishScore_mono`、支持者は投票の参加者
`rawSupporters_size_le`。`updateConfirmationWith` の `let` を名前つきの定義(`supportVotes` / `lateCount` / `score` / `eligible` / `sgRoot` /
`head` / `candidate` …)に開いて `updateConfirmationWith_eq`(`rfl`)で結び、新しい確認の記録は 元の記録 / stable の記録 / 過半の支持
`lateCount < 2 · score` を持ち SG root を延ばす head / grade の候補 `frameSgCandidate` のどれか `latestConfirmed_shape`)。
周回 136 の足場(claim の theorem はまだ無い): `Votes.lean`(投票の pool `storePool` に投票を入れるのは `onGoldfishVote` だけで、必ず
`onGoldfishVoteChecked` の守り `vote.valIndex ∈ committee' vote.slot` を通る。pool の不変条件 `PoolInv`(鍵 `k` の投票は slot `k` で committee の
投票)と拡張 `PoolExt`(元の投票は残り、増えた投票は適格)を全ハンドラ → tick / deliver → world → run の読みに積み上げ、`storeAt_pool` /
`stateBefore_pool`(前提なし)と `storeAt_poolExt`(`EventsSorted` の下で同じノードの pool は時刻について増えるだけ)。自分の投票の形
`goldfishVoteWith_some`: 投票者は自分、slot は store の `s`、head は `getHeadInTreeWith` の結果の root)、`Majority.lean`(確認の門
`lateCount < 2 · score` と honest 過半。支持の投票は遅い投票 `supportVotes_sub_lateVotes`(解決の印 ≥ 受信の印、`supportCutoff ≤ confirmationTime`)
なので `noSecondVoteIn` の絞り込みから支持の投票は投票者ごとに 1 つ `supportVotes_unique`、equivocator は無く `supportVotes_no_equivocation`
(`NaruStd.Set` の整列 `SortedLt` と `GoldfishVote` の辞書式順序から重複なし)、得点は支持者の数 `score_eq_supporters`。参加者は committee の要素
`participants_sub_committee`(`PoolInv`)。数え上げの核 `exists_honest_of_majority`(`Finset`)から、門を通るブロックには honest な支持者がいる
`exists_honest_supporter`(前提: `0 ≤ Δ`・`PoolInv`・committee の整列・`HonestCommittees` の不等式・honest な committee の要素がみな遅い投票の
参加者)/ `_of_head` / `_of_run`。手書き `Confirmation.lean` の `HonestSupport` から `vote` を「`B` 以下を指す」に弱めた `HonestSupport`
(committee は honest 過半、honest な committee の要素はみな支持の投票に `B` 以下を指す投票を持つ)から `B` とその祖先は門を通る
`HonestSupport.eligible` / `eligible_of_preceq` と門を通るどのブロックも `B` と互換 `HonestSupport.compatible_of_eligible`)。
周回 139 の足場: `Voting.lean`(honest な投票の発行。tick が出す投票は投票の時刻 `voteTime` の tick の投票の務めの出力で、投票者は自分・slot は
`slotOf e t`・投票者は committee の要素 `tick_gfVote_shape` / `emits_gfVote_shape`、1 つの tick が出す投票は 1 つ `tick_gfVote_unique`、どの投票者も
slot ごとに発行する投票は 1 つ `emits_gfVote_unique`、`ScheduleWellFormed` の下で honest な committee の要素は horizon までの各 slot `k > 0` の `voteTime` に投票を発行する
`honest_emits_gfVote`。手書き `Alignment.lean` の `emits_gfVote_shape` / `emits_gfVote_unique`)。
周回 140 の足場: 同じ `Voting.lean` に投票の head(投票の時刻は提案の時刻と違うので(Δ > 0。`voteTime_ne_proposalTime`)投票の務めが読む store は
時計を合わせただけ `voteStore_of_voteTime`、tick が出す投票の head は tick の前の store に時計を合わせたもの(`clocked`)の fork choice の head `voteHead`
(`tick_gfVote_head`)、run では `Emits` の添字 `i` の `stateBefore i` の発行者の store と `onPhaseTick` で進めた cache で読む `emits_gfVote_head` /
`honest_emits_gfVote_head`)。
周回 141 の足場: `Delivery.lean`(投票の配送の層の入口。投票は `excludes` が偽なので `PartialSynchrony` から締切 `max t tGST + Δ` より前に
honest な受信者が扱う `partialSynchrony_gfVote`、`HandlesAt` の投票の経路は自分の tick の発行・配送・運ぶブロックの受理の 3 つ `handlesAt_gfVote_cases`、
配送された投票が受信者の pool に入るのは投票者が committee の要素・受信者の slot が `u.slot` か `u.slot + 1`(`InWindow`)・同じ投票者の投票が
pool にまだ 2 つ無いときで(`mem_onGoldfishVote` / `mem_receiptProcess_gfVote`。手書き `on_goldfish_vote_insert` の窓と equivocation の守りに当たる)、run では配送の後の
どの添字でも pool に残る `deliver_gfVote_mem` / `deliver_gfVote_mem_of_lt`)。
周回 142 の足場: `Window.lean`(受信の直前の slot の窓。時計は添字について単調 `clock_mono` で、添字 `j < i` の自分の tick の時刻は
`stateBefore i` の時計以下 `tick_le_clock`、時刻が狭義に早い event は添字も前 `lt_of_time_lt`、slot の開始時刻は公開時刻なので honest な受信者への時刻 `t2` の
配送の直前の slot は `proposalTime k < t2` なら `k` 以上・`t2 < proposalTime (k + 1)` なら `k` 以下 `slot_ge_of_deliver` / `slot_le_of_deliver`、GST 以後に
発行された投票の発行の時刻 `t` 以後で締切 `t + Δ` より前の配送の直前の slot はちょうど `u.slot` で `InWindow` `slot_eq_of_deliver_gfVote` / `inWindow_of_deliver_gfVote`)。
周回 143 の足場: `PoolFrom.lean`(pool の投票の由来。run のどの添字のノード `u` の pool の投票も、`u` が処理した(`Processes`)投票か、`u` が処理したブロックが
運ぶ投票 `pool_from`(ハンドラごとに `onGoldfishVote_from` / `onBlockUsing_from` / `onBlockWith_from` / `receiptProcess_from` / `tick_from`)、`UnforgeableSignatures` の下で
honest な投票者の pool の投票はその投票者の tick が出した投票 `pool_genuine`、`ScheduleWellFormed` も合わせると同じ honest な投票者・同じ slot の pool の投票は
どのノード・どの添字でも 1 つ `pool_honest_unique` — `Delivery.deliver_gfVote_mem` の equivocation の仮定に向けた層)。
周回 144 の足場: `Equivocation.lean`(honest な投票者は run のどの添字・どのノード・どの鍵の pool でも equivocate しない `pool_no_equivocation`(pool の集合の整列による
重複なし・`PoolInv` の鍵 = slot・`PoolFrom.pool_honest_unique`)、発行された投票の投票者は committee の要素 `voteWellFormed_of_emits`。これで `ScheduleWellFormed` / `UnforgeableSignatures` / Δ > 0 の下で
`Delivery.deliver_gfVote_mem` の 3 つの仮定が外れ、GST 以後に honest な投票者が発行した投票の honest な受信者への締切 `max t tGST + Δ` より前の配送の後、受信者の鍵 `u.slot` の pool に投票がある
`deliver_honest_gfVote_mem` / `deliver_honest_gfVote_mem_of_lt` — 配送の経路 (2) の完成。経路 (1)(自分の tick)と (3)(ブロックが運ぶ投票)は残り)。
周回 145 の足場: `OwnVote.lean`(tick の投票の務めは投票を出すとき store に `onGoldfishVoteChecked` で入れ、務めの store の slot は投票の slot なので窓は自明で、Δ > 0 なら提案の務めは走らず
確定の更新と attestation の務めは pool を変えないので、tick の前の pool で equivocation が無ければ tick の後の鍵 `u.slot` の pool に投票がある `tick_gfVote_mem` / `nodeTick_gfVote_mem`。
`ScheduleWellFormed` / `UnforgeableSignatures` / Δ > 0 の下で honest な `w` の tick が出した投票は以後 `w` の pool にある `tick_honest_gfVote_mem` / `emits_honest_gfVote_mem_of_lt`(経路 (1) の完成)、
GST 以後の honest な投票を honest な `w` が発行の時刻以後・締切より前の添字 `j` で扱えば、`stateBefore (j + 1)` の `w` の pool に投票があるか経路 (3) `handlesAt_honest_gfVote_mem_or_carried`。経路 (3) は残り)。
周回 146 の足場: `Carried.lean`(ブロックの受理は新しいブロックを tree に入れるときだけ運ばれた投票を `foldl onGoldfishVoteChecked` で pool に入れ、畳み込みの途中の store は時計が元のままで
pool は最終の pool の部分集合なので、窓・committee・最終の pool の投票者の一意性 `UniqueIn` の下で運ばれた投票は受理の後の pool にある `foldl_mem` / `onBlockUsing_mem` / `processBlockCore_mem`。
tick がブロックを出すのは提案の時刻だけ `tick_block_time` で、投票の時刻以後・次の slot の提案の時刻より前は提案の時刻ではない `ne_proposalTime_of_vote_window` ので、GST 以後の honest な投票の
締切より前の経路 (3) は配送だけで、受信の直前の slot はちょうど `u.slot` で pool に入る `carried_honest_gfVote_mem`。経路 (1)(2)(3) をまとめて、GST 以後の honest な投票を honest な `w` が
発行の時刻以後・締切より前の添字 `j` で扱えば `stateBefore (j + 1)` の `w` の pool にある `handlesAt_honest_gfVote_mem`、締切が horizon 以内なら honest な各ノード `w` について
締切より前の `w` ごとのある添字の後で `w` の pool にある `partialSynchrony_honest_gfVote_mem`(全ノードに共通の添字はまだ))。
周回 147 の足場: `Stamps.lean`(受信の印の表 `timestampVote` を書くのは `onGoldfishVote` だけで、既に鍵 `u.slot` の pool にある投票は受理されないので、どのハンドラも pool の投票の印を保存し、
新しい投票の印は時計の時刻(`Step` / `Grow`)。時計は添字について単調なので run のどの添字でも pool の投票の印は時計以下 `stateBefore_stampInv`、`stateBefore (j + 1)` の pool の投票の印は
以後ずっと添字 `j` の event の時刻以下 `stamp_le_of_mem`。投票の締切 `voteTime + Δ` はちょうど `supportCutoff` なので、GST 以後の honest な投票は `supportCutoff` が horizon 以内なら honest な各ノード `w` について
`w` ごとのある添字の後で `w` の pool にあり受信の印が `supportCutoff` より前 `partialSynchrony_honest_gfVote_stamped`)。
周回 148 の足場: `BlockStamps.lean`(ブロックの受信の印の表 `timestampBlock` を書くのは `onBlockUsing` の受理(`storedOf`)だけで、受理するのはまだ tree に無いブロックなので、
どのハンドラも tree のブロックとその印を保存し新しいブロックの印は時計の時刻(`Step` / `Grow`)、初期の tree は `{Genesis}` で印は `Bottom`。run のどの添字でも tree のブロックの印は
`Bottom` か時計以下 `stateBefore_stampInv`、`stateBefore (j + 1)` の tree のブロックは以後ずっと tree にあり印は添字 `j` の event の時刻で抑えられる `stamp_le_of_mem` / `tree_stamped`。
投票の head の root を引いたブロック(slot が投票の slot 以下)と投票の 2 つの印がどちらも `γ` より前なら `storeTau` も `γ` より前 `storeTau_before`。honest な提案が締切より前に
各ノードの tree に入ることは残り)。
周回 149 の足場: `BlockReceipt.lean`(`onBlockUsing` の受理の守りのうち「まだ tree に無い」を除く 5 つ(slot が受信者の slot 以下・親が tree にある・`st.f` の子孫・提案者・親の slot が小さい)を `Admits` にまとめ、
その下で受理の後の tree にブロックがある `onBlockUsing_mem_tree`。名前付きの親が bodies にあり運ばれた attestation の round の守りも通れば、名前付きの処理・受信の処理の後の tree にあり、
tree に無かったなら bodies にもある `processBlockCore_mem_tree` / `_bodies`・`onBlockWith_mem_tree` / `_bodies`。run では配送の直前の受信者の store がこれらを満たせば `stateBefore (j + 1)` の
tree にある `deliver_block_mem` / `deliver_block_mem_bodies`、配送の時刻が `γ` より前なら以後ずっと tree にあり受信の印が `γ` より前 `deliver_block_stamped`。条件を run の事実から外すことは残り)。
周回 150 の足場: `Proposal.lean`(提案の務め `proposalWith` が出すブロックは名前付きの親を提案者の bodies から引き、slot は提案者の slot、提案者は自分、運ぶ行は `inWindow` で絞った `selectRows` の部分集合なので
round の守りを通る `proposalWith_some` / `_parent` / `_slot` / `_proposer` / `_admissible`。tick が出すブロックは提案の務めが走った tick のもので `tick_block_shape` / `tick_block_fields`、
発行されたブロックは slot の提案の時刻に発行され提案者は `proposer' (slot)` で round の守りを通る `emits_block_fields`、honest な受信者への発行より後の配送の直前の slot はブロックの slot 以上
`emits_block_slot_le`。`Admits` の残り — 親が受信者の tree / bodies にあること、`preceq st.f b`、親の slot が小さいこと — は残り)。
周回 151 の足場: `ParentSlot.lean`(tree を育てるのは受理の守り `st.s < slot b` を通ったブロックだけなので、run のどの添字でも tree のブロックの slot は store の slot 以下
`stateBefore_slotInv`。時計は初期の 0 か前の自分の tick の時刻 `clock_origin` で、同じ tick は 2 度現れないので、提案の時刻の tick の直前の slot は提案の slot より小さい
`clock_lt_of_tick` / `slot_lt_of_tick`。したがって発行されたブロックの名前付きの親は発行の直前の提案者の bodies にあり `emits_block_parent_mem`、親の slot はブロックの slot より小さい
`emits_block_parent_slot`(`Admits.parent_slot`)。`Admits` の残り — 親が受信者の tree / bodies にあること、`preceq st.f b` — は残り)。
周回 152 の足場: `DeliveredBlock.lean`(`DeliveryWellFormed` は配送の直前の受信者の store で名前付きの親が bodies にありブロック自身は無いことを要求するので
`deliver_deps` / `deliver_not_processed`、bodies の消去は tree にあるので親は受信者の tree にある `deliver_parent_tree`(`Admits.parent_mem`)。周回 150・151 と合わせて、honest な受信者に発行より後に
配送された発行されたブロックは `Admits` のうち `extends_f`(`preceq st.f b`)を除く 4 つを setup と run の前提(`ScheduleWellFormed` / `DeliveryWellFormed` / `0 < Δ`)で満たし `emits_admits_of_extends`、`extends_f` の下で配送の後の tree にあり
`deliver_emitted_block_mem`、配送の時刻が `γ` より前なら以後ずっと受信の印が `γ` より前 `deliver_emitted_block_stamped`、tree に無かったなら bodies にもある `deliver_emitted_block_mem_bodies`。残りは `extends_f`)。
周回 153 の足場: `ProposerFinality.lean`(filtered tree は `finalizedDescendants f` で絞るので要素は `f` を延ばし `filtered_extends`、anchor は filtered tree の `activePrefix` か FG root(`j` か `f`)なので
`f ⪯ j` の下で `f` を延ばし `anchor_extends`、head は anchor から `ghost` で辿るので `getHeadWith_extends`、提案されたブロックの親は head なので `proposalWith_extends`。`f ⪯ j`(`FJ`)は
`updateFinality` の 2 つの分岐の守りが保ち、他のハンドラは `f` / `j` を変えないので、run のどの添字・時刻の読みでも前提なしに成り立つ `stateBefore_fj` / `readAt_fj`。したがって発行されたブロックは
発行の tick の直前の提案者の `f` を延ばし `emits_block_extends`、受信者の `f` がその祖先なら配送の後の tree にある `deliver_emitted_block_mem_of_finalized`。残りは受信者と提案者の finalized の順序)。
周回 154 の足場: `ReceiverFinality.lean`(`f` は run の添字について `preceq` で単調 `stateBefore_f_mono`、FG root は `f` を延ばすので、後の添字の `f` か FG root がブロックの祖先なら
それ以前のどの添字の `f` も祖先 `stateBefore_f_preceq_of_later` / `_of_root`、時刻 `d` の読みについても同じ `stateBefore_f_preceq_of_storeAt` / `_of_storeAt_root`。したがって発行されたブロックが
honest な受信者に発行より後、時刻 `d` 以下に配送され、時刻 `d` の読みの受信者の `f`(または FG root)がその祖先なら、時刻 `d` の読みの tree にある
`deliver_emitted_block_mem_storeAt` / `_of_root`、時刻 `< d` の読み `stateBeforeTime` の版 `deliver_emitted_block_mem_stateBeforeTime_of_root`。手書き `finalized_preceq_at_prefix_of_storeBeforeRoot_preceq` と `ProposalFinalizedBelowAtDeliveries` の組み立ての筋。
残りは honest な提案が締切の時刻の受信者の FG root を延ばすこと)。
残るのは `SleepyRegime` の下で `HonestSupport` の `vote` を示すこと(honest な committee の要素は `voteTime` に投票を発行し(投票者・slot まで `Voting.lean`)、その投票の head は
`stateBefore i` の発行者の store に時計を合わせたものの fork choice の head で(`Voting.emits_gfVote_head`)、
その head が honest な提案 `B` を延ばして slot が `s` 以下で、`ExecutionValid` / `PartialSynchrony` で投票とブロック `B` が honest な全ノードに
`supportCutoff` までに届く — 解決の印は投票とブロックの受信の印の大きい方)、2 つの honest なノードの読みの間の正準性
(手書きの安全の核 `eligible_compatible`: 一方の支持の投票が他方の遅い投票に入る `CrossView` の下で、同じ slot に両ノードで門を通る 2 ブロックは
互換)で確認の記録の一致・finalized との交差の互換・GST-zero の枝(`t0 = 0`)の finalized の一致(stable の記録と grade の候補 `frameSgCandidate`
の分岐についても同じ)を結ぶこと、honest な提案が適格な子の一意な最大になって `ghost_reaches` で選ばれること(`IncludedFrom` ×2)を
Goldfish の投票と確認の本体から示すこと。
-/

/-- claim `constants`: `SetupWellFormed` の数値の前提の下で定数が `ConstantsValid` を満たす。
手書き `Consensus.constants`(`constants_valid`)に当たる。 -/
theorem Proofs.Consensus.Spec.Claims.constants : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) («s» : Model.Consensus.Execution.Setup.Setup), Statements.Consensus.Spec.Claims.constants committee' proposer' «s» := by
  intro committee' proposer' s
  unfold Statements.Consensus.Spec.Claims.constants
  intro hwf
  exact Proofs.Consensus.Constants.constantsValid_of_setupWellFormed committee' proposer' s hwf

/-- claim `nested`: どの run でも finalized ⪯ stable ⪯ confirmed(`OutputOrder`)。前提 `SetupWellFormed ∧ RunDomain` は使わない。
手書き `Consensus.nested`(`nestedOutputs_holds`)に当たる。 -/
theorem Proofs.Consensus.Spec.Claims.nested : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) (awake' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Bool)) (newRoot' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Model.Consensus.Objects.Identifiers.BlockId)) («s» : Model.Consensus.Execution.Setup.Setup) («rho» : Model.Consensus.Execution.Run.NamedRun), Statements.Consensus.Spec.Claims.nested committee' proposer' awake' newRoot' «s» «rho» := by
  intro committee' proposer' awake' newRoot' s rho
  unfold Statements.Consensus.Spec.Claims.nested
  intro _
  exact Proofs.Consensus.Nested.outputOrder committee' proposer' awake' newRoot' s rho

/-- claim `finalizedMonotone`: `RunWellFormed`(の中の `EventsSorted`)の下で、honest なノードの finalized の読みは時刻について単調
(`MonotoneFrom … Finalized 0`)。前提のうち `SetupWellFormed` / `RunDomain` / `Idealization` は使わない。
手書き `Consensus.finalizedMonotone`(`accountable_finalizedMonotone` → `finalized_readAt_mono_of_sorted`)に当たる。 -/
theorem Proofs.Consensus.Spec.Claims.finalizedMonotone : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) (awake' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Bool)) (newRoot' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Model.Consensus.Objects.Identifiers.BlockId)) («s» : Model.Consensus.Execution.Setup.Setup) («rho» : Model.Consensus.Execution.Run.NamedRun), Statements.Consensus.Spec.Claims.finalizedMonotone committee' proposer' awake' newRoot' «s» «rho» := by
  intro committee' proposer' awake' newRoot' s rho
  unfold Statements.Consensus.Spec.Claims.finalizedMonotone
  intro h
  obtain ⟨_, hwf⟩ := h
  unfold Statements.Consensus.Spec.Conditions.RunWellFormed at hwf
  obtain ⟨⟨_, hsorted⟩, _⟩ := hwf
  exact Proofs.Consensus.FinalizedMonotone.monotoneFrom_finalized committee' proposer' awake' newRoot' s rho hsorted

/-- claim `certificatesAccountable`: run の前提なしに、root が衝突しない 2 つの名前付きブロックの導出状態が finalize した対象は
互換(`compatible`)か、2 本の chain の attestation の間に重み `2q − W` 以上の slashable な署名者集合がある(`Evidence`)。
前提のうち `SetupWellFormed` からは `normalizedValidators`(電子集団が正規集合であること)だけを使う。
手書き `Consensus.certificatesAccountable`(`unconditional_pureFinality` → `pureAccountableFinalitySafety` → `namedChainAccountableSafety`)に当たる。 -/
theorem Proofs.Consensus.Spec.Claims.certificatesAccountable : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) («s» : Model.Consensus.Execution.Setup.Setup) («c» : Model.Consensus.Objects.NamedBlocks.NamedBlock) («c2» : Model.Consensus.Objects.NamedBlocks.NamedBlock) («target» : Model.Consensus.Objects.Blocks.Block) («target2» : Model.Consensus.Objects.Blocks.Block), Statements.Consensus.Spec.Claims.certificatesAccountable committee' proposer' «s» «c» «c2» «target» «target2» :=
  Proofs.Consensus.CertificatesAccountable.certificatesAccountable

/-- claim `finalizedAccountable`: `SetupWellFormed ∧ RunDomain ∧ RunWellFormed` の下で、honest な 2 ノードの finalized の読みは互換か、
2 つの store の attestation の間に重み `2q − W` 以上の slashable な署名者集合がある(`AccountablySafeFrom … Finalized 0`)。
前提のうち `RunDomain` は使わず、`SetupWellFormed` からは `normalizedValidators` だけを、`RunWellFormed` からは `EventsSorted` と
`Idealization`(`NamedRootCollisionFree`)を使う。
手書き `Consensus.finalizedAccountable`(`wholeRunAccountableFinalitySafety` → `storeAccountableSafety_stateBefore`)に当たる。 -/
theorem Proofs.Consensus.Spec.Claims.finalizedAccountable : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) (awake' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Bool)) (newRoot' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Model.Consensus.Objects.Identifiers.BlockId)) («s» : Model.Consensus.Execution.Setup.Setup) («rho» : Model.Consensus.Execution.Run.NamedRun), Statements.Consensus.Spec.Claims.finalizedAccountable committee' proposer' awake' newRoot' «s» «rho» :=
  Proofs.Consensus.FinalizedAccountable.finalizedAccountable

/-- claim `finalizedSafe`: `SetupWellFormed ∧ RunDomain ∧ AccountableRegime`(`RunWellFormed ∧ SlashableBound`)の下で、honest な 2 ノードの
finalized の読みは常に互換(`AgreeFrom … Finalized 0`)。`finalizedAccountable` の本体の `Evidence` の分岐を `SlashableBound` で退ける。
手書き `Consensus.finalizedSafe`(`wholeRunFinalitySafety`)に当たる。 -/
theorem Proofs.Consensus.Spec.Claims.finalizedSafe : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) (awake' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Bool)) (newRoot' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Model.Consensus.Objects.Identifiers.BlockId)) («s» : Model.Consensus.Execution.Setup.Setup) («rho» : Model.Consensus.Execution.Run.NamedRun), Statements.Consensus.Spec.Claims.finalizedSafe committee' proposer' awake' newRoot' «s» «rho» :=
  Proofs.Consensus.FinalizedAccountable.finalizedSafe

/-- claim `honestNeverSlashed`: `SetupWellFormed ∧ RunDomain ∧ UnforgeableRun` の下で、honest な validator は slash されない
(どの 2 ノードのどの時刻の store の attestation の間にも、その validator の署名の slashable な組は無い)。前提のうち使うのは
`UnforgeableRun` の `UnforgeableSignatures`(carried)と `EventsSorted` だけ。
手書き `Consensus.honestNeverSlashed`(`validatorVoteSafety.attributed`)に当たる。 -/
theorem Proofs.Consensus.Spec.Claims.honestNeverSlashed : ∀ (committee' : (Nat → (NaruStd.Set Model.Consensus.Objects.Identifiers.ValidatorId))) (proposer' : (Nat → Model.Consensus.Objects.Identifiers.ValidatorId)) (awake' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Bool)) (newRoot' : (Model.Consensus.Objects.Identifiers.ValidatorId → Nat → Model.Consensus.Objects.Identifiers.BlockId)) («s» : Model.Consensus.Execution.Setup.Setup) («rho» : Model.Consensus.Execution.Run.NamedRun), Statements.Consensus.Spec.Claims.honestNeverSlashed committee' proposer' awake' newRoot' «s» «rho» :=
  Proofs.Consensus.HonestNeverSlashed.honestNeverSlashed
