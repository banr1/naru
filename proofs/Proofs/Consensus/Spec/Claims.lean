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
`Outputs.lean`(出力 `getStable` / `getConfirmed` の単調性と一致を欄 `f` / 記録の事実と regime の事実 `StableBelowConfirmed`
(stable の記録 ⪯ 確認の記録)に還元する `safeFrom_stable_of_fields` / `safeFrom_confirmed_of_fields`)。残るのは `SleepyRegime` の下で
記録の一致・記録と finalized の交差の互換・`StableBelowConfirmed`・finalized の一致(と `IncludedFrom`)を Goldfish の投票と確認の本体から示すこと。
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
