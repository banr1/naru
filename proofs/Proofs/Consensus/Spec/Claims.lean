-- naru-obligation: Consensus.Spec.Claims.constants sha256:773e687f0e7a8283a366dd44125735d9960ff100daecb3c31b6c0e8018f5da6c
-- naru-obligation: Consensus.Spec.Claims.nested sha256:773e687f0e7a8283a366dd44125735d9960ff100daecb3c31b6c0e8018f5da6c
-- naru-obligation: Consensus.Spec.Claims.finalizedMonotone sha256:773e687f0e7a8283a366dd44125735d9960ff100daecb3c31b6c0e8018f5da6c
import Statements.Consensus.Spec.Claims
import Proofs.Consensus.Constants
import Proofs.Consensus.Nested
import Proofs.Consensus.FinalizedMonotone
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
`EventsSorted` の下で `filter (≤ t)` が `filter (≤ t2)` の接頭辞であること(`Runs.lean` / `Tables.lean`)から、`preceq` の推移律(`Blocks.lean`)で結ぶ)。
残りの 10 claims と bundle `Consensus` は未証明(`lake exe naru proofs` が `missing` と表示する)。手書き証明
(`third_party/verified-consensus/DecoupledConsensusProofs`、基準コミット)は構成・補題の分割・証明の筋を読んで参照するが import しない。
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
