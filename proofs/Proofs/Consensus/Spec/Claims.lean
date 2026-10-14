import Statements.Consensus.Spec.Claims
import Mathlib.Tactic

/-!
# consensus の証明義務の入口(IDEAL.md C71)

`generated/obligations.json` の 14 件 — claim bundle `Consensus.Spec.Claims.Consensus` と 13 claims(`constants` / `nested` /
`certificatesAccountable` / `finalizedAccountable` / `finalizedMonotone` / `honestNeverSlashed` / `finalizedSafe` / `available` /
`confirmedLive` / `stableLive` / `stableIncludedFast` / `finalized` / `stableAsynchronyResilient`)— の theorem
`Proofs.Consensus.Spec.Claims.<名前> : <義務の型>` をここに置き、補題は `Proofs/Consensus/` 配下のモジュールに分けてここから import する。
各 theorem の束縛行 `-- naru-obligation: Consensus.Spec.Claims.<名前> sha256:<束縛 hash>` はこのファイルの先頭に並べる(`proofs/README.md`)。

まだ 1 件も証明していない(`lake exe naru proofs` は 14 件を `missing` と表示する)。手書き証明(`third_party/verified-consensus/DecoupledConsensusProofs`、
基準コミット)は構成・補題の分割・証明の筋を読んで参照するが import しない。
-/
