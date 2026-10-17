import Properties.Basic
import Properties.Runs
import Properties.Premises
import Properties.Checkers
import Properties.Negative
import Properties.Report

/-!
# `Properties` — 有界検査(IDEAL.md C73 / C74)

生成 Model の具体的な run の上で、残りの claim の前提・結論の有界版と、C71 の証明の途中の中間命題を有限の horizon で判定する
検査器(用語「検査器」)と、用語「共通の run の記述」から固定 seed の決定的な擬似乱数で run を組み立てる生成器。
実行の入口は `lake exe naru_properties`(`PropertiesMain.lean`)、検査ドライバは `lake exe naru_test properties`。

- 生成 Model と `NaruStd` だけを import する(mathlib なし)。`Proofs` からは import されない(`naru_test proofs` が閉包で確かめる)。
- 実行テストは証明の前段の篩であり、証明の代用にはしない(証明状況 `naru proofs` の表示は変えない)。
- 判定は 4 区分(用語「有界検査」): 判定 / 前提不成立 / 判定外(期限が horizon を越える)/ 違反。
-/
