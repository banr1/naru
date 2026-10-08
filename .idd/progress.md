# 進捗台帳

<!-- 周回エージェントが保守する。IDEAL.md「実現する状態」の各条件を 1 行ずつ。
     状態は unmet / met / blocked の 3 値。met にできるのは証拠を記録した周回だけ。
     証拠列は、最初に現れる出典を idd が読み、出典の種類を条件の検証の主体と照合する:
       cycle N: <コマンド> exit 0   周回 N(1 以上、現在の周回以下)で検証が通った
       observed N: <要点>           周回 N のエージェントが実画面の観測(画面操作の道具・スクリーンショット等)で検証した。
                                    記録 NNNN.md の「## 検証」表に要点つきの observed 行が要る
       human <at>: <要点>           台帳(journal.jsonl)の human resume 行 <at> を出典とする人間の確認。IDEAL.md の
                                    当該条件の検証が 人間 で始まる(人間に委ねた)条件だけの出典
     検証の主体は既定でエージェント: 検証が 人間 で始まらない条件に human を引いても、人間 で始まる条件に cycle /
     observed を引いても、完了の検算が退ける(台帳の不備)。
     idd の外で作られた commit(journal.jsonl の external_commits 行)より前の出典は失効する — 検証し直して取り直す。
     対象ファイル(.idd/ の外)を変えた周回 C より前の出典も失効する: cycle N: は N < C、observed N: は N ≤ C、
     human <at>: は C より前の resume のもの。この周回で変えたなら C はこの周回(コマンド検証だけがこの周回で取り直せる)。
     IDEAL.md が変わったら(sha が下と違う)条件を投影し直し、消えた条件は行ごと消す。
     階層は 必須 / 望ましい。ID 列は IDEAL.md の番号を装飾なしで書く(`C1`。`**C1**` にしない)。
     列は 5 つ固定: | ID | 階層 | 条件 | 状態 | 証拠 |。idd はこの形で met / unmet を数え、完了を検算する。 -->

ideal_sha: 045a3d5159d54f0ac55790766d2637f2951c03c6ec6da9b16cb2e8b6c5f2c38e

| ID | 階層 | 条件 | 状態 | 証拠 |
|----|------|------|------|------|
| C1 | 必須 | 同じ naru ソースから生成される Lean は byte-for-byte 同一で、各生成ファイルの先頭にコンパイラ版・stdlib 版・ソース hash が入っている(`lake exe naru compile` を 2 回実行して `generated/` の sha256 が一致し、先頭コメントに 3 つの値) | met | cycle 4: lake exe naru compile exit 0 (2 回実行し `find generated -type f \| sort \| xargs shasum -a 256` が 2 ファイルとも一致(diff 空)。各ファイルの先頭 5 行に `naru-compiler: 0.1.0 sha256:…`・`naru-stdlib: 0.1.0 sha256:…`・`naru-source: <file> sha256:…`(`shasum -a 256` の値と一致)を含む。対象ソースは `dsl/` の移植(周回 4 時点では `Consensus/Objects/Identifiers.naru` の 1 ファイル。移植が進む周回ごとに取り直す)) |
| C2 | 必須 | runtime 宣言から spec 宣言への依存(phase leak)はコンパイルエラーになる(`tests/reject/phase_leak.naru` で exit 非 0、`E001`) | met | cycle 4: lake exe naru check-reject tests/reject/phase_leak.naru E001 exit 0 (compile と同じ経路で拒否(exit 1 相当)と `error[E001]` を検査する。生の `lake exe naru compile tests/reject/phase_leak.naru` は exit 1 で E001 を出力。メソッド記法経由の `tests/reject/phase_leak_method.naru` も同様に PASS) |
| C3 | 必須 | 無条件の選択(choose / pick / set.first / set.toList 等)はコンパイルエラーになる(`tests/reject/choose.naru` で exit 非 0、`E003`) | met | cycle 4: lake exe naru check-reject tests/reject/choose.naru E003 exit 0 (生の `lake exe naru compile tests/reject/choose.naru` は exit 1 で E003 を 4 箇所(`Set.choose` / `Set.first?` / 自由関数 `pick` / `Set.find?`)出力。`set.toList` は C5 の E004 で拒否) |
| C4 | 必須 | 停止性を確認できない再帰はコンパイルエラーになる(`tests/reject/non_total.naru` で exit 非 0、`E002`) | met | cycle 4: lake exe naru check-reject tests/reject/non_total.naru E002 exit 0 (生の `lake exe naru compile tests/reject/non_total.naru` は exit 1 で E002 を 10 箇所出力。受理するのは構造的再帰と保護された fuel だけ(`compiler/SYNTAX.md`「再帰」)。受理した形は backend が Lean の停止性証明に落とし、`tests/accept/backend.naru` / `smoke.naru` の生成コードが Lean で通ることを周回 4 で確認) |
| C5 | 必須 | 順序指定の無い Set → List 変換はコンパイルエラーになる(`tests/reject/order_loss.naru` で exit 非 0、`E004`) | met | cycle 4: lake exe naru check-reject tests/reject/order_loss.naru E004 exit 0 (生の `lake exe naru compile tests/reject/order_loss.naru` は exit 1 で E004 を 3 箇所(`Set.toList` / `by` 無しの `sort(set)` / `Set.fold`)出力) |
| C6 | 必須 | 生成 Model は Lean としてビルドでき、noncomputable / unsafe / axiom / sorry / 無制限の partial を含まない(lake target のビルド exit 0、grep 0 件) | met | cycle 4: lake build Model exit 0 (lean_lib `Model`(`generated/`、9 jobs)。`grep -rwE 'noncomputable\|unsafe\|axiom\|sorry\|partial' generated/Model` は 0 件。対象は周回 4 時点の `dsl/` の移植(1 ファイル)から生成した Model。移植が進む周回ごとに取り直す) |
| C7 | 必須 | 生成 Model は native 実行でき、scenario をシミュレーションして observer の値を表示する(`lake exe naru simulate dsl/scenarios/basic.naru` が exit 0 で time / node / confirmed / stable / finalized を出力) | unmet | simulate 未実装(exit 2)。Model backend は scenario / observer を `def` に落とすので、実行の経路(生成 Model を import する runner と `lake exe`)と `dsl/scenarios/basic.naru`(Event / Run の stdlib を含む)が次に要る |
| C8 | 必須 | 生成 Statements は生成 Model だけを import し(Proofs を import しない)、sorry を含まない(import 閉包の検査スクリプト exit 0、grep 0 件) | unmet | Statements backend 未実装(Core IR には spec 宣言も入っている) |
| C9 | 必須 | 生成 Statements の公開 claim surface は naru ソースの claim bundle と一致し、verified-consensus の 13 claims と同名(surface shape の検査スクリプトが 13 のフィールド名を列挙して exit 0) | unmet | Statements backend・検査スクリプト未実装(claim bundle の項目が claim であることの検査 E016 は周回 2 で実装) |
| C10 | 必須 | 具体的な fixture 上で手書き Model と生成 Model の confirmed / stable / finalized の読みと emitted objects が一致する(golden test が Witnesses の 4 run と naru scenario 3 本以上に対し MISMATCH 0 件で exit 0) | unmet | 移植は `dsl/Consensus/Objects/Identifiers.naru`(20 行)から着手。golden test 未実装 |
| C11 | 望ましい | naru のユーザーは Lean 固有の概念を扱わない(予約語一覧・構文エラーメッセージ・`dsl/` の移植ソースに Fintype / DecidableEq / Finset / Classical / termination_by / Prop / theorem / by が現れない) | unmet | 未検証。注意: 前提の `sort(set, by = …)` と `by` の grep 0 件が衝突する(周回 2 の申し送り参照) |
| C12 | 望ましい | capability の無い型への `==` や `<` はコンパイルエラーになる(`tests/reject/missing_capability.naru` で exit 非 0、`E005`) | met | cycle 4: lake exe naru check-reject tests/reject/missing_capability.naru E005 exit 0 (生の `lake exe naru compile tests/reject/missing_capability.naru` は exit 1 で E005 を 3 箇所(`==` / `<` / `Set.contains`)出力) |
| C13 | 望ましい | Model 内での無限量化の結果による分岐はコンパイルエラーになる(`tests/reject/infinite_quantification.naru` で exit 非 0、`E006`) | unmet | runtime 宣言内の `forall` / `exists` を E006 にする検査は周回 2 で実装済み。反例 `tests/reject/infinite_quantification.naru` が未作成 |
| C14 | 望ましい | runtime の条件が classical な命題の決定に依存するとコンパイルエラーになる(`tests/reject/classical_decision.naru` で exit 非 0、`E007`) | unmet | E007 未実装 |
| C15 | 望ましい | 人間のレビュー面(Interface・Constants・Claim Bundle)は生成 Statements の 1 ファイル `generated/Statements/Review.lean` に集約されている | unmet | Statements backend 未実装 |
