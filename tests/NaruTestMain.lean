import NaruTest

/-!
# `naru_test` — エディタ対応(C16〜C19)・golden test(C10)・生成 Statements(C8 / C9)・リポジトリの構成(C21 / C23 / C25)・
非対話の回帰一式(C36)の検査ドライバ

リポジトリのルートで `lake exe naru_test <群>` と実行する。群は `grammar`(C16)/ `zed`(C17)/ `lsp`(C18)/
`zed-install`(C19。起動中の人間の Zed を `osascript` で操作して Dev Extension を入れる)/ `golden [--finality-horizon N]`(C10。
手書き Model と生成 Model を 1 つの Lean プログラムで実行して MISMATCH を数える。N は FinalityLiveness の prefix の horizon、既定 100 = C10)/
`statements`(C8 / C9。生成 Statements の import 閉包と `sorry`、claim surface の 13 の欄名)/ `repo [--base-commit <sha>]`(C21 / C23 / C25。
README・submodule・docs。基準コミットは引数、無ければ IDEAL.md の前提から読む)/ `regression`(C36。受理例・反例・C34 の意味・C1 の決定性・
C6 / C8 のビルド・C7 の simulate・C24 の設定・上の各群(zed-install を除く)・C10 の golden を 1 コマンドで順に走らせる非対話の回帰一式。約 12 分)。
各群は検査項目ごとに `ok: …` / `FAIL: …` を標準出力に出し、すべて ok なら exit 0、1 つでも FAIL なら exit 1。
-/

def usage : String := "usage: naru_test <grammar|zed|lsp|zed-install|golden [--finality-horizon N]|statements|repo [--base-commit <sha>]|regression>"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["grammar"] => NaruTest.Grammar.run
  | ["zed"] => NaruTest.Zed.run
  | ["lsp"] => NaruTest.Lsp.run
  | ["zed-install"] => NaruTest.ZedInstall.run
  | ["statements"] => NaruTest.Statements.run
  | ["repo"] => NaruTest.Repo.run none
  | ["repo", "--base-commit", sha] => NaruTest.Repo.run (some sha)
  | ["golden"] => NaruTest.Golden.run NaruTest.Golden.c10Horizon
  | ["golden", "--finality-horizon", n] =>
    match n.toNat? with
    | some h => NaruTest.Golden.run h
    | none => IO.eprintln usage; return 2
  | ["regression"] => NaruTest.Regression.run
  | _ =>
    IO.eprintln usage
    return 2
