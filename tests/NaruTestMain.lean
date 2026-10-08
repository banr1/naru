import NaruTest

/-!
# `naru_test` — エディタ対応(C16〜C18)の検査ドライバ

リポジトリのルートで `lake exe naru_test <群>` と実行する。群は `grammar`(C16)/ `zed`(C17)/ `lsp`(C18)。
各群は検査項目ごとに `ok: …` / `FAIL: …` を標準出力に出し、すべて ok なら exit 0、1 つでも FAIL なら exit 1。
未実装の群は exit 2。
-/

def usage : String := "usage: naru_test <grammar|zed|lsp>"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["grammar"] => NaruTest.Grammar.run
  | ["zed"] =>
    IO.eprintln "naru_test zed: not implemented yet"
    return 2
  | ["lsp"] =>
    IO.eprintln "naru_test lsp: not implemented yet"
    return 2
  | _ =>
    IO.eprintln usage
    return 2
