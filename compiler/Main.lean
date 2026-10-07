import Naru

/-!
# `naru` CLI

- `naru compile [files...]` — 指定ファイル(省略時は `dsl/` 配下の全 `.naru`)を検査する。
  診断があれば標準エラーに `file:line:col: error[E0xx]: …` を出して exit 1。
- `naru simulate <scenario.naru>` — 未実装(exit 2)。
-/

open Naru

def usage : String :=
  "usage: naru compile [files...]\n       naru check-reject <file.naru> <Exxx>\n       naru simulate <scenario.naru>"

/-- `dsl/` 配下の `.naru` をパス順に列挙する(決定的な順序)。 -/
def defaultSources : IO (List String) := do
  let dir : System.FilePath := "dsl"
  if !(← dir.isDir) then return []
  let all ← dir.walkDir
  let naru := all.filter (·.extension == some "naru")
  let sorted := naru.qsort (fun a b => a.toString < b.toString)
  return sorted.toList.map (·.toString)

def runCompile (args : List String) : IO UInt32 := do
  let files ← if args.isEmpty then defaultSources else pure args
  if files.isEmpty then
    IO.eprintln "naru compile: no .naru sources given and none found under dsl/"
    return 2
  let (diags, mods) ← compileFiles files
  if diags.isEmpty then
    IO.println s!"compiled {mods.size} module(s)"
    return 0
  else
    for d in diags do IO.eprintln d.render
    IO.eprintln s!"naru compile: {diags.size} error(s)"
    return 1

/-- 反例ソースの検査。`compile <file>` と同じ経路を走らせ、診断があって(= compile なら exit 1)
その中に `code` があれば PASS(exit 0)、そうでなければ FAIL(exit 1)。
`tests/reject/*.naru` の条件(C2〜C5、C12〜C14)の証拠をこの 1 コマンドで取る。 -/
def runCheckReject (file code : String) : IO UInt32 := do
  let (diags, _) ← compileFiles [file]
  for d in diags do IO.eprintln d.render
  let compileExit : UInt32 := if diags.isEmpty then 0 else 1
  if compileExit == 0 then
    IO.println s!"FAIL: {file} compiled successfully (expected rejection with {code})"
    return 1
  if !(diags.any (·.code == code)) then
    IO.println s!"FAIL: {file} was rejected (compile exit {compileExit}) but no diagnostic has {code}"
    return 1
  IO.println s!"PASS: {file} rejected (compile exit {compileExit}) with {code}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | "compile" :: rest => runCompile rest
  | ["check-reject", file, code] => runCheckReject file code
  | "simulate" :: _ =>
    IO.eprintln "naru simulate: not implemented yet"
    return 2
  | _ =>
    IO.eprintln usage
    return 2
