import Naru

/-!
# `naru` CLI

- `naru compile` — `dsl/` 配下の全 `.naru` を検査し、Model(`generated/Model`)と Statements(`generated/Statements`)を
  `generated/` に出力する(C1)。
- `naru compile [--out <dir>] <files...>` — 指定ファイルを検査する。`--out` があればそこに Model と Statements を出力する
  (無ければ検査だけ。反例ソースの検査や受理例の確認に使う)。
  診断があれば標準エラーに `file:line:col: error[E0xx]: …` を出して exit 1。
- `naru check-reject <file.naru> <Exxx>` — 反例が `Exxx` で拒否されることを検査する。
- `naru lsp` — 標準入出力で言語サーバー(LSP)として動き、コンパイラの診断を返す(C18。`Naru/Lsp.lean`)。
- `naru simulate <dsl/…/scenario.naru>` — `dsl/` 全体を検査して `generated/` に Model を作り直し(`compile` と同じ)、
  そのファイルの scenario を実行する `generated/Simulate.lean`(`main`)を書いて `lake build naru_simulate` →
  `.lake/build/bin/naru_simulate` を実行する(C7。「naru を実行する」= 生成 Lean を native 実行する)。
  出力は scenario の `observe` の行(observer の値を `Repr` で表示)。

出力は決定的: 同じソースと stdlib から同じバイト列を生成する。各生成ファイルの先頭コメントに
コンパイラ版(と `compiler/**/*.lean` の sha256)・stdlib 版(と `stdlib/Model/**/*.lean` の sha256)・ソースの sha256 を入れる。
`--out <dir>` は `<dir>/Model.lean` と `<dir>/Model/`、`<dir>/Statements.lean` と `<dir>/Statements/` を作り直す(他は触らない)。
-/

open Naru

/-- コンパイラの版。`lakefile.toml` の `version` と合わせる。 -/
def naruVersion : String := "0.1.0"

/-- Model 用 stdlib の版(`stdlib/Model`)。内容の sha256 も併記するので、版は人間向けの目印。 -/
def stdlibVersion : String := "0.1.0"

def stdlibDir : System.FilePath := "stdlib" / "Model"

def compilerDir : System.FilePath := "compiler"

def usage : String :=
  "usage: naru compile [--out <dir>] [files...]\n       naru check-reject <file.naru> <Exxx>\n       naru lsp\n       naru simulate <dsl/.../scenario.naru>"

-- `listFiles`(ディレクトリ配下の `.naru` / `.lean` の列挙)は `Naru.Driver`(言語サーバーも使う)。

def defaultSources : IO (List String) := listFiles "dsl" "naru"

def hashFile (path : String) : IO String := do
  return sha256Hex (← IO.FS.readBinFile path)

/-- パス列の内容 hash を 1 つにまとめる(`path\n<sha256>\n` の連結の sha256)。 -/
def hashUnit (entries : List (String × String)) : String :=
  sha256HexOfString ("".intercalate (entries.map fun (p, h) => s!"{p}\n{h}\n"))

/-- 生成物を `outDir` に書く。`outDir/Model.lean` と `outDir/Model/`、`outDir/Statements.lean` と `outDir/Statements/` を
作り直す(古い生成物を残さない)。 -/
def writeGenerated (outDir : System.FilePath) (files : Array (String × String)) : IO Unit := do
  for sub in ["Model", "Statements"] do
    let dir := outDir / sub
    if ← dir.isDir then IO.FS.removeDirAll dir
    let rootFile := outDir / (sub ++ ".lean")
    if ← rootFile.pathExists then IO.FS.removeFile rootFile
  IO.FS.createDirAll outDir
  for (rel, content) in files do
    let path := outDir / rel
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path content

/-- 生成ファイルのヘッダに入れる版と hash(ソースは与えられた順、stdlib とコンパイラはパス順)。
stdlib が見つからなければ `none`(リポジトリのルートで実行していない)。 -/
def buildMeta (who : String) (files : List String) : IO (Option Backend.Model.Meta) := do
  let mut fileHashes : List (String × String) := []
  for f in files do fileHashes := fileHashes ++ [(f, ← hashFile f)]
  let stdlibFiles ← listFiles stdlibDir "lean"
  if stdlibFiles.isEmpty then
    IO.eprintln s!"{who}: stdlib not found at {stdlibDir} (run from the repository root)"
    return none
  let mut stdlibHashes : List (String × String) := []
  for f in stdlibFiles do stdlibHashes := stdlibHashes ++ [(f, ← hashFile f)]
  let compilerFiles ← listFiles compilerDir "lean"
  let mut compilerHashes : List (String × String) := []
  for f in compilerFiles do compilerHashes := compilerHashes ++ [(f, ← hashFile f)]
  return some
    { compilerVersion := naruVersion, compilerHash := hashUnit compilerHashes, stdlibVersion,
      stdlibHash := hashUnit stdlibHashes, unitHash := hashUnit fileHashes, fileHashes }

/-- 検査済みの単位から Model と Statements を生成して `out` に書く(`compile` と `simulate` が共用)。`who` は診断の接頭辞。 -/
def generateLean (who : String) (out : System.FilePath) (checked : Checked)
    (info : Backend.Model.Meta) : IO UInt32 := do
  let fail (d : Diagnostic) : IO UInt32 := do
    IO.eprintln d.render
    IO.eprintln s!"{who}: 1 error(s)"
    return 1
  match Backend.Model.emitModel checked.core checked.recursions info with
  | .error d => fail d
  | .ok model =>
    match Backend.Statements.emitStatements checked.core checked.recursions info with
    | .error d => fail d
    | .ok statements =>
      writeGenerated out (model ++ statements)
      IO.println s!"compiled {checked.mods.size} module(s); wrote {model.size} Model file(s) and {statements.size} Statements file(s) under {out}/"
      return 0

def runCompile (args : List String) : IO UInt32 := do
  -- `--out <dir>` を取り出す
  let mut outDir : Option String := none
  let mut files : List String := []
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--out" :: dir :: more =>
      outDir := some dir
      rest := more
    | "--out" :: [] =>
      IO.eprintln "naru compile: `--out` needs a directory"
      return 2
    | f :: more =>
      files := files ++ [f]
      rest := more
    | [] => pure ()
  let explicit := !files.isEmpty
  if !explicit then
    files ← defaultSources
    if outDir.isNone then outDir := some "generated"
  if files.isEmpty then
    IO.eprintln "naru compile: no .naru sources given and none found under dsl/"
    return 2
  let (diags, checked) ← compileFiles files
  if !diags.isEmpty then
    for d in diags do IO.eprintln d.render
    IO.eprintln s!"naru compile: {diags.size} error(s)"
    return 1
  match outDir with
  | none =>
    IO.println s!"checked {checked.mods.size} module(s)"
    return 0
  | some out =>
    let some info ← buildMeta "naru compile" files | return 2
    generateLean "naru compile" out checked info

/-- scenario の実行。`file` は `dsl/` 配下の `.naru`(検査の単位は `dsl/` 全体 = `generated/` の元)。
1. 単位を検査し(診断があれば exit 1)、`generated/` に Model と Statements を作り直す(`compile` と同じ)。
2. そのファイルの scenario(1 つ以上。無ければ exit 2)を順に `NaruStd.runScenario` で表示する
   `generated/Simulate.lean`(`main`)を書く(追跡対象外)。
3. `lake build naru_simulate`(lakefile の lean_exe。Model を native にビルドする)→ `.lake/build/bin/naru_simulate`
   を実行し、その exit code で終わる。 -/
def runSimulate (file : String) : IO UInt32 := do
  -- `./dsl/…` とリポジトリの絶対パス `<cwd>/dsl/…` は `dsl/…` に正規化する
  let cwdPrefix := (← IO.currentDir).toString ++ "/"
  let rel :=
    if file.startsWith "./" then (file.drop 2).toString
    else if file.startsWith cwdPrefix then (file.drop cwdPrefix.length).toString
    else file
  if !(rel.startsWith "dsl/") then
    IO.eprintln s!"naru simulate: `{file}` is not under dsl/; simulate runs the scenarios of a dsl/ source (the unit that `compile` writes to generated/)"
    return 2
  let files ← defaultSources
  if !files.contains rel then
    IO.eprintln s!"naru simulate: `{rel}` not found under dsl/"
    return 2
  let (diags, checked) ← compileFiles files
  if !diags.isEmpty then
    for d in diags do IO.eprintln d.render
    IO.eprintln s!"naru simulate: {diags.size} error(s)"
    return 1
  let some m := checked.mods.find? (·.file == rel)
    | IO.eprintln s!"naru simulate: `{rel}` was not read"; return 2
  let scenarios := m.decls.filter (·.kind == .scenario)
  if scenarios.isEmpty then
    IO.eprintln s!"naru simulate: `{rel}` declares no scenario"
    return 2
  let some info ← buildMeta "naru simulate" files | return 2
  let code ← generateLean "naru simulate" "generated" checked info
  if code != 0 then return code
  let names := scenarios.toList.map (·.name)
  let calls := names.map fun n =>
    s!"  NaruStd.runScenario \"{n}\" {Backend.Model.leanName (renderPath (m.name ++ [n]))}\n"
  -- Model と同じヘッダ(コンパイラ版・stdlib 版・ソース hash: C1)を付ける
  let runner :=
    Backend.Model.header info rel ((info.fileHashes.lookup rel).getD "") ++
    s!"-- naru simulate: runs the scenario(s) of {rel} and prints their `observe` lines (`lake build naru_simulate && .lake/build/bin/naru_simulate`).\n" ++
    "import Model\n\ndef main : IO Unit := do\n" ++ "".intercalate calls
  IO.FS.writeFile ("generated" / "Simulate.lean") runner
  IO.println s!"naru simulate: building generated/Simulate.lean (scenario {", ".intercalate names} of {rel}) with `lake build naru_simulate`"
  let build ← IO.Process.output { cmd := "lake", args := #["build", "naru_simulate"] }
  if build.exitCode != 0 then
    IO.eprint build.stdout
    IO.eprint build.stderr
    IO.eprintln s!"naru simulate: `lake build naru_simulate` failed (exit {build.exitCode})"
    return 1
  let child ← IO.Process.spawn
    { cmd := ".lake/build/bin/naru_simulate", args := #[], stdin := .inherit, stdout := .inherit, stderr := .inherit }
  child.wait

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
  | ["lsp"] => Lsp.serve naruVersion
  | ["simulate", file] => runSimulate file
  | _ =>
    IO.eprintln usage
    return 2
