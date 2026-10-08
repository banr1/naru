import Naru

/-!
# `naru` CLI

- `naru compile` — `dsl/` 配下の全 `.naru` を検査し、Model を `generated/` に出力する(C1)。
- `naru compile [--out <dir>] <files...>` — 指定ファイルを検査する。`--out` があればそこに Model を出力する
  (無ければ検査だけ。反例ソースの検査や受理例の確認に使う)。
  診断があれば標準エラーに `file:line:col: error[E0xx]: …` を出して exit 1。
- `naru check-reject <file.naru> <Exxx>` — 反例が `Exxx` で拒否されることを検査する。
- `naru simulate <scenario.naru>` — 未実装(exit 2)。

出力は決定的: 同じソースと stdlib から同じバイト列を生成する。各生成ファイルの先頭コメントに
コンパイラ版(と `compiler/**/*.lean` の sha256)・stdlib 版(と `stdlib/Model/**/*.lean` の sha256)・ソースの sha256 を入れる。
`--out <dir>` は `<dir>/Model.lean` と `<dir>/Model/` を作り直す(他は触らない)。
-/

open Naru

/-- コンパイラの版。`lakefile.toml` の `version` と合わせる。 -/
def naruVersion : String := "0.1.0"

/-- Model 用 stdlib の版(`stdlib/Model`)。内容の sha256 も併記するので、版は人間向けの目印。 -/
def stdlibVersion : String := "0.1.0"

def stdlibDir : System.FilePath := "stdlib" / "Model"

def compilerDir : System.FilePath := "compiler"

def usage : String :=
  "usage: naru compile [--out <dir>] [files...]\n       naru check-reject <file.naru> <Exxx>\n       naru simulate <scenario.naru>"

/-- ディレクトリ配下の拡張子 `ext` のファイルをパス順に列挙する(決定的な順序)。 -/
def listFiles (dir : System.FilePath) (ext : String) : IO (List String) := do
  if !(← dir.isDir) then return []
  let all ← dir.walkDir
  let hits := all.filter (·.extension == some ext)
  let sorted := hits.qsort (fun a b => a.toString < b.toString)
  return sorted.toList.map (·.toString)

def defaultSources : IO (List String) := listFiles "dsl" "naru"

def hashFile (path : String) : IO String := do
  return sha256Hex (← IO.FS.readBinFile path)

/-- パス列の内容 hash を 1 つにまとめる(`path\n<sha256>\n` の連結の sha256)。 -/
def hashUnit (entries : List (String × String)) : String :=
  sha256HexOfString ("".intercalate (entries.map fun (p, h) => s!"{p}\n{h}\n"))

/-- Model を `outDir` に書く。`outDir/Model.lean` と `outDir/Model/` を作り直す(古い生成物を残さない)。 -/
def writeModel (outDir : System.FilePath) (files : Array (String × String)) : IO Unit := do
  let modelDir := outDir / "Model"
  if ← modelDir.isDir then IO.FS.removeDirAll modelDir
  let rootFile := outDir / "Model.lean"
  if ← rootFile.pathExists then IO.FS.removeFile rootFile
  IO.FS.createDirAll outDir
  for (rel, content) in files do
    let path := outDir / rel
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path content

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
    -- hash: ソース(与えられた順)と stdlib(パス順)
    let mut fileHashes : List (String × String) := []
    for f in files do fileHashes := fileHashes ++ [(f, ← hashFile f)]
    let stdlibFiles ← listFiles stdlibDir "lean"
    if stdlibFiles.isEmpty then
      IO.eprintln s!"naru compile: stdlib not found at {stdlibDir} (run from the repository root)"
      return 2
    let mut stdlibHashes : List (String × String) := []
    for f in stdlibFiles do stdlibHashes := stdlibHashes ++ [(f, ← hashFile f)]
    let compilerFiles ← listFiles compilerDir "lean"
    let mut compilerHashes : List (String × String) := []
    for f in compilerFiles do compilerHashes := compilerHashes ++ [(f, ← hashFile f)]
    let info : Backend.Model.Meta :=
      { compilerVersion := naruVersion, compilerHash := hashUnit compilerHashes, stdlibVersion,
        stdlibHash := hashUnit stdlibHashes, unitHash := hashUnit fileHashes, fileHashes }
    match Backend.Model.emitModel checked.core checked.recursions info with
    | .error d =>
      IO.eprintln d.render
      IO.eprintln "naru compile: 1 error(s)"
      return 1
    | .ok generated =>
      writeModel out generated
      IO.println s!"compiled {checked.mods.size} module(s); wrote {generated.size} file(s) under {out}/"
      return 0

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
