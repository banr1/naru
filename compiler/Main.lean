import Naru

/-!
# `naru` CLI

- `naru compile` — `naru.toml`(リポジトリのルート。`Naru/Config.lean`)の各ソースルート配下の全 `.naru` を 1 つのコンパイル単位
  として検査し、Model(`<generated>/Model`)と Statements(`<generated>/Statements`)を生成先に出力する(C1)。
- `naru compile [--out <dir>] <files...>` — 指定ファイルを検査する。`--out` があればそこに Model と Statements を出力する
  (無ければ検査だけ。反例ソースの検査や受理例の確認に使う)。
  診断があれば標準エラーに `file:line:col: error[E0xx]: …` を出して exit 1。
- `naru check-reject <file.naru> <Exxx>` — 反例が `Exxx` で拒否されることを検査する。
- `naru lsp` — 標準入出力で言語サーバー(LSP)として動き、コンパイラの診断(C18)とホバー(C29)・定義ジャンプ(C30)・補完(C31)を返す(`Naru/Lsp.lean`)。
- `naru simulate <ソースルート配下の scenario.naru>` — そのルート全体を検査して生成先に Model を作り直し(`compile` と同じ)、
  そのファイルの scenario を実行する `.lake/naru/simulate/Simulate.lean`(`main`)を書いて `lake build naru_simulate` →
  `.lake/build/bin/naru_simulate` を実行する(C7。「naru を実行する」= 生成 Lean を native 実行する。C26: 生成先には
  `compile` の決定的な出力だけを置く)。出力は scenario の `observe` の行(observer の値を `Repr` で表示)。

出力は決定的: 同じソースと stdlib から同じバイト列を生成する。各生成ファイルの先頭コメントに
コンパイラ版(と `compiler/**/*.lean` の sha256)・stdlib 版(と `stdlib/Model/**/*.lean` の sha256)・ソースの sha256 を入れる。
ソースのパスはソースルートからの相対で書く(ルートのディレクトリ名を含まない: C1 / C24)。
生成先(`naru.toml` の `generated` も `--out <dir>` も同じ `writeGenerated`)は `Model.lean` と `Model/`、`Statements.lean` と `Statements/` を
丸ごと作り直す(他は触らない)ので、旧パスの生成物や、以前の規則で出ていた不要なファイルは残らない(C38)。Model ファイルは runtime 宣言を
出力するモジュールにだけ、Statements ファイルは spec 宣言のあるモジュールにだけでき、ルートの集約ファイルは存在するものだけを import する。

ホーム(リポジトリのルート)と Lake: `naru.toml` は cwd のものを読む。stdlib / コンパイラ(ヘッダの hash)、`naru simulate` の実行入口と
`lake build`、Lake が読む生成ソースの link は、実行ファイル `<ホーム>/.lake/build/bin/naru` の場所から求めたホームのもの(`findHome`)。
`naru.toml` の `generated` は生成先だけでなく Lake にも反映する(C24): `compile` / `simulate` は書き終えた生成先への symlink を
`<ホーム>/.lake/naru/generated`(lakefile の lean_lib `Model` / `Statements` の `srcDir`)に置くので、`lake build Model` / `Statements` /
`naru_simulate` は現在の設定の生成先を読む(lakefile の手修正は要らない)。別のディレクトリの `naru.toml` のプロジェクトでも、そこを cwd にして
`<ホーム>/.lake/build/bin/naru compile` / `simulate` と直接呼べる(`tests/config_change/` の設定変更プロジェクトはこの形で検査する)。
-/

open Naru

/-- コンパイラの版。`lakefile.toml` の `version` と合わせる。 -/
def naruVersion : String := "0.1.0"

/-- Model 用 stdlib の版(`stdlib/Model`)。内容の sha256 も併記するので、版は人間向けの目印。 -/
def stdlibVersion : String := "0.1.0"

def stdlibDir : System.FilePath := "stdlib" / "Model"

def compilerDir : System.FilePath := "compiler"

/-- `naru simulate` が書く実行入口(ホーム相対。追跡対象外。C26)。 -/
def simulateDir : System.FilePath := ".lake" / "naru" / "simulate"

/-- Lake が読む生成ソース(ホーム相対。lakefile の lean_lib `Model` / `Statements` の `srcDir`)。`compile` / `simulate` が有効な生成先への
symlink にする(C24)。 -/
def lakeGeneratedLink : System.FilePath := ".lake" / "naru" / "generated"

/-- `naru simulate` が Lake にビルドさせる実行ファイル(ホーム相対)。 -/
def simulateBin : System.FilePath := ".lake" / "build" / "bin" / "naru_simulate"

/-- naru のホーム(リポジトリのルート)。実行ファイル `<ホーム>/.lake/build/bin/naru` の場所から求める。 -/
structure Home where
  /-- ホームの実際のパス(絶対)。 -/
  dir : System.FilePath
  /-- cwd がホームそのものか(そのときはホーム相対のパスをそのまま使い、出力の形を変えない)。 -/
  atHome : Bool

/-- ホームを求める。stdlib が無ければ(実行ファイルが `lake build naru` の置く場所に無い)説明して none。 -/
def findHome (who : String) : IO (Option Home) := do
  let exe ← IO.FS.realPath (← IO.appPath)
  -- <ホーム>/.lake/build/bin/naru
  let some dir := exe.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | IO.eprintln s!"{who}: cannot locate the naru home from {exe}"; return none
  if !(← (dir / stdlibDir).isDir) then
    IO.eprintln s!"{who}: stdlib not found at {dir / stdlibDir} (the executable must be <home>/.lake/build/bin/naru, built by `lake build naru` in the repository)"
    return none
  let cwd ← IO.FS.realPath "."
  return some { dir, atHome := cwd == dir }

/-- ホーム相対のパス `rel` を cwd から使えるパスにする。 -/
def Home.path (h : Home) (rel : System.FilePath) : System.FilePath := if h.atHome then rel else h.dir / rel

/-- ホーム配下のパスをホーム相対の表示にする(ヘッダの stdlib / コンパイラの hash は cwd に依らずホーム相対のパスで計算する)。 -/
def Home.display (h : Home) (p : String) : String :=
  let pre := h.dir.toString ++ "/"
  if p.startsWith pre then (p.drop pre.length).toString else p

def usage : String :=
  "usage: naru compile [--out <dir>] [files...]\n       naru check-reject <file.naru> <Exxx>\n       naru lsp\n       naru simulate <scenario.naru under a source root of naru.toml>"

-- `listFiles`(ディレクトリ配下の `.naru` / `.lean` の列挙)は `Naru.Driver`(言語サーバーも使う)。

/-- `naru.toml`(cwd)を読む。無ければ・壊れていれば説明して none。 -/
def loadConfig (who : String) : IO (Option Config) := do
  let path : System.FilePath := configFileName
  if !(← path.pathExists) then
    IO.eprintln s!"{who}: {configFileName} not found (run from the repository root; it lists the source roots `sources` and the output directory `generated`)"
    return none
  match ← readConfig path with
  | .ok cfg => return some cfg
  | .error e =>
    IO.eprintln s!"{who}: {configFileName}: {e}"
    return none

/-- コンパイル単位: ソースルートと、その配下の `.naru`(パス順)。 -/
structure Unit' where
  root : System.FilePath
  files : List String

/-- `naru.toml` の各ソースルートを単位にする(ルートが無ければ空の単位)。 -/
def unitsOf (cfg : Config) : IO (List Unit') := do
  let mut out : List Unit' := []
  for root in cfg.rootPaths do
    out := out ++ [{ root, files := ← listFiles root "naru" }]
  return out

/-- ルートの接頭辞(`<root>/`)。生成物のパスはこれを落として書く。 -/
def prefixOf (root : System.FilePath) : String :=
  let r := root.toString
  if r.endsWith "/" then r else r ++ "/"

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

/-- 生成ファイルのヘッダに入れる版と hash(ソースは与えられた順、stdlib とコンパイラはパス順)。単位の hash はソースルートからの
相対パス(`sourcePrefix` を落としたもの)で計算するので、ルートのディレクトリ名に依らない(C24)。stdlib とコンパイラはホームのもので、
その hash もホーム相対のパスで計算する(cwd に依らない)。stdlib が見つからなければ `none`。 -/
def buildMeta (who : String) (home : Home) (files : List String) (sourcePrefix : String := "") : IO (Option Backend.Model.Meta) := do
  let display (f : String) : String :=
    if !sourcePrefix.isEmpty && f.startsWith sourcePrefix then (f.drop sourcePrefix.length).toString else f
  let mut fileHashes : List (String × String) := []
  for f in files do fileHashes := fileHashes ++ [(f, ← hashFile f)]
  let stdlibFiles ← listFiles (home.path stdlibDir) "lean"
  if stdlibFiles.isEmpty then
    IO.eprintln s!"{who}: stdlib not found at {home.path stdlibDir}"
    return none
  let mut stdlibHashes : List (String × String) := []
  for f in stdlibFiles do stdlibHashes := stdlibHashes ++ [(home.display f, ← hashFile f)]
  let compilerFiles ← listFiles (home.path compilerDir) "lean"
  let mut compilerHashes : List (String × String) := []
  for f in compilerFiles do compilerHashes := compilerHashes ++ [(home.display f, ← hashFile f)]
  return some
    { compilerVersion := naruVersion, compilerHash := hashUnit compilerHashes, stdlibVersion,
      stdlibHash := hashUnit stdlibHashes, unitHash := hashUnit (fileHashes.map fun (p, h) => (display p, h)),
      fileHashes, sourcePrefix }

/-- 検査済みの単位から Model と Statements の生成ファイル(生成先からの相対パス、内容)を作る。`who` は診断の接頭辞。 -/
def emitLean (who : String) (checked : Checked) (info : Backend.Model.Meta) :
    IO (Option (Array (String × String) × Array (String × String))) := do
  let fail (d : Diagnostic) : IO (Option (Array (String × String) × Array (String × String))) := do
    IO.eprintln d.render
    IO.eprintln s!"{who}: 1 error(s)"
    return none
  match Backend.Model.emitModel checked.core checked.recursions info with
  | .error d => fail d
  | .ok model =>
    match Backend.Statements.emitStatements checked.core checked.recursions info with
    | .error d => fail d
    | .ok statements => return some (model, statements)

/-- 1 つの単位を検査して生成ファイルにする。診断があれば標準エラーに出して none。 -/
def compileUnit (who : String) (home : Home) (u : Unit') :
    IO (Option (Checked × Backend.Model.Meta × Array (String × String) × Array (String × String))) := do
  let (diags, checked) ← compileFiles u.files
  if !diags.isEmpty then
    for d in diags do IO.eprintln d.render
    IO.eprintln s!"{who}: {diags.size} error(s)"
    return none
  let some info ← buildMeta who home u.files (prefixOf u.root) | return none
  let some (model, statements) ← emitLean who checked info | return none
  return some (checked, info, model, statements)

/-- Lake が読む生成ソース `<ホーム>/.lake/naru/generated` を、書き終えた生成先への symlink にする(C24: `naru.toml` の `generated` を
lakefile の手修正なしに Lake に反映する)。以前の link・ディレクトリ・ファイルがあれば外す(symlink は辿らない)。 -/
def linkGenerated (who : String) (home : Home) (generated : System.FilePath) : IO Bool := do
  let target ← IO.FS.realPath generated
  let link := home.path lakeGeneratedLink
  if let some parent := link.parent then IO.FS.createDirAll parent
  try
    let md ← link.symlinkMetadata
    if md.type == .dir then IO.FS.removeDirAll link else IO.FS.removeFile link
  catch _ => pure ()
  let r ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
  if r.exitCode != 0 then
    IO.eprintln s!"{who}: cannot point {link} at {target} (Lake reads the generated Model / Statements there): {r.stderr.trimAscii}"
    return false
  return true

/-- 複数の単位の生成ファイルを 1 つの生成先に束ねる。各単位のルートファイル(`Model.lean` / `Statements.lean`)は、全単位の
モジュールを import するものに置き換える。同じパスのファイルが 2 つの単位から出たら誤り(同名のモジュール。`compileAll` の共通検査が先に
E017 で退けるので、ここは安全網)。 -/
def mergeUnits (who : String) (units : List (Backend.Model.Meta × Array (String × String) × Array (String × String))) :
    IO (Option (Array (String × String))) := do
  match units with
  | [(_, model, statements)] => return some (model ++ statements)
  | _ =>
    let mut files : Array (String × String) := #[]
    let mut modelMods : List String := []
    let mut stmtMods : List String := []
    let mut unitHashes : List (String × String) := []
    for (info, model, statements) in units do
      -- 単位の位置(ルート名ではない)で束ねる: ルートのディレクトリ名に依らない(C24)
      unitHashes := unitHashes ++ [(toString unitHashes.length, info.unitHash)]
      for (rel, content) in model ++ statements do
        if rel == "Model.lean" || rel == "Statements.lean" then continue
        if files.any (·.1 == rel) then
          IO.eprintln s!"{who}: two source roots generate the same file {rel}; give the modules different names"
          return none
        files := files.push (rel, content)
        let modName := ((rel.dropEnd ".lean".length).toString.replace "/" ".")
        if rel.startsWith "Model/" then modelMods := modelMods ++ [modName]
        else if rel.startsWith "Statements/" then stmtMods := stmtMods ++ [modName]
    let some (info, _, _) := units.head? | return none
    let all := { info with unitHash := hashUnit unitHashes }
    let modelRoot := Backend.Model.header all "all sources" all.unitHash ++
      "".intercalate (modelMods.map fun m => s!"import {m}\n") ++ "\n" ++ Backend.Model.rootNote
    let stmtRoot := Backend.Model.header all "all sources" all.unitHash ++
      "".intercalate (stmtMods.map fun m => s!"import {m}\n") ++ "\n" ++ Backend.Statements.rootNote
    return some (files.push ("Model.lean", modelRoot) |>.push ("Statements.lean", stmtRoot))

/-- `naru.toml` の全単位を検査して生成先に書き、Lake が読む生成ソースの link をその生成先に向ける(`compile` と `simulate` が共用)。
成功なら検査済みの単位の列。 -/
def compileAll (who : String) (home : Home) (cfg : Config) : IO (Option (List (Unit' × Checked))) := do
  let units ← unitsOf cfg
  if units.all (·.files.isEmpty) then
    IO.eprintln s!"{who}: no .naru sources under the source roots of {configFileName} ({", ".intercalate (cfg.rootPaths.map (·.toString))})"
    return none
  let mut results : List (Unit' × Checked) := []
  let mut generated : List (Backend.Model.Meta × Array (String × String) × Array (String × String)) := []
  let mut nModel := 0
  let mut nStatements := 0
  for u in units do
    if u.files.isEmpty then continue
    let some (checked, info, model, statements) ← compileUnit who home u | return none
    results := results ++ [(u, checked)]
    generated := generated ++ [(info, model, statements)]
    nModel := nModel + model.size
    nStatements := nStatements + statements.size
  -- C18 / C38: ソースルートをまたぐ同名のモジュール(E017)。各単位の検査は単位の中の同名しか見ないので、全単位の module を束ねて同じ共通検査
  -- (`Modules.duplicates`)に掛け、各ファイルの `module` 行に出す。生成の省略で生成パスがぶつからない組(spec だけ + runtime だけ、input だけ、
  -- 宣言なし)も意味検査としては同名で退ける(`mergeUnits` のパスの衝突は安全網)
  let allMods := results.foldl (init := (#[] : Array Module)) fun acc (_, c) => acc ++ c.mods
  let dups := Modules.duplicates allMods
  if !dups.isEmpty then
    for d in dups do IO.eprintln d.render
    IO.eprintln s!"{who}: {dups.size} error(s)"
    return none
  let some files ← mergeUnits who generated | return none
  writeGenerated cfg.generatedPath files
  if !(← linkGenerated who home cfg.generatedPath) then return none
  let nMods := results.foldl (init := 0) fun n (_, c) => n + c.mods.size
  IO.println s!"compiled {nMods} module(s) from {results.length} source root(s); wrote {nModel} Model file(s) and {nStatements} Statements file(s) under {cfg.generatedPath}/"
  return some results

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
  if files.isEmpty then
    if outDir.isSome then
      IO.eprintln "naru compile: `--out` needs explicit files (without files, the output directory comes from naru.toml)"
      return 2
    let some home ← findHome "naru compile" | return 2
    let some cfg ← loadConfig "naru compile" | return 2
    let some _ ← compileAll "naru compile" home cfg | return 1
    return 0
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
    let some home ← findHome "naru compile" | return 2
    let some info ← buildMeta "naru compile" home files | return 2
    let some (model, statements) ← emitLean "naru compile" checked info | return 1
    writeGenerated out (model ++ statements)
    IO.println s!"compiled {checked.mods.size} module(s); wrote {model.size} Model file(s) and {statements.size} Statements file(s) under {out}/"
    return 0

/-- scenario の実行。`file` は `naru.toml` のソースルート配下の `.naru`(検査の単位はそのルート全体 = 生成先の元)。
1. 全単位を検査し(診断があれば exit 1、何も実行しない)、生成先に Model と Statements を作り直し、Lake が読む生成ソースの link を
   その生成先に向ける(`compile` と同じ)。
2. そのファイルの scenario(1 つ以上。無ければ exit 2)を順に `NaruStd.runScenario` で表示する
   `<ホーム>/.lake/naru/simulate/Simulate.lean`(`main`)を書く(追跡対象外。生成先を変えても所在は同じ: C26)。
3. ホームで `lake build naru_simulate`(lakefile の lean_exe。link 経由で現在の生成先の Model を native にビルドする。失敗すれば exit 1 で
   古い実行ファイルは実行しない)→ `<ホーム>/.lake/build/bin/naru_simulate` を実行し、その exit code で終わる。 -/
def runSimulate (file : String) : IO UInt32 := do
  let some home ← findHome "naru simulate" | return 2
  let some cfg ← loadConfig "naru simulate" | return 2
  if !(← (System.FilePath.mk file).pathExists) then
    IO.eprintln s!"naru simulate: `{file}` not found"
    return 2
  let target ← IO.FS.realPath file
  -- どの単位のどのファイルか(渡されたパスの書き方に依らず、実際のパスで比べる)
  let units ← unitsOf cfg
  let mut found : Option (Unit' × String) := none
  for u in units do
    for f in u.files do
      if (← IO.FS.realPath f) == target then found := some (u, f)
  let some (unit, rel) := found
    | IO.eprintln s!"naru simulate: `{file}` is not under a source root of {configFileName} ({", ".intercalate (cfg.rootPaths.map (·.toString))}); simulate runs the scenarios of a source that `compile` writes to {cfg.generatedPath}/"
      return 2
  let some results ← compileAll "naru simulate" home cfg | return 1
  let some (_, checked) := results.find? fun (u, _) => u.root == unit.root
    | IO.eprintln s!"naru simulate: `{rel}` was not read"; return 2
  let some m := checked.mods.find? (·.file == rel)
    | IO.eprintln s!"naru simulate: `{rel}` was not read"; return 2
  let scenarios := m.decls.filter (·.kind == .scenario)
  if scenarios.isEmpty then
    IO.eprintln s!"naru simulate: `{rel}` declares no scenario"
    return 2
  let some info ← buildMeta "naru simulate" home unit.files (prefixOf unit.root) | return 2
  let names := scenarios.toList.map (·.name)
  let calls := names.map fun n =>
    s!"  NaruStd.runScenario \"{n}\" {Backend.Model.leanName (renderPath (m.name ++ [n]))}\n"
  -- Model と同じヘッダ(コンパイラ版・stdlib 版・ソース hash: C1)を付ける
  let shown := info.display rel
  let runner :=
    Backend.Model.header info shown ((info.fileHashes.lookup rel).getD "") ++
    s!"-- naru simulate: runs the scenario(s) of {shown} and prints their `observe` lines (`lake build naru_simulate && .lake/build/bin/naru_simulate`).\n" ++
    "import Model\n\ndef main : IO Unit := do\n" ++ "".intercalate calls
  let simDir := home.path simulateDir
  IO.FS.createDirAll simDir
  let runnerPath := simDir / "Simulate.lean"
  IO.FS.writeFile runnerPath runner
  IO.println s!"naru simulate: building {runnerPath} (scenario {", ".intercalate names} of {rel}) with `lake build naru_simulate`"
  let build ← IO.Process.output { cmd := "lake", args := #["build", "naru_simulate"], cwd := some home.dir }
  if build.exitCode != 0 then
    IO.eprint build.stdout
    IO.eprint build.stderr
    IO.eprintln s!"naru simulate: `lake build naru_simulate` failed (exit {build.exitCode})"
    return 1
  let child ← IO.Process.spawn
    { cmd := (home.path simulateBin).toString, args := #[], stdin := .inherit, stdout := .inherit, stderr := .inherit }
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
