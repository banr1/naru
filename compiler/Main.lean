import Naru

/-!
# `naru` CLI

- `naru compile` — `naru.toml`(リポジトリのルート。`Naru/Config.lean`)の各ソースルート配下の全 `.naru` を 1 つのコンパイル単位
  として検査し、Model(`<generated>/Model`)と Statements(`<generated>/Statements`)を生成先に出力する(C1)。
- `naru compile [--out <dir>] <files...>` — 指定ファイルを検査する。`--out` があればそこに Model と Statements を出力する
  (無ければ検査だけ。反例ソースの検査や受理例の確認に使う)。
  診断があれば標準エラーに `file:line:col: error[E0xx]: …` を出して exit 1。
- `naru check-reject <file.naru> <Exxx>` — 反例が `Exxx` で拒否されることを検査する。
- `naru lsp` — 標準入出力で言語サーバー(LSP)として動き、コンパイラの診断(C18)とホバー(C29)・定義ジャンプ(C30)・補完(C31)・リネーム(C32)・
  整形(C33、`Naru/Format.lean`)を返す(`Naru/Lsp.lean`)。
- `naru simulate <ソースルート配下の scenario.naru>` — そのルート全体を検査して生成先に Model を作り直し(`compile` と同じ)、
  そのファイルの scenario を実行する `.lake/naru/simulate/Simulate.lean`(`main`)を書いて `lake build naru_simulate` →
  `.lake/build/bin/naru_simulate` を実行する(C7。「naru を実行する」= 生成 Lean を native 実行する。C26: 生成先には
  `compile` の決定的な出力だけを置く)。出力は scenario の `observe` の行(observer の値を `Repr` で表示)。
- `naru deps [--out <dir>]` — `naru.toml` のソースルートを `compile` と同じ共通の検査に通してから、依存グラフ(宣言単位・ファイル単位の参照の
  グラフ。`Naru/Deps.lean`)の `deps.json` と閲覧用の単一ファイル `index.html`(`Naru/DepsTemplate.lean`)を、`naru.toml` の `deps`(`--out` で
  上書き)に書く(C63〜C65)。診断があれば exit 1 で何も書かない。`deps` も `--out` も無ければ exit 2。生成先には触れない。
- `naru proofs [--json]` — `naru.toml` の `proofs` が指す証明ディレクトリ(Lake ライブラリ `Proofs`)と有効な生成先の証明義務の一覧
  `obligations.json`(`Naru/Obligations.lean`。`compile` が書く)を読み、`lake build Proofs` を走らせてから、義務ごとに証明(`Proofs.<…>` の theorem)を
  対応付けて証明状況(proved / missing / sorry / stale / invalid)を表示する(C70)。証明済みの判定は kernel が行う(`.lake/naru/proofs/` の検査ファイル)。
  生成先と証明ディレクトリには何も書かない。`proofs` が無ければ exit 2、`lake build Proofs` の失敗と invalid が 1 件でもあれば exit 1。

出力は決定的: 同じソースと stdlib から同じバイト列を生成する。各生成ファイルの先頭コメント(`obligations.json` は先頭のフィールド)に
コンパイラ版(と `compiler/**/*.lean` の sha256)・stdlib 版(と `stdlib/Model/**/*.lean` の sha256)・ソースの sha256 を入れる。
ソースのパスはソースルートからの相対で書く(ルートのディレクトリ名を含まない: C1 / C24)。
生成先(`naru.toml` の `generated` も `--out <dir>` も同じ `writeGenerated`)は `Model.lean` と `Model/`、`Statements.lean` と `Statements/` を
丸ごと作り直し、`obligations.json`(C69: コンパイル単位の全 claim / claim bundle の義務)を書き直す(他は触らない)ので、旧パスの生成物や、
以前の規則で出ていた不要なファイルは残らない(C38)。Model ファイルは runtime 宣言を
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

/-- Lake が読む証明ソース(ホーム相対。lakefile の lean_lib `Proofs` の `srcDir`)。`naru proofs` が `naru.toml` の `proofs` への symlink にする
(C68 / C70: 生成先と同じく、lakefile を手で直さずに現在の設定の証明ディレクトリを Lake に読ませる)。 -/
def lakeProofsLink : System.FilePath := ".lake" / "naru" / "proofs-src"

/-- `naru proofs` が検査ファイルを書く場所(ホーム相対。追跡対象外。C70)。 -/
def proofsCheckDir : System.FilePath := ".lake" / "naru" / "proofs"

/-- 証明済みの判定で許容する Lean 標準の公理(C70。`#print axioms` の閉包がこの部分集合で、`sorryAx` を含まないこと)。 -/
def allowedAxioms : List String := ["propext", "Classical.choice", "Quot.sound"]

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
  "usage: naru compile [--out <dir>] [files...]\n       naru check-reject <file.naru> <Exxx>\n       naru lsp\n       naru simulate <scenario.naru under a source root of naru.toml>\n       naru deps [--out <dir>]\n       naru proofs [--json]"

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
作り直し(古い生成物を残さない)、`outDir/obligations.json` を書き直す(`files` に含める。C69)。 -/
def writeGenerated (outDir : System.FilePath) (files : Array (String × String)) : IO Unit := do
  for sub in ["Model", "Statements"] do
    let dir := outDir / sub
    if ← dir.isDir then IO.FS.removeDirAll dir
    let rootFile := outDir / (sub ++ ".lean")
    if ← rootFile.pathExists then IO.FS.removeFile rootFile
  let obligations := outDir / Obligations.fileName
  if ← obligations.pathExists then IO.FS.removeFile obligations
  IO.FS.createDirAll outDir
  for (rel, content) in files do
    let path := outDir / rel
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path content

/-- コンパイラのソース(`compiler/**/*.lean`、パス順)の hash。ホーム相対のパスで計算する(cwd に依らない)。 -/
def hashCompiler (home : Home) : IO String := do
  let compilerFiles ← listFiles (home.path compilerDir) "lean"
  let mut compilerHashes : List (String × String) := []
  for f in compilerFiles do compilerHashes := compilerHashes ++ [(home.display f, ← hashFile f)]
  return hashUnit compilerHashes

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
  return some
    { compilerVersion := naruVersion, compilerHash := ← hashCompiler home, stdlibVersion,
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

/-- ファイルの本文(義務の一覧が宣言コメントの要旨を読む)。 -/
def readTexts (files : List String) : IO (List (String × String)) :=
  files.mapM fun (f : String) => do return (f, ← IO.FS.readFile f)

/-- 1 つの単位を検査して生成ファイルにする。診断があれば標準エラーに出して none。義務(C69)は束縛 hash が空のまま返す
(全単位の生成ファイルが揃ってから `Obligations.finish` で埋める)。 -/
def compileUnit (who : String) (home : Home) (u : Unit') :
    IO (Option (Checked × Backend.Model.Meta × Array (String × String) × Array (String × String) × List Obligations.Obligation)) := do
  let (diags, checked) ← compileFiles u.files
  if !diags.isEmpty then
    for d in diags do IO.eprintln d.render
    IO.eprintln s!"{who}: {diags.size} error(s)"
    return none
  let some info ← buildMeta who home u.files (prefixOf u.root) | return none
  let some (model, statements) ← emitLean who checked info | return none
  let obligations := Obligations.collect (prefixOf u.root) checked (← readTexts u.files)
  return some (checked, info, model, statements, obligations)

/-- 義務の一覧 `obligations.json` を生成ファイルに加える(C69)。`files` は生成先に書く Model / Statements(束縛 hash の元)、`sources` は
ソースルートからの相対パスと sha256。 -/
def withObligations (info : Backend.Model.Meta) (sources : List (String × String)) (files : Array (String × String))
    (obligations : List Obligations.Obligation) : Array (String × String) :=
  let obs := Obligations.finish info.stdlibHash files obligations
  files.push (Obligations.fileName, Obligations.render info sources obs)

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
  let mut obligations : List Obligations.Obligation := []
  let mut sources : List (String × String) := []
  let mut nModel := 0
  let mut nStatements := 0
  for u in units do
    if u.files.isEmpty then continue
    let some (checked, info, model, statements, obs) ← compileUnit who home u | return none
    results := results ++ [(u, checked)]
    generated := generated ++ [(info, model, statements)]
    obligations := obligations ++ obs
    sources := sources ++ info.fileHashes.map fun (p, h) => (info.display p, h)
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
  let some (info, _, _) := generated.head? | return none
  let files := withObligations info sources files obligations
  writeGenerated cfg.generatedPath files
  if !(← linkGenerated who home cfg.generatedPath) then return none
  let nMods := results.foldl (init := 0) fun n (_, c) => n + c.mods.size
  IO.println s!"compiled {nMods} module(s) from {results.length} source root(s); wrote {nModel} Model file(s), {nStatements} Statements file(s) and {Obligations.fileName} ({obligations.length} obligation(s)) under {cfg.generatedPath}/"
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
    let obligations := Obligations.collect "" checked (← readTexts files)
    let all := withObligations info info.fileHashes (model ++ statements) obligations
    writeGenerated out all
    IO.println s!"compiled {checked.mods.size} module(s); wrote {model.size} Model file(s), {statements.size} Statements file(s) and {Obligations.fileName} ({obligations.length} obligation(s)) under {out}/"
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

/-- パスの絶対形: 実在すれば `realPath`、無ければ実在する親の `realPath` + 名前(出力先の比較に使う)。 -/
def absoluteOf (p : System.FilePath) : IO String := do
  if ← p.pathExists then return (← IO.FS.realPath p).toString
  match p.parent, p.fileName with
  | some parent, some name =>
    if ← parent.pathExists then return ((← IO.FS.realPath parent) / name).toString
    return p.toString
  | _, _ => return p.toString

/-- 依存グラフ(C63〜C65)。`naru.toml` の各ソースルートを `compile` と同じ共通の検査(`compileFiles`: 構文解析・同名モジュール・名前解決・型検査・
Core の健全性・循環・停止性)と、ルートをまたぐ同名モジュールの検査に通してから、`Deps.build` で宣言単位・ファイル単位の参照のグラフを作り、
`deps.json`(正規形の JSON)と `index.html`(JSON を埋め込んだ単一ファイル)を出力先に書く。
- 出力先: `--out <dir>` があればそれ、無ければ `naru.toml` の `deps`(`naru.toml` のディレクトリからの相対)。どちらも無ければ exit 2。有効な生成先
  (`generated`)やその配下を出力先にすることは拒否する(exit 2)。
- 診断が 1 つでもあれば標準エラーに出して exit 1。出力先には触れない(古いグラフを残したまま成功にしない: 書くのは両方の本文が揃ってから)。
- 生成先(`generated`)と Lake の link には何も書かない。 -/
def runDeps (args : List String) : IO UInt32 := do
  let who := "naru deps"
  let mut outArg : Option String := none
  match args with
  | [] => pure ()
  | ["--out", dir] => outArg := some dir
  | ["--out"] =>
    IO.eprintln s!"{who}: `--out` needs a directory"
    return 2
  | _ =>
    IO.eprintln "usage: naru deps [--out <dir>]"
    return 2
  let some home ← findHome who | return 2
  let some cfg ← loadConfig who | return 2
  let outDir : System.FilePath ← match outArg, cfg.depsPath with
    | some d, _ => pure (System.FilePath.mk d)
    | none, some d => pure d
    | none, none =>
      IO.eprintln s!"{who}: {configFileName} has no `deps = \"<dir>\"` and no `--out <dir>` was given (the dependency graph needs an output directory)"
      return 2
  -- 有効な生成先(とその配下)には何も書かない(C63 / C26)
  let outAbs ← absoluteOf outDir
  let genAbs ← absoluteOf cfg.generatedPath
  if outAbs == genAbs || outAbs.startsWith (genAbs ++ "/") then
    IO.eprintln s!"{who}: the output directory {outDir} is the generated directory {cfg.generatedPath} (or inside it); `naru compile` owns that directory, choose another"
    return 2
  let units ← unitsOf cfg
  if units.all (·.files.isEmpty) then
    IO.eprintln s!"{who}: no .naru sources under the source roots of {configFileName} ({", ".intercalate (cfg.rootPaths.map (·.toString))})"
    return 1
  let mut inputs : List Deps.UnitInput := []
  let mut sources : List (String × String) := []
  let mut allMods : Array Module := #[]
  for u in units do
    if u.files.isEmpty then continue
    let (diags, checked) ← compileFiles u.files
    if !diags.isEmpty then
      for d in diags do IO.eprintln d.render
      IO.eprintln s!"{who}: {diags.size} error(s); the dependency graph is not written"
      return 1
    let pre := prefixOf u.root
    let mut texts : List (String × String) := []
    for f in u.files do
      texts := texts ++ [(f, ← IO.FS.readFile f)]
      sources := sources ++ [(Deps.stripPrefix pre f, ← hashFile f)]
    allMods := allMods ++ checked.mods
    inputs := inputs ++ [{ prefix_ := pre, mods := checked.mods, refs := checked.refs, sources := texts }]
  -- ルートをまたぐ同名のモジュール(`compile` の compile-all と同じ共通検査)
  let dups := Modules.duplicates allMods
  if !dups.isEmpty then
    for d in dups do IO.eprintln d.render
    IO.eprintln s!"{who}: {dups.size} error(s); the dependency graph is not written"
    return 1
  let info : Deps.Meta :=
    { compilerVersion := naruVersion, compilerHash := ← hashCompiler home, sources := sources.mergeSort fun a b => a.1 ≤ b.1 }
  let g := Deps.build inputs
  if g.dropped > 0 then
    IO.eprintln s!"{who}: internal: {g.dropped} reference(s) could not be attributed to a declaration although name resolution passed; this is a compiler bug, so the dependency graph is not written"
    return 1
  let json := Deps.renderJson info g
  let html := Deps.renderHtml (Deps.htmlHeader info) json
  -- 両方の本文が揃ってから書く。一時ファイルに書いて改名する(途中で失敗しても片方だけ新しい状態を残しにくい)
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "deps.json.tmp") json
  IO.FS.writeFile (outDir / "index.html.tmp") html
  IO.FS.rename (outDir / "deps.json.tmp") (outDir / "deps.json")
  IO.FS.rename (outDir / "index.html.tmp") (outDir / "index.html")
  let stats := g.stats
  let stat (k : String) : Nat := (stats.lookup k).getD 0
  IO.println s!"{who}: wrote {outDir / "deps.json"} and {outDir / "index.html"} ({stat "files"} file(s), {stat "decls"} declaration(s), {stat "declEdges"} declaration edge(s), {stat "fileEdges"} file edge(s), {stat "reducedEdges"} after transitive reduction, {stat "layers"} layer(s))"
  return 0

/-! ## `naru proofs`(C70) -/

/-- Lake が読む証明ソース `<ホーム>/.lake/naru/proofs-src` を、証明ディレクトリへの symlink にする(`linkGenerated` と同じ運び)。 -/
def linkProofs (who : String) (home : Home) (proofs : System.FilePath) : IO Bool := do
  let target ← IO.FS.realPath proofs
  let link := home.path lakeProofsLink
  if let some parent := link.parent then IO.FS.createDirAll parent
  try
    let md ← link.symlinkMetadata
    if md.type == .dir then IO.FS.removeDirAll link else IO.FS.removeFile link
  catch _ => pure ()
  let r ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
  if r.exitCode != 0 then
    IO.eprintln s!"{who}: cannot point {link} at {target} (Lake reads the Proofs library there): {r.stderr.trimAscii}"
    return false
  return true

/-- `obligations.json` の 1 項目(`naru proofs` が読む分)。 -/
structure ObEntry where
  name : String
  kind : String
  lean : String
  thm : String
  type : String
  hash : String
deriving Inhabited

/-- `obligations.json` の義務と `sources`(相対パス, sha256)。 -/
def readObligations (path : System.FilePath) : IO (Except String (List ObEntry × List (String × String))) := do
  let text ← IO.FS.readFile path
  return do
    let j ← Lean.Json.parse text
    let arr ← (← j.getObjVal? "obligations").getArr?
    let entries ← arr.toList.mapM fun o => do
      let get (k : String) : Except String String := do (← o.getObjVal? k).getStr?
      let e : ObEntry := { name := ← get "name", kind := ← get "kind", lean := ← get "lean", thm := ← get "theorem", type := ← get "type", hash := ← get "sha256" }
      return e
    let srcs ← (← (← j.getObjVal? "sources").getArr?).toList.mapM fun s => do
      let get (k : String) : Except String String := do (← s.getObjVal? k).getStr?
      return (← get "path", ← get "sha256")
    return (entries, srcs)

def isHexChar (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- 証明ファイルの束縛行 `-- naru-obligation: <修飾名> sha256:<hash>`。 -/
structure Binding where
  file : String
  line : Nat
  name : String
  hash : String
deriving Inhabited

def bindingPrefix : String := "-- naru-obligation:"

/-- 束縛行の読み: `(修飾名, hash)`。束縛行でなければ none、束縛行の形が崩れていれば `some none`。 -/
def parseBinding (l : String) : Option (Option (String × String)) :=
  let t := l.trimAscii.toString
  if !(t.startsWith bindingPrefix) then none
  else
    let rest := (t.drop bindingPrefix.length).toString.trimAscii.toString
    match (rest.splitOn " ").filter (!·.isEmpty) with
    | [name, h] =>
      let digest := (h.drop 7).toString
      if h.startsWith "sha256:" && digest.length == 64 && digest.toList.all isHexChar && !name.isEmpty then some (some (name, digest))
      else some none
    | _ => some none

/-- 証明ファイルで禁じる option(kernel の検査を飛ばすので、`naru proofs` の判定が信用できなくなる)。 -/
def forbiddenOptions : List String := ["debug.skipKernelTC"]

/-- 証明ディレクトリの Lean モジュール: `Proofs.lean`(ルート)と `Proofs/**/*.lean`(モジュール名, パス)。それ以外の `.lean` は Lake ライブラリ
`Proofs`(lakefile の `globs = ["Proofs.*"]`)に入らないので読まない。 -/
def proofModules (dir : System.FilePath) : IO (List (String × String)) := do
  let base := dir.toString ++ "/"
  let mut out : List (String × String) := []
  for f in (← listFiles dir "lean") do
    let rel := if f.startsWith base then (f.drop base.length).toString else f
    if rel == "Proofs.lean" then out := out ++ [("Proofs", f)]
    else if rel.startsWith "Proofs/" && rel.endsWith ".lean" then
      out := out ++ [(((rel.dropEnd ".lean".length).toString.replace "/" "."), f)]
  return out

inductive ProofStatus where
  | proved | missing | sorry_ | stale | invalid
deriving BEq, Inhabited

def ProofStatus.describe : ProofStatus → String
  | .proved => "proved"
  | .missing => "missing"
  | .sorry_ => "sorry"
  | .stale => "stale"
  | .invalid => "invalid"

structure Verdict where
  entry : ObEntry
  status : ProofStatus
  reason : String
  axioms : List String := []
  bound : Option String := none
deriving Inhabited

/-- `#print axioms` の出力から公理の一覧。 -/
def parseAxioms (msg : String) : Option (List String) :=
  if (msg.splitOn "does not depend on any axioms").length > 1 then some []
  else
    match msg.splitOn "depends on axioms: [" with
    | [_, rest] => some ((((rest.splitOn "]").head!).splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty))
    | _ => none

/-- `lean --json` の 1 行: (行, severity, 本文)。 -/
def parseLeanMessage (line : String) : Option (Nat × String × String) :=
  match Lean.Json.parse line with
  | .error _ => none
  | .ok j =>
    match (do
      let pos ← j.getObjVal? "pos"
      let l ← (← pos.getObjVal? "line").getNat?
      let sev ← (← j.getObjVal? "severity").getStr?
      let data ← (← j.getObjVal? "data").getStr?
      pure (l, sev, data) : Except String (Nat × String × String)) with
    | .ok r => some r
    | .error _ => none

def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

def firstLine (s : String) : String := ((s.splitOn "\n").head?.getD "").trimAscii.toString

/-- `naru proofs [--json]`(C70)。`naru.toml` の `proofs` が指す証明ディレクトリと有効な生成先の `obligations.json` を読み、Lake が読む link
(生成先と証明ディレクトリ)を置いて `lake build Proofs` を走らせ、`.lake/naru/proofs/Check.lean` に義務ごとの検査(型が elaboration できること、
theorem の存在、`example : <義務の型> := Proofs.<名>`、`#print axioms`)を書いて `lake env lean --json` で kernel に検査させ、証明状況を表示する。
- 状況と判定の順: missing(theorem が無い)→ invalid(theorem の型が義務の型と違う / `propext` `Classical.choice` `Quot.sound` 以外の公理に依存する。
  `sorryAx` より先に見るので sorry の下書きが独自公理を隠さない)→ sorry(`sorryAx` に依存)→ stale(束縛行が無い / hash が現在の一覧と違う / 同じ義務の
  束縛行が食い違う)→ proved(すべての束縛行の hash が現在と一致)。型の一致と公理監査は検査用の theorem `NaruProofsCheck.obligation<i> : <型> := Proofs.<名>`
  に対して行う(補われた coercion の公理もその閉包に入る)。一覧に無い修飾名の束縛行・形の崩れた束縛行・`debug.skipKernelTC` を置く行も invalid として数える。
- 前提: `obligations.json` の `sources` が現在のソース(`naru.toml` のルート)と一致すること(古ければ exit 2 で `naru compile` を促す)、証明ディレクトリに
  ルート `Proofs.lean` があること(無ければ exit 2)。
- exit: `lake build Statements Proofs` の失敗、検査ファイルの読み込みの失敗、invalid が 1 件でもあれば 1。missing / sorry / stale だけなら 0。`proofs` が無い・
  一覧が無い・古い・ルートが無ければ 2。
- 生成先と証明ディレクトリには何も書かない(書くのは `.lake/naru/` の link と検査ファイルだけ)。 -/
def runProofs (args : List String) : IO UInt32 := do
  let who := "naru proofs"
  let json ← match args with
    | [] => pure false
    | ["--json"] => pure true
    | _ =>
      IO.eprintln "usage: naru proofs [--json]"
      return 2
  let some home ← findHome who | return 2
  let some cfg ← loadConfig who | return 2
  let some proofsDir := cfg.proofsPath
    | IO.eprintln s!"{who}: {configFileName} has no `proofs = \"<dir>\"` (the directory of the Lake library `Proofs` that holds the protocol proofs)"
      return 2
  if !(← proofsDir.isDir) then
    IO.eprintln s!"{who}: the proofs directory {proofsDir} ({configFileName}: proofs) does not exist"
    return 2
  let obligationsPath := cfg.generatedPath / Obligations.fileName
  if !(← obligationsPath.pathExists) then
    IO.eprintln s!"{who}: {obligationsPath} not found (run `naru compile` first: it writes the proof obligations of the compile unit there)"
    return 2
  let (entries, listedSources) ← match ← readObligations obligationsPath with
    | .ok es => pure es
    | .error e =>
      IO.eprintln s!"{who}: {obligationsPath}: {e}"
      return 2
  -- 一覧が現在のソースから作られたものか(`sources` の相対パスと sha256 を現在のソースルートのファイルと照合)。古ければ判定しない
  let units ← unitsOf cfg
  let mut current : List (String × String) := []
  for u in units do
    let pre := prefixOf u.root
    for f in u.files do current := current ++ [(Deps.stripPrefix pre f, ← hashFile f)]
  let currentSorted := current.mergeSort fun a b => a.1 ≤ b.1
  if currentSorted != listedSources then
    let changed := currentSorted.filter fun (p, h) => listedSources.lookup p != some h
    let removed := listedSources.filter fun (p, _) => (currentSorted.lookup p).isNone
    IO.eprintln s!"{who}: {obligationsPath} is out of date with the sources under {", ".intercalate (cfg.rootPaths.map (·.toString))} (changed or new: {changed.map (·.1)}, no longer present: {removed.map (·.1)}); run `naru compile` first"
    return 2
  if !(← (proofsDir / "Proofs.lean").pathExists) then
    IO.eprintln s!"{who}: {proofsDir / "Proofs.lean"} not found (the root module of the Lake library `Proofs`; create it — it may import nothing — and put the theorems under {proofsDir / "Proofs"}/)"
    return 2
  if !(← linkGenerated who home cfg.generatedPath) then return 2
  if !(← linkProofs who home proofsDir) then return 2
  -- 証明ファイルと束縛行(禁じた option も探す)
  let modules ← proofModules proofsDir
  let mut bindings : List Binding := []
  let mut malformed : List (String × Nat) := []
  let mut forbidden : List (String × Nat × String) := []
  for (_, f) in modules do
    let mut n := 0
    for l in (← IO.FS.readFile f).splitOn "\n" do
      n := n + 1
      match parseBinding l with
      | none => pure ()
      | some none => malformed := malformed ++ [(f, n)]
      | some (some (name, h)) => bindings := bindings ++ [{ file := f, line := n, name, hash := h }]
      for opt in forbiddenOptions do
        if hasSub l opt then forbidden := forbidden ++ [(f, n, opt)]
  -- lake build Statements Proofs(検査ファイルは生成 Statements のルートも import するので、現在の生成先の Statements 全体を組んでおく)
  let build ← IO.Process.output { cmd := "lake", args := #["build", "Statements", "Proofs"], cwd := some home.dir }
  if build.exitCode != 0 then
    IO.eprint build.stdout
    IO.eprint build.stderr
    IO.eprintln s!"{who}: `lake build Statements Proofs` failed (exit {build.exitCode})"
    return 1
  -- 検査ファイル
  let checkDir := home.path proofsCheckDir
  IO.FS.createDirAll checkDir
  let checkPath := checkDir / "Check.lean"
  let mut lines : Array String := #[
    "-- naru proofs: kernel check of the proof obligations (written by `naru proofs`; not tracked). Do not edit.",
    "import Statements" ]
  for (m, _) in modules do lines := lines.push s!"import {m}"
  lines := lines.push ""
  lines := lines.push "set_option autoImplicit false"
  lines := lines.push ""
  -- 義務ごとに 4 行: 型の elaboration / theorem の存在 / 型の一致(検査用の theorem: 補われた coercion もその項に入る)/ 検査用の theorem の公理
  let mut at_ : List (Nat × Nat × Nat × Nat) := []
  let mut i := 0
  for e in entries do
    lines := lines.push s!"-- obligation {e.name}"
    let base := lines.size + 1
    let check := s!"NaruProofsCheck.obligation{i}"
    lines := lines.push s!"example : {e.type} := sorry"
    lines := lines.push s!"#check @{e.thm}"
    lines := lines.push s!"theorem {check} : {e.type} := {e.thm}"
    lines := lines.push s!"#print axioms {check}"
    lines := lines.push ""
    at_ := at_ ++ [(base, base + 1, base + 2, base + 3)]
    i := i + 1
  IO.FS.writeFile checkPath ("\n".intercalate lines.toList ++ "\n")
  let run ← IO.Process.output { cmd := "lake", args := #["env", "lean", "--json", checkPath.toString], cwd := some home.dir }
  let mut messages : List (Nat × String × String) := []
  for l in run.stdout.splitOn "\n" do
    if let some m := parseLeanMessage l then messages := messages ++ [m]
  let errorsAt (l : Nat) : List String := messages.filterMap fun (ln, sev, data) => if ln == l && sev == "error" then some data else none
  let infosAt (l : Nat) : List String := messages.filterMap fun (ln, sev, data) => if ln == l && sev == "information" then some data else none
  -- 義務の行の外のエラー(import の失敗など)と型が elaboration できない義務は内部エラー
  let obligationLines := at_.flatMap fun (a, b, c, d) => [a, b, c, d]
  let outside := messages.filter fun (ln, sev, _) => sev == "error" && !(obligationLines.contains ln)
  let badTypes := (entries.zip at_).filter fun (_, (a, _, _, _)) => !(errorsAt a).isEmpty
  if !outside.isEmpty || !badTypes.isEmpty || (run.exitCode != 0 && messages.isEmpty) then
    for (ln, _, data) in outside do IO.eprintln s!"{checkPath}:{ln}: {firstLine data}"
    for (e, (a, _, _, _)) in badTypes do IO.eprintln s!"{checkPath}:{a}: the type of obligation {e.name} does not elaborate: {firstLine ((errorsAt a).head!)}"
    if messages.isEmpty then IO.eprint run.stderr
    IO.eprintln s!"{who}: the kernel check {checkPath} could not be run against the generated Statements (is {cfg.generatedPath}/ built from the current sources? run `naru compile`)"
    return 1
  -- 判定
  let mut verdicts : List Verdict := []
  for (e, (_, b, c, d)) in entries.zip at_ do
    let bound := bindings.filter (·.name == e.name)
    let boundHash := (bound.find? (·.hash == e.hash)).map (·.hash) <|> (bound.head?.map (·.hash))
    let v : Verdict ←
      if !(errorsAt b).isEmpty then
        pure { entry := e, status := .missing, reason := s!"theorem {e.thm} is not declared under the proofs directory", bound := boundHash }
      else if let some err := (errorsAt c).head? then
        pure { entry := e, status := .invalid, reason := s!"the type of {e.thm} is not the obligation's type: {firstLine err}", bound := boundHash }
      else
        match (infosAt d).findSome? parseAxioms with
        | none => pure { entry := e, status := .invalid, reason := s!"no axiom report for {e.thm}", bound := boundHash }
        | some axioms =>
          -- 許容しない公理は sorry より先に不正(sorry の下書きが独自公理を隠さない)
          let bad := axioms.filter fun a => !(allowedAxioms.contains a) && a != "sorryAx"
          if !bad.isEmpty then
            pure { entry := e, status := .invalid, reason := s!"{e.thm} depends on axiom(s) {bad} (allowed: {allowedAxioms})", axioms, bound := boundHash }
          else if axioms.contains "sorryAx" then
            pure { entry := e, status := .sorry_, reason := s!"{e.thm} depends on sorryAx (the proof is a draft)", axioms, bound := boundHash }
          else if bound.isEmpty then
            pure { entry := e, status := .stale, reason := s!"no binding line `{bindingPrefix} {e.name} sha256:{e.hash}` in the proof files (current hash {e.hash})", axioms }
          else if bound.all (·.hash == e.hash) then
            pure { entry := e, status := .proved, reason := s!"kernel-checked against the obligation; axioms {axioms}; bound to sha256:{e.hash}", axioms, bound := boundHash }
          else if bound.any (·.hash == e.hash) then
            let other := (bound.filter (·.hash != e.hash)).head!
            pure { entry := e, status := .stale, reason := s!"conflicting binding lines: {other.file}:{other.line} has sha256:{other.hash} while another line has the current hash {e.hash} (keep one binding line per obligation)", axioms, bound := boundHash }
          else
            let found := bound.head!
            pure { entry := e, status := .stale, reason := s!"binding line {found.file}:{found.line} has sha256:{found.hash} but the current hash is {e.hash} (check the obligation's type and rebind)", axioms, bound := boundHash }
    verdicts := verdicts ++ [v]
  -- 一覧に無い修飾名の束縛行、形の崩れた束縛行、禁じた option
  let known := entries.map (·.name)
  let unknown := bindings.filter fun b => !(known.contains b.name)
  let count (s : ProofStatus) : Nat := (verdicts.filter (·.status == s)).length
  let nInvalid := count .invalid + unknown.length + malformed.length + forbidden.length
  let layer := "protocol guarantees (the theorems under the proofs directory against the generated Statements). The compiler's semantics preservation (lake build NaruSem / naru_test semantics, C45) is a separate layer and is not reported here."
  if json then
    let results := verdicts.map fun v =>
      Deps.J.obj [ ("name", .str v.entry.name), ("kind", .str v.entry.kind), ("lean", .str v.entry.lean), ("theorem", .str v.entry.thm),
                   ("status", .str v.status.describe), ("reason", .str v.reason), ("sha256", .str v.entry.hash),
                   ("bound", match v.bound with | some h => .str h | none => .null), ("axioms", .arr (v.axioms.map Deps.J.str)) ]
    let invalidBindings := unknown.map (fun b => Deps.J.obj [ ("file", .str b.file), ("line", .nat b.line), ("name", .str b.name), ("sha256", .str b.hash),
                                                             ("reason", .str "the binding line names an obligation that is not in the current list") ]) ++
      malformed.map (fun (f, n) => Deps.J.obj [ ("file", .str f), ("line", .nat n), ("name", .str ""), ("sha256", .str ""),
                                               ("reason", .str s!"malformed binding line (expected `{bindingPrefix} <qualified name> sha256:<64 hex digits>`)") ]) ++
      forbidden.map fun (f, n, opt) => Deps.J.obj [ ("file", .str f), ("line", .nat n), ("name", .str ""), ("sha256", .str ""),
                                                   ("reason", .str s!"set_option {opt} is not allowed in proof files (it skips the kernel check)") ]
    let out := Deps.J.obj
      [ ("obligations", .str obligationsPath.toString), ("proofs", .str proofsDir.toString), ("modules", .arr (modules.map fun (m, _) => .str m)),
        ("build", .str "ok"), ("results", .arr results), ("invalidBindings", .arr invalidBindings),
        ("counts", .obj [ ("proved", .nat (count .proved)), ("missing", .nat (count .missing)), ("sorry", .nat (count .sorry_)),
                          ("stale", .nat (count .stale)), ("invalid", .nat nInvalid) ]),
        ("layer", .str layer) ]
    IO.println (out.render)
  else
    IO.println s!"{who}: {entries.length} obligation(s) in {obligationsPath}; proofs in {proofsDir}/ (Lake library Proofs, {modules.length} module(s)); lake build Statements Proofs ok"
    for v in verdicts do IO.println s!"{v.entry.name}  {v.status.describe}  {v.reason}"
    for b in unknown do IO.println s!"{b.name}  invalid  binding line {b.file}:{b.line} names an obligation that is not in the current list"
    for (f, n) in malformed do IO.println s!"{f}:{n}  invalid  malformed binding line (expected `{bindingPrefix} <qualified name> sha256:<64 hex digits>`)"
    for (f, n, opt) in forbidden do IO.println s!"{f}:{n}  invalid  set_option {opt} is not allowed in proof files (it skips the kernel check)"
    IO.println s!"proved {count .proved} / missing {count .missing} / sorry {count .sorry_} / stale {count .stale} / invalid {nInvalid} (of {entries.length} obligation(s); {unknown.length + malformed.length + forbidden.length} line(s) counted as invalid)"
    IO.println s!"layer: {layer}"
  return if nInvalid > 0 then 1 else 0

def main (args : List String) : IO UInt32 := do
  match args with
  | "compile" :: rest => runCompile rest
  | ["check-reject", file, code] => runCheckReject file code
  | ["lsp"] => Lsp.serve naruVersion
  | ["simulate", file] => runSimulate file
  | "deps" :: rest => runDeps rest
  | "proofs" :: rest => runProofs rest
  | _ =>
    IO.eprintln usage
    return 2
