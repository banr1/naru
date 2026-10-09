import NaruTest.Common
import Naru

/-!
# `naru_test statements` — C8 / C9 の検査ドライバ

生成 Statements(`generated/Statements.lean` と `generated/Statements/**.lean`。`lake exe naru compile` が `naru.toml` のソースルート
(`specs/consensus/`)から出す)について:

- C8: `lake build Statements` が exit 0。`Statements` からの import 閉包(`lake env lean --deps-json` で取る。ソースの文字列から
  推測しない。`Init` / `NaruStd` は生成物の外なのでその先は辿らない)が `Init` / `NaruStd` / 生成 Model(`Model.*`)/ 生成 Statements
  (`Statements.*`)だけから成り、Proofs を含まない。`generated/Statements/` 配下の全ファイルがその閉包にある(リストされない第 2 の
  statements が無い)。閉包の生成ファイル(Statements と Model)すべてに語 `sorry` が無い(`grep -rw sorry` と同じ判定)。
  C9 の claim bundle を持つモジュールが閉包にある(中身の無い閉包で通さない)。
- C9: ソースルートの naru ソースに claim bundle `Consensus` がちょうど 1 つあり、その項目のラベルが verified-consensus の 13 claims
  (IDEAL.md 用語「claim surface」)と同名で、生成 Lean の `structure` の欄(`getStructureFields`。`run_cmd` の検査スクリプトを
  `.lake/naru/test/statements/SurfaceShape.lean` に書いて `lake env lean` で走らせる)がその項目と同じ順で並ぶ。13 の欄名を列挙する。
- C37: 移植ソースの spec 側は各ソースルートの `Consensus/Spec/` にあり(1 つ以上。改名前のディレクトリは無い)、その各ファイルの
  `module` 宣言はルート相対パスと一致する(`Consensus.Spec.<ファイル名>`)。単位の中に改名前の名前のモジュールも import も無い。
  claim bundle `Consensus` は `Consensus.Spec.*` のモジュールにある。生成先に改名前のディレクトリが無く、生成ファイルのどれも
  改名前のモジュール名(`Model.` / `Statements.` + 旧名)に触れず、`generated/Statements/Consensus/Spec/` の全モジュールが閉包にある。
  (改名前後の宣言構造の照合と、一般規則が旧名の形の利用者モジュールにも適用される検体は `naru_test regression`。)
- C38: 生成先の Model ファイルは Lean の runtime 宣言を実際に出力するモジュールにだけ、Statements ファイルは spec 宣言のあるモジュールにだけあり、
  ルート `Model.lean` / `Statements.lean` は存在する生成モジュールをちょうど import し、生成ファイルの全 import が実在し、出力される runtime 宣言と
  spec 宣言のすべてが生成ファイルに宣言として現れる(`NaruTest.checkOmission`。Core と照合する)。`generated/Model/Consensus/Spec/` には混在モジュールの
  Model が残り、spec だけのモジュール(Claims / Accountability / Properties / Regimes)の Model は無い(Model 側を丸ごと消して代用しない)。
  最小検体(spec のみ / runtime のみ / 混在 / input のみ / 宣言なし)は `naru_test regression`(`tests/units/accept/omit_model`)。

実行は `lake exe naru_test statements`(リポジトリのルート)。先に `lake exe naru compile` で `generated/` を作り直す。
-/

namespace NaruTest.Statements
open Naru

def generatedDir : System.FilePath := "generated"
def scratchDir : System.FilePath := ".lake" / "naru" / "test" / "statements"

/-- verified-consensus の `Consensus` の 13 claims(IDEAL.md 用語「claim surface」。手書き Lean の欄の順)。 -/
def claimSurface : List String :=
  [ "constants", "nested", "certificatesAccountable", "finalizedAccountable", "finalizedMonotone", "honestNeverSlashed",
    "finalizedSafe", "available", "confirmedLive", "stableLive", "stableIncludedFast", "finalized",
    "stableAsynchronyResilient" ]

/-- naru ソースの中で claim surface を公開する claim bundle の名前。 -/
def bundleName : String := "Consensus"

/-- 移植ソースの spec 側のディレクトリ(ソースルートからの相対)と、そのモジュール名の接頭辞(IDEAL.md 前提「構成」、C37)。 -/
def specDir : String := "Consensus/Spec"
def specModulePrefix : String := "Consensus.Spec."
/-- 改名前の名前(C37)。この検査自身が旧名の検索(`naru_test repo`)に掛からないよう、連結で作る。 -/
def oldSpecDir : String := "Consensus/" ++ "Statements"
def oldSpecModulePrefix : String := "Consensus." ++ "Statements."

/-- ソースルートからの相対パス。 -/
def relativeTo (root : System.FilePath) (f : String) : String :=
  let p := root.toString
  let p := if p.endsWith "/" then p else p ++ "/"
  if f.startsWith p then (f.drop p.length).toString else f

/-- 閉包に許すモジュール: Lean の `Init`、stdlib、生成 Model、生成 Statements。Proofs は決して許さない。 -/
def allowedImport (m : String) : Bool :=
  m == "Init" || m == "NaruStd" || m.startsWith "NaruStd." || m == "Model" || m.startsWith "Model." ||
  m == "Statements" || m.startsWith "Statements."

/-- 生成物の外(`Init` / stdlib)は辿らない。 -/
def external (m : String) : Bool :=
  m == "Init" || m == "NaruStd" || m.startsWith "NaruStd."

def moduleFile (m : String) : System.FilePath :=
  generatedDir / System.FilePath.mk ((m.replace "." "/") ++ ".lean")

/-- 生成ファイルのパス → モジュール名(`generated/Statements/A/B.lean` → `Statements.A.B`)。 -/
def fileModule (p : String) : String :=
  let rel := if p.startsWith "generated/" then (p.drop "generated/".length).toString else p
  let noExt := if rel.endsWith ".lean" then (rel.dropEnd ".lean".length).toString else rel
  noExt.replace "/" "."

/-- C37: 移植ソースの所在と module 宣言(ソースルートごと)。 -/
def checkSpecSources (root : System.FilePath) (sources : List String) (mods : Array Core.Module) : M Unit := do
  let specFiles := sources.filter fun f => (relativeTo root f).startsWith (specDir ++ "/")
  let oldFiles := sources.filter fun f => (relativeTo root f).startsWith (oldSpecDir ++ "/")
  if specFiles.isEmpty then fail s!"C37: {root}/{specDir}/ has no .naru file"
  else ok s!"C37: {root}/{specDir}/ has {specFiles.length} source file(s)"
  let oldDir := root / System.FilePath.mk oldSpecDir
  if oldFiles.isEmpty && !(← oldDir.pathExists) then ok s!"C37: {oldDir}/ is gone"
  else fail s!"C37: {oldDir}/ still exists ({oldFiles.length} .naru file(s))"
  -- module 宣言 = ルート相対パス
  let mut bad : List String := []
  for f in specFiles do
    let rel := relativeTo root f
    let expected := ((rel.dropEnd ".naru".length).toString.replace "/" ".")
    match mods.find? (·.file == f) with
    | some m =>
      let actual := ".".intercalate m.name
      if actual != expected then bad := bad ++ [s!"{f}: module {actual} (expected {expected})"]
    | none => bad := bad ++ [s!"{f}: not in the compiled unit"]
  if bad.isEmpty then ok s!"C37: every file under {specDir}/ declares `module {specModulePrefix}<file name>` (= its root-relative path)"
  else fail s!"C37: module declarations do not match the paths: {bad}"
  -- 旧名のモジュール宣言と import が無い
  let oldMods := mods.toList.filter fun (m : Core.Module) => (".".intercalate m.name).startsWith oldSpecModulePrefix
  let mut oldImports : List String := []
  for f in sources do
    let text ← IO.FS.readFile f
    if (text.splitOn ("import " ++ oldSpecModulePrefix)).length > 1 then oldImports := oldImports ++ [f]
  if oldMods.isEmpty && oldImports.isEmpty then ok s!"C37: no module declaration or import named `{oldSpecModulePrefix}*` under {root}/"
  else fail s!"C37: old module names remain under {root}/: modules in {oldMods.map (·.file)}, imports in {oldImports}"

/-- C37: 生成先の配置と生成ファイルの中のモジュール名。 -/
def checkGeneratedNames (closure : List String) : M Unit := do
  for sub in ["Model", "Statements"] do
    let oldDir := generatedDir / sub / System.FilePath.mk oldSpecDir
    if ← oldDir.pathExists then fail s!"C37: {oldDir}/ still exists in the generated output" else ok s!"C37: no {oldDir}/"
  let specStmt := generatedDir / "Statements" / System.FilePath.mk specDir
  let specFiles ← listFiles specStmt "lean"
  if specFiles.isEmpty then fail s!"C37: {specStmt}/ has no generated Statements file"
  else ok s!"C37: {specStmt}/ has {specFiles.length} generated Statements file(s)"
  let all ← listFiles generatedDir "lean"
  let mut hits : List String := []
  for f in all do
    let c ← IO.FS.readFile f
    if (c.splitOn ("Model." ++ oldSpecModulePrefix)).length > 1 || (c.splitOn ("Statements." ++ oldSpecModulePrefix)).length > 1 then
      hits := hits ++ [f]
  if hits.isEmpty then ok s!"C37: no generated file mentions `Model.{oldSpecModulePrefix}*` / `Statements.{oldSpecModulePrefix}*` ({all.length} file(s) scanned)"
  else fail s!"C37: old module names in generated files: {hits}"
  let outside := specFiles.filter fun f => !(closure.contains (fileModule f))
  if outside.isEmpty then ok s!"C37: all generated modules under {specStmt}/ are in the import closure of Statements"
  else fail s!"C37: generated modules under {specStmt}/ outside the closure: {outside}"

/-- `lake env lean --deps-json <file>` の import(モジュール名、ファイルの順)。 -/
def depsOf (file : System.FilePath) : IO (Except String (List String)) := do
  let r ← runProc "lake" #["env", "lean", "--deps-json", file.toString]
  if r.exitCode != 0 then
    return .error s!"lake env lean --deps-json {file}: exit {r.exitCode}\n{tail r.stderr}"
  match Lean.Json.parse r.stdout with
  | .error e => return .error s!"deps-json of {file}: {e}"
  | .ok j =>
    match j.getObjVal? "imports" >>= Lean.Json.getArr? with
    | .error e => return .error s!"deps-json of {file}: {e}"
    | .ok entries =>
      let mut out : List String := []
      for entry in entries do
        if let .ok errs := entry.getObjVal? "errors" >>= Lean.Json.getArr? then
          if !errs.isEmpty then return .error s!"import errors in {file}: {errs.toList.map (·.compress)}"
        match entry.getObjVal? "result" >>= (·.getObjVal? "imports") >>= Lean.Json.getArr? with
        | .error e => return .error s!"deps-json of {file}: {e}"
        | .ok imps =>
          for i in imps do
            match i.getObjVal? "module" >>= Lean.Json.getStr? with
            | .ok m => out := out ++ [m]
            | .error e => return .error s!"deps-json of {file}: import entry without `module` ({e}): {i.compress}"
      return .ok out

/-- 語(英数字と `_`)に分けて `sorry` を数える(`grep -w sorry` と同じ判定: `sorry'` も数え、`sorryAx` は数えない)。 -/
def countSorry (src : String) : Nat :=
  let isIdent (c : Char) : Bool := c.isAlphanum || c == '_'
  let words := (src.toList.foldl (init := ([], "")) fun (acc : List String × String) c =>
    if isIdent c then (acc.1, acc.2.push c)
    else if acc.2.isEmpty then acc else (acc.1 ++ [acc.2], "")) |> fun (ws, last) => if last.isEmpty then ws else ws ++ [last]
  words.filter (· == "sorry") |>.length

/-- `run_cmd` で生成 structure の欄名を列挙する Lean スクリプト。 -/
def surfaceShapeScript (structName : String) : String :=
  "import Statements\nimport Lean\n\n" ++
  "/-! naru_test statements (C9): list the fields of the generated claim bundle. Written by `lake exe naru_test statements`. -/\n" ++
  "open Lean Elab Command\n\n" ++
  "run_cmd do\n" ++
  "  let env ← getEnv\n" ++
  s!"  let n := \"{structName}\".toName\n" ++
  "  unless env.contains n do throwError m!\"missing generated claim bundle: {n}\"\n" ++
  "  unless isStructure env n do throwError m!\"generated claim bundle is not a structure: {n}\"\n" ++
  "  for f in getStructureFields env n do\n" ++
  "    IO.println s!\"field: {f}\"\n"

def checks : M Unit := do
  -- 1. ソースルートから `generated/` を作り直す(Model と Statements)
  let c ← runProc "lake" #["exe", "naru", "compile"]
  if c.exitCode == 0 then ok "lake exe naru compile" else fail s!"lake exe naru compile: exit {c.exitCode}\n{tail c.stderr}"
  -- 2. 生成 Statements のビルド(生成 Model も)
  let b ← runProc "lake" #["build", "Statements"]
  if b.exitCode == 0 then ok "lake build Statements" else fail s!"lake build Statements: exit {b.exitCode}\n{tail b.stderr}"
  -- 3. import 閉包(C8): `Statements` から辿り、生成物の外は Init / NaruStd だけ
  let mut seen : List String := []
  let mut pending : List String := ["Statements"]
  let mut closureOk := true
  while !pending.isEmpty do
    let m := pending.head!
    pending := pending.tail!
    if seen.contains m then continue
    seen := seen ++ [m]
    if !(allowedImport m) then
      fail s!"import closure of Statements reaches `{m}` (generated Statements may import only NaruStd, the generated Model and other generated Statements; never Proofs)"
      closureOk := false
      continue
    if external m then continue
    let file := moduleFile m
    if !(← file.pathExists) then
      fail s!"module `{m}` in the import closure has no generated file {file}"
      closureOk := false
      continue
    match ← depsOf file with
    | .error e =>
      fail e
      closureOk := false
    | .ok imps => pending := pending ++ imps
  let generatedMods := seen.filter fun m => !(external m)
  if closureOk then
    ok s!"import closure of Statements: {generatedMods.length} generated module(s) ({(generatedMods.filter (·.startsWith "Statements")).length} Statements, {(generatedMods.filter (·.startsWith "Model")).length} Model), nothing outside Init / NaruStd / Model / Statements"
  -- 4. `generated/Statements/` の全ファイルが閉包にある
  let stmtFiles ← listFiles (generatedDir / "Statements") "lean"
  let unlisted := stmtFiles.filter fun f => !(seen.contains (fileModule f))
  if unlisted.isEmpty then ok s!"every file under generated/Statements/ is in the closure ({stmtFiles.length} file(s))"
  else fail s!"generated Statements files not reachable from generated/Statements.lean: {unlisted}"
  -- 5. `sorry` が無い(C8): 閉包の生成ファイル(Statements と Model)をすべて走査する
  let closureFiles := generatedMods.map fun m => (moduleFile m).toString
  let allFiles := closureFiles ++ stmtFiles.filter fun f => !closureFiles.contains f
  let mut sorries : List String := []
  for f in allFiles do
    if ← (System.FilePath.mk f).pathExists then
      let n := countSorry (← IO.FS.readFile f)
      if n > 0 then sorries := sorries ++ [s!"{f} ({n})"]
  if sorries.isEmpty then ok s!"no `sorry` in the generated files of the closure ({allFiles.length} file(s) scanned: Statements and Model)"
  else fail s!"`sorry` in generated files: {sorries}"
  -- 6. naru ソースの claim bundle(C9)。各ソースルート(naru.toml)を 1 単位として検査し、宣言を集める
  let roots ← match ← sourceRoots with
    | .ok rs => pure rs
    | .error e => fail e; return
  let mut decls : List Core.Decl := []
  let mut cores : Array Core.Module := #[]
  for root in roots do
    let sources ← listFiles root "naru"
    let (diags, checked) ← compileFiles sources
    if !diags.isEmpty then
      fail s!"{root}/ has {diags.size} diagnostic(s); cannot read its claim bundle"
      return
    decls := decls ++ checked.core.toList.flatMap fun (m : Core.Module) => m.decls.toList
    cores := cores ++ checked.core
    -- C37: 移植ソースの所在と module 宣言
    checkSpecSources root sources checked.core
  -- C37: 生成先の配置とモジュール名
  checkGeneratedNames seen
  -- C38: Model ファイルは runtime 宣言を出力するモジュールにだけ、Statements ファイルは spec 宣言のあるモジュールにだけ。ルートの集約ファイルは
  -- 存在するモジュールだけを import し、全 import が実在し、全宣言が現れる(ファイル数の減少で欠落を見逃さない)
  let (present, omitted) ← checkOmission "C38 generated/" generatedDir cores
  let nRuntime := cores.toList.foldl (init := 0) fun n (m : Core.Module) => n + (m.decls.filter Backend.Model.emitted).size
  if !present.isEmpty && nRuntime > 0 then ok s!"C38: the port generates {present.length} Model module(s) with {nRuntime} runtime declaration(s) in total (the omission did not empty the Model)"
  else fail s!"C38: no Model module / runtime declaration generated from the port"
  -- Model 側の `Consensus/Spec/` を丸ごと消して代用していない: 混在モジュール(runtime の fn / enum も持つ)の Model は残り、spec だけのモジュールの Model は無い
  let specModel ← listFiles (generatedDir / "Model" / System.FilePath.mk specDir) "lean"
  let specOmitted := omitted.filter fun (n, _) => n.startsWith specModulePrefix
  if !specModel.isEmpty && !specOmitted.isEmpty then
    ok s!"C38: generated/Model/{specDir}/ keeps {specModel.length} file(s) for the modules with runtime declarations and omits {specOmitted.length} spec-only module(s): {specOmitted.map (·.1)}"
  else fail s!"C38: generated/Model/{specDir}/ has {specModel.length} file(s), omitted {specOmitted.length} (expected both at least 1: mixed modules keep their Model, spec-only modules have none)"
  let rootsShown := ", ".intercalate (roots.map fun r => s!"{r}/")
  let bundles : List Core.Decl := decls.filter fun (d : Core.Decl) =>
    match d with
    | .claimBundle _ n _ => n == bundleName
    | _ => false
  match bundles with
  | [Core.Decl.claimBundle key _ items] =>
    let labels := items.map (·.1)
    ok s!"{rootsShown} declares claim bundle `{bundleName}` ({key}) with {labels.length} item(s)"
    -- その bundle を持つ生成 Statements モジュールが閉包にある(中身の無い閉包で C8 を通さない)
    let bundleModule := "Statements." ++ ".".intercalate ((key.splitOn ".").dropLast)
    if seen.contains bundleModule then ok s!"the module of the claim bundle (`{bundleModule}`) is in the import closure of Statements"
    else fail s!"the module of the claim bundle (`{bundleModule}`) is not in the import closure of Statements"
    -- C37: claim bundle は移植先 `Consensus.Spec.*` のモジュールにある(生成名は `Statements.Consensus.Spec.<module>.<bundle>`)
    if key.startsWith specModulePrefix then ok s!"C37: the claim bundle `{key}` lives under `{specModulePrefix}*`"
    else fail s!"C37: the claim bundle `{key}` is not under `{specModulePrefix}*`"
    let sortedLabels := labels.mergeSort (· ≤ ·)
    let sortedSurface := claimSurface.mergeSort (· ≤ ·)
    if sortedLabels == sortedSurface then
      ok s!"claim bundle `{bundleName}` names the {claimSurface.length} claims of verified-consensus"
    else
      let missing := claimSurface.filter fun n => !labels.contains n
      let extra := labels.filter fun n => !claimSurface.contains n
      fail s!"claim bundle `{bundleName}` ≠ the {claimSurface.length} claims of verified-consensus: missing {missing}, extra {extra}"
    -- 7. 生成 structure の欄(`run_cmd`)
    let structName := Backend.Statements.stmtName key
    IO.FS.createDirAll scratchDir
    let script := scratchDir / "SurfaceShape.lean"
    IO.FS.writeFile script (surfaceShapeScript structName)
    let r ← runProc "lake" #["env", "lean", script.toString]
    let fields := (r.stdout.splitOn "\n").filterMap fun l =>
      if l.startsWith "field: " then some (l.drop "field: ".length).toString else none
    if r.exitCode != 0 then fail s!"lake env lean {script}: exit {r.exitCode}\n{tail (r.stdout ++ r.stderr)}"
    else if fields == labels then
      ok s!"generated `{structName}` has the same {fields.length} fields in the same order as the claim bundle: {", ".intercalate fields}"
    else fail s!"fields of generated `{structName}` {fields} ≠ items of the claim bundle {labels}"
  | [] => fail s!"{rootsShown} declares no claim bundle named `{bundleName}` (C9 needs one whose items are the {claimSurface.length} claims of verified-consensus: {", ".intercalate claimSurface})"
  | bs => fail s!"{rootsShown} declares {bs.length} claim bundles named `{bundleName}`; C9 needs exactly one"

def run : IO UInt32 := runGroup "statements" checks

end NaruTest.Statements
