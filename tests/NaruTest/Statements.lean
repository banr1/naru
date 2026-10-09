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
  for root in roots do
    let sources ← listFiles root "naru"
    let (diags, checked) ← compileFiles sources
    if !diags.isEmpty then
      fail s!"{root}/ has {diags.size} diagnostic(s); cannot read its claim bundle"
      return
    decls := decls ++ checked.core.toList.flatMap fun (m : Core.Module) => m.decls.toList
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
