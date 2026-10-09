import Naru

/-!
# `naru_test` の共通部品

各群(`grammar` / `zed` / `lsp` / …)が使う、検査結果の蓄積(`ok:` / `FAIL:` の出力)と子プロセス・ファイル・`naru.toml` の小さな補助、
反例の印(先頭コメントの `期待:` の E 番号、行末の `// E0dd`)の読み、複数ファイルのコンパイル単位の検体(`tests/units/`)の列挙。
-/

namespace NaruTest

structure Result where
  failures : Array String := #[]

abbrev M := StateT Result IO

def ok (msg : String) : M Unit := IO.println s!"ok: {msg}"

def fail (msg : String) : M Unit := do
  IO.println s!"FAIL: {msg}"
  modify fun r => { r with failures := r.failures.push msg }

/-- 子プロセスを走らせる。見つからなければ exit 127 相当として返す。`env` は追加・上書きする環境変数。 -/
def runProc (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  try
    IO.Process.output { cmd, args, cwd, env }
  catch e =>
    return { exitCode := 127, stdout := "", stderr := toString e }

def readBytes (p : System.FilePath) : IO (Option ByteArray) := do
  if ← p.pathExists then return some (← IO.FS.readBinFile p) else return none

/-- 長い出力の末尾だけ。 -/
def tail (s : String) (n : Nat := 2000) : String :=
  if s.length > n then (s.drop (s.length - n)).toString else s

/-- `naru.toml`(cwd = リポジトリのルート)のソースルート(IDEAL.md C24: ソースルートの名前はここから読み、ドライバに直書きしない)。 -/
def sourceRoots : IO (Except String (List System.FilePath)) := do
  let path : System.FilePath := Naru.configFileName
  if !(← path.pathExists) then return .error s!"{path} not found (run from the repository root)"
  match ← Naru.readConfig path with
  | .ok cfg => return .ok cfg.rootPaths
  | .error e => return .error s!"{path}: {e}"

/-- ディレクトリ配下の全ファイル(パス順)の (パス, sha256)。無いディレクトリは空。 -/
def snapshotTree (dirs : List System.FilePath) : IO (List (String × String)) := do
  let mut out : Array (String × String) := #[]
  for dir in dirs do
    if !(← dir.isDir) then continue
    for p in (← dir.walkDir) do
      if !(← p.isDir) then out := out.push (p.toString, Naru.sha256Hex (← IO.FS.readBinFile p))
  return (out.qsort (·.1 < ·.1)).toList

/-- 群の実行: 検査を走らせ、FAIL が無ければ `<group>: PASS` で 0、あれば `<group>: FAIL (n)` で 1。 -/
def runGroup (group : String) (checks : M Unit) : IO UInt32 := do
  let ((), r) ← checks.run {}
  if r.failures.isEmpty then
    IO.println s!"{group}: PASS"
    return 0
  else
    IO.println s!"{group}: FAIL ({r.failures.size})"
    return 1

/-! ## 反例の印 -/

/-- 文字列の中で最初に現れる `E0dd`。 -/
def firstCode (s : String) : Option String := Id.run do
  let cs := s.toList.toArray
  for i in [0:cs.size] do
    if cs[i]? == some 'E' && cs[i + 1]? == some '0' && (cs[i + 2]?.map Char.isDigit).getD false
        && (cs[i + 3]?.map Char.isDigit).getD false then
      return some (String.ofList [cs[i]!, cs[i + 1]!, cs[i + 2]!, cs[i + 3]!])
  return none

/-- 反例の本文(先頭のコメント)が名指しする E 番号: `期待:` の行の `E0dd`、その行が無ければ本文で最初の `E0dd`
(`type_path_escape.naru` のように、説明の中で別の番号に先に触れる反例がある)。 -/
def namedCode (text : String) : Option String :=
  match (text.splitOn "\n").find? (fun l => (l.splitOn "期待").length > 1 && (firstCode l).isSome) with
  | some l => firstCode l
  | none => firstCode text

/-- 反例の行末の `// E0dd`(コードの後ろのコメント)が印す期待: (1 始まりの行, E 番号)。先頭のコメント行(コードの無い行)は印ではない。 -/
def markedDiagnostics (text : String) : List (Nat × String) := Id.run do
  let mut out : List (Nat × String) := []
  let mut i := 1
  for l in text.splitOn "\n" do
    let parts := l.splitOn "//"
    if parts.length ≥ 2 then
      let code := parts.head!
      let comment := (parts.getLast!).trimAscii.toString
      if !code.trimAscii.toString.isEmpty then
        if let some c := firstCode comment then
          if comment.startsWith c then out := out ++ [(i, c)]
    i := i + 1
  return out

/-- 1 始まりの (行, 列) にある識別子のトークン(英数字と `_`。`?` の末尾を含む)。その位置が識別子の途中・識別子でなければ空。 -/
def tokenAt (text : String) (line col : Nat) : String := Id.run do
  let chars := ((text.splitOn "\n").getD (line - 1) "").toList.toArray
  let start := col - 1
  let isIdent (c : Char) : Bool := c.isAlphanum || c == '_'
  if !((chars[start]?.map fun c => c.isAlpha || c == '_').getD false) then return ""
  let mut e := start
  while (chars[e]?.map isIdent).getD false do e := e + 1
  if chars[e]? == some '?' then e := e + 1
  return String.ofList (chars.toList.drop start |>.take (e - start))

/-- CLI の標準エラーの診断行 `file:line:col: error[E0dd]: msg` → (ファイル, 行, 列, E 番号, メッセージ)。 -/
def parseFileDiags (stderr : String) : List (String × Nat × Nat × String × String) :=
  (stderr.splitOn "\n").filterMap fun l =>
    if (l.splitOn ": error[").length < 2 then none
    else
      let parts := l.splitOn ":"
      let msg := ": ".intercalate (((l.splitOn ": error[").getLast!.splitOn "]: ").drop 1)
      match parts[0]?, parts[1]?.bind (·.trimAscii.toString.toNat?), parts[2]?.bind (·.trimAscii.toString.toNat?),
            firstCode ((l.splitOn ": error[").getLast!) with
      | some file, some line, some col, some code => some (file, line, col, code, msg)
      | _, _, _, _ => none

/-! ## 複数ファイルのコンパイル単位の検体(`tests/units/`、IDEAL.md C18)

`tests/units/reject/<名前>/` と `tests/units/accept/<名前>/` に、`naru.toml`(`sources = ["src"]`)と `src/**/*.naru`(1 つのコンパイル単位)。
反例は各ファイルの行末の `// E0dd` が期待の (行, 番号)。反例の `fix/<ファイル名>.naru` は、その `src/` のファイルを置き換えると誤りが消える内容
(`naru_test lsp` が didChange で差し替え、関係する URI すべての診断が消えることを確かめる)。 -/

def unitsDir : System.FilePath := "tests" / "units"

/-- 1 つの検体: 名前、ディレクトリ、`src/` の `.naru`(パス順)、`fix/` の (src のパス, 置換後の内容)。 -/
structure UnitFixture where
  name : String
  dir : System.FilePath
  files : List String
  fixes : List (String × String)

/-- `tests/units/<kind>/` の検体(名前順)。 -/
def listUnits (kind : String) : IO (List UnitFixture) := do
  let base := unitsDir / kind
  if !(← base.isDir) then return []
  let entries ← base.readDir
  let names := (entries.map fun e => e.fileName).qsort (· < ·)
  let mut out : List UnitFixture := []
  for name in names do
    let dir := base / name
    if !(← dir.isDir) then continue
    let files ← Naru.listFiles (dir / "src") "naru"
    let mut fixes : List (String × String) := []
    for f in (← Naru.listFiles (dir / "fix") "naru") do
      let fileName := ((System.FilePath.mk f).fileName).getD f
      let target := (dir / "src" / fileName).toString
      fixes := fixes ++ [(target, ← IO.FS.readFile f)]
    let u : UnitFixture := { name := name, dir := dir, files := files, fixes := fixes }
    out := out ++ [u]
  return out

/-! ## 生成 Model / Statements の省略の規則(IDEAL.md C38)

Model ファイルは Lean の runtime 宣言を実際に出力するモジュール(`Backend.Model.emitted` な宣言が 1 つ以上)にだけ、Statements ファイルは
spec 宣言のあるモジュールにだけでき、ルートの集約ファイル `Model.lean` / `Statements.lean` は宣言が無くても生成されて、存在する生成モジュールだけを
import する。`statements` 群(`generated/`)と `regression`(`tests/units/accept/omit_model` と設定変更プロジェクトの `custom/`)が同じ
`checkOmission` で、生成ファイルの有無・ルートの import・全 import の実在・全宣言の出現を Core と照合する。 -/

/-- 生成ファイルの `import` 行のモジュール名(ファイルの順)。 -/
def importsOf (content : String) : List String :=
  (content.splitOn "\n").filterMap fun l =>
    if l.startsWith "import " then some ((l.drop "import ".length).toString.trimAscii.toString) else none

/-- 生成 Lean の宣言の頭(`def` / `structure` / `inductive` / `abbrev` で始まる行)の完全修飾名。 -/
def declHeads (content : String) : List String :=
  (content.splitOn "\n").filterMap fun l =>
    ["def ", "structure ", "inductive ", "abbrev "].findSome? fun kw =>
      if l.startsWith kw then ((l.drop kw.length).toString.splitOn " ").head? else none

/-- 生成モジュール名 → 生成先からの相対パス(`Model.A.B` → `Model/A/B.lean`。`«»` は外す)。 -/
def modulePathOf (m : String) : String :=
  ((m.replace "«" "").replace "»" "").replace "." "/" ++ ".lean"

/-- モジュールが Model ファイルを出さない理由(出すなら none): 宣言なし / input だけ / spec 宣言(と input)だけ。 -/
def omissionReason (m : Naru.Core.Module) : Option String :=
  if m.decls.any Naru.Backend.Model.emitted then none
  else if m.decls.isEmpty then some "no declarations"
  else if m.decls.all Naru.Backend.Model.isInput then some "only inputs"
  else if m.decls.any Naru.Backend.Model.isInput then some "only spec declarations and inputs"
  else some "only spec declarations"

/-- C38: 生成先 `out` の Model / Statements が Core のモジュール・宣言と対応することを照合する(`label` は項目の接頭辞):
- Model ファイルは runtime 宣言を出力するモジュールにだけ、Statements ファイルは spec 宣言のあるモジュールにだけある(Core に無いモジュールの
  ファイル・旧構成の生成物も無い)。
- ルート `Model.lean` / `Statements.lean` はあり(宣言が無くても)、存在する生成モジュールをちょうど import する。
- 生成ファイルの全 `import` が `NaruStd` か実在する生成ファイル(存在しない生成モジュールへの import は 0 件)。
- 出力される runtime 宣言のすべてが Model ファイルに、spec 宣言のすべてが Statements ファイルに宣言の頭として現れる(ファイル数の減少で欠落を見逃さない)。
返り値: (Model ファイルになった生成モジュール名, 省いた naru モジュール名と理由)。 -/
def checkOmission (label : String) (out : System.FilePath) (core : Array Naru.Core.Module) :
    M (List String × List (String × String)) := do
  let mut present : List String := []
  let mut specPresent : List String := []
  let mut omitted : List (String × String) := []
  let mut bad : List String := []
  let mut missingDecls : List String := []
  let mut nRuntime := 0
  let mut nSpec := 0
  for m in core do
    let modelFile := out / System.FilePath.mk (Naru.Backend.Model.modulePath m.name)
    let stmtFile := out / System.FilePath.mk (Naru.Backend.Statements.stmtPath m.name)
    let wantModel := (omissionReason m).isNone
    let wantSpec := m.decls.any Naru.Backend.Statements.isSpecDecl
    let hasModel ← modelFile.pathExists
    let hasStmt ← stmtFile.pathExists
    if hasModel != wantModel then
      bad := bad ++ [if wantModel then s!"{modelFile} is missing (the module outputs runtime declarations)"
                     else s!"{modelFile} exists although the module outputs no runtime declaration"]
    if hasStmt != wantSpec then
      bad := bad ++ [if wantSpec then s!"{stmtFile} is missing (the module has spec declarations)"
                     else s!"{stmtFile} exists although the module has no spec declaration"]
    match omissionReason m with
    | none => present := present ++ [Naru.Backend.Model.leanModule m.name]
    | some why => omitted := omitted ++ [(Naru.renderPath m.name, why)]
    if wantSpec then specPresent := specPresent ++ [Naru.Backend.Statements.stmtModule m.name]
    if wantModel && hasModel then
      let heads := declHeads (← IO.FS.readFile modelFile)
      for d in m.decls do
        if Naru.Backend.Model.emitted d then
          nRuntime := nRuntime + 1
          let want := Naru.Backend.Model.leanName d.key
          if !(heads.contains want) then missingDecls := missingDecls ++ [s!"{want} ({modelFile})"]
    if wantSpec && hasStmt then
      let heads := declHeads (← IO.FS.readFile stmtFile)
      for d in m.decls do
        if Naru.Backend.Statements.isSpecDecl d then
          nSpec := nSpec + 1
          let want := Naru.Backend.Statements.stmtName d.key
          if !(heads.contains want) then missingDecls := missingDecls ++ [s!"{want} ({stmtFile})"]
  -- 生成先のファイル集合は期待とちょうど一致する(Core に無いモジュールのファイル・旧構成の生成物が無い)
  let expectedFiles := present.map modulePathOf ++ specPresent.map modulePathOf ++ ["Model.lean", "Statements.lean"]
  let mut actual : List String := []
  for sub in ["Model", "Statements"] do
    let files ← Naru.listFiles (out / sub) "lean"
    actual := actual ++ files.map fun (f : String) => (f.drop (out.toString.length + 1)).toString
    if ← (out / (sub ++ ".lean")).pathExists then actual := actual ++ [sub ++ ".lean"]
  let stray := actual.filter fun f => !expectedFiles.contains f
  let absent := expectedFiles.filter fun f => !actual.contains f
  if bad.isEmpty && stray.isEmpty && absent.isEmpty then
    ok s!"{label}: Model files exactly for the {present.length} module(s) with runtime declarations and Statements files exactly for the {specPresent.length} module(s) with spec declarations ({actual.length} files); no Model file for {omitted.length} module(s): {omitted.map fun (n, why) => s!"{n} ({why})"}"
  else fail s!"{label}: generated file layout: {bad ++ stray.map (fun f => s!"stray {f}") ++ absent.map (fun f => s!"absent {f}")}"
  -- ルートの集約ファイル: 宣言が無くても生成され、存在する生成モジュールをちょうど import する
  for (sub, want) in [("Model", present), ("Statements", specPresent)] do
    let rootFile := out / (sub ++ ".lean")
    if !(← rootFile.pathExists) then
      fail s!"{label}: {rootFile} is missing (the root aggregate file is generated even without declarations)"
    else
      let imps := importsOf (← IO.FS.readFile rootFile)
      if imps.mergeSort (· ≤ ·) == want.mergeSort (· ≤ ·) then
        ok s!"{label}: {rootFile} imports exactly the {want.length} generated {sub} module(s)"
      else fail s!"{label}: {rootFile} imports {imps} but the generated {sub} modules are {want}"
  -- 全 import が実在する
  let mut unresolved : List String := []
  let mut nImports := 0
  for f in actual do
    for i in importsOf (← IO.FS.readFile (out / f)) do
      nImports := nImports + 1
      if i == "NaruStd" || i.startsWith "NaruStd." then continue
      if !(← (out / System.FilePath.mk (modulePathOf i)).pathExists) then unresolved := unresolved ++ [s!"{f}: import {i}"]
  if unresolved.isEmpty then
    ok s!"{label}: all {nImports} imports of the {actual.length} generated files resolve to NaruStd or an existing generated file (0 imports of a non-existent generated module)"
  else fail s!"{label}: imports of non-existent generated modules: {unresolved} ({nImports} imports scanned)"
  -- 宣言の欠落なし(宣言の無い単位では 0 件: ルートの集約ファイルだけが生成される)
  if missingDecls.isEmpty then
    ok s!"{label}: all {nRuntime} emitted runtime declaration(s) appear in the Model files and all {nSpec} spec declaration(s) in the Statements files (no declaration lost with the omitted files)"
  else fail s!"{label}: declarations missing from the generated files: {missingDecls.take 10} ({nRuntime} runtime / {nSpec} spec expected)"
  return (present, omitted)

end NaruTest
