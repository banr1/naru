import Naru
import NaruTest.Common

/-!
# `naru_test grammar` — tree-sitter 文法の検査(IDEAL.md C16)

`editors/tree-sitter-naru/` の文法が naru の正本(`compiler/Naru/Parser.lean`・`docs/language.md`)に追従していることを、
tree-sitter CLI(0.27)を子プロセスで呼んで確かめる。リポジトリのルートで実行する。

1. `tree-sitter generate` の出力が追跡対象の `src/` と一致する(`grammar.js` と `tree-sitter.json` を一時ディレクトリに写して
   generate し、`src/` 配下の全ファイルをバイト単位で比べる。`src/` は手で編集しない: IDEAL.md「不変条件」)。
2. `tree-sitter build` が exit 0(共有ライブラリを一時ディレクトリに出す)。
3. `naru.toml` のソースルート(`specs/consensus/`)・`tests/accept/`・`tests/reject/` 配下のすべての `.naru`(E010 を期待する反例は除く)の `tree-sitter parse -q` が
   exit 0 で、出力に ERROR / MISSING が無い。
4. `tests/accept/editors_syntax.naru` への `tree-sitter query queries/highlights.scm` で、`tests/accept/editors_syntax.captures`
   に書いた(行、捕捉名、字句)がすべて出て、捕捉名に keyword / type / constructor / comment / string / number / function /
   property がすべて含まれる。
5. `tests/accept/editors_syntax.naru` がコンパイラの検査を通る(`lake exe naru compile tests/accept/editors_syntax.naru` と同じ
   `compileFiles` を同一プロセスで呼ぶ)。
6. `editors/zed-naru/languages/naru/highlights.scm` が `editors/tree-sitter-naru/queries/highlights.scm` と同一。

一時ファイルは `.lake/naru/test/grammar/` に置く(追跡対象外)。
-/

namespace NaruTest.Grammar

def grammarDir : System.FilePath := "editors" / "tree-sitter-naru"
def zedHighlights : System.FilePath := "editors" / "zed-naru" / "languages" / "naru" / "highlights.scm"
def syntaxExample : System.FilePath := "tests" / "accept" / "editors_syntax.naru"
def capturesExpected : System.FilePath := "tests" / "accept" / "editors_syntax.captures"
def scratchDir : System.FilePath := ".lake" / "naru" / "test" / "grammar"

/-- `highlights.scm` が必ず捕捉していなければならない名前(C16)。 -/
def requiredCaptures : List String :=
  ["keyword", "type", "constructor", "comment", "string", "number", "function", "property"]

/-- `dir` 配下のファイル(ディレクトリを除く)を、`dir` からの相対パスでパス順に列挙する。 -/
def listFilesUnder (dir : System.FilePath) : IO (List String) := do
  if !(← dir.isDir) then return []
  let all ← dir.walkDir
  let mut files : Array String := #[]
  let prefixLen := dir.toString.length + 1
  for p in all do
    if !(← p.isDir) then
      files := files.push (p.toString.drop prefixLen).toString
  return (files.qsort (· < ·)).toList

/-- `.naru` をパス順に列挙する(`Main.lean` の `listFiles` と同じ順)。 -/
def listNaru (dir : System.FilePath) : IO (List String) := do
  if !(← dir.isDir) then return []
  let all ← dir.walkDir
  let hits := all.filter (·.extension == some "naru")
  return (hits.qsort (fun a b => a.toString < b.toString)).toList.map (·.toString)

/-! ## 1. generate の出力が `src/` と一致 -/

def checkGenerate : M Unit := do
  let gen := scratchDir / "generate"
  if ← gen.isDir then IO.FS.removeDirAll gen
  IO.FS.createDirAll gen
  for f in ["grammar.js", "tree-sitter.json"] do
    IO.FS.writeFile (gen / f) (← IO.FS.readFile (grammarDir / f))
  let out ← runProc "tree-sitter" #["generate"] (some gen)
  if out.exitCode != 0 then
    fail s!"tree-sitter generate exit {out.exitCode}: {tail out.stderr}"
    return
  let tracked ← listFilesUnder (grammarDir / "src")
  let fresh ← listFilesUnder (gen / "src")
  if tracked.isEmpty then
    fail s!"{grammarDir / "src"} is empty (run `tree-sitter generate` in {grammarDir})"
    return
  if tracked != fresh then
    fail s!"tree-sitter generate wrote a different file set: tracked {tracked}, fresh {fresh}"
    return
  let mut differ : Array String := #[]
  for rel in tracked do
    let a ← readBytes (grammarDir / "src" / rel)
    let b ← readBytes (gen / "src" / rel)
    match a, b with
    | some a, some b => if a.data != b.data then differ := differ.push rel
    | _, _ => differ := differ.push rel
  if differ.isEmpty then
    ok s!"tree-sitter generate matches tracked src/ ({tracked.length} files)"
  else
    fail s!"tree-sitter generate differs from tracked src/ in {differ} (regenerate and commit src/)"

/-! ## 2. build -/

def checkBuild : M Unit := do
  -- cwd は文法ディレクトリなので、出力先は絶対パスで渡す(相対だと `editors/tree-sitter-naru/.lake/` に落ちる)
  let lib := (← IO.currentDir) / scratchDir / "naru.dylib"
  let out ← runProc "tree-sitter" #["build", "-o", lib.toString] (some grammarDir)
  if out.exitCode == 0 then
    ok s!"tree-sitter build exit 0 ({lib})"
  else
    fail s!"tree-sitter build exit {out.exitCode}: {tail out.stderr}"

/-! ## 3. 全ソースの parse -/

/-- E010 を期待する反例: `tests/reject/` のファイルで、本文(先頭のコメント)に `E010` と書いてあるもの。 -/
def expectsSyntaxError (path : String) : IO Bool := do
  let src ← IO.FS.readFile path
  return (src.splitOn "E010").length > 1

def checkParse : M Unit := do
  let roots ← match ← sourceRoots with
    | .ok rs => pure (rs.map (·.toString))
    | .error e => fail e; return
  let mut files : List String := []
  let dirs := roots ++ ["tests/accept", "tests/reject"]
  for dir in dirs do
    for f in ← listNaru dir do
      if dir == "tests/reject" && (← expectsSyntaxError f) then continue
      files := files ++ [f]
  if files.isEmpty then
    fail s!"no .naru sources found under {", ".intercalate dirs}"
    return
  let cwd ← IO.currentDir
  let abs := files.map fun f => (cwd / System.FilePath.mk f).toString
  let out ← runProc "tree-sitter" (#["parse", "-q"] ++ abs.toArray) (some grammarDir)
  let bad := (out.stdout.splitOn "\n").filter fun l =>
    (l.splitOn "ERROR").length > 1 || (l.splitOn "MISSING").length > 1
  if out.exitCode == 0 && bad.isEmpty then
    ok s!"tree-sitter parse -q: {files.length} files, ERROR / MISSING 0"
  else
    fail s!"tree-sitter parse -q exit {out.exitCode}, {bad.length} file(s) with ERROR / MISSING:\n{"\n".intercalate bad}\n{tail out.stderr 500}"

/-! ## 4. highlights の捕捉 -/

structure Capture where
  line : Nat          -- 1 始まり
  name : String
  text : String
deriving BEq, Repr

/-- `tree-sitter query` の 1 行 `capture: N - name, start: (r, c), end: (r, c), text: \`…\`` を読む。 -/
def parseCaptureLine (l : String) : Option Capture := do
  let rest := (l.splitOn "capture: ")[1]?
  let rest ← rest
  let name ← ((rest.splitOn " - ")[1]?).bind fun s => (s.splitOn ",")[0]?
  let row ← ((rest.splitOn "start: (")[1]?).bind fun s => ((s.splitOn ",")[0]?).bind fun r => r.trimAscii.toNat?
  let textParts := rest.splitOn "text: `"
  if textParts.length < 2 then none
  let text := "text: `".intercalate (textParts.drop 1)
  let text := (text.dropEnd 1).toString
  some { line := row + 1, name, text }

/-- 期待値ファイルを読む。1 行 = `<行番号> TAB <捕捉名> TAB <字句>`。空行と `#` 始まりはコメント。
それ以外の形の行は黙って捨てず、エラーとして返す。 -/
def parseExpectations (src : String) : Array Capture × Array String := Id.run do
  let mut out := #[]
  let mut bad := #[]
  for l in src.splitOn "\n" do
    if l.trimAscii.toString.isEmpty || l.startsWith "#" then continue
    match l.splitOn "\t" with
    | [line, name, text] =>
      match line.trimAscii.toNat? with
      | some n => out := out.push { line := n, name := name.trimAscii.toString, text }
      | none => bad := bad.push l
    | _ => bad := bad.push l
  return (out, bad)

def checkQuery : M Unit := do
  let cwd ← IO.currentDir
  let out ← runProc "tree-sitter"
    #["query", "queries/highlights.scm", (cwd / syntaxExample).toString] (some grammarDir)
  if out.exitCode != 0 then
    fail s!"tree-sitter query exit {out.exitCode}: {tail out.stderr}"
    return
  let observed := ((out.stdout.splitOn "\n").filterMap parseCaptureLine)
  let (expected, malformed) := parseExpectations (← IO.FS.readFile capturesExpected)
  if !malformed.isEmpty then
    fail s!"{capturesExpected}: {malformed.size} malformed line(s) (expected `<line> TAB <capture> TAB <text>`): {malformed}"
    return
  if expected.isEmpty then
    fail s!"{capturesExpected} has no expectations"
    return
  let observedNames := observed.map (·.name)
  let missingKinds := requiredCaptures.filter fun k => !observedNames.contains k
  let missing := expected.filter fun e => !observed.contains e
  if missingKinds.isEmpty && missing.isEmpty then
    ok s!"tree-sitter query: {expected.size} expected captures found (observed {observed.length}); kinds {requiredCaptures} all present"
  else
    for k in missingKinds do fail s!"highlights.scm never captures @{k} in {syntaxExample}"
    for e in missing do
      let sameLine := observed.filter (·.line == e.line)
      fail s!"expected line {e.line} @{e.name} `{e.text}` not captured (line {e.line} has {sameLine.map fun c => s!"@{c.name} `{c.text}`"})"

/-! ## 5. 受理例がコンパイラの検査を通る -/

def checkCompile : M Unit := do
  let (diags, checked) ← Naru.compileFiles [syntaxExample.toString]
  if diags.isEmpty then
    ok s!"naru compile {syntaxExample}: checked {checked.mods.size} module(s)"
  else
    for d in diags do IO.println s!"  {d.render}"
    fail s!"naru compile {syntaxExample}: {diags.size} error(s)"

/-! ## 6. Zed 側の highlights が同一 -/

def checkZedHighlights : M Unit := do
  let a ← readBytes (grammarDir / "queries" / "highlights.scm")
  let b ← readBytes zedHighlights
  match a, b with
  | some a, some b =>
    if a.data == b.data then ok s!"{zedHighlights} is identical to {grammarDir / "queries" / "highlights.scm"}"
    else fail s!"{zedHighlights} differs from {grammarDir / "queries" / "highlights.scm"}"
  | _, _ => fail s!"{zedHighlights} or {grammarDir / "queries" / "highlights.scm"} is missing"

def run : IO UInt32 := do
  if !(← (grammarDir / "grammar.js").pathExists) then
    IO.eprintln s!"naru_test grammar: {grammarDir / "grammar.js"} not found (run from the repository root)"
    return 2
  IO.FS.createDirAll scratchDir
  runGroup "naru_test grammar" do
    checkGenerate
    checkBuild
    checkParse
    checkQuery
    checkCompile
    checkZedHighlights

end NaruTest.Grammar
