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

end NaruTest
