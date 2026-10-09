import Naru.Config

/-!
# `naru_test` の共通部品

各群(`grammar` / `zed` / `lsp` / …)が使う、検査結果の蓄積(`ok:` / `FAIL:` の出力)と子プロセス・ファイル・`naru.toml` の小さな補助。
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

/-- 群の実行: 検査を走らせ、FAIL が無ければ `<group>: PASS` で 0、あれば `<group>: FAIL (n)` で 1。 -/
def runGroup (group : String) (checks : M Unit) : IO UInt32 := do
  let ((), r) ← checks.run {}
  if r.failures.isEmpty then
    IO.println s!"{group}: PASS"
    return 0
  else
    IO.println s!"{group}: FAIL ({r.failures.size})"
    return 1

end NaruTest
