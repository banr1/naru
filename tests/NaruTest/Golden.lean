import NaruTest.Common

/-!
# `naru_test golden` — C10 の golden test のドライバ

`tests/golden/Golden.lean`(手書き Model と生成 Model を 1 つの Lean プログラムから import し、同じ fixture を両側で畳み込んで
MISMATCH を数える)を、verified-consensus の `LEAN_PATH`(mathlib と手書き Model の olean)にルートの `.lake/build/lib/lean`
(生成 Model `Model` と `NaruStd`)を足して `lean --run` で走らせ、出力の `ok` / `FAIL` / `MISMATCH total` を検査項目にする。

- 先に `lake build Model`(生成 Model)を走らせる。手書き Model は `verified-consensus/.lake/build` にビルド済みであること
  (無ければ `cd verified-consensus && lake build DecoupledConsensusModel`。周回は verified-consensus を変えない)。
- `lake exe naru_test golden [--finality-horizon N]`。N は Witnesses の FinalityLiveness run の horizon(既定は Witnesses の 33729)。
  interpreter(`lean --run`)では手書き Model の 1 tick が 0.1 秒以上かかるので、全 horizon は compile した実行形が要る(周回 21 の計測)。
  既定より小さい N で PASS しても C10 の証拠にはならない(`note:` を出す)。
-/

namespace NaruTest.Golden

def vcDir : System.FilePath := "verified-consensus"
def goldenFile : System.FilePath := "tests" / "golden" / "Golden.lean"
def fullHorizon : Nat := 33729

/-- C10 の文面が求める case(Witnesses の 4 run、複数ノード・equivocation を含む naru scenario 3 本以上、scenario の `observe` との結び付き)。
`Golden.lean` から case が消えても `MISMATCH total: 0` では通らないよう、`ok <case>:` の行があることを 1 つずつ確かめる。 -/
def expectedCases (horizon : Nat) : List String :=
  [ "witness:weakGenesis", "witness:outage", "witness:strongRecovery", s!"witness:finalityLiveness(horizon {horizon})",
    "scenario:basic", "scenario:basic/observe trace(s, rho, v0)",
    "scenario:outage", "scenario:outage/observe trace(s, rho, v0)",
    "scenario:strongRecovery", "scenario:strongRecovery/observe trace(s, rho, v0)",
    "scenario:twoNodes", "scenario:twoNodes/observe trace(s, rho, v1)",
    "scenario:equivocation/twoFaced", "scenario:equivocation/observe trace(s, twoFaced, v0)",
    "scenario:equivocation/oneVote", "scenario:equivocation/observe trace(s, oneVote, v0)" ]

def checks (horizon : Nat) : M Unit := do
  -- 1. 生成 Model
  let b ← runProc "lake" #["build", "Model"]
  if b.exitCode == 0 then ok "lake build Model" else fail s!"lake build Model: exit {b.exitCode}\n{tail b.stderr}"
  -- 2. 手書き Model の olean
  let inst := vcDir / ".lake" / "build" / "lib" / "lean" / "DecoupledConsensusModel" / "Execution" / "Instance.olean"
  if ← inst.pathExists then ok "verified-consensus: DecoupledConsensusModel/Execution/Instance.olean exists"
  else fail s!"{inst} not found (cd verified-consensus && lake build DecoupledConsensusModel)"
  -- 3. LEAN_PATH = verified-consensus の環境 + ルートの build
  let e ← runProc "lake" #["env", "printenv", "LEAN_PATH"] (cwd := some vcDir)
  let vcPath := e.stdout.trimAscii.toString
  if e.exitCode == 0 && !vcPath.isEmpty then ok "lake env printenv LEAN_PATH (verified-consensus)"
  else fail s!"lake env printenv LEAN_PATH in verified-consensus: exit {e.exitCode}\n{tail e.stderr}"
  let rootLib ← IO.FS.realPath (".lake" / "build" / "lib" / "lean")
  let leanPath := vcPath ++ ":" ++ rootLib.toString
  -- 4. golden を 1 つの Lean プログラムとして実行
  let r ← runProc "lean" #["--run", goldenFile.toString, "--finality-horizon", toString horizon] (env := #[("LEAN_PATH", some leanPath)])
  let lines := r.stdout.splitOn "\n"
  for l in lines do
    if l.startsWith "ok " then ok (l.drop 3).toString
    else if l.startsWith "FAIL " then fail (l.drop 5).toString
    else if l.startsWith "MISMATCH " && !l.startsWith "MISMATCH total" then IO.println l
    else if l.startsWith "  " then IO.println l
  let missing := (expectedCases horizon).filter (fun c => !(lines.any (fun l => l.startsWith s!"ok {c}:")))
  if missing.isEmpty then ok s!"all {(expectedCases horizon).length} expected cases reported ok"
  else fail s!"expected cases not ok: {missing}"
  match lines.find? (·.startsWith "MISMATCH total: ") with
  | some t => if t == "MISMATCH total: 0" then ok t else fail t
  | none => fail s!"no `MISMATCH total` line in the output of lean --run {goldenFile} (exit {r.exitCode})\n{tail r.stderr}"
  if r.exitCode == 0 then ok s!"lean --run {goldenFile} --finality-horizon {horizon} exit 0"
  else fail s!"lean --run {goldenFile}: exit {r.exitCode}\n{tail r.stderr}"
  if horizon < fullHorizon then
    IO.println s!"note: finalityLiveness horizon {horizon} of {fullHorizon} (partial: C10 requires the full Witnesses run)"

def run (horizon : Nat) : IO UInt32 := runGroup "golden" (checks horizon)

end NaruTest.Golden
