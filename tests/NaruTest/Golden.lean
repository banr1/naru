import NaruTest.Common

/-!
# `naru_test golden` — C10 の golden test のドライバ

`tests/golden/Golden.lean`(手書き Model と生成 Model を 1 つの Lean プログラムから import し、同じ fixture を両側で畳み込んで
MISMATCH を数える)を、`third_party/verified-consensus`(submodule)の `LEAN_PATH`(mathlib と手書き Model の olean)にルートの
`.lake/build/lib/lean`(生成 Model `Model` と `NaruStd`)を足して `lean --run` で走らせ、出力の `comparator …` / `ok` / `FAIL` /
`MISMATCH total` を検査項目にする。

- 先に現在の naru ソースを再生成(`lake exe naru compile`)して `lake build Model`(生成 Model)を走らせる(IDEAL.md C10: 再生成してビルドしてから
  全 16 ケース)。手書き Model は `third_party/verified-consensus/.lake/build` にビルド済みであること
  (無ければ `cd third_party/verified-consensus && lake build DecoupledConsensusModel`。周回は verified-consensus を変えない)。
- `lake exe naru_test golden [--finality-horizon N]`。N は FinalityLiveness の prefix の horizon(t = 0 … N、N + 1 tick)。既定は C10 が
  求める 100(手書き側 interpreter で約 8 分)。Witness 自身の horizon 33729 は両 Model とも実行不能(周回 21 の計測)。
  C10 の証拠は引数なし(= horizon 100)の PASS。他の N で PASS しても C10 の証拠にはならない(`note:` を出す。回帰は `--finality-horizon 40`)。
- `lake exe naru_test golden --comparator`: 比較器の検体だけ(`Golden.lean --comparator-check`。C10 の比較器回帰、`naru_test regression` が呼ぶ)。
  同じ意味の両表現が一致する検体(`expectedAgreements`)と、各フィールド・入れ子・親関係・Option・variant・リスト順序を一つだけ変えた検体
  (`expectedProbes`)がすべて `ok` で報告され、旧 3 つ組 `(kind, root, author)` が見逃す検体(`expectedLegacyMisses`。`none` と root 99 の `some` の
  混同を含む)が `legacy-miss` で報告されること。引数なしの golden もまず検体を検査するので、同じ項目を要求する。
-/

namespace NaruTest.Golden

def vcDir : System.FilePath := "third_party" / "verified-consensus"
def goldenFile : System.FilePath := "tests" / "golden" / "Golden.lean"
/-- C10 の FinalityLiveness の prefix の horizon(IDEAL.md: `horizon = 100`、t = 0〜100、101 tick)。 -/
def c10Horizon : Nat := 100

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- C10 の文面が求める case(Witnesses の 4 run、複数ノード・equivocation を含む naru scenario 3 本以上、scenario の `observe` との結び付き)。
`Golden.lean` から case が消えても `MISMATCH total: 0` では通らないよう、`ok <case>:` の行があることを 1 つずつ確かめる。 -/
def expectedCases (horizon : Nat) : List String :=
  [ "witness:weakGenesis", "witness:outage", "witness:strongRecovery(seed rho 30)", s!"witness:finalityLiveness(horizon {horizon})",
    "scenario:basic", "scenario:basic/observe trace(s, rho, v0)",
    "scenario:outage", "scenario:outage/observe trace(s, rho, v0)",
    "scenario:strongRecovery", "scenario:strongRecovery/observe trace(s, rho, v0)",
    "scenario:twoNodes", "scenario:twoNodes/observe trace(s, rho, v1)",
    "scenario:equivocation/twoFaced", "scenario:equivocation/observe trace(s, twoFaced, v0)",
    "scenario:equivocation/oneVote", "scenario:equivocation/observe trace(s, oneVote, v0)" ]

/-- 比較器の検体のうち、同じ意味の両表現が一致する検体(`Golden.lean` の `Probe.agreements`)。 -/
def expectedAgreements : List String :=
  [ "gfVote", "row full", "row none / empty / none", "row timeout", "block with 2 ancestors, votes, support, rows", "genesis",
    "tick list block, gfVote, attest" ]

/-- 比較器の検体のうち、一つだけ変えた検体(`Golden.lean` の `Probe.probes`)。`Golden.lean` から検体が消えても通らないよう 1 つずつ確かめる。
IDEAL.md C10: 各フィールド・入れ子・親関係・Option・variant・リスト順序を一つだけ変えた検体はすべて不一致、`none` と通常の root の `some` を混同しない。 -/
def expectedProbes : List String :=
  [ "kind block → gfVote", "kind gfVote → attest",
    "vote.author", "vote.slot", "vote.head",
    "row.author", "row.round", "row.confirmed some → none", "row.confirmed some 4 → some 5", "row.confirmed none → some 99",
    "row.confirmed none → some 0 (genesis root)", "row.heightPair vote → empty", "row.heightPair empty → vote", "row.heightPair.height",
    "row.heightPair.entry", "row.heightPair.timeout", "row.finalityPair some → none", "row.finalityPair none → some",
    "row.finalityPair.height", "row.finalityPair.target",
    "block node → genesis", "block.slot", "block.root", "block.proposer", "block.parent.root", "block.parent.slot", "block.parent.proposer",
    "block.parent.votes element", "block.parent.rows nested timeout", "block.parent.parent.root (grandparent)",
    "block.parent.parent.parent genesis → node (one more ancestor)", "block.votes order", "block.votes element.slot",
    "block.votes dropped element", "block.support element", "block.support added element", "block.support order", "block.rows order",
    "block.rows dropped element", "block.rows nested confirmed none → some 99", "block.rows nested finalityPair.target",
    "block.rows nested heightPair empty → vote" ]

/-- 失敗例: 周回 35 までの 3 つ組 `(kind, root, author)` が見逃す検体(`Golden.lean` の `H.Legacy`)。これらを旧比較が見逃し、現在の比較器が
検出することで、検体が元の不具合(`confirmed` の `none` と root 99 の混同、slot / round / 祖先 / 列の順序の無視)を捉えていると確かめる。 -/
def expectedLegacyMisses : List String :=
  [ "vote.slot", "row.round", "row.confirmed none → some 99", "row.heightPair.timeout", "row.finalityPair some → none",
    "block.slot", "block.parent.root", "block.parent.parent.root (grandparent)", "block.votes order", "block.votes dropped element",
    "block.support element", "block.rows order", "block.rows nested confirmed none → some 99" ]

/-- 現在の naru ソースを再生成して生成 Model をビルドし、手書き Model の olean を確かめ、golden を走らせる `LEAN_PATH` を返す(失敗なら none)。 -/
def prepare : M (Option String) := do
  -- 1. 現在のソースの再生成(C10: 再生成してビルドしてから)
  let c ← runProc "lake" #["exe", "naru", "compile"]
  if c.exitCode == 0 then ok "lake exe naru compile (regenerate from the current sources)"
  else fail s!"lake exe naru compile: exit {c.exitCode}\n{tail c.stderr}"
  -- 2. 生成 Model
  let b ← runProc "lake" #["build", "Model"]
  if b.exitCode == 0 then ok "lake build Model" else fail s!"lake build Model: exit {b.exitCode}\n{tail b.stderr}"
  -- 3. 手書き Model の olean
  let inst := vcDir / ".lake" / "build" / "lib" / "lean" / "DecoupledConsensusModel" / "Execution" / "Instance.olean"
  if ← inst.pathExists then ok s!"{vcDir}: DecoupledConsensusModel/Execution/Instance.olean exists"
  else fail s!"{inst} not found (cd {vcDir} && lake build DecoupledConsensusModel)"
  -- 4. LEAN_PATH = verified-consensus の環境 + ルートの build
  let e ← runProc "lake" #["env", "printenv", "LEAN_PATH"] (cwd := some vcDir)
  let vcPath := e.stdout.trimAscii.toString
  if e.exitCode == 0 && !vcPath.isEmpty then ok s!"lake env printenv LEAN_PATH ({vcDir})"
  else
    fail s!"lake env printenv LEAN_PATH in {vcDir}: exit {e.exitCode}\n{tail e.stderr}"
    return none
  if c.exitCode != 0 || b.exitCode != 0 then return none
  let rootLib ← IO.FS.realPath (".lake" / "build" / "lib" / "lean")
  return some (vcPath ++ ":" ++ rootLib.toString)

/-- `comparator …` の行を検査項目にし、期待する検体(agree / probe)がすべて ok で、旧 3 つ組の見逃しが期待どおり報告され、失敗 0 の
`comparator total` があることを確かめる。 -/
def checkComparatorLines (lines : List String) : M Unit := do
  for l in lines do
    if l.startsWith "comparator agree " || l.startsWith "comparator probe " then
      if has l ": ok" then ok (l.drop "comparator ".length).toString
      else fail (l.drop "comparator ".length).toString
    else if l.startsWith "  " && !(l.startsWith "  hand") && !(l.startsWith "  gen") && !(l.startsWith "  base") && !(l.startsWith "  variant") then pure ()
    else if l.startsWith "  " then IO.println l
  let missingA := expectedAgreements.filter fun n => !(lines.any fun l => l.startsWith s!"comparator agree {n}: ok")
  if missingA.isEmpty then ok s!"comparator: all {expectedAgreements.length} expected agreements reported ok"
  else fail s!"comparator: expected agreements not ok: {missingA}"
  let missingP := expectedProbes.filter fun n => !(lines.any fun l => l.startsWith s!"comparator probe {n}: ok")
  if missingP.isEmpty then ok s!"comparator: all {expectedProbes.length} expected probes reported ok (one-field changes detected)"
  else fail s!"comparator: expected probes not ok: {missingP}"
  let missingL := expectedLegacyMisses.filter fun n => !(lines.any fun l => l.startsWith s!"comparator legacy-miss {n}:")
  if missingL.isEmpty then ok s!"comparator: the old (kind, root, author) triple misses all {expectedLegacyMisses.length} expected probes (the probes catch the original defect)"
  else fail s!"comparator: expected legacy misses not reported: {missingL}"
  match lines.find? (·.startsWith "comparator total: ") with
  | some t => if has t " 0 failure(s)" then ok t else fail t
  | none => fail "no `comparator total` line in the output"

def checks (horizon : Nat) : M Unit := do
  let some leanPath ← prepare | return
  -- golden を 1 つの Lean プログラムとして実行(比較器の検体 → 16 case)
  let r ← runProc "lean" #["--run", goldenFile.toString, "--finality-horizon", toString horizon] (env := #[("LEAN_PATH", some leanPath)])
  let lines := r.stdout.splitOn "\n"
  checkComparatorLines lines
  for l in lines do
    if l.startsWith "ok " then ok (l.drop 3).toString
    else if l.startsWith "FAIL " then fail (l.drop 5).toString
    else if l.startsWith "MISMATCH " && !l.startsWith "MISMATCH total" then IO.println l
  let missing := (expectedCases horizon).filter (fun c => !(lines.any (fun l => l.startsWith s!"ok {c}:")))
  if missing.isEmpty then ok s!"all {(expectedCases horizon).length} expected cases reported ok"
  else fail s!"expected cases not ok: {missing}"
  match lines.find? (·.startsWith "MISMATCH total: ") with
  | some t => if t == "MISMATCH total: 0" then ok t else fail t
  | none => fail s!"no `MISMATCH total` line in the output of lean --run {goldenFile} (exit {r.exitCode})\n{tail r.stderr}"
  if r.exitCode == 0 then ok s!"lean --run {goldenFile} --finality-horizon {horizon} exit 0"
  else fail s!"lean --run {goldenFile}: exit {r.exitCode}\n{tail r.stderr}"
  if horizon != c10Horizon then
    IO.println s!"note: finalityLiveness horizon {horizon} (not the C10 prefix: C10 requires horizon {c10Horizon}; run without --finality-horizon)"

/-- 比較器の検体だけ(`--comparator-check`)。 -/
def comparatorChecks : M Unit := do
  let some leanPath ← prepare | return
  let r ← runProc "lean" #["--run", goldenFile.toString, "--comparator-check"] (env := #[("LEAN_PATH", some leanPath)])
  let lines := r.stdout.splitOn "\n"
  checkComparatorLines lines
  if r.exitCode == 0 then ok s!"lean --run {goldenFile} --comparator-check exit 0"
  else fail s!"lean --run {goldenFile} --comparator-check: exit {r.exitCode}\n{tail r.stderr}"

def run (horizon : Nat) : IO UInt32 := runGroup "golden" (checks horizon)

def comparatorRun : IO UInt32 := runGroup "golden --comparator" comparatorChecks

end NaruTest.Golden
