import NaruTest.Common
import NaruTest.Proofs

/-!
# `naru_test properties` — 有界検査のドライバ(IDEAL.md C73)

現在の naru ソースを再生成して生成 Model と有界検査の実行ファイル `naru_properties`(`tests/properties/`。Lake の lean_exe)を
ビルドし、固定の短い設定(`--mode short`)で 2 回走らせて、報告が byte 一致すること(決定性)、検査器ごとの 4 区分の件数と違反 0、
byzantine を 1 人以上含み前提を満たす run で実際に判定された件数が検査器ごとに 1 以上、負の検体がすべて捉えられたこと、
実行の前後で有効な生成先と `proofs/` の全ファイルの sha256 が同じこと、文書(`docs/testing.md` / `proofs/README.md` / `docs/roadmap.md`)に
有界検査の節があることを検査項目にする。
-/

namespace NaruTest.Properties

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- 検査器の名前(`tests/properties/Properties/Report.lean` の `reportRun` の順)。 -/
def expectedCheckers : List String := ["hreadBound", "includedFrom(confirmed)", "includedFrom(stable)"]

/-- 固定設定の run の名前(`Properties.shortSpecs`)。 -/
def expectedRuns : List String :=
  [ "h3-sync", "h3-byz-equivocate", "h3-byz-silent-proposer", "h3-byz-attest", "h4-gst-delay-twofaced", "h4-sleepy-equivocate",
    "h3-long-equivocate", "h4-gst24-twofaced", "h4-delta2-equivocate" ]

/-- byzantine を 1 人以上含む run(`judged >= 1` の要求はこの run の判定を数える)。 -/
def byzantineRuns : List String := expectedRuns.filter fun n => n != "h3-sync"

/-- 負の検体の名前(`Properties.negatives`)。 -/
def expectedNegatives : List String :=
  [ "hreadBound(corrupted fg-root read)", "hreadBound(control: genuine read, deadline 0)", "includedFrom(confirmed)(corrupted output read)",
    "includedFrom(stable)(corrupted output read)", "byzantine beyond one third", "withheld block delivery after GST", "unsorted events",
    "missing honest tick", "replay agrees with generation" ]

/-- `Properties` の import 閉包に許すモジュールのルート(生成 Model・NaruStd・Lean 本体だけ。mathlib・`Proofs`・`NaruSem`・コンパイラ・`NaruTest`・手書きは不可)。 -/
def allowedRoots : List String := ["Properties", "Model", "NaruStd", "Init", "Lean", "Std", "Lake"]
def forbiddenRoots : List String := ["Proofs", "Statements", "NaruSem", "Naru", "NaruTest", "DecoupledConsensus"] ++ NaruTest.Proofs.mathlibRoots
def rootOf (n : String) : String := (n.splitOn ".").head!

/-- `checker <name>: judged N / premise-unmet M / out-of-horizon K / violations V` → (name, N, M, K, V)。 -/
def parseChecker (l : String) : Option (String × Nat × Nat × Nat × Nat) := do
  let body := (l.trimAscii.toString.drop "checker ".length).toString
  let parts := body.splitOn ": judged "
  let name ← parts[0]?
  let rest ← parts[1]?
  let nums := (rest.splitOn " / ").map fun p => ((p.splitOn " ").getLast!).trimAscii.toString.toNat?
  match nums with
  | [some j, some u, some o, some v] => some (name, j, u, o, v)
  | _ => none

def checks : M Unit := do
  -- 1. 現在のソースの再生成と、生成 Model + 実行ファイルのビルド
  let c ← runProc "lake" #["exe", "naru", "compile"]
  if c.exitCode == 0 then ok "lake exe naru compile (regenerate from the current sources)"
  else fail s!"lake exe naru compile: exit {c.exitCode}\n{tail c.stderr}"
  let b ← runProc "lake" #["build", "Properties", "naru_properties"]
  if b.exitCode == 0 then ok "lake build Properties naru_properties (checkers and their executable; generated Model + NaruStd only)"
  else
    fail s!"lake build Properties naru_properties: exit {b.exitCode}\n{tail b.stderr}"
    return
  -- 1b. import 閉包: 生成 Model・NaruStd・Lean 本体だけ(mathlib なし、Proofs / NaruSem / コンパイラ / NaruTest / 手書きなし)
  match ← NaruTest.Proofs.leanClosure ["Properties"] with
  | .ok names =>
    let outside := names.filter fun n => !(allowedRoots.contains (rootOf n))
    let bad := names.filter fun n => forbiddenRoots.contains (rootOf n)
    if outside.isEmpty && bad.isEmpty && names.any (·.startsWith "Model.") then
      ok s!"the import closure of Properties ({names.length} modules) lies within {allowedRoots}: generated Model and NaruStd only, 0 modules of Mathlib / Proofs / Statements / NaruSem / Naru / NaruTest / DecoupledConsensus"
    else fail s!"the import closure of Properties has modules outside {allowedRoots}: {outside.take 5}, forbidden {bad.take 5}"
  | .error e => fail s!"import closure of Properties: {e}"
  -- 2. 実行の前の生成先と proofs/ の snapshot
  let generated : System.FilePath := match ← Naru.readConfig Naru.configFileName with
    | .ok cfg => cfg.generatedPath
    | .error _ => "generated"
  let before ← snapshotTree [generated, "proofs"]
  -- 3. 2 回の実行と決定性
  let exe : System.FilePath := ".lake" / "build" / "bin" / "naru_properties"
  let r1 ← runProc exe.toString #["--mode", "short"]
  let r2 ← runProc exe.toString #["--mode", "short"]
  if r1.stdout == r2.stdout && !r1.stdout.isEmpty then ok "two runs of naru_properties --mode short print byte-identical reports (deterministic)"
  else fail s!"the two reports of naru_properties --mode short differ (or are empty)"
  let lines := r1.stdout.splitOn "\n"
  for l in lines do
    if l.startsWith "run " || l.startsWith "  premises" || l.startsWith "  progress" || l.startsWith "  checker" || l.startsWith "  diag"
        || l.startsWith "  violation" || l.startsWith "  outputAt" || l.startsWith "negative " || l.startsWith "checker " || l.startsWith "properties" then
      IO.println s!"  | {l}"
  -- 4. run ごとの行
  for n in expectedRuns do
    if lines.any (·.startsWith s!"run {n}:") then ok s!"run {n} reported" else fail s!"run {n} not reported"
  let nProgress := lines.countP (·.startsWith "  progress: ")
  if nProgress == expectedRuns.length then ok s!"every run reports its progress (output depths, attestation rows and timeouts, postponed deliveries)"
  else fail s!"{nProgress} progress line(s) for {expectedRuns.length} runs"
  -- 配送順の入れ替えが実際に起きた run がある(受信者ごとに、予約の順が前の object より後に届いた回数が 1 以上)
  let inversions := lines.foldl (fun acc l =>
    if l.startsWith "  progress: " then
      acc + ((((l.splitOn "delivery inversions ").getLast!).splitOn ",").head!.trimAscii.toString.toNat?.getD 0)
    else acc) 0
  if inversions ≥ 1 then ok s!"delivery reordering happened: {inversions} inversions of the emission order across the runs"
  else fail "no delivery inversion in any run (no reordering happened)"
  if lines.all (fun l => !(l.startsWith "  outputAt") || (has l "outputAt: true" && has l "proposedBlock: true")) then
    ok "the timeline's outputAt / proposedBlock agree with the generated Model's Spec.Interface.outputAt / proposedBlock in every run"
  else fail "the timeline's outputAt or proposedBlock disagrees with the generated Model's Spec.Interface functions in some run"
  -- 5. 検査器ごとの総計: 違反 0、byzantine を含む run での判定 >= 1
  let totals := lines.filterMap fun l => if l.startsWith "checker " then parseChecker l else none
  for name in expectedCheckers do
    match totals.find? (·.1 == name) with
    | some (_, j, u, o, v) =>
      if v == 0 then ok s!"checker {name}: violations 0 (judged {j}, premise-unmet {u}, out-of-horizon {o})"
      else fail s!"checker {name}: {v} violation(s)"
    | none => fail s!"checker {name}: no total line"
  -- byzantine を含む run の判定の件数(run の節の中の `  checker` 行を run 名ごとに集める)
  let mut current := ""
  let mut judgedByz : List (String × Nat) := expectedCheckers.map (·, 0)
  for l in lines do
    if l.startsWith "run " then current := ((l.drop 4).toString.splitOn ":").head!
    else if l.startsWith "  checker " && byzantineRuns.contains current then
      if let some (name, j, _, _, _) := parseChecker l then
        judgedByz := judgedByz.map fun (n, k) => if n == name then (n, k + j) else (n, k)
  for (name, k) in judgedByz do
    if k ≥ 1 then ok s!"checker {name}: {k} case(s) judged in runs with a byzantine validator (premises met, deadline within the horizon)"
    else fail s!"checker {name}: no case judged in runs with a byzantine validator (premises met, deadline within the horizon)"
  -- 6. 負の検体
  for n in expectedNegatives do
    match lines.find? (·.startsWith s!"negative {n}:") with
    | some l => if has l ": detected" then ok s!"negative {n}: detected" else fail l
    | none => fail s!"negative {n}: not reported"
  -- 7. 総計と exit
  match lines.find? (·.startsWith "properties total: ") with
  | some t => if has t "violations 0," && has t "all detected" then ok t else fail t
  | none => fail "no `properties total` line"
  if r1.exitCode == 0 then ok "naru_properties --mode short exit 0" else fail s!"naru_properties --mode short: exit {r1.exitCode}\n{tail r1.stderr}"
  -- 8. 生成先と proofs/ は変わらない
  let after ← snapshotTree [generated, "proofs"]
  if before == after then ok s!"{generated} and proofs/ unchanged by the bounded checks ({before.length} files)"
  else fail s!"{generated} or proofs/ changed by the bounded checks"
  -- 9. 文書
  for (f, needle) in [("docs/testing.md", "## 有界検査"), ("proofs/README.md", "有界検査"), ("docs/roadmap.md", "有界検査")] do
    let text ← IO.FS.readFile f
    if has text needle then ok s!"{f} mentions the bounded checks ({needle})" else fail s!"{f} does not mention {needle}"
  let testing ← IO.FS.readFile "docs/testing.md"
  let missingDoc := expectedRuns.filter fun n => !(has testing n)
  if missingDoc.isEmpty then ok "docs/testing.md lists every run of the fixed setting by name" else fail s!"docs/testing.md does not list: {missingDoc}"

def run : IO UInt32 := runGroup "properties" checks

end NaruTest.Properties
