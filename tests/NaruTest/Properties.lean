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
def expectedCheckers : List String := ["hreadBound", "includedFrom(confirmed)", "includedFrom(stable)", "available"]

/-- 固定設定の run の名前(`Properties.shortSpecs`)。 -/
def expectedRuns : List String :=
  [ "h3-sync", "h3-byz-equivocate", "h3-byz-silent-proposer", "h3-byz-attest", "h4-gst-delay-twofaced", "h4-sleepy-equivocate",
    "h3-long-equivocate", "h4-gst24-twofaced", "h4-delta2-equivocate" ]

/-- byzantine を 1 人以上含む run(`judged >= 1` の要求はこの run の判定を数える)。 -/
def byzantineRuns : List String := expectedRuns.filter fun n => n != "h3-sync"

/-- 強い形を判定の形にした中間命題の検査器(判定の件数は強い形の判定件数。強い形の違反のうち「期限の前の正常な挙動」に分けたものは
`classified <name>: pre-deadline normal behaviour N` の行に別に数え、exit を落とさない)。 -/
def strongCheckers : List String := ["hreadBound"]

/-- 負の検体の名前(`Properties.negatives`)。 -/
def expectedNegatives : List String :=
  [ "hreadBound(corrupted fg-root read)", "hreadBound(control: pre-deadline classification with golden agreement)",
    "hreadBound(strong-form violation at or after the deadline is not classified)", "hreadBound(corrupted proposal parent)",
    "hreadBound(control: genuine read, strong form)",
    "includedFrom(confirmed)(corrupted output read)",
    "includedFrom(stable)(corrupted output read)", "available(AgreeFrom: conflicting confirmed reads)",
    "available(MonotoneFrom: regressing stable read)", "available(control: genuine reads)", "byzantine beyond one third", "WindowMajority broken (honest asleep)",
    "SlashableBound(conflicting height targets)", "RecoveredBy(recovered branch out of reach)",
    "AgreesUntil(prefix agreement of the recovered branch)", "RecoveredBy(source of another run description)", "withheld block delivery after GST", "unsorted events",
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
        || l.startsWith "  violation" || l.startsWith "  outputAt" || l.startsWith "negative " || l.startsWith "checker " || l.startsWith "properties"
        || l.startsWith "  classified" || l.startsWith "classified " || l.startsWith "  classification" || l.startsWith "classification" then
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
    let form := if strongCheckers.contains name then " in the strong form" else ""
    if k ≥ 1 then ok s!"checker {name}: {k} case(s) judged{form} in runs with a byzantine validator (premises met, deadline within the horizon)"
    else fail s!"checker {name}: no case judged{form} in runs with a byzantine validator (premises met, deadline within the horizon)"
  -- hreadBound の強い形は投票の義務と提案の親の義務の両方を byzantine を含む run で 1 件以上判定する(診断の行の内訳)
  let mut cur := ""
  let mut votesByz := 0
  let mut propsByz := 0
  for l in lines do
    if l.startsWith "run " then cur := ((l.drop 4).toString.splitOn ":").head!
    else if l.startsWith "  diag hreadBound: strong form" && byzantineRuns.contains cur then
      let after := ((l.splitOn "judged ").getD 1 "")
      votesByz := votesByz + ((after.splitOn " vote").head!.trimAscii.toString.toNat?.getD 0)
      propsByz := propsByz + ((((after.splitOn "and ").getD 1 "").splitOn " proposal").head!.trimAscii.toString.toNat?.getD 0)
  if votesByz ≥ 1 && propsByz ≥ 1 then
    ok s!"checker hreadBound: the strong form judged {votesByz} vote obligation(s) and {propsByz} proposal-parent obligation(s) in runs with a byzantine validator"
  else fail s!"checker hreadBound: vote obligations {votesByz} / proposal-parent obligations {propsByz} judged in runs with a byzantine validator (each must be >= 1)"
  -- 強い形の違反のうち「期限の前の正常な挙動」に分けたもの: 総計の行があり、件数と根拠(run・命題・分類の根拠)を報告する(exit は落とさない)
  for name in strongCheckers do
    match lines.find? (·.startsWith s!"classified {name}: pre-deadline normal behaviour ") with
    | some l =>
      let n := ((l.splitOn "behaviour ").getLast!).trimAscii.toString.toNat?.getD 0
      let reasons := lines.countP (·.startsWith "classification: ")
      if reasons == n then ok s!"checker {name}: strong-form violations classified as pre-deadline normal behaviour: {n} (reported separately with run, proposition and reason; not counted as violations)"
      else fail s!"checker {name}: {n} classified strong-form violation(s) but {reasons} reported reason line(s)"
    | none => fail s!"checker {name}: no `classified` total line for the strong form"
  -- 5b. includedFrom の前提は SleepyRegime の本来の形(WindowMajority の窓の欄と RecoveredBy。BFT の形の十分条件ではない): sleepy の run は
  --     FullParticipation が破れても前提を満たして判定され、tGST > 0 の run は回復の枝がどの証人でも成り立たない理由を診断に出す
  let mut cur2 := ""
  let mut sleepyJudged := 0
  let mut sleepyFullNo := false
  let mut recoveredDiag := 0
  let mut gstRuns := 0
  for l in lines do
    if l.startsWith "run " then
      cur2 := ((l.drop 4).toString.splitOn ":").head!
      if !(has l "gst 0,") then gstRuns := gstRuns + 1
    else if cur2 == "h4-sleepy-equivocate" && l.startsWith "  premises: " then
      sleepyFullNo := has l "FullParticipation=NO" && has l "WindowMajority=ok"
    else if cur2 == "h4-sleepy-equivocate" && l.startsWith "  checker includedFrom(" then
      if let some (_, j, _, _, _) := parseChecker l then sleepyJudged := sleepyJudged + j
    else if l.startsWith "  diag includedFrom(" && has l "every t0 > 0 needs the recovered branch" && has l "recoveryEnd(tGST, 0) = " then
      recoveredDiag := recoveredDiag + 1
  if sleepyFullNo && sleepyJudged ≥ 1 then
    ok s!"includedFrom judges the premise SleepyRegime in its own form: the sleepy run breaks FullParticipation but meets WindowMajority and is judged ({sleepyJudged} case(s))"
  else fail s!"includedFrom on the sleepy run: FullParticipation=NO and WindowMajority=ok {sleepyFullNo}, judged {sleepyJudged} (expected >= 1)"
  if gstRuns ≥ 1 && recoveredDiag == 2 * gstRuns then
    ok s!"includedFrom reports why the recovered branch of RecoveredBy fails for every witness in the {gstRuns} run(s) with tGST > 0"
  else fail s!"includedFrom: {recoveredDiag} diagnostic line(s) on the recovered branch for {gstRuns} run(s) with tGST > 0 (expected 2 per run)"
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
