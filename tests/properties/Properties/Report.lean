import Properties.Negative

/-!
# 固定の設定と報告(IDEAL.md C73)

回帰に入れる短い設定(`short`: seed・件数・horizon を固定。`docs/testing.md`「有界検査」に同じ値を書く)と、回帰の外の長い設定(`long`)。
報告は決定的な文字列の列(時刻や所要時間を含まない。所要時間は標準エラーに出す)で、`naru_test properties` が 2 回の実行の
byte 一致を確かめる。
-/

namespace Properties
open Model.Consensus Model.Consensus.Objects Model.Consensus.Protocol Model.Consensus.Execution

/-- 回帰の固定設定。3〜4 validator、byzantine を 1 人以上含む run、GST 前の遅延と配送順の入れ替え、sleepy、timeout と height の進行、
複数ノードの finality の進行、回復(GST 後)を覆う 8 本。 -/
def shortSpecs : List RunSpec :=
  [ { name := "h3-sync", seed := 1, validators := 3, horizon := 48 },
    { name := "h3-byz-equivocate", seed := 2, validators := 3, byzantine := [2], weights := [2, 2, 1], byz := .equivocate, horizon := 48 },
    { name := "h3-byz-silent-proposer", seed := 3, validators := 3, byzantine := [2], weights := [2, 2, 1], byz := .silent, horizon := 48 },
    { name := "h3-byz-attest", seed := 4, validators := 3, byzantine := [2], weights := [2, 2, 1], byz := .conflictingAttest, horizon := 60 },
    { name := "h4-gst-delay-twofaced", seed := 5, validators := 4, byzantine := [3], byz := .twoFaced, gst := 12, preGstDelay := 6, horizon := 60 },
    { name := "h4-sleepy-equivocate", seed := 6, validators := 4, byzantine := [3], byz := .equivocate, sleepy := true, horizon := 60 },
    { name := "h3-long-equivocate", seed := 7, validators := 3, byzantine := [2], weights := [2, 2, 1], byz := .equivocate, horizon := 120 },
    { name := "h4-gst24-twofaced", seed := 8, validators := 4, byzantine := [3], byz := .twoFaced, gst := 24, preGstDelay := 4, horizon := 96 },
    { name := "h4-delta2-equivocate", seed := 10, validators := 4, byzantine := [3], byz := .equivocate, delta := 2, gst := 8, preGstDelay := 3, horizon := 96 } ]

/-- run の進み(timeout と height の進行、finality の進行の観測。判定ではない): honest ごとの horizon での 3 出力の深さ、発行された attestation の行と
timeout の行の数、依存待ちで次の時刻へ送った配送の数(配送順の入れ替えが起きた印)。 -/
def progressLine (tl : Timeline) : String :=
  let honest := tl.rho.honest.elems
  let per := honest.map fun v =>
    let st := (tl.storeAt v tl.rho.horizon).core
    s!"{v.value}: confirmed depth {Blocks.depth (Handlers.getConfirmed st)}, stable depth {Blocks.depth (Handlers.getStable st)}, finalized depth {Blocks.depth st.f}"
  let rows := tl.emitted.toList.flatten.filterMap fun o => match o with | .Attest a => some a | _ => none
  let timeouts := rows.countP fun a => match a.heightPair with | .Vote _ _ true => true | _ => false
  s!"  progress: {"; ".intercalate per}; attestation rows {rows.length} (timeout {timeouts}); delivery inversions {tl.inversions}, postponed deliveries {tl.postponed}"

/-- `hreadBound` の期限 `a(D)` を horizon に収める長い run(3 validator、byzantine は equivocate、提案者は honest だけで gap 1)。
`--mode probe <horizon>` が所要時間の計測に使い、計測で予算に収まれば固定設定に入れる。 -/
def deadlineSpec (horizon : Int) : RunSpec :=
  { name := s!"h3-deadline-{horizon}", seed := 9, validators := 3, byzantine := [2], weights := [2, 2, 1], byz := .equivocate,
    proposers := .honestOnly, horizon := horizon }

/-- 回帰の外の長い設定(seed を増やし、horizon を延ばす)。 -/
def longSpecs : List RunSpec :=
  shortSpecs.map (fun sp => { sp with name := sp.name ++ "-long", seed := sp.seed + 100, horizon := sp.horizon * 3 })
    ++ ((List.range 6).map fun i =>
          { name := s!"h4-mix-{i}", seed := 200 + i, validators := 4, byzantine := [3],
            byz := if i % 2 == 0 then .equivocate else .conflictingAttest, sleepy := i % 3 == 0, gst := (i % 3 : Nat) * 8,
            preGstDelay := i % 4, horizon := 120 })

def renderList (xs : List Nat) : String := "[" ++ ", ".intercalate (xs.map toString) ++ "]"

def byzLabel : Byz → String
  | .silent => "silent"
  | .equivocate => "equivocate"
  | .twoFaced => "twoFaced"
  | .conflictingAttest => "conflictingAttest"

/-- 1 つの run の報告の行と、検査器ごとの判定。 -/
def reportRun (sp : RunSpec) : IO (List String × List Verdict) := do
  let t0 ← IO.monoMsNow
  let tl ← IO.lazyPure fun _ => generate sp
  let tGen ← IO.monoMsNow
  let p ← IO.lazyPure fun _ => Premises.of tl
  let tPrem ← IO.monoMsNow
  IO.eprintln s!"[properties] {sp.name}: generate {tGen - t0} ms, premises {tPrem - tGen} ms"
  let ticks := tl.events.toList.countP fun ev => match ev with | Run.NamedEvent.Tick _ _ => true | _ => false
  let delivers := tl.events.size - ticks
  let s := tl.setup
  let agree := tl.outputAgrees .Confirmed (vid (sp.honestIds.getD 0 0)) (sp.horizon / 2)
  let agreeP := tl.proposedAgrees (slotOfTime s (sp.horizon / 2))
  let verdicts := [ hreadBound tl p, includedFrom tl p .Confirmed (Spec.Constants.confirmationDelay s),
                    includedFrom tl p .Stable (Spec.Constants.stableInclusionDelay s), available tl p, confirmedLive tl p, stableLive tl p,
                    stableIncludedFast tl p ]
  let mut lines : List String :=
    [ s!"run {sp.name}: seed {sp.seed}, validators {sp.validators}, honest {renderList sp.honestIds}, byzantine {renderList sp.byzantine} ({byzLabel sp.byz}), gst {sp.gst}, delta {sp.delta}, horizon {sp.horizon}, events {tl.events.size} (ticks {ticks}, deliveries {delivers}), injected {tl.injected}, dropped {tl.dropped}",
      s!"  premises: {p.render}",
      progressLine tl,
      s!"  outputAt agrees with the generated Model's Spec.Interface.outputAt: {agree}; proposedBlock agrees with Spec.Interface.proposedBlock: {agreeP}" ]
  for v in verdicts do
    lines := lines ++ [s!"  {v.render}"]
    if let some d := v.diag then lines := lines ++ [s!"  diag {v.name}: {d}"]
    for n in v.notes do lines := lines ++ [s!"  violation: {n}"]
    if v.strong then lines := lines ++ [s!"  {v.renderClassified}"]
    for n in v.classNotes do lines := lines ++ [s!"  classification: {n}"]
  let t1 ← IO.monoMsNow
  IO.eprintln s!"[properties] {sp.name}: {t1 - t0} ms"
  return (lines, verdicts)

/-- C75 の判断材料(IDEAL.md「今回の周回の運び」): golden の FinalityLiveness の fixture(1 ノード、committee {0}、proposer 0、
`newRoot s = s + 1`、重み 3 / 1、`HeightConfig ⟨5, 2, 6⟩`)を native の生成 Model で `horizon` まで畳み込み、所要時間と最後の読みを出す。
Witness 自身の horizon は 33,729。 -/
def finalityProbe (horizon : Nat) : IO Unit := do
  let S : Setup.Setup := ⟨⟨1, 0, ⟨tblOf [(vid 0, 3), (vid 1, 1)]⟩⟩, ⟨3, 2⟩, ⟨5, 2, 6⟩⟩
  let I : Inputs := { committee := fun _ => NaruStd.Set.singleton (vid 0), proposer := fun _ => vid 0,
                      awake := fun v _ => v.value == 0, newRoot := fun _ s => ⟨s + 1⟩ }
  let t0 ← IO.monoMsNow
  let mut w : World := Run.worldInit
  let mut emitted := 0
  for k in List.range (horizon + 1) do
    let (n', out) := tickNode I S (vid 0) (Timeline.nodeIn w (vid 0)) (k : Int)
    w := w.insert (vid 0) n'
    emitted := emitted + out.length
  let t1 ← IO.monoMsNow
  let st := (Timeline.nodeIn w (vid 0)).st.core
  IO.println s!"finality probe: horizon {horizon} ({horizon + 1} ticks, {emitted} emitted objects): {t1 - t0} ms; tree {st.tree.size}, confirmed root {(Blocks.root (Handlers.getConfirmed st)).value}, stable root {(Blocks.root (Handlers.getStable st)).value}, finalized root {(Blocks.root st.f).value}"

/-- 設定全体の報告。戻り値は (行, 違反の総数, 負の検体がすべて捉えられたか)。 -/
def report (mode : String) (specs : List RunSpec) : IO (List String × Nat × Bool) := do
  let mut lines : List String := [s!"properties: setting {mode}: {specs.length} runs"]
  let mut totals : List Verdict := []
  for sp in specs do
    let (ls, vs) ← reportRun sp
    lines := lines ++ ls
    totals := if totals.isEmpty then vs else totals.zipWith Verdict.combine vs
  let negs := negatives
  for n in negs do lines := lines ++ [n.render]
  let mut violations := 0
  for v in totals do
    lines := lines ++ [v.render]
    if v.strong then lines := lines ++ [v.renderClassified]
    for n in v.classNotes do lines := lines ++ [s!"classification: {n}"]
    violations := violations + v.violations
  let allDetected := negs.all (·.detected)
  lines := lines ++ [s!"properties total: violations {violations}, checkers {totals.length}, negatives {negs.length} ({if allDetected then "all detected" else "NOT all detected"})"]
  return (lines, violations, allDetected)

end Properties
