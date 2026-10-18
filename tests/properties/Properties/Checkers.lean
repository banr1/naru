import Properties.Premises

/-!
# 検査器(IDEAL.md C73): 中間命題 `hreadBound` と `IncludedFrom` の有界版

1 つの命題を 1 つの具体的な run の上で判定し、4 区分(判定 / 前提不成立 / 判定外 / 違反)の件数を返す。各検査器のコメントに
対応する生成 Statements の述語と手書きの補題名(中間命題は `proofs/` の定義名も)を記す。

この周回の検査器は 2 つの中間命題(IDEAL.md「今回の周回の運び」の最優先):
- `hreadBound`: honest な読みの FG root が honest な投票の head・提案の親の祖先であること(手書き `ProposalAdoptionNamedClosed.lean` の局所仮定
  `hreadBound` = `fgRoot_preceq_previousHead_through_confirmation_after_GST`(`FGSafetyRootNamed.lean`)、`fgSafetyProgressDeadline` 以後)。
  期限が horizon を越えるので用語「強い形」(GST 以後のすべての読み)で判定し、期限付きの形は判定外として併せて数える。
- `IncludedFrom`: honest の提案が期限内にすべての honest の読みに入ること(生成 Statements `Statements.Consensus.Spec.Properties.IncludedFrom`、
  claim `available` の結論 `AvailableAt` の 2 項目。`proofs/Proofs/Consensus/Liveness.lean` の `liveFrom_of_includedFrom` の前提)。

claim の検査器は `available`(前提 `SleepyRegime`、結論 `AvailableAt`)と `confirmedLive` / `stableLive`(前提 `LiveSleepyRegime`、結論 `LiveFrom`)、
`stableIncludedFast`(前提 `FreshSleepyRegime`、結論 `IncludedFrom(Stable, fastStableInclusionDelay)`)、
`stableAsynchronyResilient`(前提 `OutageRegime`、結論 `PersistsFrom(Stable, tRead, b0)`)、
`finalized`(前提 `FinalityRegime`、結論 `FinalizedAt`)。
-/

namespace Properties
open Model.Consensus Model.Consensus.Objects Model.Consensus.Protocol Model.Consensus.Execution

/-- 1 つの検査器の 1 つの run での判定の集計(用語「有界検査」の 4 区分)。強い形を判定の形にした中間命題では、強い形の違反のうち
用語「反例の分類」の「期限の前の正常な挙動」に分けたものを `classified` に別に数える(違反には数えない)。 -/
structure Verdict where
  name : String
  judged : Nat := 0
  unmet : Nat := 0
  outside : Nat := 0
  violations : Nat := 0
  /-- 「期限の前の正常な挙動」に分けた強い形の違反の件数(強い形を判定の形にした検査器だけが使う)。 -/
  classified : Nat := 0
  /-- 強い形を判定の形にした検査器か(報告に分類の行を出す)。 -/
  strong : Bool := false
  /-- 違反の説明(先頭の数件)。 -/
  notes : Array String := #[]
  /-- 分類の説明(run・命題・根拠。分類した件ごとに 1 行、切らない)。 -/
  classNotes : Array String := #[]
  /-- 判定ではない補助の情報(期限や、強い形の判定の内訳)。 -/
  diag : Option String := none
deriving Repr

def Verdict.render (v : Verdict) : String :=
  s!"checker {v.name}: judged {v.judged} / premise-unmet {v.unmet} / out-of-horizon {v.outside} / violations {v.violations}"

/-- 分類の行(強い形を判定の形にした検査器だけ)。 -/
def Verdict.renderClassified (v : Verdict) : String :=
  s!"classified {v.name}: pre-deadline normal behaviour {v.classified}"

def Verdict.combine (a b : Verdict) : Verdict :=
  { name := a.name, judged := a.judged + b.judged, unmet := a.unmet + b.unmet, outside := a.outside + b.outside,
    violations := a.violations + b.violations, classified := a.classified + b.classified, strong := a.strong || b.strong,
    notes := (a.notes ++ b.notes).extract 0 8, classNotes := a.classNotes ++ b.classNotes, diag := none }

def Verdict.note (v : Verdict) (msg : String) : Verdict :=
  { v with violations := v.violations + 1, notes := if v.notes.size < 8 then v.notes.push msg else v.notes }

def Verdict.classify (v : Verdict) (msg : String) : Verdict :=
  { v with classified := v.classified + 1, classNotes := v.classNotes.push msg }

/-! ## run の読み(`outputAt` / `proposedBlock`) -/

/-- 生成 Statements の `outputAt(g, s, rho, v, t)` と同じ読み(`storeAt(s, rho, v, t).core` の `getConfirmed` / `getStable` / `f`)を
時間軸から取る。 -/
def Timeline.outputAt (tl : Timeline) (g : Spec.Interface.Output) (v : Identifiers.ValidatorId) (t : Int) : Blocks.Block :=
  let st := (tl.storeAt v t).core
  match g with
  | .Confirmed => Handlers.getConfirmed st
  | .Stable => Handlers.getStable st
  | .Finalized => st.f

/-- 生成 Model の `Spec.Interface.outputAt`(run の畳み込みをやり直す本物)との一致を 1 点で確かめる(時間軸の読みが同じ値であること)。 -/
def Timeline.outputAgrees (tl : Timeline) (g : Spec.Interface.Output) (v : Identifiers.ValidatorId) (t : Int) : Bool :=
  let I := tl.inputs
  tl.outputAt g v t == Spec.Interface.outputAt I.committee I.proposer I.awake I.newRoot g tl.setup tl.rho v t

/-- 生成 Statements の `proposedBlock(s, rho, k)` と同じ値を時間軸から取る: 提案者の提案時刻の読み `confirmationReadAt`(= `stateBeforeTime` の状態に
`confirmationReadFrom` で時計と cache の段取り)に提案の務め `proposalWith` を当て、名前を消す。 -/
def Timeline.proposedBlock (tl : Timeline) (k : Nat) : Option Blocks.Block :=
  let s := tl.setup
  let I := tl.inputs
  let t := proposalTime s k
  let v := I.proposer k
  let n := Run.confirmationReadFrom s (Timeline.nodeIn (tl.stateBeforeTime t) v) t
  (Duties.Proposals.proposalWith I.newRoot n.cache .PoolAndCarried s.e s.hc (Setup.setupNode v) n.st).map NamedBlocks.eraseBlock

/-- 生成 Model の `Spec.Interface.proposedBlock`(run の畳み込みをやり直す本物)との一致を 1 つの slot で確かめる。 -/
def Timeline.proposedAgrees (tl : Timeline) (k : Nat) : Bool :=
  let I := tl.inputs
  tl.proposedBlock k == Spec.Interface.proposedBlock I.committee I.proposer I.awake I.newRoot tl.setup tl.rho k

/-! ## 中間命題 1: `hreadBound`(強い形で判定し、期限付きの形は判定外として併せて数える) -/

/-- 手書き `fgSafetyProgressDeadline S rho rGST gap delayExtra = rGST + 1 + (1 + (D + K + 5) · progressLag' gap delayExtra)`、
`progressLag' gap extra = (4 gap + 12 + 2 extra) + 3 gap + 10 + 2 extra = 7 gap + 22 + 4 extra`(手書き `HeightProgressCompose.lean`)。
`rGST` は `tGST <= a(rGST)` を満たす最初の round(`nextRound`)。round 単位。 -/
def hreadBoundDeadline (s : Setup.Setup) (gap extra : Nat) : Nat :=
  let rGST := Spec.Constants.nextRound s s.e.tGST
  rGST + 1 + (1 + (s.cfg.d + s.cfg.k + 5) * (7 * gap + 22 + 4 * extra))

/-- golden(C10)で両 Model(手書き / 生成)の読みと emitted objects が一致すると確かめた run の名前。用語「反例の分類」の
「期限の前の正常な挙動」に分けてよいのは、違反の時刻が手書きの期限より前で、かつ run がこの一覧にあるときに限る(一覧に無い run の
強い形の違反は、時刻によらず違反として数えて exit を落とす)。共通の run の記述から golden の fixture を作ったら(C10 の拡充)、その run を足す。 -/
def goldenAgreedRuns : List String := []

/-- `hreadBound` の検査器。手書き `fgRoot_preceq_previousHead_through_confirmation_after_GST`(`DecoupledConsensusProofs/Objects/FGSafetyRootNamed.lean`)の命題:
honest な `u`, `v`、slot `s` と読みの時刻 `read` について、`a(D) <= read <= horizon`、`openingSlot(D) + 1 <= s`、`read <= confirmationTime(s)`、
`voteTime(s) + Δ <= horizon` なら `preceq (getFgRoot (stateBeforeTime(u, read)).toHealing) (voteDutyHead v s)`(`D = fgSafetyProgressDeadline`)。
手書き `ProposalAdoptionNamedClosed.lean` / `W4VoteStoreExtendsSlot.lean` の局所仮定 `hreadBound` はこれを投票の head の共通の上界へ持ち上げ、
`read = proposalTime(start)` の提案者の読みに当てて提案の親を抑える。
期限 `a(D)` は最小の設定でも 321 round = 時刻 3858 で、生成 Model の run の費用では届かない(周回197の計測)。そこで用語「強い形」
(GST 以後のすべての honest な読みで FG root ⪯ honest な投票の head・提案の親)を判定の形にする:
- 投票の義務 `(u, v, s)`: `v` が slot `s` の投票を発行したとき、`max(0, tGST) <= read <= min(horizon, confirmationTime(s))` のすべての読みで
  `preceq (fgRootBeforeTime u read) (voteHead v s)`。`voteTime(s) + Δ > horizon` の義務は判定外(手書きの `hshor`)。
- 提案の義務 `(u, s)`: `proposer(s)` が honest で提案 `b = proposedBlock(s)` があるとき、`max(0, tGST) <= read <= min(horizon, confirmationTime(s - 1))`
  (slot 0 は `proposalTime(0)` まで。`proposalTime(s) <= confirmationTime(s - 1)`、手書きの `hproposalNext`)のすべての読みで
  `preceq (fgRootBeforeTime u read) (parent b)`。`proposalTime(s) > horizon` の義務は判定外(手書きの `hproposalHor`)。
読みの範囲が空の義務(`confirmationTime(s)` / `proposalTime(s)` が `tGST` より前)は量化の外なので数えない(診断に件数を出す)。
期限付きの形(`a(D) <= read`、`openingSlot(D) + 1 <= s`)は強い形が含意するので別に判定せず、期限付きの形の範囲が horizon の中に無い義務を
判定外として併せて数える(強い形で判定した義務も、期限付きの形では判定外に数える)。
強い形の違反は、その義務の破れた読みがすべて `a(D)` より前で、かつ run が
`goldenAgreedRuns` にあるときに限り「期限の前の正常な挙動」に分けて `classified` に数え(run・命題・根拠を `classNotes` に残す)、
そうでなければ違反として数える。
前提は手書きの仮定 `Admissible`(= `ExecutionValid` ∧ `PartialSynchrony` ∧ GST 以後の全 round で awake)、`HonestCommittees`、
`BelowOneThird`、`MultiProposerRecurrence(gap)`、`TimeoutDelayBound(extra)`、`tGST <= a(rGST)`(`rGST` の取り方で常に成立)に、naru 側の
`SetupWellFormed` / `RunDomain` を足したもの。`voteDutyHead` は実際に発行された票の head(`Timeline.voteHead`。票が無い `(v, s)` は数えない)。
gap は naru の `MultiProposerRecurrence(tGST, gap)`(opening と 3 つの honest な提案者)の最小値で、手書きの round 単位の再発(`Internal.MultiProposerRecurrence`、
窓は `[r, r + gap]`)より強い述語なので期限は手書きの値以上(保守的)。
naru 側の対応: `proofs/Proofs/Consensus/ProposerRoot.lean` が残りとして挙げる「honest な読みの FG root を提案の親の祖先である共通の上界で抑えること」、
読みの FG root の補題 `RootWitness.stateBeforeTime_fgRoot_named` / `JustifiedCarrier.stateBeforeTime_fgRoot_preceq_body` / `FinalizedSource.stateBeforeTime_fgRoot_justified_preceq`。
`readFg` / `deadlineRounds` / `agreed` / `parentOf` は負の検体のための差し替え(既定は run の読み・手書きの期限・`goldenAgreedRuns`・提案の親)。 -/
def hreadBound (tl : Timeline) (p : Premises)
    (readFg : Identifiers.ValidatorId → Int → Blocks.Block := tl.fgRootBeforeTime)
    (deadlineRounds : Option Nat := none) (agreed : List String := goldenAgreedRuns)
    (parentOf : Blocks.Block → Blocks.Block := Blocks.parent) : Verdict := Id.run do
  let s := tl.setup
  let I := tl.inputs
  let horizon := tl.rho.horizon
  let extra := Spec.Constants.extraRounds s
  let premiseOk := p.setup.holds && p.runDomain.holds && p.executionValid && p.partialSync.holds && p.allAwake.holds
    && p.honestCommittees.holds && p.belowOneThird.holds && p.recurrenceGap.isSome && tl.timeoutDelayBound extra
  let gap := p.recurrenceGap.getD 1
  let D := deadlineRounds.getD (hreadBoundDeadline s gap extra)
  let aD := actionTime s D
  let lo : Int := max 0 s.e.tGST
  let goldenOk := agreed.contains tl.spec.name
  let honest := tl.rho.honest.elems
  let slots := List.range (maxSlot s horizon + 1)
  let mut out : Verdict := { name := "hreadBound", strong := true }
  let mut vacuous := 0
  let mut noVote := 0
  let mut votesJudged := 0
  let mut propsJudged := 0
  let mut strongOutside := 0
  let mut deadlineOutside := 0
  -- 1 つの義務を強い形で判定する: 読みの範囲 [lo, hi] で `fgAt r ⪯ bound`。破れたら、`a(D)` 以後の読みにも破れがあるかで分類する
  -- (あれば違反の時刻が期限より前とは言えないので、分類せず違反)
  let judge (out : Verdict) (fgAt : Int → Blocks.Block) (hi : Int) (bound : Blocks.Block) (what : String) : Verdict × Bool :=
    let bad (r : Int) : Bool := !Blocks.preceq (fgAt r) bound
    match (intRange lo hi).find? bad with
    | none => ({ out with judged := out.judged + 1 }, true)
    | some r =>
      let late := (intRange (max lo aD) hi).find? bad
      let msg := s!"hreadBound (strong form): run {tl.spec.name}: the FG root of the read at t = {r} (root {(Blocks.root (fgAt r)).value}) is not an ancestor of {what} (root {(Blocks.root bound).value})"
      match late with
      | some r' => (out.note s!"{msg}; also broken at t = {r'} >= a(D) = {aD} (not before the deadline)", false)
      | none =>
        if goldenOk then
          (out.classify s!"{msg}; pre-deadline normal behaviour: every broken read is before a(D) = {aD}, and both Models agree on this run in golden", false)
        else
          (out.note s!"{msg} (every broken read is before a(D) = {aD}, but the run is not confirmed by golden)", false)
  -- 読みの FG root は (u, read) ごとに 1 回だけ計算する
  let reads := intRange 0 horizon
  for u in honest do
    let fg : Array Blocks.Block := (reads.map fun r => readFg u r).toArray
    let fgAt (r : Int) : Blocks.Block := fg[r.toNat]!
    -- 投票の義務 (u, v, s)
    for v in honest do
      for k in slots do
        match tl.voteHead v k with
        | none => noVote := noVote + 1
        | some head =>
          let hi := min horizon (confirmationTime s k)
          if hi < lo then vacuous := vacuous + 1
          else if !premiseOk then out := { out with unmet := out.unmet + 1 }
          else
            if aD > hi || openingSlot s D + 1 > k then
              deadlineOutside := deadlineOutside + 1
              out := { out with outside := out.outside + 1 }
            if voteTime s k + s.e.delta > horizon then
              strongOutside := strongOutside + 1
              out := { out with outside := out.outside + 1 }
            else
              let (o, ok) := judge out fgAt hi head s!"the vote head of {v.value} at slot {k} (read of {u.value})"
              out := o
              if ok then votesJudged := votesJudged + 1
    -- 提案の義務 (u, s): honest な提案者の提案の親
    for k in slots do
      if tl.rho.honest.contains (I.proposer k) then
        -- 読みの上端: 手書きは `hreadBound`(`read <= confirmationTime(d)`)と `E ⪯ parent(proposal(d + 1))` の 2 段で、slot `s = d + 1` の
        -- 提案の親を `confirmationTime(s - 1)`(>= `proposalTime(s)`)までの読みで抑える。slot 0 は `proposalTime(0)`
        let hi := if k == 0 then proposalTime s k else min horizon (max (proposalTime s k) (confirmationTime s (k - 1)))
        if proposalTime s k > horizon then
          if premiseOk then
            strongOutside := strongOutside + 1
            deadlineOutside := deadlineOutside + 1
            out := { out with outside := out.outside + 2 }
          else out := { out with unmet := out.unmet + 1 }
        else if hi < lo then vacuous := vacuous + 1
        else if !premiseOk then out := { out with unmet := out.unmet + 1 }
        else
          match tl.proposedBlock k with
          | none => out := out.note s!"hreadBound (strong form): run {tl.spec.name}: no honest proposal computed at slot {k} (proposer {(I.proposer k).value})"
          | some b =>
            if aD > hi || openingSlot s D + 1 > k then
              deadlineOutside := deadlineOutside + 1
              out := { out with outside := out.outside + 1 }
            let (o, ok) := judge out fgAt hi (parentOf b) s!"the parent of the honest proposal of {(I.proposer k).value} at slot {k} (read of {u.value})"
            out := o
            if ok then propsJudged := propsJudged + 1
  return { out with diag := some s!"strong form (reads from max(0, tGST) = {lo}): judged {votesJudged} vote obligation(s) and {propsJudged} proposal-parent obligation(s), {strongOutside} out of the horizon, {vacuous} with an empty read range, {noVote} (u, v, s) without an emitted vote; deadline form a(D) = {aD} (D = {D} rounds, gap {gap}, extra {extra}, horizon {horizon}): {deadlineOutside} obligation(s) out of the horizon (counted in out-of-horizon together)" }

/-! ## 中間命題 2: `IncludedFrom` -/

def outputLabel : Spec.Interface.Output → String
  | .Confirmed => "confirmed"
  | .Stable => "stable"
  | .Finalized => "finalized"

/-- 生成 Statements `Statements.Consensus.Spec.Regimes.SleepyRegime(s, rho, t0)`(手書き `SleepyRegime`)の有界版を 1 つの `t0` で判定する
(最初の不成立の理由): `SetupWellFormed` ∧ `RunDomain` ∧ `ExecutionValid` ∧ `PartialSynchrony` ∧ `tGST <= t0` ∧ `HonestCommittees` ∧
窓の欄(`t0` 以後の各時刻の `WindowMajority`。`Timeline.sleepyWindows`)∧ `RecoveredBy(s, rho, t0)`(`Timeline.recoveredBy`)。
`BelowOneThird` / `FullParticipation` は `SleepyRegime` に無いので見ない。claim `available` と `IncludedFrom` の検査器が使う。 -/
def sleepyAt (tl : Timeline) (p : Premises) (recovery : Option RecoveryWitness) (t0 : Int) : Judge :=
  let s := tl.setup
  let windows := if t0 == 0 then p.windows else tl.sleepyWindows t0
  let base := firstFailure "SleepyRegime"
    [ (p.setup.holds, p.setup.render), (p.runDomain.holds, p.runDomain.render),
      (p.executionValid, "ExecutionValid"), (p.partialSync.holds, p.partialSync.render),
      (s.e.tGST ≤ t0, s!"tGST {s.e.tGST} > t0 = {t0}"), (p.honestCommittees.holds, p.honestCommittees.render),
      (windows.holds, windows.render) ]
  if !base.holds then base else
    let r := tl.recoveredBy p.slashable t0 recovery
    if r.holds then base else Judge.no "SleepyRegime" r.render

/-- 自由変数 `t0` の候補: genesis の枝の `0` と、生成側が回復の枝の証人を与えたときのその `recoveryEnd(s, t0', gap)`。
`RecoveredBy(s, rho, t0)` は `t0 = 0` か `t0 = recoveryEnd(s, t0', gap)`(証人の値)でしか成り立たないので、証人を与えた下で候補は尽きている。 -/
def sleepyCandidates (tl : Timeline) (recovery : Option RecoveryWitness) : List Int :=
  0 :: (recovery.map fun w => Spec.Constants.recoveryEnd tl.setup w.t0 w.gap).toList

/-- 各候補の `t0` での `SleepyRegime` の判定。 -/
def sleepyChoices (tl : Timeline) (p : Premises) (recovery : Option RecoveryWitness) : List (Int × Judge) :=
  (sleepyCandidates tl recovery).map fun t0 => (t0, sleepyAt tl p recovery t0)

/-- どの候補でも `SleepyRegime` が成り立たないときの診断。`t0 > 0` は回復の枝でしか `RecoveredBy` を満たさないので、証人が無ければ
その枝がどの証人でも成り立たないかを示す。 -/
def sleepyFailure (tl : Timeline) (p : Premises) (recovery : Option RecoveryWitness) (judged : List (Int × Judge)) : String :=
  let s := tl.setup
  let recovered := if recovery.isSome then "" else
    let r := tl.recoveredBy p.slashable (Spec.Constants.recoveryEnd s s.e.tGST 0) none
    s!"; every t0 > 0 needs the recovered branch: {r.reason}"
  "SleepyRegime fails for every t0 candidate: " ++ "; ".intercalate (judged.map fun (q : Int × Judge) => s!"t0 = {q.1}: {q.2.reason}") ++ recovered

/-- `IncludedFrom(s, rho, g, t0, delay)` の義務(slot)を 1 つの `t0` で判定して `out` に足す(`premiseOk` が偽なら前提不成立に数える)。 -/
def includedFromAt (tl : Timeline) (g : Spec.Interface.Output) (delay : Int)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block) (premiseOk : Bool) (t0 : Int)
    (out : Verdict) : Verdict := Id.run do
  let s := tl.setup
  let I := tl.inputs
  let horizon := tl.rho.horizon
  let honest := tl.rho.honest.elems
  let mut out := out
  for k in List.range (maxSlot s horizon + 1) do
    if t0 < proposalTime s k && tl.rho.honest.contains (I.proposer k) then
      if !premiseOk then out := { out with unmet := out.unmet + 1 }
      else if proposalTime s k + delay > horizon then out := { out with outside := out.outside + 1 }
      else
        match tl.proposedBlock k with
        | none => out := out.note s!"includedFrom({outputLabel g}): no honest proposal computed at slot {k} (proposer {(I.proposer k).value})"
        | some b =>
          let t := proposalTime s k + delay
          match honest.find? (fun v => !Blocks.preceq b (readOut g v t)) with
          | none => out := { out with judged := out.judged + 1 }
          | some v =>
            out := out.note s!"includedFrom({outputLabel g}): the honest proposal of slot {k} (root {(Blocks.root b).value}) is not in the {outputLabel g} read of {v.value} at t = {t} (root {(Blocks.root (readOut g v t)).value})"
  return out

/-- `IncludedFrom(s, rho, g, t0, d)` の検査器(生成 Statements `Statements.Consensus.Spec.Properties.IncludedFrom`)。
`t0 < proposalTime(k)`、`proposer(k)` が honest、`proposalTime(k) + d <= horizon` の各 slot `k` について、`proposedBlock(s, rho, k)` が
`Some(b)` で、`InBy(s, rho, g, b, proposalTime(k) + d)`(honest な全 `v` で `preceq(b, outputAt(g, s, rho, v, …))`)。期限が horizon を越える slot は判定外。
前提は claim `available` の `SetupWellFormed(s)` ∧ `RunDomain(s, rho)` ∧ `SleepyRegime(s, rho, t0)` の本来の形の有界版:
`ExecutionValid` ∧ `PartialSynchrony` ∧ `tGST <= t0` ∧ `HonestCommittees` ∧ 窓の欄(`t0` 以後の各時刻の `WindowMajority`。`Timeline.sleepyWindows`)∧
`RecoveredBy(s, rho, t0)`(genesis の枝 `t0 = 0`、または回復の枝。`Timeline.recoveredBy`)。`BelowOneThird` / `FullParticipation` は `SleepyRegime` に無いので見ない。
自由変数 `t0` は run ごとに、genesis の枝の `0` と、生成側が回復の枝の証人 `recovery` を与えたときのその `recoveryEnd(s, t0', gap)` を列挙し、
前提が成り立つ最初の値で判定する(どれも成り立たなければ、`proposalTime(k) > 0` の honest な提案の slot を前提不成立に数える)。
回復の枝の証人(`source` の horizon は `prefixEnd(s, t0', gap)`)は、最小の設定でも `prefixEnd` が数千の時刻で生成の予算に収まらないので
固定設定では与えない。`tGST > 0` の run は genesis の枝で `tGST <= 0` を満たさず、回復の枝は `rho.horizon < recoveryEnd(s, tGST, 0)` で
どの証人でも成り立たないことを `recoveredBy` が厳密に退けるので前提不成立になる(理由は診断の行)。
`readOut` は負の検体のための差し替え。 -/
def includedFrom (tl : Timeline) (p : Premises) (g : Spec.Interface.Output) (delay : Int)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block := tl.outputAt)
    (recovery : Option RecoveryWitness := none) : Verdict :=
  let judged := sleepyChoices tl p recovery
  let chosen := judged.find? (·.2.holds)
  let t0 : Int := (chosen.map (·.1)).getD 0
  let out := includedFromAt tl g delay readOut chosen.isSome t0 { name := s!"includedFrom({outputLabel g})" }
  let premiseDiag := match chosen with
    | some (t0, _) => s!"SleepyRegime holds at t0 = {t0}"
    | none => sleepyFailure tl p recovery judged
  { out with diag := some s!"delay {delay}, t0 = {t0}; {premiseDiag}" }

/-! ## claim `available`(前提 `SleepyRegime`、結論 `AvailableAt`) -/

/-- `SafeFrom(s, rho, g, t0)`(生成 Statements `Statements.Consensus.Spec.Properties.SafeFrom` = `AgreeFrom` ∧ `MonotoneFrom`。手書き `SafeFrom`)を
判定して `out` に足す。量化は述語自身が `t0 <= t, t2 <= rho.horizon` と honest に切っているので、有界版は本物と同じ範囲を尽くす:
- `AgreeFrom(g, t0)` = `ConsistentFrom(g, g, t0)`: honest な `u`, `v` と `[t0, horizon]` の `t`, `t2` で `compatible(outputAt(u, t), outputAt(v, t2))`。
  `compatible` の結果は読みの値だけで決まるので、すべての読みの値の異なるものの順序対(自身との対を含む)を比べる(厳密)。1 件の義務に数える。
- `MonotoneFrom(g, t0)`: honest な `v` と `t0 <= t <= t2 <= horizon` で `preceq(outputAt(v, t), outputAt(v, t2))`。`v` の読みの列を同じ値の連なりで
  縮め、縮めた列の `i <= j` の対を比べる(厳密)。honest な `v` ごとに 1 件の義務に数える。
`premiseOk` が偽なら義務をすべて前提不成立に数える。 -/
def safeFrom (tl : Timeline) (g : Spec.Interface.Output) (t0 : Int) (premiseOk : Bool)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block) (out : Verdict) : Verdict := Id.run do
  let honest := tl.rho.honest.elems
  if !premiseOk then return { out with unmet := out.unmet + 1 + honest.length }
  let times := intRange t0 tl.rho.horizon
  let mut out := out
  -- 各 honest の読みの列(同じ値の連なりを縮める。値と最初の時刻)
  let mut runs : List (Identifiers.ValidatorId × Array (Blocks.Block × Int)) := []
  let mut distinct : Array (Blocks.Block × Identifiers.ValidatorId × Int) := #[]
  for v in honest do
    let mut seq : Array (Blocks.Block × Int) := #[]
    for t in times do
      let b := readOut g v t
      match seq.back? with
      | some (b', _) => if b' != b then seq := seq.push (b, t)
      | none => seq := seq.push (b, t)
    for (b, t) in seq do
      if !(distinct.any (·.1 == b)) then distinct := distinct.push (b, v, t)
    runs := runs ++ [(v, seq)]
  -- AgreeFrom: 異なる読みの値の順序対
  let bad := Id.run do
    for (b, u, t) in distinct do
      for (c, v, t2) in distinct do
        if !Blocks.compatible b c then return some (u, t, b, v, t2, c)
    return none
  match bad with
  | none => out := { out with judged := out.judged + 1 }
  | some (u, t, b, v, t2, c) =>
    out := out.note s!"AgreeFrom({outputLabel g}, t0 = {t0}): the {outputLabel g} read of {u.value} at t = {t} (root {(Blocks.root b).value}) and that of {v.value} at t = {t2} (root {(Blocks.root c).value}) are not compatible"
  -- MonotoneFrom: honest ごとに、縮めた列の i <= j の対
  for (v, seq) in runs do
    let broken := Id.run do
      for i in List.range seq.size do
        for j in List.range seq.size do
          if i ≤ j && !Blocks.preceq seq[i]!.1 seq[j]!.1 then return some (seq[i]!, seq[j]!)
      return none
    match broken with
    | none => out := { out with judged := out.judged + 1 }
    | some ((b, t), (c, t2)) =>
      out := out.note s!"MonotoneFrom({outputLabel g}, t0 = {t0}): the {outputLabel g} read of {v.value} at t = {t} (root {(Blocks.root b).value}) is not a prefix of its read at t = {t2} (root {(Blocks.root c).value})"
  return out

/-- claim `available(s, rho, t0)` の検査器(生成 Statements `Statements.Consensus.Spec.Claims.available`。手書き `Consensus.available`):
前提 `SetupWellFormed(s)` ∧ `RunDomain(s, rho)` ∧ `SleepyRegime(s, rho, t0)`(`includedFrom` と同じ本来の形の有界版。`sleepyAt`)、
結論 `AvailableAt(s, rho, t0)`(生成 Statements `Statements.Consensus.Spec.Claims.AvailableAt`。手書き `AvailableAt`)=
`SafeFrom(Confirmed, t0)` ∧ `IncludedFrom(Confirmed, t0, confirmationDelay(s))` ∧ `SafeFrom(Stable, t0)` ∧ `IncludedFrom(Stable, t0, stableInclusionDelay(s))`。
義務は `SafeFrom` ごとに `AgreeFrom` 1 件と honest ごとの `MonotoneFrom`、`IncludedFrom` ごとに `includedFromAt` の slot(期限が horizon を
越える slot は判定外)。自由変数 `t0` は `sleepyCandidates` の値のうち前提が成り立つものをすべて判定する(どれも成り立たなければ `t0 = 0` の
義務を前提不成立に数える)。手書きの補題は結論の 4 項目ごとに `available_confirmedSafe` / `available_confirmedIncluded` /
`available_stableSafe`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`)/ `available_stableIncluded_any`
(`Bridge/StableIncludedAnySlot.lean`)。naru 側の `proofs/` の証明は未着手(C71 の残り)。`readOut` は負の検体のための差し替え。 -/
def available (tl : Timeline) (p : Premises)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block := tl.outputAt)
    (recovery : Option RecoveryWitness := none) : Verdict := Id.run do
  let s := tl.setup
  let judged := sleepyChoices tl p recovery
  let holding := judged.filter (·.2.holds)
  let ts : List (Int × Bool) := if holding.isEmpty then [(0, false)] else holding.map fun q => (q.1, true)
  let mut out : Verdict := { name := "available" }
  for (t0, ok) in ts do
    out := safeFrom tl .Confirmed t0 ok readOut out
    out := includedFromAt tl .Confirmed (Spec.Constants.confirmationDelay s) readOut ok t0 out
    out := safeFrom tl .Stable t0 ok readOut out
    out := includedFromAt tl .Stable (Spec.Constants.stableInclusionDelay s) readOut ok t0 out
  let premiseDiag := if holding.isEmpty then sleepyFailure tl p recovery judged
    else s!"SleepyRegime holds at t0 in {(holding.map (·.1))}"
  return { out with diag := some s!"AvailableAt = SafeFrom(confirmed) ∧ IncludedFrom(confirmed, confirmationDelay {Spec.Constants.confirmationDelay s}) ∧ SafeFrom(stable) ∧ IncludedFrom(stable, stableInclusionDelay {Spec.Constants.stableInclusionDelay s}); {premiseDiag}" }

/-! ## claim `confirmedLive` / `stableLive`(前提 `LiveSleepyRegime`、結論 `LiveFrom`) -/

/-- 自由変数 `gap` の候補 `[1, (horizon - t0) / period]`。`gap = 0` の `SingleProposerRecurrence` は窓 `(t, t]` が空で、`t0 <= horizon` なら
成り立たない。`gap · period > horizon - t0` の `gap` は `SingleProposerRecurrence` が空虚に成り立つが、結論の遅れ `gap · period + …` も
horizon を越えて `LiveFrom` の義務がすべて判定外になるので列挙しない。 -/
def liveGaps (tl : Timeline) (t0 : Int) : List Nat :=
  let per := period tl.setup
  if per ≤ 0 then [] else (List.range ((tl.rho.horizon - t0) / per).toNat.succ).filter (· ≥ 1)

/-- `LiveFrom(s, rho, g, t0, d)`(生成 Statements `Statements.Consensus.Spec.Properties.LiveFrom`。手書き `LiveFrom`)の義務(時刻 `t`)を
1 つの `(t0, d)` で判定して `out` に足す。`[t0, horizon]` の各 `t` について、`t + d > horizon` なら判定外、そうでなければ
`HonestAfter(s, rho, t, b)`(`t < proposalTime(k)` の honest な提案 `proposedBlock(s, rho, k) = Some(b)`)∧ honest な全 `v` で
`prec(outputAt(g, v, t), b)` ∧ `InBy(s, rho, g, b, t + d)` を満たす `b` を探す。存在量化の `b` は `HonestAfter` が honest な提案に限るので、
候補は slot `k <= maxSlot(horizon)` の提案(`props`)で尽くす(それより後の slot の提案を候補から外すのは、見つからないときに違反を報告する側に
しか働かない)。`read v t` は honest の読み(前もって表にしたもの)。`premiseOk` が偽なら義務を前提不成立に数える。 -/
def liveFromAt (tl : Timeline) (g : Spec.Interface.Output) (d : Int) (read : Identifiers.ValidatorId → Int → Blocks.Block)
    (props : Array (Option Blocks.Block)) (premiseOk : Bool) (t0 gap : Int) (out : Verdict) : Verdict := Id.run do
  let s := tl.setup
  let horizon := tl.rho.horizon
  let honest := tl.rho.honest.elems
  let mut out := out
  for t in intRange t0 horizon do
    if !premiseOk then out := { out with unmet := out.unmet + 1 }
    else if t + d > horizon then out := { out with outside := out.outside + 1 }
    else
      let cands := (List.range props.size).filterMap fun k => if t < proposalTime s k then props[k]! else none
      let above (b : Blocks.Block) : Bool := honest.all fun v => Blocks.prec (read v t) b
      let inBy (b : Blocks.Block) : Bool := honest.all fun v => Blocks.preceq b (read v (t + d))
      if cands.any fun b => above b && inBy b then out := { out with judged := out.judged + 1 }
      else
        let nAbove := (cands.filter above).length
        let nIn := (cands.filter inBy).length
        out := out.note s!"LiveFrom({outputLabel g}, t0 = {t0}, gap {gap}, d = {d}): at t = {t} no honest proposal after t is strictly above every honest {outputLabel g} read at t and in every honest read at t + d = {t + d} ({cands.length} candidate(s): {nAbove} strictly above the reads at t, {nIn} in the reads at t + d)"
  return out

/-- claim `confirmedLive(s, rho, t0, gap)` / `stableLive(s, rho, t0, gap)` の検査器(生成 Statements `Statements.Consensus.Spec.Claims.confirmedLive` /
`stableLive`。手書き `Consensus.confirmedLive` / `Consensus.stableLive`): 前提 `SetupWellFormed(s)` ∧ `RunDomain(s, rho)` ∧
`LiveSleepyRegime(s, rho, t0, gap)`(生成 Statements `Statements.Consensus.Spec.Regimes.LiveSleepyRegime` = `SleepyRegime(s, rho, t0)`(`sleepyAt`)∧
`SingleProposerRecurrence(s, rho, t0, gap)`(`Timeline.singleProposerRecurrence`、厳密))、結論 `LiveFrom(s, rho, g, t0, delay(gap))`
(`confirmedLive` は `g = Confirmed`、`delay = growthDelay(s, gap) = gap · period + confirmationDelay`、`stableLive` は `g = Stable`、
`delay = stableGrowthDelay(s, gap) = gap · period + stableInclusionDelay`。`liveFromAt`)。自由変数 `t0` は `sleepyCandidates`、`gap` は `liveGaps` の値の
うち前提が成り立つ組をすべて判定する(どれも成り立たなければ `(t0, gap) = (0, 1)` の義務を前提不成立に数える)。手書きの補題は
`Generic.liveFrom_of_includedFrom`(`DecoupledConsensusProofs/Generic/Lemmas.lean`。`MonotoneFrom` ∧ `NoFutureRead` ∧ `IncludedFrom` ∧
`SingleProposerRecurrence` から `LiveFrom`)で、`DecoupledConsensusProofs/ReviewTheorem.lean` が `confirmedLive` には `available_confirmedIncluded`、
`stableLive` には `available_stableIncluded_any` を `IncludedFrom` に当てる。naru 側の `proofs/` は `proofs/Proofs/Consensus/Liveness.lean` の
`liveFrom_of_includedFrom` / `confirmedLive_of_available` / `stableLive_of_available`(`AvailableAt` からの帰着。claim の theorem は C71 の残り)。
`readOut` は負の検体のための差し替え。 -/
def liveClaim (name : String) (g : Spec.Interface.Output) (delayOf : Nat → Int) (tl : Timeline) (p : Premises)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block := tl.outputAt)
    (recovery : Option RecoveryWitness := none) : Verdict := Id.run do
  let s := tl.setup
  let I := tl.inputs
  let horizon := tl.rho.horizon
  let judged := sleepyChoices tl p recovery
  let mut pairs : List (Int × Nat) := []
  for (t0, j) in judged do
    if j.holds then
      pairs := pairs ++ ((liveGaps tl t0).filter (tl.singleProposerRecurrence t0)).map (t0, ·)
  let ts : List (Int × Nat × Bool) := if pairs.isEmpty then [(0, 1, false)] else pairs.map fun (t0, gap) => (t0, gap, true)
  let mut out : Verdict := { name := name }
  if !pairs.isEmpty then
    -- 読みと honest な提案は (v, t) / slot ごとに 1 回だけ計算する
    let honest := tl.rho.honest.elems
    let reads : List (Identifiers.ValidatorId × Array Blocks.Block) :=
      honest.map fun v => (v, ((intRange 0 horizon).map fun t => readOut g v t).toArray)
    let read (v : Identifiers.ValidatorId) (t : Int) : Blocks.Block :=
      match reads.find? (·.1 == v) with
      | some (_, arr) => arr[t.toNat]!
      | none => readOut g v t
    let props : Array (Option Blocks.Block) := (List.range (maxSlot s horizon + 1)).toArray.map fun k =>
      if tl.rho.honest.contains (I.proposer k) then tl.proposedBlock k else none
    for (t0, gap, ok) in ts do
      out := liveFromAt tl g (delayOf gap) read props ok t0 gap out
  else
    for (t0, gap, ok) in ts do
      out := liveFromAt tl g (delayOf gap) (readOut g) #[] ok t0 gap out
  let premiseDiag :=
    if !pairs.isEmpty then s!"LiveSleepyRegime holds at (t0, gap) in {pairs}"
    else
      let sleepy := judged.filter (·.2.holds)
      if sleepy.isEmpty then sleepyFailure tl p recovery judged
      else s!"SleepyRegime holds at t0 in {sleepy.map (·.1)}, but SingleProposerRecurrence fails for every gap in " ++
        ", ".intercalate (sleepy.map fun (q : Int × Judge) => s!"{liveGaps tl q.1} (t0 = {q.1})")
  return { out with diag := some s!"LiveFrom({outputLabel g}, t0, delay(gap)), delay(1) = {delayOf 1}, period {period s}; {premiseDiag}" }

/-- claim `confirmedLive`: `LiveFrom(Confirmed, t0, growthDelay(s, gap))`。 -/
def confirmedLive (tl : Timeline) (p : Premises)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block := tl.outputAt)
    (recovery : Option RecoveryWitness := none) : Verdict :=
  liveClaim "confirmedLive" .Confirmed (Spec.Constants.growthDelay tl.setup) tl p readOut recovery

/-- claim `stableLive`: `LiveFrom(Stable, t0, stableGrowthDelay(s, gap))`。 -/
def stableLive (tl : Timeline) (p : Premises)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block := tl.outputAt)
    (recovery : Option RecoveryWitness := none) : Verdict :=
  liveClaim "stableLive" .Stable (Spec.Constants.stableGrowthDelay tl.setup) tl p readOut recovery

/-! ## claim `stableIncludedFast`(前提 `FreshSleepyRegime`、結論 `IncludedFrom(Stable, fastStableInclusionDelay)`) -/

/-- 生成 Statements `Statements.Consensus.Spec.Regimes.FreshSleepyRegime(s, rho, t0)`(手書き `FreshSleepyRegime`)の判定を 1 つの `t0` で返す:
`SleepyRegime(s, rho, t0)`(`sleepyAt`)∧ `t0` 以後の各時刻の `FreshMajority`(`Timeline.freshWindows`、厳密)。 -/
def freshSleepyAt (tl : Timeline) (p : Premises) (recovery : Option RecoveryWitness) (t0 : Int) : Judge :=
  let j := sleepyAt tl p recovery t0
  if !j.holds then j else
    let f := tl.freshWindows t0
    if f.holds then Judge.ok "FreshSleepyRegime" else Judge.no "FreshSleepyRegime" f.render

/-- claim `stableIncludedFast(s, rho, t0)` の検査器(生成 Statements `Statements.Consensus.Spec.Claims.stableIncludedFast`。手書き
`Consensus.stableIncludedFast`): 前提 `SetupWellFormed(s)` ∧ `RunDomain(s, rho)` ∧ `FreshSleepyRegime(s, rho, t0)`(`freshSleepyAt`)、
結論 `IncludedFrom(s, rho, Stable, t0, fastStableInclusionDelay(s))`(`includedFromAt`。期限が horizon を越える slot は判定外)。
自由変数 `t0` は `sleepyCandidates` の値のうち前提が成り立つものをすべて判定する(どれも成り立たなければ `t0 = 0` の義務を前提不成立に数える)。
手書きの補題は `stableIncludedFast_concrete`(`DecoupledConsensusProofs/ReviewTheorem.lean` が claim に当てる)と、その中心の
`Bridge/StableIncludedFresh.lean`(`FreshMajority` から参照標本の過半数を出す)。naru 側の `proofs/` の証明は未着手(C71 の残り)。
`readOut` は負の検体のための差し替え。 -/
def stableIncludedFast (tl : Timeline) (p : Premises)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block := tl.outputAt)
    (recovery : Option RecoveryWitness := none) : Verdict := Id.run do
  let delay := Spec.Constants.fastStableInclusionDelay tl.setup
  let judged := (sleepyCandidates tl recovery).map fun t0 => (t0, freshSleepyAt tl p recovery t0)
  let holding := judged.filter (·.2.holds)
  let ts : List (Int × Bool) := if holding.isEmpty then [(0, false)] else holding.map fun q => (q.1, true)
  let mut out : Verdict := { name := "stableIncludedFast" }
  for (t0, ok) in ts do
    out := includedFromAt tl .Stable delay readOut ok t0 out
  let sleepy := sleepyChoices tl p recovery
  let premiseDiag :=
    if !holding.isEmpty then s!"FreshSleepyRegime holds at t0 in {(holding.map (·.1))}"
    else if sleepy.all (!·.2.holds) then sleepyFailure tl p recovery sleepy
    else "SleepyRegime holds at t0 in " ++ toString ((sleepy.filter (·.2.holds)).map (·.1)) ++ ", but FreshSleepyRegime fails: " ++
      "; ".intercalate (judged.map fun (q : Int × Judge) => s!"t0 = {q.1}: {q.2.reason}")
  return { out with diag := some s!"IncludedFrom(stable, fastStableInclusionDelay {delay}); {premiseDiag}" }

/-! ## claim `stableAsynchronyResilient`(前提 `OutageRegime`、結論 `PersistsFrom(Stable, tRead, b0)`) -/

/-- `PersistsFrom(s, rho, g, tRead, b0)`(生成 Statements `Statements.Consensus.Spec.Properties.PersistsFrom`。手書き `PersistsFrom`)が成り立つ
`b0` の境: honest な `v` の時刻 `tRead` の読み `r` と `[0, horizon]` の時刻 `t`、honest な `w` で `preceq(r, outputAt(g, w, t))` が破れる最後の
`t`(と説明)。`PersistsFrom(tRead, b0)` はこの `t` より大きい `b0` で、またそのときに限り成り立つ: 述語の `b` は `preceq(b, r)` を満たす
すべてのブロックだが、`preceq` は反射的(`b == c`)で推移的(祖先の関係)なので `b = r` を確かめれば足り、`r` 自身も `b` に入る(厳密)。
`read v t` は honest の読み(前もって表にしたもの)。 -/
def persistsBreak (tl : Timeline) (g : Spec.Interface.Output) (read : Identifiers.ValidatorId → Int → Blocks.Block) (tRead : Int) :
    Option (Int × String) := Id.run do
  let honest := tl.rho.honest.elems
  let rs := (honest.map fun v => (v, read v tRead)).foldl (fun acc q => if acc.any (·.2 == q.2) then acc else acc ++ [q]) []
  for t in (intRange 0 tl.rho.horizon).reverse do
    for (v, r) in rs do
      if let some w := honest.find? (fun w => !Blocks.preceq r (read w t)) then
        return some (t, s!"the {outputLabel g} read of {v.value} at tRead = {tRead} (root {(Blocks.root r).value}) is not in the {outputLabel g} read of {w.value} at t = {t} (root {(Blocks.root (read w t)).value})")
  return none

/-- claim `stableAsynchronyResilient(s, rho, tRead, b0, b1)` の検査器(生成 Statements `Statements.Consensus.Spec.Claims.stableAsynchronyResilient`。
手書き `Consensus.stableAsynchronyResilient`): 前提 `SetupWellFormed(s)` ∧ `RunDomain(s, rho)` ∧ `OutageRegime(s, rho, tRead, b0, b1)`
(生成 Statements `Statements.Consensus.Spec.Regimes.OutageRegime`。手書き `OutageRegime`)、結論 `PersistsFrom(s, rho, Stable, tRead, b0)`。
`OutageRegime` の有界版: run 全体の欄 `ExecutionValid` ∧ `PartialSynchrony` ∧ `HonestCommittees` ∧ `[lag, horizon + lag]` の各時刻の
`FreshMajority`(`Timeline.freshWindows 0`、厳密)∧ `SlashableBound` と、自由変数に掛かる欄 `tGST <= b1` ∧ `HealthyPrefixDelivery(s, rho, b0)`
(`Timeline.healthyPrefixLimit`)∧ `0 <= b0 <= b1 <= horizon` ∧ `PublicTime(s.e, b0)` ∧ `outageStart(s, tRead) <= b0` ∧
`b1 + Δ <= expiry(s, tRead)` ∧ `b1 + Δ <= horizon`。
自由変数の列挙: `tRead` は `[0, horizon]`(`tRead < 0` の読みは event の前の初期状態のもので、その stable が genesis であることを診断の行に
出す。genesis はどのブロックの祖先でもあるので、そこでは `PersistsFrom` は判定するまでもなく成り立つ。`tRead > horizon` は `b0 >= outageStart(tRead) > tRead > horizon` で区間の欄が偽)、
`b0` は `[max(0, outageStart(tRead)), expiry(tRead) − Δ]` の public time(それ以外の `b0` は区間・`PublicTime`・窓の位置の欄が偽で前提が空虚に
偽)。結論は `b1` を含まず、`b1` の欄はどれも下限(`b0`、`tGST`)か上限(`expiry − Δ`、`horizon − Δ`)なので、`(tRead, b0)` ごとに最小の
`b1 = max(b0, tGST)` で前提を判定し、`(tRead, b0)` を 1 件の義務に数える。run 全体の欄・`b1 + Δ <= expiry(tRead)`・`HealthyPrefixDelivery(b0)` が破れる
義務は(horizon を延ばしても成り立たないので)前提不成立に先に数え、残りのうち `b1 + Δ > horizon` の義務は判定外(窓が horizon に収まらない)。
手書きの補題は `outage_stablePersists`(`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean`。`ReviewTheorem.lean` が `outageRegime_of_generic` で前提を写して claim に当てる)。naru 側の
`proofs/` の証明は未着手(C71 の残り)。`readOut` は負の検体のための差し替え。 -/
def stableAsynchronyResilient (tl : Timeline) (p : Premises)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block := tl.outputAt) : Verdict := Id.run do
  let s := tl.setup
  let horizon := tl.rho.horizon
  let delta := s.e.delta
  let fresh := tl.freshWindows 0
  let base := firstFailure "OutageRegime"
    [ (p.setup.holds, p.setup.render), (p.runDomain.holds, p.runDomain.render), (p.executionValid, "ExecutionValid"),
      (p.partialSync.holds, p.partialSync.render), (p.honestCommittees.holds, p.honestCommittees.render),
      (fresh.holds, fresh.render), (p.slashable.holds, p.slashable.render) ]
  let healthy := tl.healthyPrefixLimit
  -- 読みは (v, t) ごとに 1 回だけ計算する
  let honest := tl.rho.honest.elems
  let reads : List (Identifiers.ValidatorId × Array Blocks.Block) :=
    honest.map fun v => (v, ((intRange 0 horizon).map fun t => readOut .Stable v t).toArray)
  let read (v : Identifiers.ValidatorId) (t : Int) : Blocks.Block :=
    match reads.find? (·.1 == v) with
    | some (_, arr) => if 0 ≤ t && t ≤ horizon then arr[t.toNat]! else readOut .Stable v t
    | none => readOut .Stable v t
  let mut out : Verdict := { name := "stableAsynchronyResilient" }
  let mut hpdUnmet := 0
  let mut expiryUnmet := 0
  let mut tReads := 0
  for tRead in intRange 0 horizon do
    let lo := max 0 (Spec.Constants.outageStart s tRead)
    let ex := Spec.Constants.expiry s tRead
    let b0s := (intRange lo (ex - delta)).filter (publicTime s)
    let brk := if base.holds then persistsBreak tl .Stable read tRead else none
    let mut any := false
    for b0 in b0s do
      let b1 := max b0 s.e.tGST
      -- horizon を延ばしても成り立たない欄の破れを前提不成立として先に数え、窓が horizon に収まらない義務を判定外に数える
      if !base.holds then out := { out with unmet := out.unmet + 1 }
      else if b1 + delta > ex then
        expiryUnmet := expiryUnmet + 1
        out := { out with unmet := out.unmet + 1 }
      else if healthy.any (·.1 ≤ b0) then
        hpdUnmet := hpdUnmet + 1
        out := { out with unmet := out.unmet + 1 }
      else if b1 + delta > horizon then out := { out with outside := out.outside + 1 }
      else
        any := true
        match brk with
        | some (t, why) =>
          if b0 ≤ t then out := out.note s!"PersistsFrom(stable, tRead = {tRead}, b0 = {b0}): {why}"
          else out := { out with judged := out.judged + 1 }
        | none => out := { out with judged := out.judged + 1 }
    if any then tReads := tReads + 1
  let hpd := match healthy with
    | some (d, why) => s!"HealthyPrefixDelivery(b0) fails for b0 >= {d} ({why})"
    | none => "HealthyPrefixDelivery(b0) holds for every b0 <= horizon"
  let premiseDiag := if base.holds then s!"the run-wide fields of OutageRegime hold; {hpd}" else s!"OutageRegime fails: {base.reason}"
  let initialGenesis := honest.all fun v => readOut .Stable v (-1) == .Genesis
  return { out with diag := some s!"PersistsFrom(stable, tRead, b0) over tRead in [0, {horizon}] (the initial stable read for tRead < 0 is genesis: {initialGenesis}) and public b0 in [outageStart(tRead), expiry(tRead) - delta] (outageStart(0) = {Spec.Constants.outageStart s 0}, expiry(0) = {Spec.Constants.expiry s 0}), b1 = max(b0, tGST); judged at {tReads} tRead(s); premise-unmet by HealthyPrefixDelivery {hpdUnmet}, by b1 + delta > expiry {expiryUnmet}; {premiseDiag}" }

/-! ## claim `finalized`(前提 `FinalityRegime`、結論 `FinalizedAt`) -/

/-- honest な提案(`proposalTime(k) >= tGST`、horizon 以内)が honest な全 `v` の finalized の読みに入るまでの遅れ(判定ではない。期限の判断材料):
`(遅れの最大, 入った提案の数, horizon までに入らなかった提案の数)`。 -/
def finalizationLag (tl : Timeline) (read : Identifiers.ValidatorId → Int → Blocks.Block) : Option Int × Nat × Nat := Id.run do
  let s := tl.setup
  let horizon := tl.rho.horizon
  let honest := tl.rho.honest.elems
  let mut worst : Option Int := none
  let mut inN := 0
  let mut notIn := 0
  for k in List.range (maxSlot s horizon + 1) do
    let pt := proposalTime s k
    if s.e.tGST ≤ pt && pt ≤ horizon && tl.rho.honest.contains (tl.inputs.proposer k) then
      if let some b := tl.proposedBlock k then
        match (intRange pt horizon).find? (fun t => honest.all fun v => Blocks.preceq b (read v t)) with
        | some t =>
          inN := inN + 1
          worst := some (max (worst.getD 0) (t - pt))
        | none => notIn := notIn + 1
  return (worst, inN, notIn)

/-- claim `finalized(s, rho, t0, gap)` の検査器(生成 Statements `Statements.Consensus.Spec.Claims.finalized`。手書き `Consensus.finalized`):
前提 `SetupWellFormed(s)` ∧ `RunDomain(s, rho)` ∧ `FinalityRegime(s, rho, t0, gap)`(生成 Statements `Statements.Consensus.Spec.Regimes.FinalityRegime`。
手書き `FinalityRegime`)= `BFTRegime(s, rho, t0)`(`ExecutionValid` ∧ `PartialSynchrony` ∧ `tGST <= t0` ∧ `HonestCommittees` ∧ `BelowOneThird` ∧
`FullParticipation`)∧ `StrongMultiProposerRecurrence(s, rho, tGST, gap)`(`Timeline.strongMultiProposerBreak`、厳密)∧ `gap + 2 <= maxGap(s)` ∧
`t0 + finalityStartup(s, gap) <= horizon`、結論 `FinalizedAt(s, rho, t1, gap)`(`t1 = t0 + finalityStartup(s, gap)`)=
`IncludedFrom(Finalized, t1, finalityDeadline(s, gap))`(`includedFromAt`)∧ `LiveFrom(Finalized, t1, gap · period + finalityDeadline(s, gap))`(`liveFromAt`)。
自由変数の列挙: `gap` は `gap + 2 <= maxGap(s)` を満たす `[0, maxGap − 2]`(それより大きい gap は前提が空虚に偽)、`t0` は `[tGST, horizon]` の整数
(`t0 < tGST` は前提が偽、`t0 > horizon` は `t1 > horizon` で結論の義務がすべて horizon の外)。horizon を延ばしても成り立たない欄
(`BFTRegime` の run 全体の欄、horizon 以内で破れた `StrongMultiProposerRecurrence`)が破れる `(t0, gap)` は 1 件の義務として前提不成立に先に数え、
残りのうち `t1 > horizon` の `(t0, gap)` は 1 件の義務として判定外に数える(最後の欄 `t0 + finalityStartup <= horizon` は horizon の長さの欄で、
`finalityStartup` は最小の設定でも数千の時刻なので、生成の予算の run ではここに入る)。`t1 <= horizon` なら結論の義務(slot と時刻)を数える。
手書きの補題は `DecoupledConsensusProofs/ReviewTheorem.lean` の `finalized` の項が当てる `finalized_included`(`IncludedFrom`)と `finalized_growth`
(`LiveFrom`)。naru 側の `proofs/` は `proofs/Proofs/Consensus/Liveness.lean` の `finalizedLive_of_included`(`IncludedFrom` から `LiveFrom` への帰着。
`IncludedFrom` の証明は C71 の残り)。`gap + 2 <= maxGap` を満たす gap が無ければ 1 件を前提不成立に数える。
診断の行に、honest な提案が finalized の読みに入るまでの実際の遅れ(`finalizationLag`)を出す。
`readOut` / `startupOf` / `deadlineOf` は負の検体のための差し替え(結論の判定の経路を horizon の内側で通す)。 -/
def finalized (tl : Timeline) (p : Premises)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block := tl.outputAt)
    (startupOf : Nat → Int := Spec.Constants.finalityStartup tl.setup)
    (deadlineOf : Nat → Int := Spec.Constants.finalityDeadline tl.setup) : Verdict := Id.run do
  let s := tl.setup
  let I := tl.inputs
  let horizon := tl.rho.horizon
  let base := firstFailure "BFTRegime"
    [ (p.setup.holds, p.setup.render), (p.runDomain.holds, p.runDomain.render), (p.executionValid, "ExecutionValid"),
      (p.partialSync.holds, p.partialSync.render), (p.honestCommittees.holds, p.honestCommittees.render),
      (p.belowOneThird.holds, p.belowOneThird.render), (p.fullParticipation.holds, p.fullParticipation.render) ]
  let gaps := List.range (Spec.Constants.maxGap s - 1)
  let recur := gaps.map fun gap => (gap, tl.strongMultiProposerBreak s.e.tGST gap)
  let t0s := intRange s.e.tGST horizon
  -- 読みと honest な提案は (v, t) / slot ごとに 1 回だけ計算する
  let honest := tl.rho.honest.elems
  let reads : List (Identifiers.ValidatorId × Array Blocks.Block) :=
    honest.map fun v => (v, ((intRange 0 horizon).map fun t => readOut .Finalized v t).toArray)
  let read (v : Identifiers.ValidatorId) (t : Int) : Blocks.Block :=
    match reads.find? (·.1 == v) with
    | some (_, arr) => if 0 ≤ t && t ≤ horizon then arr[t.toNat]! else readOut .Finalized v t
    | none => readOut .Finalized v t
  let inside := base.holds && recur.any fun (gap, b) => b.isNone && t0s.any fun t0 => t0 + startupOf gap ≤ horizon
  let props : Array (Option Blocks.Block) := if !inside then #[] else (List.range (maxSlot s horizon + 1)).toArray.map fun k =>
    if tl.rho.honest.contains (I.proposer k) then tl.proposedBlock k else none
  let mut out : Verdict := { name := "finalized", unmet := if gaps.isEmpty then 1 else 0 }
  for (gap, brk) in recur do
    for t0 in t0s do
      let t1 := t0 + startupOf gap
      if !base.holds || brk.isSome then out := { out with unmet := out.unmet + 1 }
      else if t1 > horizon then out := { out with outside := out.outside + 1 }
      else
        out := includedFromAt tl .Finalized (deadlineOf gap) (fun _ => read) true t1 out
        out := liveFromAt tl .Finalized ((gap : Int) * period s + deadlineOf gap) read props true t1 gap out
  let recurDiag := ", ".intercalate (recur.map fun (gap, b) => match b with
    | some t => s!"gap {gap}: StrongMultiProposerRecurrence(tGST, {gap}) fails at t = {t}"
    | none => s!"gap {gap}: StrongMultiProposerRecurrence(tGST, {gap}) holds, finalityStartup {startupOf gap}, finalityDeadline {deadlineOf gap}")
  let premiseDiag := if base.holds then recurDiag else s!"BFTRegime fails: {base.reason}"
  let (worst, inN, notIn) := finalizationLag tl read
  let lag := match worst with | some w => toString w | none => "none"
  return { out with diag := some s!"FinalizedAt(t0 + finalityStartup(gap), gap) over t0 in [tGST, {horizon}] and gap in {gaps} (gap + 2 <= maxGap {Spec.Constants.maxGap s}); {if gaps.isEmpty then "no gap meets gap + 2 <= maxGap" else premiseDiag}; observed finalization lag of honest proposals after GST: max {lag} over {inN} proposal(s) finalized by the horizon, {notIn} not finalized by the horizon" }

end Properties
