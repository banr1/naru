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
    (recovery : Option RecoveryWitness := none) : Verdict := Id.run do
  let s := tl.setup
  let I := tl.inputs
  let horizon := tl.rho.horizon
  -- `SleepyRegime(s, rho, t0)` を 1 つの t0 で判定する(最初の不成立の理由)
  let sleepy (t0 : Int) : Judge :=
    let windows := if t0 == 0 then p.windows else tl.sleepyWindows t0
    let base := firstFailure "SleepyRegime"
      [ (p.setup.holds, p.setup.render), (p.runDomain.holds, p.runDomain.render),
        (p.executionValid, "ExecutionValid"), (p.partialSync.holds, p.partialSync.render),
        (s.e.tGST ≤ t0, s!"tGST {s.e.tGST} > t0 = {t0}"), (p.honestCommittees.holds, p.honestCommittees.render),
        (windows.holds, windows.render) ]
    if !base.holds then base else
      let r := tl.recoveredBy p.slashable t0 recovery
      if r.holds then base else Judge.no "SleepyRegime" r.render
  let candidates : List Int := 0 :: (recovery.map fun w => Spec.Constants.recoveryEnd s w.t0 w.gap).toList
  let judged := candidates.map fun t0 => (t0, sleepy t0)
  let chosen := judged.find? (·.2.holds)
  let premiseOk := chosen.isSome
  let t0 : Int := (chosen.map (·.1)).getD 0
  let honest := tl.rho.honest.elems
  let mut out : Verdict := { name := s!"includedFrom({outputLabel g})" }
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
  let premiseDiag := match chosen with
    | some (t0, _) => s!"SleepyRegime holds at t0 = {t0}"
    | none =>
      -- t0 > 0 は回復の枝でしか `RecoveredBy` を満たさない。証人が無ければ、その枝がどの証人でも成り立たないかを示す
      let recovered := if recovery.isSome then "" else
        let r := tl.recoveredBy p.slashable (Spec.Constants.recoveryEnd s s.e.tGST 0) none
        s!"; every t0 > 0 needs the recovered branch: {r.reason}"
      "SleepyRegime fails for every t0 candidate: " ++ "; ".intercalate (judged.map fun (q : Int × Judge) => s!"t0 = {q.1}: {q.2.reason}") ++ recovered
  return { out with diag := some s!"delay {delay}, t0 = {t0}; {premiseDiag}" }

end Properties
