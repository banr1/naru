import Properties.Premises

/-!
# 検査器(IDEAL.md C73): 中間命題 `hreadBound` と `IncludedFrom` の有界版

1 つの命題を 1 つの具体的な run の上で判定し、4 区分(判定 / 前提不成立 / 判定外 / 違反)の件数を返す。各検査器のコメントに
対応する生成 Statements の述語と手書きの補題名(中間命題は `proofs/` の定義名も)を記す。

この周回の検査器は 2 つの中間命題(IDEAL.md「今回の周回の運び」の最優先):
- `hreadBound`: honest な読みの FG root が honest な投票の head の祖先であること(手書き `ProposalAdoptionNamedClosed.lean` の局所仮定
  `hreadBound` = `fgRoot_preceq_previousHead_through_confirmation_after_GST`(`FGSafetyRootNamed.lean`)、`fgSafetyProgressDeadline` 以後)。
- `IncludedFrom`: honest の提案が期限内にすべての honest の読みに入ること(生成 Statements `Statements.Consensus.Spec.Properties.IncludedFrom`、
  claim `available` の結論 `AvailableAt` の 2 項目。`proofs/Proofs/Consensus/Liveness.lean` の `liveFrom_of_includedFrom` の前提)。
-/

namespace Properties
open Model.Consensus Model.Consensus.Objects Model.Consensus.Protocol Model.Consensus.Execution

/-- 1 つの検査器の 1 つの run での判定の集計(用語「有界検査」の 4 区分)。 -/
structure Verdict where
  name : String
  judged : Nat := 0
  unmet : Nat := 0
  outside : Nat := 0
  violations : Nat := 0
  /-- 違反の説明(先頭の数件)。 -/
  notes : Array String := #[]
  /-- 判定ではない補助の情報(期限や、期限を外したときに最後に破れた時刻)。 -/
  diag : Option String := none
deriving Repr

def Verdict.render (v : Verdict) : String :=
  s!"checker {v.name}: judged {v.judged} / premise-unmet {v.unmet} / out-of-horizon {v.outside} / violations {v.violations}"

def Verdict.combine (a b : Verdict) : Verdict :=
  { name := a.name, judged := a.judged + b.judged, unmet := a.unmet + b.unmet, outside := a.outside + b.outside,
    violations := a.violations + b.violations, notes := (a.notes ++ b.notes).extract 0 8, diag := none }

def Verdict.note (v : Verdict) (msg : String) : Verdict :=
  { v with violations := v.violations + 1, notes := if v.notes.size < 8 then v.notes.push msg else v.notes }

/-! ## 中間命題 1: `hreadBound` -/

/-- 手書き `fgSafetyProgressDeadline S rho rGST gap delayExtra = rGST + 1 + (1 + (D + K + 5) · progressLag' gap delayExtra)`、
`progressLag' gap extra = (4 gap + 12 + 2 extra) + 3 gap + 10 + 2 extra = 7 gap + 22 + 4 extra`(手書き `HeightProgressCompose.lean`)。
`rGST` は `tGST <= a(rGST)` を満たす最初の round(`nextRound`)。round 単位。 -/
def hreadBoundDeadline (s : Setup.Setup) (gap extra : Nat) : Nat :=
  let rGST := Spec.Constants.nextRound s s.e.tGST
  rGST + 1 + (1 + (s.cfg.d + s.cfg.k + 5) * (7 * gap + 22 + 4 * extra))

/-- `hreadBound` の検査器。手書き `fgRoot_preceq_previousHead_through_confirmation_after_GST`(`DecoupledConsensusProofs/Objects/FGSafetyRootNamed.lean`)の命題:
honest な `u`, `v`、slot `s` と読みの時刻 `read` について、`a(D) <= read <= horizon`、`openingSlot(D) + 1 <= s`、`read <= confirmationTime(s)`、
`voteTime(s) + Δ <= horizon` なら `preceq (getFgRoot (stateBeforeTime(u, read)).toHealing) (voteDutyHead v s)`。
前提は手書きの仮定 `Admissible`(= `ExecutionValid` ∧ `PartialSynchrony` ∧ GST 以後の全 round で awake)、`HonestCommittees`、
`BelowOneThird`、`MultiProposerRecurrence(gap)`、`TimeoutDelayBound(extra)`、`tGST <= a(rGST)`(`rGST` の取り方で常に成立)に、naru 側の
`SetupWellFormed` / `RunDomain` を足したもの。`voteDutyHead` は実際に発行された票の head(`Timeline.voteHead`。票が無い `(v, s)` は数えない)。
判定の単位は `(u, v, s)` の組。期限(`a(D)` か `voteTime(s) + Δ`)が horizon を越える組は判定外。`openingSlot(D) + 1 > s` の slot は命題の
量化の外(空虚)なので数えず、票を出していない `(v, s)` も数えない(どちらも診断に件数を出す)。
gap は naru の `MultiProposerRecurrence(tGST, gap)`(opening と 3 つの honest な提案者)の最小値で、手書きの round 単位の再発(`Internal.MultiProposerRecurrence`、
窓は `[r, r + gap]`)より強い述語なので期限は手書きの値以上(保守的)。
naru 側の対応: `proofs/Proofs/Consensus/ProposerRoot.lean` が残りとして挙げる「honest な読みの FG root を提案の親の祖先である共通の上界で抑えること」、
読みの FG root の補題 `RootWitness.stateBeforeTime_fgRoot_named` / `JustifiedCarrier.stateBeforeTime_fgRoot_preceq_body` / `FinalizedSource.stateBeforeTime_fgRoot_justified_preceq`。
`readFg` と `deadlineRounds` は負の検体のための差し替え(既定は run の読みと手書きの期限)。 -/
def hreadBound (tl : Timeline) (p : Premises)
    (readFg : Identifiers.ValidatorId → Int → Blocks.Block := tl.fgRootBeforeTime)
    (deadlineRounds : Option Nat := none) : Verdict := Id.run do
  let s := tl.setup
  let horizon := tl.rho.horizon
  let extra := Spec.Constants.extraRounds s
  let premiseOk := p.setup.holds && p.runDomain.holds && p.executionValid && p.partialSync.holds && p.allAwake.holds
    && p.honestCommittees.holds && p.belowOneThird.holds && p.recurrenceGap.isSome && tl.timeoutDelayBound extra
  let gap := p.recurrenceGap.getD 1
  let D := deadlineRounds.getD (hreadBoundDeadline s gap extra)
  let aD := actionTime s D
  let honest := tl.rho.honest.elems
  let slots := List.range (maxSlot s horizon + 1)
  let mut out : Verdict := { name := "hreadBound" }
  let mut lastFail : Option Int := none
  let mut vacuous := 0
  let mut noVote := 0
  let firstSlot := openingSlot s D + 1
  -- 命題の slot の範囲(firstSlot 以上)がまるごと horizon の外なら、(u, v) の組ごとに 1 つの義務を判定外として数える
  let domainOutside := voteTime s firstSlot + s.e.delta > horizon
  -- 読みの FG root は (u, read) ごとに 1 回だけ計算する
  let reads := intRange 0 horizon
  for u in honest do
    let fg : Array Blocks.Block := (reads.map fun r => readFg u r).toArray
    let fgAt (r : Int) : Blocks.Block := fg[r.toNat]!
    for v in honest do
      if domainOutside && premiseOk then out := { out with outside := out.outside + 1 }
      if domainOutside && !premiseOk then out := { out with unmet := out.unmet + 1 }
      for k in slots do
        if k < firstSlot then
          vacuous := vacuous + 1
        else
          match tl.voteHead v k with
          | none => noVote := noVote + 1
          | some head =>
            -- 補助: 期限を外したときに最後に破れる読みの時刻(判定ではない)
            for r in intRange 0 (min horizon (confirmationTime s k)) do
              if !Blocks.preceq (fgAt r) head then
                lastFail := some (max r (lastFail.getD r))
            if !premiseOk then out := { out with unmet := out.unmet + 1 }
            else
              let hi := min horizon (confirmationTime s k)
              if voteTime s k + s.e.delta > horizon || aD > hi then out := { out with outside := out.outside + 1 }
              else
                match (intRange aD hi).find? (fun r => !Blocks.preceq (fgAt r) head) with
                | none => out := { out with judged := out.judged + 1 }
                | some r =>
                  out := out.note s!"hreadBound: fgRoot of {u.value} at read t = {r} (root {(Blocks.root (fgAt r)).value}) is not an ancestor of the vote head of {v.value} at slot {k} (root {(Blocks.root head).value})"
  let lf := match lastFail with | some t => s!"t = {t}" | none => "never"
  return { out with diag := some s!"deadline a(D) = {aD} (D = {D} rounds, gap {gap}, extra {extra}, horizon {horizon}); the proposition quantifies over slots >= openingSlot(D) + 1 = {firstSlot}{if domainOutside then " (all beyond the horizon: one out-of-horizon obligation per honest pair)" else ""}; {vacuous} (u, v, s) below that slot, {noVote} without an emitted vote; without the deadline the bound fails last at {lf}" }

/-! ## 中間命題 2: `IncludedFrom` -/

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

def outputLabel : Spec.Interface.Output → String
  | .Confirmed => "confirmed"
  | .Stable => "stable"
  | .Finalized => "finalized"

/-- `IncludedFrom(s, rho, g, t0, d)` の検査器(生成 Statements `Statements.Consensus.Spec.Properties.IncludedFrom`)。
`t0 < proposalTime(k)`、`proposer(k)` が honest、`proposalTime(k) + d <= horizon` の各 slot `k` について、`proposedBlock(s, rho, k)` が
`Some(b)` で、`InBy(s, rho, g, b, proposalTime(k) + d)`(honest な全 `v` で `preceq(b, outputAt(g, s, rho, v, …))`)。期限が horizon を越える slot は判定外。
前提は claim `available` の `SleepyRegime(s, rho, t0)` を、この周回は BFT の形(`ExecutionValid` ∧ `PartialSynchrony` ∧ `tGST <= t0` ∧
`HonestCommittees` ∧ `BelowOneThird` ∧ `FullParticipation`)と `RecoveredBy` の genesis の枝(`t0 = 0`)で判定する(`WindowMajority` /
`RecoveredBy` の回復の枝の有界版は後続の周回)。`t0 = 0` を取るので `tGST > 0` の run は前提不成立(回復の枝を判定しないため)。
`readOut` は負の検体のための差し替え。 -/
def includedFrom (tl : Timeline) (p : Premises) (g : Spec.Interface.Output) (delay : Int)
    (readOut : Spec.Interface.Output → Identifiers.ValidatorId → Int → Blocks.Block := tl.outputAt) : Verdict := Id.run do
  let s := tl.setup
  let I := tl.inputs
  let horizon := tl.rho.horizon
  let t0 : Int := 0
  let premiseOk := p.setup.holds && p.runDomain.holds && p.executionValid && p.partialSync.holds && s.e.tGST ≤ t0
    && p.honestCommittees.holds && p.belowOneThird.holds && p.fullParticipation.holds
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
  return { out with diag := some s!"delay {delay}, t0 = {t0}" }

end Properties
