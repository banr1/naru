import Properties.Runs

/-!
# 前提の有界版(IDEAL.md C73)

claim の前提(`SetupWellFormed` / `RunDomain` / `ExecutionValid` / `PartialSynchrony` / `HonestCommittees` / `BelowOneThird` /
`FullParticipation` / `MultiProposerRecurrence` …。生成 Statements `Statements.Consensus.Spec.Conditions.*` の述語)を、1 つの具体的な run の
上で有限に判定する Bool の判定器。量化は run の範囲で切る: slot は horizon の slot + 1 まで、時刻は `[0, horizon]`、event は run の列。
各判定器のコメントに対応する生成 Statements の述語を記す。本物との差(量化の切り方)は `docs/testing.md`「有界検査」に書く。

前提を満たさない run は反例にも支持にも数えず「前提不成立」として別に数える(用語「有界検査」)。判定器の誤りは
テストコードを直す(用語「反例の分類」)。
-/

namespace Properties
open Model.Consensus Model.Consensus.Objects Model.Consensus.Protocol Model.Consensus.Execution

/-- 1 つの前提の判定: 名前・成否・不成立の理由(最初の 1 つ)。 -/
structure Judge where
  name : String
  holds : Bool
  reason : String := ""
deriving Repr

def Judge.ok (name : String) : Judge := ⟨name, true, ""⟩
def Judge.no (name why : String) : Judge := ⟨name, false, why⟩
def Judge.render (j : Judge) : String := if j.holds then s!"{j.name}=ok" else s!"{j.name}=NO({j.reason})"

/-- 最初の不成立の理由を返す補助: `checks` の `(成立, 理由)` を順に見る。 -/
def firstFailure (name : String) (checks : List (Bool × String)) : Judge :=
  match checks.find? (fun c => !c.1) with
  | some (_, why) => Judge.no name why
  | none => Judge.ok name

namespace Timeline

/-- 生成 Statements `SetupWellFormed(s)` の有界版(slot は `maxSlot` まで)。 -/
def setupWellFormed (tl : Timeline) : Judge :=
  let s := tl.setup
  let e := s.e
  let I := tl.inputs
  let vals := Weights.validators e.electorate
  let slots := List.range (maxSlot s tl.rho.horizon + 1)
  firstFailure "SetupWellFormed"
    [ (0 < e.delta, "delta <= 0"), (0 ≤ e.tGST, "tGST < 0"), (3 ≤ s.hc.r, "r < 3"), (1 ≤ s.hc.etaSG, "etaSG < 1"),
      (4 ≤ s.cfg.k, "k < 4"), (2 ≤ s.cfg.d, "d < 2"), (s.cfg.timeoutDelay % s.hc.r == 0, "timeoutDelay % r != 0"),
      (2 * s.hc.r ≤ s.cfg.timeoutDelay, "timeoutDelay < 2 r"), (4 ≤ s.hc.r * s.hc.etaSG, "r * etaSG < 4"),
      (Spec.Conditions.normalizedValidators vals, "electorate not normalized"),
      (vals.elems.all fun v => 0 < Weights.weightOfValidator e.electorate v, "a validator has weight 0"),
      (slots.all fun k => !(I.committee k).isEmpty, "an empty committee"),
      (slots.all fun k => Spec.Conditions.normalizedValidators (I.committee k), "a committee not normalized"),
      (slots.all fun k => (I.committee k).subset vals, "a committee outside the electorate"),
      (slots.all fun k => vals.contains (I.proposer k), "a proposer outside the electorate") ]

/-- 生成 Statements `RunDomain(s, rho)`。 -/
def runDomain (tl : Timeline) : Judge :=
  let vals := Weights.validators tl.setup.e.electorate
  firstFailure "RunDomain"
    [ (Spec.Conditions.normalizedValidators tl.rho.honest, "honest not normalized"),
      (tl.rho.honest.subset vals, "honest outside the electorate") ]

def phaseOf (ev : Event) : Nat := Run.eventPhase ev

/-- 生成 Statements `ScheduleWellFormed(s, rho)`(`EventsSorted` / `EventsNodup` / `HonestOnly` / in_horizon / tick_public / tick_total)。 -/
def scheduleWellFormed (tl : Timeline) : Judge := Id.run do
  let s := tl.setup
  let evs := tl.events
  let n := evs.size
  let honest := tl.rho.honest
  -- sorted: 隣り合う event の key が非減少
  let mut sorted := true
  for i in [1:n] do
    let a := evs[i - 1]!
    let b := evs[i]!
    let (ta, pa) := (eventTime a, phaseOf a)
    let (tb, pb) := (eventTime b, phaseOf b)
    if !(ta < tb || (ta == tb && pa ≤ pb)) then sorted := false
  -- nodup: 同じ時刻の group の中で重複が無い(整列済みなので同じ event は同じ group にある)
  let mut nodup := true
  let mut i := 0
  while i < n do
    let t := eventTime evs[i]!
    let mut j := i
    while j < n && eventTime evs[j]! == t do j := j + 1
    let grp := (evs.extract i j).toList
    if grp.length != grp.eraseDups.length then nodup := false
    i := j
  let inHorizon := evs.all fun ev => 0 ≤ eventTime ev && eventTime ev ≤ tl.rho.horizon
  let honestOnly := evs.all fun ev => honest.contains (eventNode ev)
  let tickPublic := evs.all fun ev => match ev with
    | Run.NamedEvent.Tick _ t => publicTime s t
    | _ => true
  let ticks : List (Nat × Int) := evs.toList.filterMap fun ev => match ev with
    | Run.NamedEvent.Tick v t => some (v.value, t)
    | _ => none
  let publicTimes := (intRange 0 tl.rho.horizon).filter (publicTime s)
  let tickTotal := honest.elems.all fun v => publicTimes.all fun t => ticks.contains (v.value, t)
  return firstFailure "ScheduleWellFormed"
    [ (0 ≤ tl.rho.horizon, "horizon < 0"), (sorted, "events not sorted by (time, phase)"), (nodup, "duplicate events"),
      (inHorizon, "an event outside [0, horizon]"), (honestOnly, "an event at a non-honest node"),
      (tickPublic, "a tick at a non-public time"), (tickTotal, "a missing honest tick at a public time") ]

/-- 生成 Statements `DeliveryWellFormed(s, rho)`: 各配送の直前の受信者の store で `wellFormed` / `depsPresent` / `!processed`。 -/
def deliveryWellFormed (tl : Timeline) : Judge := Id.run do
  for i in [0:tl.events.size] do
    match tl.events[i]! with
    | Run.NamedEvent.Deliver v o t =>
      let st := (nodeIn tl.worlds[i]! v).st
      if !Node.wellFormed tl.inputs.committee o then return Judge.no "DeliveryWellFormed" s!"not wellFormed at index {i} (t = {t})"
      if !Node.depsPresent st o then return Judge.no "DeliveryWellFormed" s!"deps missing at index {i} (t = {t})"
      if Node.processed st o then return Judge.no "DeliveryWellFormed" s!"already processed at index {i} (t = {t})"
    | _ => pure ()
  return Judge.ok "DeliveryWellFormed"

/-- ブロックが運ぶ object(`Carries`)。 -/
def carried (o : Obj) : List Obj :=
  match o with
  | .Block b => (NamedBlocks.namedGfVotes b).map (.GfVote ·) ++ (NamedBlocks.namedAttestations b).map (.Attest ·)
  | _ => []

/-- 生成 Statements `UnforgeableSignatures(s, rho)`: 処理された object(と運ばれる object)の author が honest なら、その author が
以前に発行している(有界版: 発行は tick の出力の記録から引く)。 -/
def unforgeable (tl : Timeline) : Judge := Id.run do
  let honest := tl.rho.honest
  -- 発行の記録: 発行者ごとの (object, 時刻)
  let mut emittedBy : NaruStd.Table Identifiers.ValidatorId (List (Obj × Int)) := NaruStd.Table.empty
  for i in [0:tl.events.size] do
    match tl.events[i]! with
    | Run.NamedEvent.Tick v t =>
      for o in tl.emitted[i]! do emittedBy := emittedBy.insert v ((o, t) :: emittedBy.getOr v [])
    | _ => pure ()
  let check (o : Obj) (t : Int) : Bool :=
    match Model.Consensus.Execution.Objects.author o with
    | some u => if honest.contains u then (emittedBy.getOr u []).any (fun (o', t') => t' ≤ t && o' == o) else true
    | none => true
  for i in [0:tl.events.size] do
    match tl.events[i]! with
    | Run.NamedEvent.Deliver _ o t =>
      if !check o t then return Judge.no "UnforgeableSignatures" s!"object with an honest author not emitted by it (index {i}, t = {t})"
      for o2 in carried o do
        if !check o2 t then return Judge.no "UnforgeableSignatures" s!"carried object with an honest author not emitted by it (index {i}, t = {t})"
    | Run.NamedEvent.Tick _ t =>
      -- `Processes` の `Emits` の枝: 自分が発行したブロックが運ぶ object も、その author が honest なら発行の時刻以前に発行されている
      for o in tl.emitted[i]! do
        for o2 in carried o do
          if !check o2 t then return Judge.no "UnforgeableSignatures" s!"object carried by an emitted block has an honest author who did not emit it (index {i}, t = {t})"
  return Judge.ok "UnforgeableSignatures"

/-- root → 名前付きブロックの表に、ブロックとその祖先を登録する。同じ root に構造の違うブロックが来たら衝突(`some root`)。 -/
partial def registerAncestors (b : NamedBlocks.NamedBlock) (seen : NaruStd.Table Identifiers.BlockId NamedBlocks.NamedBlock) :
    NaruStd.Table Identifiers.BlockId NamedBlocks.NamedBlock × Option Identifiers.BlockId :=
  let r := NamedBlocks.namedRoot b
  match seen.get? r with
  | some b' => if b' == b then (seen, none) else (seen, some r)
  | none =>
    let seen' := seen.insert r b
    match b with
    | .Genesis => (seen', none)
    | .Node p _ _ _ _ _ _ => registerAncestors p seen'

/-- 生成 Statements `DirectBlockInRun(s, rho, b)` を満たすブロック: 配送された payload(`runObjects`)と honest の bodies(bodies は
増えるだけなので最後の世界のもの)。 -/
def directBlocks (tl : Timeline) : List NamedBlocks.NamedBlock := Id.run do
  let mut blocks : List NamedBlocks.NamedBlock := []
  for ev in tl.events do
    match ev with
    | Run.NamedEvent.Deliver _ (.Block b) _ => blocks := b :: blocks
    | _ => pure ()
  let last := tl.worlds[tl.worlds.size - 1]!
  for v in tl.rho.honest.elems do
    blocks := blocks ++ (nodeIn last v).st.bodies.elems
  return blocks

/-- 生成 Statements `Idealization(s, rho)` = `NamedRootCollisionFree`: run の範囲のブロック(`directBlocks`)の祖先の閉包の上で root が単射。 -/
def idealization (tl : Timeline) : Judge := Id.run do
  let mut seen : NaruStd.Table Identifiers.BlockId NamedBlocks.NamedBlock := NaruStd.Table.empty
  for b in tl.directBlocks do
    let (seen', clash) := registerAncestors b seen
    seen := seen'
    if let some r := clash then
      return Judge.no "Idealization" s!"two distinct named blocks share the root {r.value}"
  return Judge.ok "Idealization"

/-- 添字の範囲 `[lo, hi)` で時刻が `[t, deadline)` の event の添字(整列済みなので二分で境を取る)。 -/
def indexRange (tl : Timeline) (t deadline : Int) : Nat × Nat := Id.run do
  let n := tl.events.size
  let mut lo := 0
  let mut hi := n
  while lo < hi do
    let mid := (lo + hi) / 2
    if eventTime tl.events[mid]! < t then lo := mid + 1 else hi := mid
  let start := lo
  lo := start
  hi := n
  while lo < hi do
    let mid := (lo + hi) / 2
    if eventTime tl.events[mid]! < deadline then lo := mid + 1 else hi := mid
  return (start, lo)

/-- `exists t2 j, t <= t2 < deadline && HandlesAt(s, rho, j, w, o, t2)` の有界版: `w` への `o` の配送、`w` の tick の出力に `o` がある、
または `o` を運ぶブロックの `w` への配送(受理されたもの)。 -/
def handledBy (tl : Timeline) (w : Identifiers.ValidatorId) (o : Obj) (t deadline : Int) : Bool := Id.run do
  let (lo, hi) := tl.indexRange t deadline
  for j in [lo:hi] do
    match tl.events[j]! with
    | Run.NamedEvent.Deliver w' o' _ =>
      if w' == w then
        if o' == o then return true
        if (carried o').contains o && tl.acceptedAt j then return true
    | Run.NamedEvent.Tick w' _ =>
      if w' == w && (tl.emitted[j]!).contains o then return true
  return false

/-- 生成 Statements `PartialSynchrony(s, rho)` の有界版(broadcast と relay)。 -/
def partialSynchrony (tl : Timeline) : Judge := Id.run do
  let s := tl.setup
  let honest := tl.rho.honest
  for i in [0:tl.events.size] do
    match tl.events[i]! with
    | Run.NamedEvent.Tick v t =>
      for o in tl.emitted[i]! do
        let deadline := (max t s.e.tGST) + s.e.delta
        if deadline ≤ tl.rho.horizon then
          for w in honest.elems do
            if w != v && !Node.excludes (nodeIn (tl.stateBeforeTime deadline) w).st o && !tl.handledBy w o t deadline then
              return Judge.no "PartialSynchrony" s!"broadcast: object emitted by {v.value} at t = {t} not handled by {w.value} before {deadline}"
    | Run.NamedEvent.Deliver v o t =>
      -- relay: 受理された object(配送された object 自身と、受理されたブロックが運ぶ object のうち `processed` が偽から真に変わったもの。
      -- `AcceptsAt` は `HandlesAt` の `BlockCall` の枝を含む)
      let before := (nodeIn tl.worlds[i]! v).st
      let after := (nodeIn tl.worlds[i + 1]! v).st
      let accepted := (o :: carried o).filter fun o2 => !Node.processed before o2 && Node.processed after o2
      for o2 in accepted do
        let deadline := (max t s.e.tGST) + s.e.delta
        if deadline ≤ tl.rho.horizon then
          for w in honest.elems do
            if w != v && !Node.processed (nodeIn tl.worlds[i + 1]! w).st o2
                && !Node.excludes (nodeIn (tl.stateBeforeTime deadline) w).st o2 && !tl.handledBy w o2 t deadline then
              return Judge.no "PartialSynchrony" s!"relay: object accepted by {v.value} at t = {t} not handled by {w.value} before {deadline}"
  return Judge.ok "PartialSynchrony"

/-- 生成 Statements `FullParticipation(s, rho)`: honest は GST から horizon まで awake(`envAwake`)。 -/
def fullParticipation (tl : Timeline) : Judge :=
  let s := tl.setup
  let bad := tl.rho.honest.elems.find? fun v =>
    (intRange s.e.tGST tl.rho.horizon).any fun t => !Spec.Interface.envAwake tl.inputs.awake s v t
  match bad with
  | some v => Judge.no "FullParticipation" s!"honest {v.value} asleep after GST"
  | none => Judge.ok "FullParticipation"

/-- 手書き `Admissible.all_awake`: honest は GST 以後 horizon 以内の action round で awake。 -/
def allAwakeRounds (tl : Timeline) : Judge :=
  let s := tl.setup
  let rounds := (List.range (maxSlot s tl.rho.horizon + 1)).filter fun r => s.e.tGST ≤ actionTime s r && actionTime s r ≤ tl.rho.horizon
  match tl.rho.honest.elems.find? (fun v => rounds.any fun r => !tl.inputs.awake v r) with
  | some v => Judge.no "AllAwake" s!"honest {v.value} asleep in an action round after GST"
  | none => Judge.ok "AllAwake"

/-- 生成 Statements `HonestCommittees(rho.honest)` の有界版(slot は `maxSlot` まで)。 -/
def honestCommittees (tl : Timeline) : Judge :=
  let honest := tl.rho.honest
  let slots := List.range (maxSlot tl.setup tl.rho.horizon + 1)
  match slots.find? (fun k => !((tl.inputs.committee k).size < 2 * ((tl.inputs.committee k).inter honest).size)) with
  | some k => Judge.no "HonestCommittees" s!"committee of slot {k} is not an honest strict majority"
  | none => Judge.ok "HonestCommittees"

/-- 生成 Statements `BelowOneThird(s, rho.honest)`。 -/
def belowOneThird (tl : Timeline) : Judge :=
  let e := tl.setup.e.electorate
  let f := Weights.weightOf e (Spec.Conditions.faulty tl.setup tl.rho.honest)
  if 3 * f < Weights.totalWeight e then Judge.ok "BelowOneThird"
  else Judge.no "BelowOneThird" s!"faulty weight {f} is not below one third of {Weights.totalWeight e}"

/-- 生成 Statements `Opening(s, k)` / `MultiProposerAt(s, h, k)`。 -/
def multiProposerAt (tl : Timeline) (k : Nat) : Bool :=
  k % tl.setup.hc.r == 0
    && (List.range Spec.Constants.proposerSlots).all fun j => tl.rho.honest.contains (tl.inputs.proposer (k + j))

/-- 生成 Statements `MultiProposerRecurrence(s, rho, start, gap)` の有界版(時刻 `t` は `[start, horizon - gap · period]` の整数)。 -/
def multiProposerRecurrence (tl : Timeline) (start : Int) (gap : Nat) : Bool :=
  let s := tl.setup
  let span : Int := (gap : Int) * period s
  let slots := List.range (maxSlot s tl.rho.horizon + 1)
  (intRange start (tl.rho.horizon - span)).all fun t =>
    slots.any fun k => t < proposalTime s k && proposalTime s k ≤ t + span && tl.multiProposerAt k

/-- 手書き `TimeoutDelayBound S extra`: `timeoutDelay = (2 + extra) · R`。 -/
def timeoutDelayBound (tl : Timeline) (extra : Nat) : Bool :=
  tl.setup.cfg.timeoutDelay == (2 + extra) * tl.setup.hc.r

/-- 生成 Statements `AwakeInExactly(s, h, a, b, w)` を満たす唯一の集合 `w`: `h` のうち `[a, b)` のどこかで `envAwake` な validator
(`AwakeIn` の `exists u: Time` は区間 `[a, b)` の整数で尽くせる)。`Set.of` が正規形にする。 -/
def awakeIn (tl : Timeline) (a b : Int) : NaruStd.Set Identifiers.ValidatorId :=
  NaruStd.Set.of (tl.rho.honest.elems.filter fun v =>
    (intRange a (b - 1)).any fun u => Spec.Interface.envAwake tl.inputs.awake tl.setup v u)

/-- 生成 Statements `WindowMajority(s, rho.honest, window, t)`。存在量化される `members` は `AwakeInExactly` で集合が一意に決まる
(`awakeIn`)ので、その集合の重みと faulty の重みを比べれば厳密に判定できる(有界版ではない)。 -/
def windowMajority (tl : Timeline) (window t : Int) : Bool :=
  let e := tl.setup.e.electorate
  Weights.weightOf e (Spec.Conditions.faulty tl.setup tl.rho.honest) < Weights.weightOf e (tl.awakeIn (t - window) t)

/-- 生成 Statements `SleepyRegime` の窓の欄: `t0 <= t`、`participationLag(s) <= t`、`t - participationLag(s) <= rho.horizon` の各時刻 `t` で
`WindowMajority(s, rho.honest, participationWindow(s), t)`。`t` の範囲は `[max(t0, lag), horizon + lag]` で有限なので厳密に判定できる。 -/
def sleepyWindows (tl : Timeline) (t0 : Int) : Judge :=
  let s := tl.setup
  let lag := Spec.Constants.participationLag s
  let window := Spec.Constants.participationWindow s
  match (intRange (max t0 lag) (tl.rho.horizon + lag)).find? (fun t => !tl.windowMajority window t) with
  | some t => Judge.no "WindowMajority" s!"t = {t}: awake honest weight in [{t - window}, {t}) is not above the faulty weight"
  | none => Judge.ok "WindowMajority"

/-- 生成 Statements `AgreesUntil(source, rho, cut)`: `rho.honest ⊆ source.honest`、`rho` の honest な各 `v` の `time < cut` の event の列が一致。 -/
def agreesUntil (source rho : Timeline) (cut : Int) : Bool :=
  let pre (tl : Timeline) (v : Identifiers.ValidatorId) : List Event :=
    tl.rho.events.filter fun ev => eventNode ev == v && eventTime ev < cut
  rho.rho.honest.subset source.rho.honest && rho.rho.honest.elems.all fun v => pre rho v == pre source v

end Timeline

/-! ## `SlashableBound` と `RecoveredBy` -/

/-- 生成 Statements `HasSlashableWeightBetween(e, a1, a2)`。存在量化される集合 `w` は、各要素が `SlashableBetween(a1, a2, i)` を満たす
ことと重みの下限 `HasIntersectionWeight` だけを求め、重みは集合について単調なので、`SlashableBetween` を満たす validator 全体の集合で
判定すれば厳密。 -/
def hasSlashableWeightBetween (e : Parameters.ProtocolEnv) (a1 a2 : List Blocks.CombinedAttestation) : Bool :=
  let ids := a1.filterMap fun a => if a2.any (fun b => a.valIndex == b.valIndex && ChainState.slashable a b) then some a.valIndex else none
  2 * Parameters.envQ e ≤ Parameters.envW e + Weights.weightOf e.electorate (NaruStd.Set.of ids)

/-- 生成 Statements `SlashableBound(s, rho)` を、run の範囲のブロックの代表 `tips`(名前を消したもの)の組で判定する:
`InRun(s, rho, c)` は `DirectBlockInRun` のあるブロックの祖先であることで、`chainAttestations` は祖先から子孫へ増え、
`HasSlashableWeightBetween` は 2 つの attestation 集合について単調なので、`DirectBlockInRun` のブロックのうち他の直接のブロックの
真の祖先でないもの(`tips`)の組(同じブロックの組を含む)だけを見れば厳密。組は `i <= j` だけを見る: `slashable`(`e1Fields` /
`e2Fields` / `sameValidator`)は左右対称なので `HasSlashableWeightBetween(a1, a2)` と `(a2, a1)` は同値。 -/
def slashableBoundOn (s : Setup.Setup) (tips : List Blocks.Block) : Judge := Id.run do
  let ats := tips.map fun b => (Evidence.chainAttestations b).elems
  for i in [0:tips.length] do
    for j in [i:tips.length] do
      if hasSlashableWeightBetween s.e ats[i]! ats[j]! then
        return Judge.no "SlashableBound" s!"slashable weight between the chain attestations of blocks {(Blocks.root tips[i]!).value} and {(Blocks.root tips[j]!).value}"
  return Judge.ok "SlashableBound"

/-- 名前付きブロックの真の祖先(genesis を含む)。 -/
def properAncestors : NamedBlocks.NamedBlock → List NamedBlocks.NamedBlock
  | .Genesis => []
  | .Node p _ _ _ _ _ _ => p :: properAncestors p

/-- run の `DirectBlockInRun` のブロックから、重複と他の直接のブロックの真の祖先を除いたもの(名前を消す)。 -/
def Timeline.blockTips (tl : Timeline) : List Blocks.Block := Id.run do
  let direct := tl.directBlocks.eraseDups
  let below := (direct.flatMap properAncestors).eraseDups
  return (direct.filter fun b => !below.contains b).map NamedBlocks.eraseBlock

def Timeline.slashableBound (tl : Timeline) : Judge := slashableBoundOn tl.setup tl.blockTips

/-- 1 つの run の前提の判定の束。 -/
structure Premises where
  setup : Judge
  runDomain : Judge
  schedule : Judge
  delivery : Judge
  unforgeable : Judge
  idealization : Judge
  partialSync : Judge
  fullParticipation : Judge
  allAwake : Judge
  honestCommittees : Judge
  belowOneThird : Judge
  /-- `SleepyRegime` の窓の欄(`t0 = 0` から。`WindowMajority`)。 -/
  windows : Judge
  /-- `SlashableBound(s, rho)`。 -/
  slashable : Judge
  /-- GST から始まる `MultiProposerRecurrence` が成り立つ最小の gap(1 … 3)。 -/
  recurrenceGap : Option Nat

def Premises.of (tl : Timeline) : Premises :=
  { setup := tl.setupWellFormed, runDomain := tl.runDomain, schedule := tl.scheduleWellFormed, delivery := tl.deliveryWellFormed,
    unforgeable := tl.unforgeable, idealization := tl.idealization, partialSync := tl.partialSynchrony,
    fullParticipation := tl.fullParticipation, allAwake := tl.allAwakeRounds, honestCommittees := tl.honestCommittees,
    belowOneThird := tl.belowOneThird, windows := tl.sleepyWindows 0, slashable := tl.slashableBound,
    recurrenceGap := [1, 2, 3].find? fun gap => tl.multiProposerRecurrence tl.setup.e.tGST gap }

/-- 生成 Statements `ExecutionValid(s, rho)`。 -/
def Premises.executionValid (p : Premises) : Bool :=
  p.schedule.holds && p.delivery.holds && p.unforgeable.holds && p.idealization.holds

def Premises.render (p : Premises) : String :=
  " ".intercalate ([p.setup, p.runDomain, p.schedule, p.delivery, p.unforgeable, p.idealization, p.partialSync, p.fullParticipation,
                    p.allAwake, p.honestCommittees, p.belowOneThird, p.windows, p.slashable].map Judge.render)
    ++ s!" MultiProposerRecurrence(gap)={match p.recurrenceGap with | some g => toString g | none => "none"}"

/-- `RecoveredBy` の回復の枝の存在量化(`source`・`t0`・`gap`)に、run の生成側が与える証人。 -/
structure RecoveryWitness where
  source : Timeline
  t0 : Int
  gap : Nat

/-- 生成 Statements `RecoveredBy(s, rho, t)`: genesis の枝 `t == 0`、または回復の枝(`RunDomain(s, source)`・
`RecoveryRegime(s, source, t0', gap)`・`Continues(source, rho, prefixEnd(s, t0', gap), recoveryEnd(s, t0', gap))`・`SlashableBound(s, rho)`・
`t == recoveryEnd(s, t0', gap)`)。回復の枝は生成側の証人 `w` で判定し、探索しない(`検査器 = true → 述語` の向き)。
証人が無くても回復の枝が成り立たないと言える場合は厳密に退ける: `Continues` は `recoveryEnd(s, t0', gap) <= rho.horizon` を求め、
`RecoveryRegime` の `BFTRegime` は `tGST <= t0'` を求め、`recoveryEnd` は `t0'` と `gap` について単調(`roundAt` と
`boundedPhaseStartLag` が単調)なので、`rho.horizon < recoveryEnd(s, tGST, 0)` ならどの `source`・`t0'`・`gap` でも成り立たない。
`slashable` は `rho` の `SlashableBound`(`Premises.slashable`)。証人の `source` は `rho` と同じ `s` と同じ入力のインタフェースの下の run で
なければならない(生成 Statements の `RecoveredBy` は同じ `s` と input を量化の外に持つ)ので、run の記述が名前と horizon を除いて等しいことを
先に確かめる。証人が無く `rho.horizon >= recoveryEnd(s, tGST, 0)` の run は回復の枝の成否が決まらないが前提不成立に数える(保守的。固定設定には無い)。 -/
def Timeline.recoveredBy (tl : Timeline) (slashable : Judge) (t : Int) (w : Option RecoveryWitness) : Judge := Id.run do
  let s := tl.setup
  if t == 0 then return Judge.ok "RecoveredBy"
  let lower := Spec.Constants.recoveryEnd s s.e.tGST 0
  match w with
  | none =>
    if tl.rho.horizon < lower then
      return Judge.no "RecoveredBy" s!"t = {t} is not 0 (genesis), and the recovered branch needs recoveryEnd(t0', gap) <= horizon {tl.rho.horizon}, but recoveryEnd(t0', gap) >= recoveryEnd(tGST, 0) = {lower} for every t0' >= tGST and gap"
    return Judge.no "RecoveredBy" s!"t = {t} is not 0 (genesis), and the generator gives no source run for the recovered branch"
  | some w =>
    let src := w.source
    let ps := Premises.of src
    let pEnd := Spec.Constants.prefixEnd s w.t0 w.gap
    let rEnd := Spec.Constants.recoveryEnd s w.t0 w.gap
    -- source の `RecoveryRegime(s, source, t0', gap)` = `BFTRegime(s, source, t0')` ∧ `MultiProposerRecurrence(s, source, tGST, gap)` ∧
    -- `source.horizon == prefixEnd(s, t0', gap)`
    return firstFailure "RecoveredBy"
      [ (src.setup == s && { src.spec with name := tl.spec.name, horizon := tl.spec.horizon } == tl.spec,
          "source: not a run of the same setup and inputs (the run description differs beyond its name and horizon)"),
        (ps.runDomain.holds, s!"source: {ps.runDomain.render}"),
        (ps.executionValid, "source: ExecutionValid"),
        (ps.partialSync.holds, s!"source: {ps.partialSync.render}"),
        (s.e.tGST ≤ w.t0, s!"source: tGST > t0' = {w.t0}"),
        (ps.honestCommittees.holds, s!"source: {ps.honestCommittees.render}"),
        (ps.belowOneThird.holds, s!"source: {ps.belowOneThird.render}"),
        (ps.fullParticipation.holds, s!"source: {ps.fullParticipation.render}"),
        (src.multiProposerRecurrence s.e.tGST w.gap, s!"source: MultiProposerRecurrence(tGST, {w.gap}) fails"),
        (src.rho.horizon == pEnd, s!"source: horizon {src.rho.horizon} != prefixEnd(t0', gap) = {pEnd}"),
        (Timeline.agreesUntil src tl pEnd, "Continues: the honest events before prefixEnd differ from the source"),
        (rEnd ≤ tl.rho.horizon, s!"Continues: recoveryEnd(t0', gap) = {rEnd} > horizon {tl.rho.horizon}"),
        (slashable.holds, s!"SlashableBound: {slashable.reason}"),
        (t == rEnd, s!"t = {t} != recoveryEnd(t0', gap) = {rEnd}") ]

end Properties
