import Properties.Basic

/-!
# 共通の run の記述からの run の生成と、run の時間軸(IDEAL.md C73)

`RunSpec`(Basic.lean)から生成 Model の `NamedRun` を組み立てる。生成は run を実際に 1 回シミュレーションしながら進める:
各時刻に honest な validator の tick を置き、その出力を他の honest へ配送(GST 後は `max(t, GST) + Δ` より前、GST 前は追加の遅れ)として
予約し、byzantine は honest の出力から作った object(equivocation の 2 票・衝突する attestation)を配送 event として注入する(byzantine は
tick しない)。遅れは受信者ごと・object ごとに独立な乱数なので配送の順は受信者の間と object の間で入れ替わる(ブロックだけは受信者ごとに
発行順を保ち、子が親より先に届かない)。配送の時点で `wellFormed` / `depsPresent` / `!processed` を確かめ、依存がまだ無い object は期限の中で
次の時刻へ送り、それ以外の満たさないものは落とす(`DeliveryWellFormed` を run の前提として保つため。送った数と落とした数は報告に出す)。

`Timeline` は run の各添字 `i` の直前の世界 `stateBefore(s, rho, i)`(`worlds[i]`)と各 tick の出力 `emittedAt` を 1 回の畳み込みで
持ち、検査器が `stateBeforeTime` / `readAt` / `storeAt` の読みを添字の二分で引けるようにする(生成 Model の同名の関数と同じ値。
`Run.stateBeforeTime` は `eventTime < t` の filter、`Run.readAt` は `<= t` の filter の畳み込みで、event は時刻順なので接頭辞になる)。
-/

namespace Properties
open Model.Consensus Model.Consensus.Objects Model.Consensus.Protocol Model.Consensus.Execution

abbrev World := NaruStd.Table Identifiers.ValidatorId Node.NamedNodeState
abbrev Event := Run.NamedEvent
abbrev Obj := Model.Consensus.Execution.Objects.NamedObject

instance : Inhabited Event := ⟨Run.NamedEvent.Tick ⟨0⟩ 0⟩
instance : Inhabited World := ⟨NaruStd.Table.empty⟩
instance : Inhabited NamedBlocks.NamedBlock := ⟨.Genesis⟩
instance : Inhabited Blocks.Block := ⟨.Genesis⟩

def eventTime (ev : Event) : Int := Run.eventTime ev
def eventNode (ev : Event) : Identifiers.ValidatorId := Run.eventNode ev

def genesisRoot : Identifiers.BlockId := Blocks.root Blocks.Block.Genesis

/-- 生成 Model の 1 tick(scenario の `input` 束縛を先頭に渡す)。 -/
def tickNode (I : Inputs) (S : Setup.Setup) (v : Identifiers.ValidatorId) (n : Node.NamedNodeState) (t : Int) :
    Node.NamedNodeState × List Obj :=
  Node.nodeTick I.committee I.proposer I.awake I.newRoot S v n t

def processNode (I : Inputs) (S : Setup.Setup) (n : Node.NamedNodeState) (o : Obj) : Node.NamedNodeState :=
  Node.nodeProcess I.committee I.proposer S n o

/-- 予約した配送。`deadline` は `max(t, GST) + Δ`(配送はこれより前)。 -/
structure Pend where
  time : Int
  deadline : Int
  node : Nat
  obj : Obj
  seq : Nat

/-- run の時間軸: 記述・Setup・入力・run と、添字ごとの直前の世界・tick の出力。 -/
structure Timeline where
  spec : RunSpec
  setup : Setup.Setup
  inputs : Inputs
  rho : Run.NamedRun
  events : Array Event
  /-- `worlds[i] = stateBefore(s, rho, i)`。長さは event 数 + 1。 -/
  worlds : Array World
  /-- 添字 `i` の tick の出力(配送の添字は空)。 -/
  emitted : Array (List Obj)
  injected : Nat
  dropped : Nat
  /-- 依存がまだ無くて次の時刻へ送った配送の数。 -/
  postponed : Nat := 0
  /-- 配送順の入れ替え: 受信者ごとに、直前に届いた object より発行(予約)の順が早い object が届いた回数。 -/
  inversions : Nat := 0

namespace Timeline

def size (tl : Timeline) : Nat := tl.events.size

/-- 時刻 `t` 未満の event をすべて畳み込んだ世界(`Run.stateBeforeTime`)。 -/
def stateBeforeTime (tl : Timeline) (t : Int) : World := Id.run do
  -- event は時刻順なので、時刻が t 以上になる最初の添字が境
  let mut lo := 0
  let mut hi := tl.events.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if eventTime tl.events[mid]! < t then lo := mid + 1 else hi := mid
  return tl.worlds[lo]!

/-- 時刻 `t` 以下の event をすべて畳み込んだ世界(`Run.readAt`)。 -/
def readAt (tl : Timeline) (t : Int) : World := Id.run do
  let mut lo := 0
  let mut hi := tl.events.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if eventTime tl.events[mid]! ≤ t then lo := mid + 1 else hi := mid
  return tl.worlds[lo]!

def nodeIn (w : World) (v : Identifiers.ValidatorId) : Node.NamedNodeState := Run.worldAt w v

def storeAt (tl : Timeline) (v : Identifiers.ValidatorId) (t : Int) : Handlers.NamedStore := (nodeIn (tl.readAt t) v).st

/-- honest `u` の時刻 `t` の読み(`stateBeforeTime`)の FG root(手書き `get_fg_root (storeBeforeTime S u read).toHealing.toFG`)。 -/
def fgRootBeforeTime (tl : Timeline) (u : Identifiers.ValidatorId) (t : Int) : Blocks.Block :=
  ForkChoice.Goldfish.getFgRoot (Store.storeToHealing (nodeIn (tl.stateBeforeTime t) u).st.core)

/-- `Tick v t` の添字。 -/
def tickIndex (tl : Timeline) (v : Identifiers.ValidatorId) (t : Int) : Option Nat := Id.run do
  for i in [0:tl.events.size] do
    match tl.events[i]! with
    | Run.NamedEvent.Tick v' t' => if v' == v && t' == t then return some i
    | _ => pure ()
  return none

/-- honest `v` が slot `k` の投票の時刻に発行した Goldfish 票の head(ブロック)。票が無ければ `none`。手書き `voteDutyHead`(投票義務の
読みの fork choice の head)に当たる値を、実際に発行された票の head(`Voting.emits_gfVote_head` が同じ値であることを示す)から取り、
root からブロックへは発行者のその tick の後の tree で `findRoot?` を引く。 -/
def voteHead (tl : Timeline) (v : Identifiers.ValidatorId) (k : Nat) : Option Blocks.Block := do
  let i ← tl.tickIndex v (voteTime tl.setup k)
  let u ← (tl.emitted[i]!).findSome? fun o => match o with
    | .GfVote u => if u.valIndex == v && u.slot == k then some u else none
    | _ => none
  Blocks.findRoot? (nodeIn tl.worlds[i + 1]! v).st.core.tree u.head

/-- 添字 `i` の event `Deliver(v, o, t)` が受理された(`processed` が偽から真に変わった)か。 -/
def acceptedAt (tl : Timeline) (i : Nat) : Bool :=
  match tl.events[i]! with
  | Run.NamedEvent.Deliver v o _ =>
    !Node.processed (nodeIn tl.worlds[i]! v).st o && Node.processed (nodeIn tl.worlds[i + 1]! v).st o
  | Run.NamedEvent.Tick _ _ => false

end Timeline

/-! ## 生成 -/

structure GenState where
  rng : Rng
  world : World
  events : Array Event := #[]
  worlds : Array World
  emitted : Array (List Obj) := #[]
  pending : Array Pend := #[]
  /-- 受信者ごとの、最後に予約したブロックの配送の時刻(ブロックだけ発行順を保つ: 子が親より先に届かない)。 -/
  lastBlockAt : Array Int
  seq : Nat := 0
  injected : Nat := 0
  dropped : Nat := 0
  postponed : Nat := 0
  inversions : Nat := 0
  /-- 受信者ごとの、最後に届いた object の予約の順。 -/
  lastSeq : Array Nat

/-- 配送の予約: 送り手 `sender`(byzantine の注入なら `none`)の object `o` を時刻 `t` から、honest な各受信者へ期限
`max(t, GST) + Δ` より前に届ける。遅れは受信者ごとに独立な乱数(GST 後は `[0, Δ)`、GST 前は `preGstDelay` までの追加の遅れ。期限は守る)なので
受信者の間と object の間で配送の順は入れ替わる。ブロックだけは受信者ごとに発行順を保つ(子のブロックが親より先に届かない)。
票や行が依存するブロックより先に届く場合は、配送の時点で `depsPresent` が偽になるので次の時刻へ送る(`generate`)。 -/
def schedule (sp : RunSpec) (st : GenState) (sender : Option Nat) (o : Obj) (t : Int) (receivers : List Nat) : GenState := Id.run do
  let mut st := st
  let deadline := (max t sp.gst) + sp.delta
  for w in receivers do
    if sender == some w then continue
    if let some dropTo := sp.dropBlocksTo then
      if w == dropTo && t ≥ sp.gst then
        if let .Block _ := o then continue
    let maxDelay : Nat := if t ≥ sp.gst then (sp.delta - 1).toNat else sp.preGstDelay + (sp.delta - 1).toNat
    let (dl, rng) := st.rng.below (maxDelay + 1)
    st := { st with rng := rng }
    let d0 : Int := min (t + dl) (deadline - 1)
    let d := match o with
      | .Block _ => max d0 (st.lastBlockAt.getD w 0)
      | _ => d0
    if let .Block _ := o then st := { st with lastBlockAt := st.lastBlockAt.set! w d }
    st := { st with pending := st.pending.push ⟨d, deadline, w, o, st.seq⟩, seq := st.seq + 1 }
  return st

/-- byzantine `b` の注入: honest の出力 `outs`(時刻 `t`)から振る舞いに応じた object を作る。 -/
def injections (sp : RunSpec) (I : Inputs) (S : Setup.Setup) (w : World) (b : Nat) (outs : List (Nat × Obj)) : List Obj :=
  match sp.byz with
  | .silent => []
  | .equivocate | .twoFaced =>
    match outs.findSome? (fun (v, o) => match o with | .GfVote u => some (v, u) | _ => none) with
    | none => []
    | some (v, u) =>
      let tree := (Timeline.nodeIn w (vid v)).st.core.tree
      let alt : Identifiers.BlockId :=
        match Blocks.findRoot? tree u.head with
        | some hb => Blocks.root (Blocks.parent hb)
        | none => genesisRoot
      let u1 : Blocks.GoldfishVote := ⟨vid b, u.slot, u.head⟩
      let u2 : Blocks.GoldfishVote := ⟨vid b, u.slot, alt⟩
      if u1.head == u2.head then [.GfVote u1] else [.GfVote u1, .GfVote u2]
  | .conflictingAttest =>
    match outs.findSome? (fun (_, o) => match o with | .Attest a => some a | _ => none) with
    | none => []
    | some a =>
      let a1 : NamedBlocks.NamedAttestation := { a with valIndex := vid b }
      let a2 : NamedBlocks.NamedAttestation := { a1 with confirmed := match a.confirmed with | some _ => none | none => some genesisRoot }
      [.Attest a1, .Attest a2]
  where _unused := (I, S)

/-- 記述から run を組み立て、時間軸を返す。 -/
def generate (sp : RunSpec) : Timeline := Id.run do
  let S := sp.setup
  let I := sp.inputs
  let honest := sp.honestIds
  let mut st : GenState := { rng := Rng.ofSeed sp.seed, world := Run.worldInit, worlds := #[Run.worldInit],
                             lastBlockAt := (List.replicate sp.validators (0 : Int)).toArray,
                             lastSeq := (List.replicate sp.validators (0 : Nat)).toArray }
  let times := intRange 0 sp.horizon
  for t in times do
    -- 1. honest の tick(public time にだけ)
    let mut outs : List (Nat × Obj) := []
    if publicTime S t then
      for v in honest do
        let n := Timeline.nodeIn st.world (vid v)
        let (n', out) := tickNode I S (vid v) n t
        st := { st with world := st.world.insert (vid v) n', events := st.events.push (.Tick (vid v) t),
                        emitted := st.emitted.push out }
        st := { st with worlds := st.worlds.push st.world }
        for o in out do
          outs := outs ++ [(v, o)]
          st := schedule sp st (some v) o t honest
    -- 2. byzantine の注入(honest の出力から)
    for b in sp.byzantine do
      let objs := injections sp I S st.world b outs
      st := { st with injected := st.injected + objs.length }
      match sp.byz, objs with
      | .twoFaced, [o1, o2] =>
        -- two-faced: 受信者ごとに 2 票の順を変える(先に届く票が受信者によって違う)
        for w in honest do
          let (flip, rng) := st.rng.chance 1 2
          st := { st with rng := rng }
          let (first, second) := if flip then (o2, o1) else (o1, o2)
          st := schedule sp st none first t [w]
          st := schedule sp st none second t [w]
      | _, _ =>
        for o in objs do st := schedule sp st none o t honest
    -- 3. 時刻 t の配送(受信者の id 順、受信者ごとに予約の順)。依存がまだ無い object は次の時刻へ送る(期限の中で)
    let due := (st.pending.filter fun p => p.time == t).qsort fun a b => a.node < b.node || (a.node == b.node && a.seq < b.seq)
    st := { st with pending := st.pending.filter fun p => p.time != t }
    for p in due do
      let n := Timeline.nodeIn st.world (vid p.node)
      if Node.wellFormed I.committee p.obj && Node.depsPresent n.st p.obj && !Node.processed n.st p.obj then
        let n' := processNode I S n p.obj
        st := { st with world := st.world.insert (vid p.node) n', events := st.events.push (.Deliver (vid p.node) p.obj t),
                        emitted := st.emitted.push [] }
        st := { st with worlds := st.worlds.push st.world }
        if p.seq < st.lastSeq.getD p.node 0 then st := { st with inversions := st.inversions + 1 }
        st := { st with lastSeq := st.lastSeq.set! p.node p.seq }
      else if Node.wellFormed I.committee p.obj && !Node.processed n.st p.obj && t + 1 < p.deadline then
        st := { st with pending := st.pending.push { p with time := t + 1 }, postponed := st.postponed + 1 }
      else
        st := { st with dropped := st.dropped + 1 }
  let rho : Run.NamedRun := ⟨sp.honestSet, sp.horizon, st.events.toList⟩
  return { spec := sp, setup := S, inputs := I, rho := rho, events := st.events, worlds := st.worlds, emitted := st.emitted,
           injected := st.injected, dropped := st.dropped + st.pending.size, postponed := st.postponed, inversions := st.inversions }

end Properties
