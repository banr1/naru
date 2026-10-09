import DecoupledConsensusModel.Protocol.Tick
import DecoupledConsensusModel.Protocol.Evidence
import DecoupledConsensusModel.Execution.Instance
import Model
/-!
# tests/golden/Golden.lean — C10 の golden test(同一 Lean プログラム)

手書き Model(`verified-consensus/DecoupledConsensusModel`、mathlib の上)と生成 Model(`generated/Model` + `NaruStd`)を **1 つの Lean
プログラム**から import し、同じ fixture(run)を両側で畳み込んで、各 event の前後の両 node の読みと tick が emit した object を
行の列にして突き合わせ、MISMATCH を数える。IDEAL.md C10 の検証そのもの(ドライバは `lake exe naru_test golden`)。

実行(リポジトリのルートで。`lake build Model` 済みで、verified-consensus の Model の olean がビルド済みであること):
  LEAN_PATH="$(cd verified-consensus && lake env printenv LEAN_PATH):$PWD/.lake/build/lib/lean" \
    lean --run tests/golden/Golden.lean [--finality-horizon N]
出力: case ごとに `ok <case>: n lines agree` か `FAIL <case>: …` と `MISMATCH …` の行、最後に `MISMATCH total: N`。exit 0 ⇔ N = 0。

fixture(case):
- `witness:weakGenesis` / `witness:outage` / `witness:strongRecovery` / `witness:finalityLiveness` — verified-consensus の Witnesses の 4 run を
  両側で Lean に書き写したもの(Witnesses のモジュールは Proofs を import するので使えない)。FinalityLiveness の horizon は
  `--finality-horizon N`(既定は Witnesses の 33729)。
- `scenario:<name>` — naru の scenario(`dsl/scenarios/*.naru`)が fn として公開する Setup と run を生成 Model からそのまま取り、手書き側は
  同じ run を書き写したもの。basic / outage / strongRecovery / twoNodes(複数ノード)/ equivocation(twoFaced と oneVote)。
- `scenario:<name>/observe <label>` — scenario の `observe` の行(`naru simulate` の出力そのもの)が、golden が生成 Model で畳み込んだ同じ
  run の読みと一致すること(scenario 本体が公開 fn の Setup / run を使っていることの結び付け。両側とも生成 Model)。

行の形(event index j は「j 個の event を畳み込んだ後」): `events n horizon h`、`j reads <node> (t, s, |T|, |bodies|, F, J, h_max, h_j,
stable, confirmed, live_confirmed, |gf_votes[s]|, rows in rounds 0‥2)`、event j を適用する前に `j tick <node> <t> -> ([kinds], [roots], [authors])`
(その tick が emit する object: kind 0 = block / 1 = Goldfish vote / 2 = attestation、root、作者)か `j deliver <node> <t> (…)`(配達される object)。
-/

namespace Golden

/-- 1 つの照合: 名前と、左右の行の列(時間を測るため遅延する)。 -/
structure Case where
  name : String
  leftName : String
  left : Unit → List String
  rightName : String
  right : Unit → List String

/-! ## 手書き Model(H) -/
namespace H
open DecoupledConsensusModel DecoupledConsensusModel.Protocol

abbrev V := Fin 2

def objKind (o : Execution.NamedObject V) : Nat := match o with | .block _ => 0 | .gfVote _ => 1 | .attest _ => 2
def objRoot (o : Execution.NamedObject V) : Nat := match o with
  | .block b => b.root.value
  | .gfVote v => v.head.value
  | .attest row => (row.confirmed.map (·.value)).getD 99
def objAuthor (o : Execution.NamedObject V) : Option Nat := (Execution.NamedObject.author o).map (fun v => (v : Nat))
def objsOf (os : List (Execution.NamedObject V)) : String := toString (os.map objKind, os.map objRoot, os.map objAuthor)
def rootOf (b : Block V) : Nat := b.root.value

def readSt (st : NamedStore V) : String :=
  toString (st.core.t, st.core.s, st.core.T.card, st.bodies.card, rootOf st.core.F, rootOf st.core.J, st.core.h_max, st.core.h_j,
            rootOf (get_stable st.core), rootOf (get_confirmed st.core), rootOf st.core.live_confirmed,
            (st.core.gf_votes st.core.s).length, (st.sg_rows 0).length + (st.sg_rows 1).length + (st.sg_rows 2).length)

def readsLines (j : Nat) (w : Execution.NamedWorld V) : List String :=
  [s!"{j} reads 0 {readSt (w 0).st}", s!"{j} reads 1 {readSt (w 1).st}"]

def emitsOf (S : Execution.Setup V) (w : Execution.NamedWorld V) (v : V) (t : Time) : List (Execution.NamedObject V) :=
  (Execution.NamedNode.tick S v (w v) t).2

/-- run の行の列: 各 event の前に tick の emit / 配達の object、各 event の後に両 node の読み。 -/
def lines (S : Execution.Setup V) (rho : Execution.NamedRun V) : List String := Id.run do
  let mut w : Execution.NamedWorld V := Execution.NamedWorld.init
  let mut out : Array String := #[s!"events {rho.events.length} horizon {rho.horizon}"]
  let mut j := 0
  out := out ++ (readsLines j w).toArray
  for ev in rho.events do
    match ev with
    | .tick v t => out := out.push s!"{j} tick {(v : Nat)} {t} -> {objsOf (emitsOf S w v t)}"
    | .deliver v o t => out := out.push s!"{j} deliver {(v : Nat)} {t} {objsOf [o]}"
    w := Execution.NamedWorld.step S w ev
    j := j + 1
    out := out ++ (readsLines j w).toArray
  return out.toList

-- fixtures(Witnesses の WeakGenesis / Outage / StrongRecovery / FinalityLiveness と、scenario の run の書き写し)
def wNode (v : V) : Node V := { val_index := v, new_root := fun s => ⟨s + 1⟩, awake := fun _ => v = 0 }
def allNode (v : V) : Node V := { val_index := v, new_root := fun s => ⟨s + 1⟩, awake := fun _ => true }
def wHc : HealConfig := ⟨3, by decide, 2, by decide⟩
def wCfg : HeightConfig := ⟨4, 2, 6, by decide, by decide⟩
def fCfg : HeightConfig := ⟨5, 2, 6, by decide, by decide⟩

-- WeakGenesis: Δ 1, GST 0, proposer 0, committee {0}, weights 2 / 1
def wE : Env V :=
  { Δ := 1, Δ_pos := by decide, t_GST := 0, t_GST_nonneg := by decide, proposer := fun _ => 0, committees := ⟨fun _ => {0}⟩,
    electorate := { weight := fun v => if v = 0 then 2 else 1, weight_pos := by decide } }
def wS : Execution.Setup V :=
  { E := wE, hc := wHc, cfg := wCfg, node := wNode, node_val_index := by intro v; rfl, timeout_rounds := by decide,
    committee_nonempty := by intro s; change ({0} : Finset V).Nonempty; exact Finset.singleton_nonempty 0, outage_window := by decide }
-- Outage: GST 44, proposer s = 1 → 0 else 1, weights 3 / 1
def oE : Env V :=
  { Δ := 1, Δ_pos := by decide, t_GST := 44, t_GST_nonneg := by decide, proposer := fun s => if s = 1 then 0 else 1, committees := ⟨fun _ => {0}⟩,
    electorate := { weight := fun v => if v = 0 then 3 else 1, weight_pos := by decide } }
def oS : Execution.Setup V :=
  { E := oE, hc := wHc, cfg := wCfg, node := wNode, node_val_index := by intro v; rfl, timeout_rounds := by decide,
    committee_nonempty := by intro s; change ({0} : Finset V).Nonempty; exact Finset.singleton_nonempty 0, outage_window := by decide }
-- StrongRecovery: GST 1, weights 3 / 1, every node awake
def rE : Env V :=
  { Δ := 1, Δ_pos := by decide, t_GST := 1, t_GST_nonneg := by decide, proposer := fun _ => 0, committees := ⟨fun _ => {0}⟩,
    electorate := { weight := fun v => if v = 0 then 3 else 1, weight_pos := by decide } }
def rS : Execution.Setup V :=
  { E := rE, hc := wHc, cfg := wCfg, node := allNode, node_val_index := by intro v; rfl, timeout_rounds := by decide,
    committee_nonempty := by intro s; change ({0} : Finset V).Nonempty; exact Finset.singleton_nonempty 0, outage_window := by decide }
-- FinalityLiveness: GST 0, weights 3 / 1, K 5
def fE : Env V :=
  { Δ := 1, Δ_pos := by decide, t_GST := 0, t_GST_nonneg := by decide, proposer := fun _ => 0, committees := ⟨fun _ => {0}⟩,
    electorate := { weight := fun v => if v = 0 then 3 else 1, weight_pos := by decide } }
def fS : Execution.Setup V :=
  { E := fE, hc := wHc, cfg := fCfg, node := wNode, node_val_index := by intro v; rfl, timeout_rounds := by decide,
    committee_nonempty := by intro s; change ({0} : Finset V).Nonempty; exact Finset.singleton_nonempty 0, outage_window := by decide }
-- equivocation scenario: WeakGenesis with committee {0, 1}
def qE : Env V :=
  { Δ := 1, Δ_pos := by decide, t_GST := 0, t_GST_nonneg := by decide, proposer := fun _ => 0, committees := ⟨fun _ => {0, 1}⟩,
    electorate := { weight := fun v => if v = 0 then 2 else 1, weight_pos := by decide } }
def qS : Execution.Setup V :=
  { E := qE, hc := wHc, cfg := wCfg, node := wNode, node_val_index := by intro v; rfl, timeout_rounds := by decide,
    committee_nonempty := by intro s; change ({0, 1} : Finset V).Nonempty; exact Finset.insert_nonempty 0 {1}, outage_window := by decide }

def ticks (n : Nat) : List (Execution.NamedEvent V) := (List.range n).map (fun (k : Nat) => .tick 0 (k : Time))
def wRho : Execution.NamedRun V := { honest := {0}, horizon := 30, events := ticks 31 }
def oRho : Execution.NamedRun V := { honest := {0}, horizon := 45, events := ticks 46 }
def fRho (h : Nat) : Execution.NamedRun V := { honest := {0}, horizon := (h : Time), events := ticks (h + 1) }

/-- 2 ノード run の event 列(scenario `twoNodeEvents` と同じ作り方: 各 t で node 0 の tick、node 1 の tick、node 0 の emit の node 1 への配達。
世界は同じ batch で進める)。 -/
def twoNodeEvents (S : Execution.Setup V) (n : Nat) : List (Execution.NamedEvent V) := Id.run do
  let mut w : Execution.NamedWorld V := Execution.NamedWorld.init
  let mut evs : Array (Execution.NamedEvent V) := #[]
  for k in List.range n do
    let t : Time := k
    let batch : List (Execution.NamedEvent V) := [.tick 0 t, .tick 1 t] ++ (emitsOf S w 0 t).map (fun o => .deliver 1 o t)
    w := batch.foldl (fun w2 ev => Execution.NamedWorld.step S w2 ev) w
    evs := evs ++ batch.toArray
  return evs.toList
def wRho2 : Execution.NamedRun V := { honest := {0, 1}, horizon := 7, events := twoNodeEvents wS 8 }

def qV2 : GoldfishVote V := ⟨1, 1, ⟨2⟩⟩
def qV0 : GoldfishVote V := ⟨1, 1, ⟨0⟩⟩
def qEvents (votes : List (GoldfishVote V)) : List (Execution.NamedEvent V) :=
  (List.range 15).flatMap (fun (n : Nat) =>
    [(.tick 0 (n : Time) : Execution.NamedEvent V)] ++ (if n == 5 then votes.map (fun u => (.deliver 0 (.gfVote u) 5 : Execution.NamedEvent V)) else []))
def qRho : Execution.NamedRun V := { honest := {0}, horizon := 14, events := qEvents [qV2, qV0] }
def qRho1 : Execution.NamedRun V := { honest := {0}, horizon := 14, events := qEvents [qV2] }

end H

/-! ## 生成 Model(G) -/
namespace G
open Model.Consensus Model.Consensus.Objects Model.Consensus.Protocol Model.Consensus.Execution

/-- scenario の `input` 束縛(環境のオラクル)。生成 Model の fn は先頭にこの 4 つの関数引数を取る。 -/
structure Inputs where
  committee : Nat → NaruStd.Set Identifiers.ValidatorId
  proposer : Nat → Identifiers.ValidatorId
  awake : Identifiers.ValidatorId → Nat → Bool
  newRoot : Identifiers.ValidatorId → Nat → Identifiers.BlockId

def vid (n : Nat) : Identifiers.ValidatorId := ⟨n⟩
def objKind (o : Model.Consensus.Execution.Objects.NamedObject) : Nat := match o with | .Block _ => 0 | .GfVote _ => 1 | .Attest _ => 2
def objRoot (o : Model.Consensus.Execution.Objects.NamedObject) : Nat := match o with
  | .Block b => (NamedBlocks.namedRoot b).value
  | .GfVote v => v.head.value
  | .Attest row => (row.confirmed.map (·.value)).getD 99
def objAuthor (o : Model.Consensus.Execution.Objects.NamedObject) : Option Nat := (Model.Consensus.Execution.Objects.author o).map (·.value)
def objsOf (os : List Model.Consensus.Execution.Objects.NamedObject) : String := toString (os.map objKind, os.map objRoot, os.map objAuthor)
def rootOf (b : Blocks.Block) : Nat := (Blocks.root b).value

def readSt (st : Handlers.NamedStore) : String :=
  toString (st.core.t, st.core.s, st.core.tree.size, st.bodies.size, rootOf st.core.f, rootOf st.core.j, st.core.hMax, st.core.hJ,
            rootOf (Handlers.getStable st.core), rootOf (Handlers.getConfirmed st.core), rootOf st.core.liveConfirmed,
            (st.core.gfVotes.getOr st.core.s []).length, (st.sgRows.getOr 0 []).length + (st.sgRows.getOr 1 []).length + (st.sgRows.getOr 2 []).length)

def readsLines (j : Nat) (w : Run.NamedWorld) : List String :=
  [s!"{j} reads 0 {readSt (Run.worldAt w (vid 0)).st}", s!"{j} reads 1 {readSt (Run.worldAt w (vid 1)).st}"]

def emitsOf (I : Inputs) (S : Setup.Setup) (w : Run.NamedWorld) (v : Identifiers.ValidatorId) (t : Int) :
    List Model.Consensus.Execution.Objects.NamedObject :=
  (Node.nodeTick I.committee I.proposer I.awake I.newRoot S v (Run.worldAt w v) t).2

/-- H.lines と同じ形の行の列。 -/
def lines (I : Inputs) (S : Setup.Setup) (rho : Run.NamedRun) : List String := Id.run do
  let mut w : Run.NamedWorld := Run.worldInit
  let mut out : Array String := #[s!"events {rho.events.length} horizon {rho.horizon}"]
  let mut j := 0
  out := out ++ (readsLines j w).toArray
  for ev in rho.events do
    match ev with
    | .Tick v t => out := out.push s!"{j} tick {v.value} {t} -> {objsOf (emitsOf I S w v t)}"
    | .Deliver v o t => out := out.push s!"{j} deliver {v.value} {t} {objsOf [o]}"
    w := Run.worldStep I.committee I.proposer I.awake I.newRoot S w ev
    j := j + 1
    out := out ++ (readsLines j w).toArray
  return out.toList

-- Witnesses の fixture の書き写し(scenario を経由しない側)
def tblOf {κ ν : Type} [Ord κ] (xs : List (κ × ν)) : NaruStd.Table κ ν := xs.foldl (fun t e => t.insert e.1 e.2) NaruStd.Table.empty
def env (gst : Int) (w0 w1 : Nat) : Parameters.ProtocolEnv := ⟨1, gst, ⟨tblOf [(vid 0, w0), (vid 1, w1)]⟩⟩
def wHc : Grades.HealConfig := ⟨3, 2⟩
def wCfg : ChainState.HeightConfig := ⟨4, 2, 6⟩
def fCfg : ChainState.HeightConfig := ⟨5, 2, 6⟩
def wS : Setup.Setup := ⟨env 0 2 1, wHc, wCfg⟩
def oS : Setup.Setup := ⟨env 44 3 1, wHc, wCfg⟩
def rS : Setup.Setup := ⟨env 1 3 1, wHc, wCfg⟩
def fS : Setup.Setup := ⟨env 0 3 1, wHc, fCfg⟩

-- 環境のオラクル(scenario の `input` 束縛と同じ値)
def wI : Inputs :=
  { committee := fun _ => NaruStd.Set.singleton (vid 0), proposer := fun _ => vid 0, awake := fun v _ => v.value == 0, newRoot := fun _ s => ⟨s + 1⟩ }
def oI : Inputs := { wI with proposer := fun s => if s == 1 then vid 0 else vid 1 }
def rI : Inputs := { wI with awake := fun _ _ => true }
def qI : Inputs := { wI with committee := fun _ => (NaruStd.Set.singleton (vid 0)).insert (vid 1) }

def ticks (n : Nat) : List Run.NamedEvent := (List.range n).map (fun (k : Nat) => .Tick (vid 0) (k : Int))
def wRho : Run.NamedRun := ⟨NaruStd.Set.singleton (vid 0), 30, ticks 31⟩
def oRho : Run.NamedRun := ⟨NaruStd.Set.singleton (vid 0), 45, ticks 46⟩
def fRho (h : Nat) : Run.NamedRun := ⟨NaruStd.Set.singleton (vid 0), (h : Int), ticks (h + 1)⟩

/-- scenario の observer `trace` の行(`naru simulate` の表示と同じ `Repr` の描画)。 -/
def traceLines (I : Inputs) (S : Setup.Setup) (rho : Run.NamedRun) (v : Identifiers.ValidatorId) : List String :=
  (Model.Scenarios.Trace.trace I.committee I.proposer I.awake I.newRoot S rho v).map NaruStd.render

/-- scenario の `observe` の行を label で引く。 -/
def obsLines (obs : List NaruStd.Observation) (label : String) : List String :=
  match obs.find? (fun o => o.label == label) with
  | some o => o.lines
  | none => [s!"<no observation {label}>"]

end G

/-! ## case -/

def v0 : Model.Consensus.Objects.Identifiers.ValidatorId := G.vid 0
def v1 : Model.Consensus.Objects.Identifiers.ValidatorId := G.vid 1

/-- 手書き ↔ 生成の case。 -/
def hg (name : String) (hand : Unit → List String) (gen : Unit → List String) : Case :=
  { name, leftName := "hand", left := hand, rightName := "gen", right := gen }

/-- scenario の `observe` の行 ↔ 生成 Model での同じ run の読み。 -/
def tie (name : String) (obs : List NaruStd.Observation) (label : String) (gen : Unit → List String) : Case :=
  { name := s!"{name}/observe {label}", leftName := "observe", left := fun _ => G.obsLines obs label, rightName := "gen", right := gen }

def witnessCases (finalityHorizon : Nat) : List Case :=
  [ hg "witness:weakGenesis" (fun _ => H.lines H.wS H.wRho) (fun _ => G.lines G.wI G.wS G.wRho),
    hg "witness:outage" (fun _ => H.lines H.oS H.oRho) (fun _ => G.lines G.oI G.oS G.oRho),
    hg "witness:strongRecovery" (fun _ => H.lines H.rS H.wRho) (fun _ => G.lines G.rI G.rS G.wRho),
    hg s!"witness:finalityLiveness(horizon {finalityHorizon})" (fun _ => H.lines H.fS (H.fRho finalityHorizon)) (fun _ => G.lines G.wI G.fS (G.fRho finalityHorizon)) ]

open Model.Scenarios in
def scenarioCases : List Case :=
  let bS := Basic.basicSetup
  let bR := Basic.basicRun v0
  let oS := Outage.outageSetup
  let oR := Outage.outageRun v0
  let rS := StrongRecovery.strongRecoverySetup
  let rR := StrongRecovery.strongRecoveryRun v0
  let tS := TwoNodes.twoNodesSetup
  let tR := TwoNodes.twoNodesRun G.wI.committee G.wI.proposer G.wI.awake G.wI.newRoot tS v0 v1
  let qS := Equivocation.equivocationSetup
  let q2 := Equivocation.twoFacedRun v0 v1
  let q1 := Equivocation.oneVoteRun v0 v1
  [ hg "scenario:basic" (fun _ => H.lines H.wS H.wRho) (fun _ => G.lines G.wI bS bR),
    tie "scenario:basic" Basic.basic "trace(s, rho, v0)" (fun _ => G.traceLines G.wI bS bR v0),
    hg "scenario:outage" (fun _ => H.lines H.oS H.oRho) (fun _ => G.lines G.oI oS oR),
    tie "scenario:outage" Outage.outage "trace(s, rho, v0)" (fun _ => G.traceLines G.oI oS oR v0),
    hg "scenario:strongRecovery" (fun _ => H.lines H.rS H.wRho) (fun _ => G.lines G.rI rS rR),
    tie "scenario:strongRecovery" StrongRecovery.strongRecovery "trace(s, rho, v0)" (fun _ => G.traceLines G.rI rS rR v0),
    hg "scenario:twoNodes" (fun _ => H.lines H.wS H.wRho2) (fun _ => G.lines G.wI tS tR),
    tie "scenario:twoNodes" TwoNodes.twoNodes "trace(s, rho, v1)" (fun _ => G.traceLines G.wI tS tR v1),
    hg "scenario:equivocation/twoFaced" (fun _ => H.lines H.qS H.qRho) (fun _ => G.lines G.qI qS q2),
    tie "scenario:equivocation" Equivocation.equivocation "trace(s, twoFaced, v0)" (fun _ => G.traceLines G.qI qS q2 v0),
    hg "scenario:equivocation/oneVote" (fun _ => H.lines H.qS H.qRho1) (fun _ => G.lines G.qI qS q1),
    tie "scenario:equivocation" Equivocation.equivocation "trace(s, oneVote, v0)" (fun _ => G.traceLines G.qI qS q1 v0) ]

/-- 左右の行を順に比べ、違う行の数を返す(最初の 5 件は表示する)。行数の違いも数える。 -/
def runCase (c : Case) : IO Nat := do
  -- `IO.lazyPure` で計算を IO の列に固定する(純粋な `let` はコンパイラが最初の使用まで動かすので計時がずれる)
  let t0 ← IO.monoMsNow
  let l ← IO.lazyPure c.left
  let t1 ← IO.monoMsNow
  let r ← IO.lazyPure c.right
  let t2 ← IO.monoMsNow
  let n := max l.length r.length
  let mut bad := 0
  for i in List.range n do
    let a := l.getD i "<missing>"
    let b := r.getD i "<missing>"
    if a != b then
      bad := bad + 1
      if bad ≤ 5 then IO.println s!"MISMATCH {c.name} line {i}:\n  {c.leftName}: {a}\n  {c.rightName}: {b}"
  if bad == 0 then
    IO.println s!"ok {c.name}: {l.length} lines agree ({c.leftName} {t1 - t0} ms, {c.rightName} {t2 - t1} ms)"
  else
    IO.println s!"FAIL {c.name}: {bad} mismatching lines of {n} ({c.leftName} {l.length} lines in {t1 - t0} ms, {c.rightName} {r.length} lines in {t2 - t1} ms)"
  return bad

def defaultFinalityHorizon : Nat := 33729

/-- 引数: `--finality-horizon N`(FinalityLiveness の horizon。既定 33729)、`--side hand|gen`(計測用: FinalityLiveness の case を
片側だけ計算して行数と時間を出す。照合はしない)。 -/
structure Args where
  finalityHorizon : Nat := defaultFinalityHorizon
  side : Option String := none

def parseArgs : List String → Option Args
  | [] => some {}
  | "--finality-horizon" :: n :: rest => do let a ← parseArgs rest; let h ← n.toNat?; pure { a with finalityHorizon := h }
  | "--side" :: s :: rest => if s == "hand" || s == "gen" then do let a ← parseArgs rest; pure { a with side := some s } else none
  | _ => none

/-- 片側だけの計測(FinalityLiveness の case)。 -/
def measure (c : Case) (side : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let l ← IO.lazyPure (if side == "hand" then c.left else c.right)
  let t1 ← IO.monoMsNow
  IO.println s!"measure {c.name} {side}: {l.length} lines in {t1 - t0} ms"
  IO.println s!"  last: {l.getLastD ""}"
  return 0

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | none =>
    IO.eprintln "usage: lean --run tests/golden/Golden.lean [--finality-horizon N] [--side hand|gen]"
    return 2
  | some a =>
    match a.side with
    | some side =>
      match (witnessCases a.finalityHorizon).getLast? with
      | some c => measure c side
      | none => return 2
    | none =>
      let mut total := 0
      for c in witnessCases a.finalityHorizon ++ scenarioCases do
        total := total + (← runCase c)
      IO.println s!"MISMATCH total: {total}"
      return if total == 0 then 0 else 1

end Golden

def main (args : List String) : IO UInt32 := Golden.main args
