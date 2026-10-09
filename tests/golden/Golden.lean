import DecoupledConsensusModel.Protocol.Tick
import DecoupledConsensusModel.Protocol.Evidence
import DecoupledConsensusModel.Execution.Instance
import Model
/-!
# tests/golden/Golden.lean — C10 の golden test(同一 Lean プログラム)

手書き Model(`third_party/verified-consensus/DecoupledConsensusModel`、mathlib の上)と生成 Model(`generated/Model` + `NaruStd`)を **1 つの Lean
プログラム**から import し、同じ fixture(run)を両側で畳み込んで、各 event の前後の両 node の読みと tick が emit した object を
行の列にして突き合わせ、MISMATCH を数える。IDEAL.md C10 の検証そのもの(ドライバは `lake exe naru_test golden`)。

実行(リポジトリのルートで。`lake exe naru compile` → `lake build Model` 済みで、third_party/verified-consensus の Model の olean がビルド済みであること):
  LEAN_PATH="$(cd third_party/verified-consensus && lake env printenv LEAN_PATH):$PWD/.lake/build/lib/lean" \
    lean --run tests/golden/Golden.lean [--finality-horizon N] [--comparator-check]
出力: まず比較器の検体(下)の `comparator agree <名前>: ok` / `comparator probe <名前>: ok (detected)` と `comparator total: …`、次に case ごとに
`ok <case>: n lines agree` か `FAIL <case>: …` と `MISMATCH …` の行、最後に `MISMATCH total: N`。exit 0 ⇔ 比較器の失敗 0 かつ N = 0。
`--comparator-check` は比較器の検体だけを検査する(`lake exe naru_test golden --comparator`。`naru_test regression` の C10 の比較器回帰)。

fixture(case):
- `witness:weakGenesis` / `witness:outage` / `witness:strongRecovery(seed rho 30)` / `witness:finalityLiveness(horizon N)` — verified-consensus の
  Witnesses の 4 run を両側で Lean に書き写したもの(Witnesses のモジュールは Proofs を import するので使えない)。WeakGenesis(horizon 30)と
  Outage(horizon 45)は全 horizon。StrongRecovery は Witness の seed `rho 30`(本番の `rho eventCount` = 約 5,743 tick は両 Model とも実行不能)。
  FinalityLiveness は同じ Setup と同じ tick 列の先頭から `--finality-horizon N` までの prefix(t = 0 … N、N + 1 tick)。既定の N は C10 が
  求める 100(Witness の全 horizon 33729 = 33,730 tick は両 Model とも実行不能: 周回 21 の計測)。
- `scenario:<name>` — naru の scenario(`specs/consensus/scenarios/*.naru`)が fn として公開する Setup と run を生成 Model からそのまま取り、手書き側は
  同じ run を書き写したもの。basic / outage / strongRecovery / twoNodes(複数ノード)/ equivocation(twoFaced と oneVote)。
- `scenario:<name>/observe <label>` — scenario の `observe` の行(`naru simulate` の出力そのもの)が、golden が生成 Model で畳み込んだ同じ
  run の読みと一致すること(scenario 本体が公開 fn の Setup / run を使っていることの結び付け。両側とも生成 Model)。

行の形(event index j は「j 個の event を畳み込んだ後」): `events n horizon h`、`j reads <node> (t, s, |T|, |bodies|, F, J, h_max, h_j,
stable, confirmed, live_confirmed, |gf_votes[s]|, rows in rounds 0‥2)`、event j を適用する前に `j tick <node> <t> -> [obj, …]`
(その tick が emit する object の列。各 obj は下の共通表現)か `j deliver <node> <t> [obj]`(配達される object)。

## emitted objects の共通表現(`Common`)

両 Model の object(`NamedObject`: block / Goldfish vote / attestation)を、表現上の差(型名・構築子名・欄名、`Fin 2` と `ValidatorId`、
`BlockId` の構造)だけを吸収して木 `Common` に写し、`Common.render` の文字列(単射)で比べる。写す内容(IDEAL.md C10):
- Goldfish vote: 作者・slot・head(root の値)。
- attestation(named row): 作者・round・confirmed(`Option BlockId`: `none` / `(some r)`)・height pair(variant `empty` / `(vote height entry timeout)`)・
  finality pair(`none` / `(some (finality height target))`)。
- block: variant(`genesis` / `node`)と、node なら 親(再帰的に genesis までの全祖先。各祖先の votes / support / rows も含む)・slot・root・
  `gf_votes` / `gf_support_votes`(`[vote, …]`、順序を保つ)・attestations(`[row, …]`、順序を保つ)・proposer。
- Option は `none` / `(some v)` をそのまま写す(None と Some を混同しない。以前の 3 つ組 `(kind, root, author)` は confirmed の `none` を
  `99` に潰していたので root 99 の `some` と区別できなかった)。variant は構築子名ごと写す。
- 正規化は無い: object の中の列(`gf_votes` / `gf_support_votes` / `attestations`)は両 Model とも `List` で、順序ごと比べる。集合(手書きの
  `Finset`、生成の `NaruStd.Set`)は object の中に現れず、node の状態(`reads` の `|T|` / `|bodies|`)にだけ現れて濃度で比べる。

## 比較器の検体(`--comparator-check`。IDEAL.md C10 の比較器回帰)

同じ記述(`Probe.DObj`)から手書き側(`H.objOf`)と生成側(`G.objOf`)の object を組み立て、
- `agree`: 同じ意味の両表現が一致する(vote / 各 variant の row / 2 代の祖先と votes・support・rows を持つ block / genesis / tick の列)、
- `probe`: 基準と、一つだけ変えた検体(object の種類、vote の各欄、row の各欄と Option の none ↔ some・variant、block の variant・各欄・親と祖先の欄・
  列の順序・要素・要素の入れ子の欄)が、両側とも一致したうえで基準と不一致になる(`none` と root 99 / root 0(genesis)の `some` の区別を含む)
ことを確かめ、1 つでも破れば exit 1。検体の名前の一覧は `tests/NaruTest/Golden.lean` の `expectedProbes` が要求する。
-/

namespace Golden

/-- 1 つの照合: 名前と、左右の行の列(時間を測るため遅延する)。 -/
structure Case where
  name : String
  leftName : String
  left : Unit → List String
  rightName : String
  right : Unit → List String

/-! ## emitted objects の共通表現 -/

/-- 両 Model の object を写す共通表現(冒頭の説明)。 -/
inductive Common where
  | nat (n : Nat)
  | bool (b : Bool)
  | opt (v : Option Common)
  | ctor (name : String) (args : List Common)
  | list (xs : List Common)

mutual
/-- 共通表現の文字列: 数、`true` / `false`、`none` / `(some v)`、`name` / `(name 引数 …)`、`[要素, …]`。 -/
def Common.render : Common → String
  | .nat n => toString n
  | .bool b => toString b
  | .opt none => "none"
  | .opt (some v) => "(some " ++ v.render ++ ")"
  | .ctor name [] => name
  | .ctor name args => "(" ++ name ++ Common.renderArgs args ++ ")"
  | .list xs => "[" ++ Common.renderItems xs ++ "]"
def Common.renderArgs : List Common → String
  | [] => ""
  | v :: vs => " " ++ v.render ++ Common.renderArgs vs
def Common.renderItems : List Common → String
  | [] => ""
  | [v] => v.render
  | v :: vs => v.render ++ ", " ++ Common.renderItems vs
end

/-! ## 比較器の検体の記述(両側の object をここから組み立てる) -/
namespace Probe

structure DVote where
  author : Nat
  slot : Nat
  head : Nat

inductive DHp where
  | empty
  | vote (height entry : Nat) (timeout : Bool)

structure DAtt where
  author : Nat
  round : Nat
  confirmed : Option Nat
  hp : DHp
  fp : Option (Nat × Nat)

inductive DBlock where
  | genesis
  | node (parent : DBlock) (slot root : Nat) (votes support : List DVote) (atts : List DAtt) (proposer : Nat)

inductive DObj where
  | block (b : DBlock)
  | vote (v : DVote)
  | attest (a : DAtt)

/-- 基準と、一つだけ変えた検体。 -/
structure Sample where
  name : String
  base : DObj
  variant : DObj

end Probe

/-! ## 手書き Model(H) -/
namespace H
open DecoupledConsensusModel DecoupledConsensusModel.Protocol

abbrev V := Fin 2

-- 共通表現への写像
def vidV (v : V) : Common := .nat (v : Nat)
def bidV (r : BlockId) : Common := .nat r.value
def voteV (u : GoldfishVote V) : Common := .ctor "vote" [vidV u.val_index, .nat u.slot, bidV u.head]
def hpV : NamedHeightPair → Common
  | .empty => .ctor "empty" []
  | .vote h e t => .ctor "vote" [.nat h, bidV e, .bool t]
def fpV (p : FinalityPair) : Common := .ctor "finality" [.nat p.height, bidV p.target]
def attV (a : NamedAttestation V) : Common :=
  .ctor "row" [vidV a.val_index, .nat a.round, .opt (a.confirmed.map bidV), hpV a.height_pair, .opt (a.finality_pair.map fpV)]
def blockV : NamedBlock V → Common
  | .genesis => .ctor "genesis" []
  | .node p s r votes support rows proposer =>
    .ctor "node" [blockV p, .nat s, bidV r, .list (votes.map voteV), .list (support.map voteV), .list (rows.map attV), vidV proposer]
def objV : Execution.NamedObject V → Common
  | .block b => .ctor "block" [blockV b]
  | .gfVote u => .ctor "gfVote" [voteV u]
  | .attest a => .ctor "attest" [attV a]
def objsOf (os : List (Execution.NamedObject V)) : String := (Common.list (os.map objV)).render
def rootOf (b : Block V) : Nat := b.root.value

/-! 周回 35 までの比較(失敗例): object を `(kind, root, author)` の 3 つ組にしか写さず、attestation の `confirmed` の `none` を 99 に潰していた。
比較器の検体のうちこれが見逃すもの(`comparator legacy-miss`)を報告し、検体に検出力があることを示す。 -/
namespace Legacy
def objKind (o : Execution.NamedObject V) : Nat := match o with | .block _ => 0 | .gfVote _ => 1 | .attest _ => 2
def objRoot (o : Execution.NamedObject V) : Nat := match o with
  | .block b => b.root.value
  | .gfVote v => v.head.value
  | .attest row => (row.confirmed.map (·.value)).getD 99
def objAuthor (o : Execution.NamedObject V) : Option Nat := (Execution.NamedObject.author o).map (fun v => (v : Nat))
def objsOf (os : List (Execution.NamedObject V)) : String := toString (os.map objKind, os.map objRoot, os.map objAuthor)
end Legacy

-- 検体の記述からの組み立て
def fin2 (n : Nat) : V := if n == 0 then 0 else 1
def voteOf (d : Probe.DVote) : GoldfishVote V := ⟨fin2 d.author, d.slot, ⟨d.head⟩⟩
def hpOf : Probe.DHp → NamedHeightPair
  | .empty => .empty
  | .vote h e t => .vote h ⟨e⟩ t
def attOf (d : Probe.DAtt) : NamedAttestation V :=
  ⟨fin2 d.author, d.round, d.confirmed.map (fun n => ⟨n⟩), hpOf d.hp, d.fp.map (fun (h, t) => ⟨h, ⟨t⟩⟩)⟩
def blockOf : Probe.DBlock → NamedBlock V
  | .genesis => .genesis
  | .node p s r votes support atts proposer =>
    .node (blockOf p) s ⟨r⟩ (votes.map voteOf) (support.map voteOf) (atts.map attOf) (fin2 proposer)
def objOf : Probe.DObj → Execution.NamedObject V
  | .block b => .block (blockOf b)
  | .vote v => .gfVote (voteOf v)
  | .attest a => .attest (attOf a)

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

-- 共通表現への写像(H と同じ形)
def vidV (v : Identifiers.ValidatorId) : Common := .nat v.value
def bidV (r : Identifiers.BlockId) : Common := .nat r.value
def voteV (u : Blocks.GoldfishVote) : Common := .ctor "vote" [vidV u.valIndex, .nat u.slot, bidV u.head]
def hpV : NamedBlocks.NamedHeightPair → Common
  | .Empty => .ctor "empty" []
  | .Vote h e t => .ctor "vote" [.nat h, bidV e, .bool t]
def fpV (p : Blocks.FinalityPair) : Common := .ctor "finality" [.nat p.height, bidV p.target]
def attV (a : NamedBlocks.NamedAttestation) : Common :=
  .ctor "row" [vidV a.valIndex, .nat a.round, .opt (a.confirmed.map bidV), hpV a.heightPair, .opt (a.finalityPair.map fpV)]
def blockV : NamedBlocks.NamedBlock → Common
  | .Genesis => .ctor "genesis" []
  | .Node p s r votes support rows proposer =>
    .ctor "node" [blockV p, .nat s, bidV r, .list (votes.map voteV), .list (support.map voteV), .list (rows.map attV), vidV proposer]
def objV : Model.Consensus.Execution.Objects.NamedObject → Common
  | .Block b => .ctor "block" [blockV b]
  | .GfVote u => .ctor "gfVote" [voteV u]
  | .Attest a => .ctor "attest" [attV a]
def objsOf (os : List Model.Consensus.Execution.Objects.NamedObject) : String := (Common.list (os.map objV)).render
def rootOf (b : Blocks.Block) : Nat := (Blocks.root b).value

-- 検体の記述からの組み立て
def voteOf (d : Probe.DVote) : Blocks.GoldfishVote := ⟨vid d.author, d.slot, ⟨d.head⟩⟩
def hpOf : Probe.DHp → NamedBlocks.NamedHeightPair
  | .empty => .Empty
  | .vote h e t => .Vote h ⟨e⟩ t
def attOf (d : Probe.DAtt) : NamedBlocks.NamedAttestation :=
  ⟨vid d.author, d.round, d.confirmed.map (fun n => ⟨n⟩), hpOf d.hp, d.fp.map (fun (h, t) => ⟨h, ⟨t⟩⟩)⟩
def blockOf : Probe.DBlock → NamedBlocks.NamedBlock
  | .genesis => .Genesis
  | .node p s r votes support atts proposer =>
    .Node (blockOf p) s ⟨r⟩ (votes.map voteOf) (support.map voteOf) (atts.map attOf) (vid proposer)
def objOf : Probe.DObj → Model.Consensus.Execution.Objects.NamedObject
  | .block b => .Block (blockOf b)
  | .vote v => .GfVote (voteOf v)
  | .attest a => .Attest (attOf a)

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

/-! ## 比較器の検体 -/
namespace Probe

def vA : DVote := ⟨1, 3, 4⟩
def vB : DVote := ⟨0, 3, 2⟩
/-- confirmed が some、height pair が target vote、finality pair が some の row。 -/
def aFull : DAtt := ⟨0, 2, some 4, .vote 5 4 false, some (1, 2)⟩
/-- confirmed が none、height pair が empty、finality pair が none の row。 -/
def aNone : DAtt := ⟨1, 7, none, .empty, none⟩
/-- timeout の height pair を持つ row。 -/
def aTimeout : DAtt := ⟨1, 6, some 2, .vote 6 2 true, none⟩
/-- 祖父(genesis の子)。 -/
def gp : DBlock := .node .genesis 1 1 [] [] [] 0
/-- 親(vote と timeout の row を持つ)。 -/
def par : DBlock := .node gp 2 2 [vB] [] [aTimeout] 0

/-- 基準の block(2 代の祖先、votes 2、support 1、rows 2)。引数を 1 つ変えて検体を作る。 -/
def b (parent : DBlock := par) (slot : Nat := 3) (root : Nat := 4) (votes : List DVote := [vA, vB]) (support : List DVote := [vA])
    (atts : List DAtt := [aFull, aNone]) (proposer : Nat := 1) : DObj :=
  .block (.node parent slot root votes support atts proposer)
/-- 基準の row(`aFull`)。引数を 1 つ変えて検体を作る。 -/
def a (author : Nat := 0) (round : Nat := 2) (confirmed : Option Nat := some 4) (hp : DHp := .vote 5 4 false)
    (fp : Option (Nat × Nat) := some (1, 2)) : DObj :=
  .attest ⟨author, round, confirmed, hp, fp⟩
/-- `aNone` を基準にした row。 -/
def aN (confirmed : Option Nat := none) (hp : DHp := .empty) (fp : Option (Nat × Nat) := none) : DObj :=
  .attest ⟨1, 7, confirmed, hp, fp⟩
/-- 基準の vote(`vA`)。 -/
def v (author : Nat := 1) (slot : Nat := 3) (head : Nat := 4) : DObj := .vote ⟨author, slot, head⟩

/-- 同じ意味の両表現が一致する検体(名前, object の列)。 -/
def agreements : List (String × List DObj) :=
  [ ("gfVote", [v]),
    ("row full", [a]),
    ("row none / empty / none", [aN]),
    ("row timeout", [.attest aTimeout]),
    ("block with 2 ancestors, votes, support, rows", [b]),
    ("genesis", [.block .genesis]),
    ("tick list block, gfVote, attest", [b, v, a]) ]

/-- 一つだけ変えた検体(名前, 基準, 検体)。 -/
def probes : List Sample :=
  [ -- object の種類
    ⟨"kind block → gfVote", b, v⟩,
    ⟨"kind gfVote → attest", v, a⟩,
    -- Goldfish vote
    ⟨"vote.author", v, v (author := 0)⟩,
    ⟨"vote.slot", v, v (slot := 2)⟩,
    ⟨"vote.head", v, v (head := 5)⟩,
    -- attestation row
    ⟨"row.author", a, a (author := 1)⟩,
    ⟨"row.round", a, a (round := 3)⟩,
    ⟨"row.confirmed some → none", a, a (confirmed := none)⟩,
    ⟨"row.confirmed some 4 → some 5", a, a (confirmed := some 5)⟩,
    ⟨"row.confirmed none → some 99", aN, aN (confirmed := some 99)⟩,
    ⟨"row.confirmed none → some 0 (genesis root)", aN, aN (confirmed := some 0)⟩,
    ⟨"row.heightPair vote → empty", a, a (hp := .empty)⟩,
    ⟨"row.heightPair empty → vote", aN, aN (hp := .vote 5 4 false)⟩,
    ⟨"row.heightPair.height", a, a (hp := .vote 6 4 false)⟩,
    ⟨"row.heightPair.entry", a, a (hp := .vote 5 3 false)⟩,
    ⟨"row.heightPair.timeout", a, a (hp := .vote 5 4 true)⟩,
    ⟨"row.finalityPair some → none", a, a (fp := none)⟩,
    ⟨"row.finalityPair none → some", aN, aN (fp := some (1, 2))⟩,
    ⟨"row.finalityPair.height", a, a (fp := some (2, 2))⟩,
    ⟨"row.finalityPair.target", a, a (fp := some (1, 3))⟩,
    -- block
    ⟨"block node → genesis", b, .block .genesis⟩,
    ⟨"block.slot", b, b (slot := 2)⟩,
    ⟨"block.root", b, b (root := 5)⟩,
    ⟨"block.proposer", b, b (proposer := 0)⟩,
    ⟨"block.parent.root", b, b (parent := .node gp 2 9 [vB] [] [aTimeout] 0)⟩,
    ⟨"block.parent.slot", b, b (parent := .node gp 1 2 [vB] [] [aTimeout] 0)⟩,
    ⟨"block.parent.proposer", b, b (parent := .node gp 2 2 [vB] [] [aTimeout] 1)⟩,
    ⟨"block.parent.votes element", b, b (parent := .node gp 2 2 [vA] [] [aTimeout] 0)⟩,
    ⟨"block.parent.rows nested timeout", b, b (parent := .node gp 2 2 [vB] [] [⟨1, 6, some 2, .vote 6 2 false, none⟩] 0)⟩,
    ⟨"block.parent.parent.root (grandparent)", b, b (parent := .node (.node .genesis 1 7 [] [] [] 0) 2 2 [vB] [] [aTimeout] 0)⟩,
    ⟨"block.parent.parent.parent genesis → node (one more ancestor)", b,
      b (parent := .node (.node (.node .genesis 1 7 [] [] [] 1) 1 1 [] [] [] 0) 2 2 [vB] [] [aTimeout] 0)⟩,
    ⟨"block.votes order", b, b (votes := [vB, vA])⟩,
    ⟨"block.votes element.slot", b, b (votes := [vA, ⟨0, 9, 2⟩])⟩,
    ⟨"block.votes dropped element", b, b (votes := [vA])⟩,
    ⟨"block.support element", b, b (support := [vB])⟩,
    ⟨"block.support added element", b, b (support := [vA, vB])⟩,
    ⟨"block.support order", b (support := [vA, vB]), b (support := [vB, vA])⟩,
    ⟨"block.rows order", b, b (atts := [aNone, aFull])⟩,
    ⟨"block.rows dropped element", b, b (atts := [aFull])⟩,
    ⟨"block.rows nested confirmed none → some 99", b, b (atts := [aFull, ⟨1, 7, some 99, .empty, none⟩])⟩,
    ⟨"block.rows nested finalityPair.target", b, b (atts := [⟨0, 2, some 4, .vote 5 4 false, some (1, 3)⟩, aNone])⟩,
    ⟨"block.rows nested heightPair empty → vote", b, b (atts := [aFull, ⟨1, 7, none, .vote 1 1 false, none⟩])⟩ ]

end Probe

/-- 比較器の検体を検査する: 同じ記述から両側の object を組み立て、agree は両表現が一致し、probe は基準・検体とも両側で一致したうえで
基準と検体が不一致になる。失敗の数を返す。 -/
def runComparator : IO Nat := do
  let mut bad := 0
  for (name, ds) in Probe.agreements do
    let h := H.objsOf (ds.map H.objOf)
    let g := G.objsOf (ds.map G.objOf)
    if h == g then IO.println s!"comparator agree {name}: ok {h}"
    else
      bad := bad + 1
      IO.println s!"comparator agree {name}: FAIL\n  hand: {h}\n  gen: {g}"
  for p in Probe.probes do
    let hb := H.objsOf [H.objOf p.base]
    let gb := G.objsOf [G.objOf p.base]
    let hv := H.objsOf [H.objOf p.variant]
    let gv := G.objsOf [G.objOf p.variant]
    if hb == gb && hv == gv && hb != hv && gb != gv then IO.println s!"comparator probe {p.name}: ok (detected)"
    else
      bad := bad + 1
      IO.println s!"comparator probe {p.name}: FAIL (base agrees {hb == gb}, variant agrees {hv == gv}, base ≠ variant {hb != hv} / {gb != gv})\n  base: {hb}\n  variant: {gv}"
  -- 失敗例: 旧 3 つ組が見逃す検体(情報。ドライバが期待する見逃しの一覧と照合する)
  let mut misses := 0
  for p in Probe.probes do
    if H.Legacy.objsOf [H.objOf p.base] == H.Legacy.objsOf [H.objOf p.variant] then
      misses := misses + 1
      IO.println s!"comparator legacy-miss {p.name}: not detected by the old (kind, root, author) triple"
  IO.println s!"comparator total: {Probe.agreements.length} agreements, {Probe.probes.length} probes, {bad} failure(s); the old triple misses {misses}"
  return bad

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
    hg "witness:strongRecovery(seed rho 30)" (fun _ => H.lines H.rS H.wRho) (fun _ => G.lines G.rI G.rS G.wRho),
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

/-- FinalityLiveness の prefix の既定 horizon。IDEAL.md C10 の「`horizon = 100` までの prefix(t = 0〜100、101 tick)」。 -/
def defaultFinalityHorizon : Nat := 100
/-- Witness 自身の horizon(tick 33,730)。両 Model とも実行不能なので既定にはしない(記録のため)。 -/
def witnessFinalityHorizon : Nat := 33729

/-- 引数: `--finality-horizon N`(FinalityLiveness の prefix の horizon。既定 100 = C10)、`--side hand|gen`(計測用: FinalityLiveness の case を
片側だけ計算して行数と時間を出す。照合はしない)、`--comparator-check`(比較器の検体だけを検査する)。 -/
structure Args where
  finalityHorizon : Nat := defaultFinalityHorizon
  side : Option String := none
  comparatorOnly : Bool := false

def parseArgs : List String → Option Args
  | [] => some {}
  | "--finality-horizon" :: n :: rest => do let a ← parseArgs rest; let h ← n.toNat?; pure { a with finalityHorizon := h }
  | "--side" :: s :: rest => if s == "hand" || s == "gen" then do let a ← parseArgs rest; pure { a with side := some s } else none
  | "--comparator-check" :: rest => do let a ← parseArgs rest; pure { a with comparatorOnly := true }
  | _ => none

/-- 片側だけの計測(FinalityLiveness の case)。 -/
def measure (c : Case) (side : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let l ← IO.lazyPure (if side == "hand" then c.left else c.right)
  let t1 ← IO.monoMsNow
  IO.println s!"measure {c.name} {side}: {l.length} lines in {t1 - t0} ms"
  IO.println s!"  first emitting tick: {(l.find? (fun s => (s.splitOn " tick ").length > 1 && !s.endsWith "[]")).getD ""}"
  IO.println s!"  longest: {l.foldl (fun best s => if s.length > best.length then s else best) ""}"
  IO.println s!"  last: {l.getLastD ""}"
  return 0

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | none =>
    IO.eprintln "usage: lean --run tests/golden/Golden.lean [--finality-horizon N] [--side hand|gen] [--comparator-check]"
    return 2
  | some a =>
    if a.comparatorOnly then
      let bad ← runComparator
      return if bad == 0 then 0 else 1
    match a.side with
    | some side =>
      match (witnessCases a.finalityHorizon).getLast? with
      | some c => measure c side
      | none => return 2
    | none =>
      let cbad ← runComparator
      let mut total := 0
      for c in witnessCases a.finalityHorizon ++ scenarioCases do
        total := total + (← runCase c)
      IO.println s!"MISMATCH total: {total}"
      return if total == 0 && cbad == 0 then 0 else 1

end Golden

def main (args : List String) : IO UInt32 := Golden.main args
