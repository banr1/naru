import Model

/-!
# 有界検査の共通部品(IDEAL.md C73)

生成 Model(`generated/Model`)の具体的な run の上で claim の前提・結論の有界版と証明の途中の中間命題を判定する「検査器」の土台:
決定的な擬似乱数、用語「共通の run の記述」(`RunSpec`)、記述から組み立てる `Setup` と scenario の `input` 束縛(環境のオラクル)、
時刻の補助。生成 Model と `NaruStd` だけを import する(mathlib なし。`Proofs` からは import されない)。

- run の記述は Setup・validator 数・honest 集合・byzantine の振る舞い・配送・awake・seed を 1 つにまとめたもので、手書き側(golden)と
  生成側(golden と有界検査)の run を同じ記述から組み立てるための形(C10 の比較器の検体 `Probe.DObj` と同じ考え方)。この周回は
  生成側だけを組み立てる(手書き側への写しは C10 の拡充の周回で足す)。
- 乱数は seed から決まる SplitMix64 で、同じ記述からは byte 単位で同じ run と報告が出る(`naru_test properties` が 2 回の実行を比べる)。
-/

namespace Properties
open Model.Consensus Model.Consensus.Objects Model.Consensus.Protocol Model.Consensus.Execution

/-! ## 決定的な擬似乱数(SplitMix64) -/

structure Rng where
  state : UInt64
deriving Repr

def Rng.ofSeed (seed : Nat) : Rng := ⟨UInt64.ofNat (seed * 0x9E3779B97F4A7C15 % 18446744073709551616 + 1)⟩

def Rng.next (g : Rng) : UInt64 × Rng :=
  let z := g.state + 0x9E3779B97F4A7C15
  let z1 := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB
  (z2 ^^^ (z2 >>> 31), ⟨z⟩)

/-- `[0, n)` の一様な自然数(`n = 0` なら 0)。 -/
def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  if n == 0 then (0, g) else
    let (x, g') := g.next
    (x.toNat % n, g')

/-- 確率 `num / den` で真。 -/
def Rng.chance (g : Rng) (num den : Nat) : Bool × Rng :=
  let (x, g') := g.below den
  (x < num, g')

/-- 列の決定的なシャッフル(Fisher–Yates)。 -/
def Rng.shuffle {α : Type} [Inhabited α] (g : Rng) (xs : List α) : List α × Rng := Id.run do
  let mut arr := xs.toArray
  let mut g := g
  let n := arr.size
  for i in [0:n] do
    let (j, g') := g.below (n - i)
    g := g'
    let a := n - 1 - i
    let b := j
    if a < arr.size && b < arr.size then
      let x := arr[a]!
      let y := arr[b]!
      arr := (arr.set! a y).set! b x
  return (arr.toList, g)

/-! ## 共通の run の記述 -/

/-- byzantine の振る舞い。byzantine なノードは tick せず(IDEAL.md「言語の意味論」: Byzantine は注入 object で表す)、
honest の出力から作った object を配送 event として注入する。 -/
inductive Byz where
  /-- 何もしない(投票・ブロック・attestation の差し控え)。 -/
  | silent
  /-- 投票の時刻に、honest の投票と同じ slot で head の違う 2 つの投票を出す(equivocation)。 -/
  | equivocate
  /-- equivocation の 2 票を honest ごとに違う順と遅れで配る(two-faced)。 -/
  | twoFaced
  /-- action の時刻に、honest の行を写して `confirmed` の違う 2 つの attestation を出す。 -/
  | conflictingAttest
deriving Repr, DecidableEq, BEq

/-- 提案者の予定。`roundRobin` は slot ごとに validator を巡回(byzantine が毎 round 1 回提案者になるので
`MultiProposerAt` の窓は無い)、`honestRounds` は byzantine を奇数 round の開始 slot だけに置く(偶数 round の opening で
`MultiProposerAt`、`MultiProposerRecurrence` の gap は 2)。 -/
inductive ProposerPattern where
  | roundRobin
  | honestRounds
  /-- byzantine は提案者にならない(毎 round の opening で `MultiProposerAt`、`MultiProposerRecurrence` の gap は 1)。 -/
  | honestOnly
deriving Repr, DecidableEq, BEq

structure RunSpec where
  name : String
  seed : Nat
  /-- validator の数(id は 0 … n − 1)。 -/
  validators : Nat
  /-- byzantine な validator の id。 -/
  byzantine : List Nat := []
  /-- validator ごとの重み(足りなければ 1)。 -/
  weights : List Nat := []
  delta : Int := 1
  gst : Int := 0
  horizon : Int
  r : Nat := 3
  etaSG : Nat := 2
  k : Nat := 4
  d : Nat := 2
  timeoutDelay : Nat := 6
  byz : Byz := .silent
  proposers : ProposerPattern := .honestRounds
  /-- honest の一部が GST 後も round ごとに眠る(awake の変化)。 -/
  sleepy : Bool := false
  /-- GST 前の配送の最大の追加遅れ(0 なら GST 前も Δ 以内)。 -/
  preGstDelay : Nat := 0
  /-- 負の検体: この honest ノードへは GST 後もブロックを配送しない(`PartialSynchrony` を壊す)。 -/
  dropBlocksTo : Option Nat := none
deriving Repr

def vid (n : Nat) : Identifiers.ValidatorId := ⟨n⟩

def RunSpec.allIds (sp : RunSpec) : List Nat := List.range sp.validators
def RunSpec.honestIds (sp : RunSpec) : List Nat := sp.allIds.filter fun v => !sp.byzantine.contains v
def RunSpec.honestSet (sp : RunSpec) : NaruStd.Set Identifiers.ValidatorId := NaruStd.Set.of (sp.honestIds.map vid)
def RunSpec.weightOf (sp : RunSpec) (v : Nat) : Nat := sp.weights.getD v 1

def tblOf {κ ν : Type} [Ord κ] (xs : List (κ × ν)) : NaruStd.Table κ ν :=
  xs.foldl (fun t e => t.insert e.1 e.2) NaruStd.Table.empty

def RunSpec.setup (sp : RunSpec) : Setup.Setup :=
  ⟨⟨sp.delta, sp.gst, ⟨tblOf (sp.allIds.map fun v => (vid v, sp.weightOf v))⟩⟩, ⟨sp.r, sp.etaSG⟩, ⟨sp.k, sp.d, sp.timeoutDelay⟩⟩

/-- scenario の `input` 束縛(環境のオラクル)。生成 Model の fn は先頭にこの 4 つの関数引数を取る(名前順 committee' / proposer' /
awake' / newRoot')。 -/
structure Inputs where
  committee : Nat → NaruStd.Set Identifiers.ValidatorId
  proposer : Nat → Identifiers.ValidatorId
  awake : Identifiers.ValidatorId → Nat → Bool
  newRoot : Identifiers.ValidatorId → Nat → Identifiers.BlockId

/-- 決定的な小さいハッシュ(awake の予定に使う)。 -/
def mix (a b c : Nat) : Nat :=
  let x := (a * 1000003 + b * 10007 + c * 101 + 7) % 4294967291
  (x * 2654435761) % 4294967291

def RunSpec.inputs (sp : RunSpec) : Inputs :=
  let honest := sp.honestIds
  let nHonest := honest.length
  let byz := sp.byzantine
  { committee := fun _ => NaruStd.Set.of (sp.allIds.map vid)
    proposer := fun slot =>
      match sp.proposers with
      | .roundRobin => vid (slot % sp.validators)
      | .honestRounds =>
        let round := slot / sp.r
        if byz.length > 0 && round % 2 == 1 && slot % sp.r == 0 then vid (byz.getD 0 0)
        else vid (honest.getD (slot % (max nHonest 1)) 0)
      | .honestOnly => vid (honest.getD (slot % (max nHonest 1)) 0)
    awake := fun v round =>
      if sp.sleepy && round ≥ 1 && !byz.contains v.value then mix sp.seed v.value round % 3 != 0 else true
    newRoot := fun v slot => ⟨slot * 8 + v.value + 1⟩ }

/-! ## 時刻の補助(生成 Model の関数の短い名前) -/

def proposalTime (s : Setup.Setup) (k : Nat) : Int := Schedule.proposalTime s.e k
def voteTime (s : Setup.Setup) (k : Nat) : Int := Schedule.voteTime s.e k
def confirmationTime (s : Setup.Setup) (k : Nat) : Int := Schedule.confirmationTime s.e k
def actionTime (s : Setup.Setup) (r : Nat) : Int := Setup.setupActionTime s r
def openingSlot (s : Setup.Setup) (r : Nat) : Nat := Grades.openingSlot s.hc r
def period (s : Setup.Setup) : Int := Model.Consensus.Spec.Constants.period s
/-- 時刻 `t` 以下の最後の slot(`t < 0` なら 0)。 -/
def slotOfTime (s : Setup.Setup) (t : Int) : Nat := Parameters.slotOf s.e t
/-- run の中に現れうる slot の上限(horizon の slot + 1)。有界版の `forall k: Slot` はこの範囲で判定する。 -/
def maxSlot (s : Setup.Setup) (horizon : Int) : Nat := slotOfTime s horizon + 1

/-- `PublicTime(e, t)`: `t = k · Δ`(k は自然数)。 -/
def publicTime (s : Setup.Setup) (t : Int) : Bool := 0 ≤ t && t % s.e.delta == 0

/-- `[lo, hi]` の整数の列。 -/
def intRange (lo hi : Int) : List Int :=
  if hi < lo then [] else (List.range (hi - lo).toNat.succ).map fun (i : Nat) => lo + (i : Int)

end Properties
