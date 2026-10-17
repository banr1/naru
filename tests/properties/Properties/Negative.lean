import Properties.Checkers

/-!
# 負の検体(IDEAL.md C73): 検査器が違反を報告し、前提の判定器が前提の破れを捉えることの確認

検査器ごとに「違反を報告すべき検体」を置く: 読みを意図的に壊した値(FG root / 出力の読みの差し替え)、しきい値を超える byzantine、
GST 後の配送の差し控え、整列や tick の欠けた event 列。各検体は `detected`(期待どおり捉えた)か `NOT detected` を報告し、
`naru_test properties` が名前ごとに `detected` を要求する。
-/

namespace Properties
open Model.Consensus Model.Consensus.Objects Model.Consensus.Protocol Model.Consensus.Execution

/-- event の列を生成 Model でもう一度畳み込んで時間軸にする(生成器を通さない run の読み。検体の加工と、生成器の畳み込みとの一致の確認に使う)。 -/
def replay (sp : RunSpec) (events : List Event) : Timeline := Id.run do
  let S := sp.setup
  let I := sp.inputs
  let mut w : World := Run.worldInit
  let mut worlds : Array World := #[w]
  let mut emitted : Array (List Obj) := #[]
  for ev in events do
    match ev with
    | Run.NamedEvent.Tick v t =>
      let (n', out) := tickNode I S v (Timeline.nodeIn w v) t
      w := w.insert v n'
      emitted := emitted.push out
    | Run.NamedEvent.Deliver v o _ =>
      w := w.insert v (processNode I S (Timeline.nodeIn w v) o)
      emitted := emitted.push []
    worlds := worlds.push w
  return { spec := sp, setup := S, inputs := I, rho := ⟨sp.honestSet, sp.horizon, events⟩, events := events.toArray,
           worlds := worlds, emitted := emitted, injected := 0, dropped := 0, postponed := 0 }

/-- 検体の土台: 3 validator、byzantine なし、GST 0。 -/
def baseSpec : RunSpec := { name := "negative-base", seed := 11, validators := 3, horizon := 40 }

/-- 名前と結果(捉えたか)。 -/
structure Negative where
  name : String
  detected : Bool
  detail : String

def Negative.render (n : Negative) : String :=
  s!"negative {n.name}: {if n.detected then "detected" else "NOT detected"} ({n.detail})"

/-- head の祖先にならないブロック(root 999 の genesis の子)。 -/
def strayBlock : Blocks.Block := .Node .Genesis 1 ⟨999⟩ [] [] [] (vid 0)

def negatives : List Negative := Id.run do
  let mut out : List Negative := []
  -- 1. hreadBound(強い形): FG root の読みを壊す。違反の時刻は期限 a(D) より前だが、run は golden の一致の一覧に無いので
  --    「期限の前の正常な挙動」に分けず違反として数える
  let tl := generate baseSpec
  let p := Premises.of tl
  let v1 := hreadBound tl p (readFg := fun _ _ => strayBlock)
  out := out ++ [⟨"hreadBound(corrupted fg-root read)", v1.violations > 0 && v1.judged == 0 && v1.classified == 0,
                  s!"judged {v1.judged} violations {v1.violations} classified {v1.classified}; premises {p.render}"⟩]
  -- 1b. 分類の経路(対照): 同じ壊れた読みで、run が golden で一致したと仮定すると、期限の前の違反は「期限の前の正常な挙動」に分かれ、
  --     違反に数えない
  let v1c := hreadBound tl p (readFg := fun _ _ => strayBlock) (agreed := [baseSpec.name])
  out := out ++ [⟨"hreadBound(control: pre-deadline classification with golden agreement)", v1c.classified > 0 && v1c.violations == 0,
                  s!"classified {v1c.classified} violations {v1c.violations}"⟩]
  -- 1c. a(D) 以後の読みに破れがある義務は、golden で一致しても分類しない(期限を 0 round に置く。a(0) より前に閉じる義務だけが分類に残る)
  let v1d := hreadBound tl p (readFg := fun _ _ => strayBlock) (deadlineRounds := some 0) (agreed := [baseSpec.name])
  out := out ++ [⟨"hreadBound(strong-form violation at or after the deadline is not classified)",
                  v1d.violations > 0 && v1d.violations + v1d.classified == v1.violations && v1d.classified < v1c.classified,
                  s!"violations {v1d.violations} classified {v1d.classified}"⟩]
  -- 1e. 提案の親だけを壊す(投票の義務は本物のまま): 提案の義務の経路が違反を報告し、投票の義務は判定に残る
  let v1p := hreadBound tl p (parentOf := fun _ => strayBlock)
  out := out ++ [⟨"hreadBound(corrupted proposal parent)", v1p.violations > 0 && v1p.judged > 0 && v1p.classified == 0,
                  s!"judged {v1p.judged} violations {v1p.violations}"⟩]
  -- 1d. 本物の読みは強い形で判定の経路を通り、違反しない(対照)
  let v1e := hreadBound tl p
  out := out ++ [⟨"hreadBound(control: genuine read, strong form)", v1e.judged > 0 && v1e.violations == 0,
                  s!"judged {v1e.judged} violations {v1e.violations}"⟩]
  -- 2. includedFrom(confirmed / stable): 出力の読みを genesis に壊す
  let v2 := includedFrom tl p .Confirmed (Spec.Constants.confirmationDelay tl.setup) (readOut := fun _ _ _ => .Genesis)
  out := out ++ [⟨"includedFrom(confirmed)(corrupted output read)", v2.violations > 0 && v2.judged == 0,
                  s!"judged {v2.judged} violations {v2.violations}"⟩]
  let tlS := generate { baseSpec with name := "negative-base-long", horizon := 96 }
  let pS := Premises.of tlS
  let v2s := includedFrom tlS pS .Stable (Spec.Constants.stableInclusionDelay tlS.setup) (readOut := fun _ _ _ => .Genesis)
  out := out ++ [⟨"includedFrom(stable)(corrupted output read)", v2s.violations > 0 && v2s.judged == 0,
                  s!"judged {v2s.judged} violations {v2s.violations}"⟩]
  -- 3. しきい値を超える byzantine(3 人中 2 人): BelowOneThird が破れ、判定ではなく前提不成立に数える
  let tl3 := generate { baseSpec with name := "negative-two-thirds-byzantine", byzantine := [1, 2], byz := .equivocate }
  let p3 := Premises.of tl3
  let v3 := includedFrom tl3 p3 .Confirmed (Spec.Constants.confirmationDelay tl3.setup)
  let v3h := hreadBound tl3 p3 (deadlineRounds := some 0)
  out := out ++ [⟨"byzantine beyond one third", !p3.belowOneThird.holds && v3.judged == 0 && v3.unmet > 0 && v3h.judged == 0 && v3h.unmet > 0,
                  s!"{p3.belowOneThird.render}; includedFrom judged {v3.judged} unmet {v3.unmet}; hreadBound judged {v3h.judged} unmet {v3h.unmet}"⟩]
  -- 4. GST 後の配送の差し控え(ノード 1 へブロックを配らない): PartialSynchrony が破れる
  let tl4 := generate { baseSpec with name := "negative-withheld-blocks", dropBlocksTo := some 1 }
  let p4 := Premises.of tl4
  let v4 := includedFrom tl4 p4 .Confirmed (Spec.Constants.confirmationDelay tl4.setup)
  out := out ++ [⟨"withheld block delivery after GST", !p4.partialSync.holds && v4.judged == 0 && v4.unmet > 0,
                  s!"{p4.partialSync.render}; includedFrom judged {v4.judged} unmet {v4.unmet}"⟩]
  -- 5. 整列の崩れ: 先頭の event(時刻 0 の tick)を末尾に移す
  let evs := tl.events.toList
  let swapped := match evs with
    | a :: rest => rest ++ [a]
    | _ => evs
  let tl5 := replay baseSpec swapped
  out := out ++ [⟨"unsorted events", !tl5.scheduleWellFormed.holds, tl5.scheduleWellFormed.render⟩]
  -- 6. tick の欠け: 最初の tick を落とす
  let tl6 := replay baseSpec (evs.drop 1)
  out := out ++ [⟨"missing honest tick", !tl6.scheduleWellFormed.holds, tl6.scheduleWellFormed.render⟩]
  -- 7. 生成器の畳み込みと event 列の再畳み込みが同じ世界を与える(生成の自己整合。生成 Model の `stateBefore` と同じ値)
  let tl7 := replay baseSpec evs
  let same := tl7.worlds.size == tl.worlds.size && (List.range tl.worlds.size).all fun i =>
    tl.rho.honest.elems.all fun v => (Timeline.nodeIn tl.worlds[i]! v).st == (Timeline.nodeIn tl7.worlds[i]! v).st
  out := out ++ [⟨"replay agrees with generation", same, s!"{tl.worlds.size} worlds"⟩]
  return out

end Properties
