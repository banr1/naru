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
  -- 3. しきい値を超える byzantine(3 人中 2 人): BelowOneThird(hreadBound の前提)と WindowMajority(includedFrom の前提 SleepyRegime)が
  --    破れ、判定ではなく前提不成立に数える
  let tl3 := generate { baseSpec with name := "negative-two-thirds-byzantine", byzantine := [1, 2], byz := .equivocate }
  let p3 := Premises.of tl3
  let v3 := includedFrom tl3 p3 .Confirmed (Spec.Constants.confirmationDelay tl3.setup)
  let v3h := hreadBound tl3 p3 (deadlineRounds := some 0)
  out := out ++ [⟨"byzantine beyond one third", !p3.belowOneThird.holds && !p3.windows.holds && v3.judged == 0 && v3.unmet > 0 && v3h.judged == 0 && v3h.unmet > 0,
                  s!"{p3.belowOneThird.render} {p3.windows.render}; includedFrom judged {v3.judged} unmet {v3.unmet}; hreadBound judged {v3h.judged} unmet {v3h.unmet}"⟩]
  -- 3b. honest が round 1 以後すべて眠る(horizon 40 + lag 12 までの窓 [t − 24, t) が t >= 42 で全員眠る): SleepyRegime の窓の欄(WindowMajority)が破れ、includedFrom は前提不成立に数える
  let tl3w := generate { baseSpec with name := "negative-asleep", asleepFromRound := some 1 }
  let p3w := Premises.of tl3w
  let v3w := includedFrom tl3w p3w .Confirmed (Spec.Constants.confirmationDelay tl3w.setup)
  out := out ++ [⟨"WindowMajority broken (honest asleep)", !p3w.windows.holds && v3w.judged == 0 && v3w.unmet > 0,
                  s!"{p3w.windows.render}; includedFrom judged {v3w.judged} unmet {v3w.unmet}"⟩]
  -- 3c. SlashableBound: validator 0 の同じ高さで target の違う 2 行(E2)を運ぶ 2 つのブロック。重み 1 は 2q − W = 1 に届くので
  --     slashable な証拠があり、判定器が捉える。本物の run(対照)は成り立つ
  let row (target : Nat) : Blocks.CombinedAttestation := ⟨vid 0, 1, none, .Target 1 ⟨target⟩, none⟩
  let blockWith (r : Nat) : Blocks.Block := .Node .Genesis 1 ⟨r⟩ [] [] [row r] (vid 0)
  let js := slashableBoundOn tl.setup [blockWith 501, blockWith 502]
  out := out ++ [⟨"SlashableBound(conflicting height targets)", !js.holds && p.slashable.holds,
                  s!"{js.render}; control on the genuine run: {p.slashable.render}"⟩]
  -- 3d. RecoveredBy の回復の枝: tGST > 0 の run では genesis の枝(t = 0)が SleepyRegime の tGST <= t0 と両立せず、回復の枝は
  --     recoveryEnd(tGST, 0) が horizon を越えるのでどの証人でも成り立たない(証人なしで退ける)。証人を与えた経路は source の
  --     horizon が prefixEnd に届かないことで退ける
  let evs0 := tl.events.toList
  let tlG := generate { baseSpec with name := "negative-gst", gst := 6, preGstDelay := 2 }
  let pG := Premises.of tlG
  let lower := Spec.Constants.recoveryEnd tlG.setup tlG.setup.e.tGST 0
  let rNo := tlG.recoveredBy pG.slashable lower none
  let rW := tlG.recoveredBy pG.slashable lower (some ⟨tlG, tlG.setup.e.tGST, 1⟩)
  let vG := includedFrom tlG pG .Confirmed (Spec.Constants.confirmationDelay tlG.setup)
  -- 3e. AgreesUntil(source, rho, cut)(Continues の前半。証人の経路は固定設定では horizon の項で止まるので単体で確かめる): 同じ run どうしは
  --     成り立ち、honest の最初の tick を落とした source とは cut がその後なら成り立たず、rho の honest が source の honest に含まれないと成り立たない
  let cut : Int := 20
  let dropped := replay baseSpec (evs0.drop 1)
  let fewer : Timeline := { tl with rho := ⟨NaruStd.Set.of [vid 0], tl.rho.horizon, tl.rho.events⟩ }
  let a1 := Timeline.agreesUntil tl tl cut
  let a2 := Timeline.agreesUntil dropped tl cut
  let a3 := Timeline.agreesUntil fewer tl cut
  out := out ++ [⟨"AgreesUntil(prefix agreement of the recovered branch)", a1 && !a2 && !a3,
                  s!"same run {a1}; source without the first honest tick {a2}; rho.honest not within source.honest {a3}"⟩]
  -- 3f. 証人の source は同じ記述(名前と horizon を除く)の run でなければならない: 別の seed の run を source にすると最初の項で退ける
  let other := generate { baseSpec with name := "negative-gst-other", seed := 99, gst := 6, preGstDelay := 2 }
  let rO := tlG.recoveredBy pG.slashable lower (some ⟨other, tlG.setup.e.tGST, 1⟩)
  out := out ++ [⟨"RecoveredBy(source of another run description)", !rO.holds && (rO.reason.splitOn "same setup and inputs").length > 1, rO.render⟩]
  out := out ++ [⟨"RecoveredBy(recovered branch out of reach)", !rNo.holds && !rW.holds && (tlG.recoveredBy pG.slashable 0 none).holds
                    && vG.judged == 0 && vG.unmet > 0,
                  s!"without a witness: {rNo.render}; with the run itself as the source: {rW.render}; includedFrom judged {vG.judged} unmet {vG.unmet}"⟩]
  -- 4. GST 後の配送の差し控え(ノード 1 へブロックを配らない): PartialSynchrony が破れる
  let tl4 := generate { baseSpec with name := "negative-withheld-blocks", dropBlocksTo := some 1 }
  let p4 := Premises.of tl4
  let v4 := includedFrom tl4 p4 .Confirmed (Spec.Constants.confirmationDelay tl4.setup)
  out := out ++ [⟨"withheld block delivery after GST", !p4.partialSync.holds && v4.judged == 0 && v4.unmet > 0,
                  s!"{p4.partialSync.render}; includedFrom judged {v4.judged} unmet {v4.unmet}"⟩]
  -- 5. 整列の崩れ: 先頭の event(時刻 0 の tick)を末尾に移す
  let evs := evs0
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
