import Properties

/-!
# `naru_properties` — 有界検査の実行ファイル(IDEAL.md C73)

`lake exe naru_properties [--mode short|long]`。固定の設定(`short`、回帰の設定)か長い設定(`long`、回帰の外)で
用語「共通の run の記述」から run を生成し、各検査器の 4 区分の件数と負の検体の結果を決定的な行で標準出力に書く
(所要時間は標準エラー)。exit 0 ⇔ 違反 0 かつ負の検体がすべて捉えられた。検査ドライバは `lake exe naru_test properties`。
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--mode", "probe", h] =>
    -- 計測: `hreadBound` の期限を horizon に収める長い run を 1 本(報告の行はそのまま、所要時間は標準エラー)
    match h.toInt? with
    | some horizon =>
      let (lines, _) ← Properties.reportRun (Properties.deadlineSpec horizon)
      for l in lines do IO.println l
      return 0
    | none => IO.eprintln "usage: naru_properties --mode probe <horizon>"; return 2
  | ["--mode", "finality", h] =>
    match h.toNat? with
    | some horizon => Properties.finalityProbe horizon; return 0
    | none => IO.eprintln "usage: naru_properties --mode finality <horizon>"; return 2
  | _ =>
    let mode := match args with
      | ["--mode", m] => m
      | [] => "short"
      | _ => "?"
    let specs := match mode with
      | "short" => some Properties.shortSpecs
      | "long" => some Properties.longSpecs
      | _ => none
    match specs with
    | none =>
      IO.eprintln "usage: naru_properties [--mode short|long|probe <horizon>|finality <horizon>]"
      return 2
    | some specs =>
      let (lines, violations, allDetected) ← Properties.report mode specs
      for l in lines do IO.println l
      return if violations == 0 && allDetected then 0 else 1
