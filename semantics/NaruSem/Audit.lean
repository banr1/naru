import Lean

/-!
# 公理監査(IDEAL.md C45)

`#audit_axioms c₁ c₂ …` は、各定数の依存閉包に現れる公理を `Lean.collectAxioms`(`#print axioms` と同じ)で集め、許容する Lean 標準の
論理公理以外に依存していれば **失敗**(ビルドが exit 非 0)し、定数が無ければ名前解決で失敗する。`lake build NaruSem` の中で
`NaruSem.lean`(ルート)が必須の定理・補題・接続証拠をすべて列挙して監査するので、証明の未完了(`sorryAx`)、`native_decide`
(`Lean.ofReduceBool`)、独自の未証明公理、必要な定理の欠落はビルドの失敗として現れる。

許容する公理(Lean 標準の論理公理。理由):
- `propext` — 命題外延性。`simp` / `funext` / `Iff` からの書き換えに使う。`Sem_unique` は量化の意味 `∀ a, F a` の一意性を
  `F = G` から導くので、束縛ごとの命題の等しさを関数の等しさに上げる(`funext` は `Quot.sound` に依る)。
- `Classical.choice` — `Sem_exists` が量化の意味を束縛ごとの意味の存在から関数 `F : carrier → Prop` として取り出すのに使う
  (`Classical.choose`)。`by_cases` / `Decidable` の古典的な補完にも現れうる。
- `Quot.sound` — 商の健全性。`funext` の基礎。

禁止する依存(0 件を要求): `sorryAx`(未完了の証明)、`native_decide` が持ち込む公理(Lean 4.34 では定理ごとの補助公理
`<名前>._native.native_decide.ax_*`。`Lean.ofReduceBool` / `Lean.ofReduceNat` / `Lean.trustCompiler` も同類: コンパイル済みコードの評価を信頼する)、
上記以外のすべての公理(独自の仮定・保存自体を仮定する公理)。`unsafe` な定義は定理の依存閉包に入れない(kernel が拒否する)。
-/

namespace NaruSem.Audit
open Lean Elab Command

/-- 許容する Lean 標準の論理公理。 -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- 1 つの定数の監査: (依存する公理の一覧, 許容しない公理の一覧)。 -/
def auditConst (n : Name) : CoreM (List Name × List Name) := do
  let axs ← collectAxioms n
  let bad := axs.toList.filter fun a => !allowedAxioms.contains a
  return (axs.toList, bad)

elab "#audit_axioms " ids:ident+ : command => do
  let mut failures : List String := []
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let (axs, bad) ← liftCoreM (auditConst n)
    if bad.isEmpty then
      logInfo m!"audit ok: {n} depends on axioms {axs} (all allowed)"
    else
      failures := failures ++ [s!"{n}: forbidden dependencies {bad} (all axioms: {axs})"]
  unless failures.isEmpty do
    throwError "axiom audit failed:\n{"\n".intercalate failures}"

end NaruSem.Audit
