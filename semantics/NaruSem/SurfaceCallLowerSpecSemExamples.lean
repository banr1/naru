import NaruSem.SurfaceCallLowerSpecSem

/-! 局所証明書の非空虚な検体。input と spec の任意解釈、および閉じた正負対照。 -/
namespace NaruSem.Surf.Call
open Naru

def letsSemTable : Table :=
  { resolve := fun p => if p = ["flag"] then some "M.flag" else if p = ["p"] then some "M.p" else none
    sig := fun k => if k = "M.flag" then some (.input [] .bool)
      else if k = "M.p" then some (.spec []) else none }

def letsSemFlag : Expr := .call {} (.var {} ["flag"]) []
def letsSemPred : Expr := .call {} (.var {} ["p"]) []
def letsSemStmts : List Stmt :=
  [.letS {} "q" none letsSemFlag, .letS {} "q" none letsSemPred]
def letsSemSurface : Expr := .block {} letsSemStmts (some (.var {} ["q"]))
def letsSemCore : Core.Expr :=
  .let_ "q" .bool (.call "M.flag" []) (.let_ "q" .bool (.call "M.p" []) (.var "q"))

theorem lets_sem_wt : wtS letsSemTable SCtx.empty letsSemSurface = some .prop := rfl
theorem lets_sem_lower : lowerS letsSemTable SCtx.empty letsSemSurface = some letsSemCore := rfl

private theorem var_bridge (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (Γ : SCtx) (x : String) : SpecSemEquiv T Φ Ψ Γ (.var {} [x]) (.var x) := by
  intro ρ _ P
  constructor
  · intro hs
    refine ⟨P, ?_, Iff.rfl⟩
    cases hs with
    | varVal h => exact .varVal h
    | varProp h => exact .varProp h
  · intro hc
    refine ⟨P, ?_, Iff.rfl⟩
    cases hc with
    | varVal h => exact .varVal h
    | varProp h => exact .varProp h

private theorem pred_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (Γ : SCtx) (hp : Γ "p" = none) :
    SpecSemEquiv letsSemTable Φ Ψ Γ letsSemPred (.call "M.p" []) := by
  intro ρ hΓ P
  have hρ : ρ "p" = none := by
    have hh : ρ.ctx "p" = none := by rw [← hΓ]; exact hp
    cases hhρ : ρ "p" <;> simp_all [SEnv.ctx]
  constructor
  · intro hs
    refine ⟨P, ?_, Iff.rfl⟩
    cases hs with
    | callVal hs hr hd hf ha harr hv =>
      simp [letsSemTable] at hr
      subst hr
      simp [letsSemTable, DeclSig.value?] at hd
    | callSpec hs hr hd hF ha harr =>
      simp [letsSemTable] at hr
      subst hr
      simp [letsSemTable] at hd
      subst hd
      simp [evalArgs] at ha
      subst ha
      change some [] = some _ at harr
      simp only [Option.some.injEq] at harr
      subst harr
      exact .callSpec rfl hF rfl
  · intro hc
    refine ⟨P, ?_, Iff.rfl⟩
    cases hc with
    | callVal hk hf ha hv =>
      simp [NaruSem.Call.isValueKey, NaruSem.Call.valueSig?, Table.Δ,
        letsSemTable, DeclSig.toSig, NaruSem.Call.Sig.value?] at hk
    | callSpec hk hF ha =>
      simp [NaruSem.Call.evalArgs] at ha
      subst ha
      exact .callSpec (by simp [headBound, hρ]) rfl rfl hF rfl rfl

/-- 実 AST で命題の子式と末尾の対応を充足。input の子式は runtime 保存で処理する。 -/
theorem lets_sem_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SpecLetsBridge letsSemTable Φ Ψ SCtx.empty letsSemStmts
      [("q", .bool, .call "M.flag" []), ("q", .bool, .call "M.p" [])]
      (.var {} ["q"]) (.var "q") := by
  apply SpecLetsBridge.value (t := .bool) (by rfl) (by rfl) (by rfl)
  apply SpecLetsBridge.prop (by rfl) (by rfl) (by rfl)
  · exact pred_bridge Φ Ψ _ (by decide)
  · exact .nil (var_bridge letsSemTable Φ Ψ _ "q")

/-- 任意の署名を守る input 解釈、任意 spec 解釈で、同名 shadowing の意味を保存。 -/
theorem lets_sem_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects letsSemTable.Δ) (P : Prop) :
    Sem letsSemTable Φ Ψ SEnv.empty letsSemSurface P ↔
      NaruSem.Call.Sem letsSemTable.Δ Φ Ψ SEnv.empty letsSemCore P := by
  exact lowerS_block_sem_iff (by rfl) (by rfl) (by rfl) lets_sem_lower
    (lets_sem_bridge Φ Ψ) hΦ rfl P

/-- 命題解釈の存在を明示した、input 結果に依らない意味の存在。 -/
theorem lets_sem_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects letsSemTable.Δ) (F : List Val → Prop) (hF : Ψ "M.p" = some F) :
    Sem letsSemTable Φ Ψ SEnv.empty letsSemSurface (F []) ∧
      NaruSem.Call.Sem letsSemTable.Δ Φ Ψ SEnv.empty letsSemCore (F []) := by
  obtain ⟨w, hv, ht⟩ := eval_total (T := letsSemTable) (Γ := SCtx.empty)
    (e := letsSemFlag) (t := .bool) rfl Φ SEnv.empty rfl hΦ
  have hs : Sem letsSemTable Φ Ψ SEnv.empty letsSemSurface (F []) := by
    apply Sem.blockLetVal (w := w) rfl hv
    apply Sem.blockLetProp (P := F []) (by cases w <;> rfl)
    · exact .callSpec (by cases w <;> rfl) rfl rfl hF rfl rfl
    · exact .blockTail (.varProp (by rfl))
  exact ⟨hs, (lets_sem_arbitrary Φ Ψ hΦ _).mp hs⟩

def letsSemΦ : NaruSem.Call.FEnv := fun k =>
  if k = "M.flag" then some (fun _ => some (.bool false)) else none
def letsSemΨ : NaruSem.Call.PEnv := fun k =>
  if k = "M.p" then some (fun _ => True) else none

theorem lets_sem_closed_respects : letsSemΦ.Respects letsSemTable.Δ := by
  intro k ps t hk
  by_cases h : k = "M.flag"
  · subst k
    simp [NaruSem.Call.valueSig?, Table.Δ, letsSemTable, DeclSig.toSig,
      NaruSem.Call.Sig.value?] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine ⟨fun _ => some (.bool false), rfl, ?_⟩
    intro vs _
    exact ⟨.bool false, rfl, rfl⟩
  · by_cases hp : k = "M.p" <;>
      simp [NaruSem.Call.valueSig?, Table.Δ, letsSemTable, h, hp,
        DeclSig.toSig, NaruSem.Call.Sig.value?] at hk

theorem lets_sem_closed_positive :
    Sem letsSemTable letsSemΦ letsSemΨ SEnv.empty letsSemSurface True ∧
      NaruSem.Call.Sem letsSemTable.Δ letsSemΦ letsSemΨ SEnv.empty letsSemCore True := by
  exact lets_sem_meaning letsSemΦ letsSemΨ lets_sem_closed_respects (fun _ => True) rfl

/-- 命題の子式を否定した Core。同じ型で適格でも意味保存にならない。 -/
def letsSemWrongCore : Core.Expr :=
  .let_ "q" .bool (.call "M.flag" [])
    (.let_ "q" .bool (.unop "!" (.call "M.p" [])) (.var "q"))

theorem lets_sem_wrong_wt :
    NaruSem.Call.wtS letsSemTable.Δ SCtx.empty letsSemWrongCore = some .prop := rfl

theorem lets_sem_wrong_meaning :
    NaruSem.Call.Sem letsSemTable.Δ letsSemΦ letsSemΨ SEnv.empty letsSemWrongCore (¬ True) := by
  apply NaruSem.Call.Sem.letBoolVal (w := false) rfl rfl
  apply NaruSem.Call.Sem.letProp (P := ¬ True) rfl
  · exact .not (.callSpec (vs := []) (F := fun _ => True) rfl rfl rfl)
  · exact .varProp (by rfl)

theorem lets_sem_wrong_not_true :
    ¬ NaruSem.Call.Sem letsSemTable.Δ letsSemΦ letsSemΨ SEnv.empty letsSemWrongCore True := by
  intro h
  have he := NaruSem.Call.Sem_unique lets_sem_wrong_meaning h
  exact (he.mpr True.intro) True.intro

theorem lets_sem_wrong_not_preserved :
    ¬ (Sem letsSemTable letsSemΦ letsSemΨ SEnv.empty letsSemSurface True ↔
      NaruSem.Call.Sem letsSemTable.Δ letsSemΦ letsSemΨ SEnv.empty letsSemWrongCore True) := by
  intro h
  exact lets_sem_wrong_not_true (h.mp lets_sem_closed_positive.1)

end NaruSem.Surf.Call
