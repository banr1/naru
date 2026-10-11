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

/-! ## match の局所合成: 命題と Bool のガード、外側の同名束縛 -/

private theorem lit_bridge (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (Γ : SCtx) (b : Bool) :
    SpecSemEquiv T Φ Ψ Γ (.lit {} (.bool b)) (.lit (.bool b) .bool) := by
  intro ρ _ P
  constructor <;> intro h <;> refine ⟨P, ?_, Iff.rfl⟩ <;> cases h <;> exact .lit

def matchSemCtx : SCtx := SCtx.ofList [("x", .val .bool), ("q", .prop)]
def matchSemArms : List Arm :=
  [.mk (.lit {} (.bool false)) none (.var {} ["x"]),
   .mk (.bind {} "q") (some letsSemPred) (.var {} ["q"]),
   .mk (.bind {} "x") (some (.lit {} (.bool false))) (.var {} ["x"]),
   .mk (.wild {}) none (.var {} ["x"])]
def matchSemCoreArms : List Core.Arm :=
  [.mk (.lit (.bool false)) none (.var "x"),
   .mk (.bind "q") (some (.call "M.p" [])) (.var "q"),
   .mk (.bind "x") (some (.lit (.bool false) .bool)) (.var "x"),
   .mk .wild none (.var "x")]
def matchSemSurface : Expr := .matchE {} letsSemFlag matchSemArms
def matchSemCore : Core.Expr := .match_ (.call "M.flag" []) .bool matchSemCoreArms

theorem match_sem_wt : wtS letsSemTable matchSemCtx matchSemSurface = some .prop := rfl
theorem match_sem_lower : lowerS letsSemTable matchSemCtx matchSemSurface = some matchSemCore := rfl

/-- 任意の関数/input と spec の解釈で、4腕の局所前提が成立する。
外側の命題 q はパターンの Bool 束縛に隠され、後続の腕へ漏れない。 -/
theorem match_sem_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SpecArmsBridge letsSemTable Φ Ψ matchSemCtx .bool matchSemArms matchSemCoreArms := by
  apply SpecArmsBridge.hit (by rfl) (by rfl)
  · exact var_bridge letsSemTable Φ Ψ _ "x"
  · apply SpecArmsBridge.guard (by rfl) (by rfl) (by rfl)
    · exact pred_bridge Φ Ψ _ (by decide)
    · exact var_bridge letsSemTable Φ Ψ _ "q"
    · apply SpecArmsBridge.guard (by rfl) (by rfl) (by rfl)
      · exact lit_bridge letsSemTable Φ Ψ _ false
      · exact var_bridge letsSemTable Φ Ψ _ "x"
      · apply SpecArmsBridge.hit (by rfl) (by rfl)
        · exact var_bridge letsSemTable Φ Ψ _ "x"
        · exact .nil

/-- input の任意の型に合う解釈で scrutinee を評価し、実 lowerS 出力へ合成。
spec 解釈の存在は仮定せず、存在しないガードに意味を補わない。 -/
theorem match_sem_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects letsSemTable.Δ) (ρ : SEnv) (hρ : matchSemCtx = ρ.ctx) (P : Prop) :
    Sem letsSemTable Φ Ψ ρ matchSemSurface P ↔
      NaruSem.Call.Sem letsSemTable.Δ Φ Ψ ρ matchSemCore P := by
  exact lowerS_match_sem_iff (by rfl) (by rfl) match_sem_lower
    (match_sem_bridge Φ Ψ) hΦ hρ P

def matchSemEnv (x : Bool) (Q : Prop) : SEnv := SEnv.ofList [("x", .val (.bool x)), ("q", .prop Q)]
def matchSemΦ (b : Bool) : NaruSem.Call.FEnv := fun k =>
  if k = "M.flag" then some (fun _ => some (.bool b)) else none

theorem match_sem_ctx (x : Bool) (Q : Prop) : matchSemCtx = (matchSemEnv x Q).ctx := by
  funext y
  simp [matchSemCtx, matchSemEnv, SCtx.ofList, SEnv.ofList, SEnv.ctx,
    SCtx.extList, SCtx.ext, SCtx.empty, SEnv.extList, SEnv.ext, SEnv.empty]
  split <;> simp_all [SVal.ty, Val.ty]

theorem match_sem_respects (b : Bool) : (matchSemΦ b).Respects letsSemTable.Δ := by
  intro k ps t hk
  by_cases h : k = "M.flag"
  · subst k
    simp [NaruSem.Call.valueSig?, Table.Δ, letsSemTable, DeclSig.toSig,
      NaruSem.Call.Sig.value?] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine ⟨fun _ => some (.bool b), rfl, ?_⟩
    intro vs _
    exact ⟨.bool b, rfl, rfl⟩
  · by_cases hp : k = "M.p" <;>
      simp [NaruSem.Call.valueSig?, Table.Δ, letsSemTable, h, hp,
        DeclSig.toSig, NaruSem.Call.Sig.value?] at hk

/-- false のリテラル腕が先に成功する。後続ガードの spec 解釈は不要。 -/
theorem match_sem_first_hit (x : Bool) (Q : Prop) (Ψ : NaruSem.Call.PEnv) :
    Sem letsSemTable (matchSemΦ false) Ψ (matchSemEnv x Q) matchSemSurface (x = true) ∧
      NaruSem.Call.Sem letsSemTable.Δ (matchSemΦ false) Ψ (matchSemEnv x Q) matchSemCore (x = true) := by
  have hs : Sem letsSemTable (matchSemΦ false) Ψ (matchSemEnv x Q) matchSemSurface (x = true) :=
    .matchHit (v := .bool false) (bs := []) rfl (by rfl) (.varVal (by rfl))
  exact ⟨hs, (match_sem_arbitrary _ _ (match_sem_respects false) _ (match_sem_ctx x Q) _).mp hs⟩

/-- true はリテラル腕を飛ばす。Prop ガードと Bool ガードを含む命題の意味を
任意の P と外側 x/Q で検査し、後続腕はパターンの q に捕捉されない。 -/
theorem match_sem_guards (x : Bool) (Q P : Prop) (Ψ : NaruSem.Call.PEnv)
    (hΨ : Ψ "M.p" = some (fun _ => P)) :
    let R := (P → true = true) ∧
      (¬ P → ((false = true → true = true) ∧ (¬ (false = true) → x = true)))
    Sem letsSemTable (matchSemΦ true) Ψ (matchSemEnv x Q) matchSemSurface R ∧
      NaruSem.Call.Sem letsSemTable.Δ (matchSemΦ true) Ψ (matchSemEnv x Q) matchSemCore R := by
  dsimp only
  have hs : Sem letsSemTable (matchSemΦ true) Ψ (matchSemEnv x Q) matchSemSurface
      ((P → true = true) ∧
        (¬ P → ((false = true → true = true) ∧ (¬ (false = true) → x = true)))) := by
    apply Sem.matchSkip (v := .bool true) rfl (by rfl)
    apply Sem.matchGuard (v := .bool true) (bs := [("q", .bool true)]) rfl (by rfl)
    · exact .callSpec (by rfl) rfl rfl hΨ rfl rfl
    · exact .varVal (by rfl)
    · apply Sem.matchGuard (v := .bool true) (bs := [("x", .bool true)]) rfl (by rfl)
      · exact .lit
      · exact .varVal (by rfl)
      · exact .matchHit (v := .bool true) (bs := []) rfl (by rfl) (.varVal (by rfl))
  exact ⟨hs, (match_sem_arbitrary _ _ (match_sem_respects true) _ (match_sem_ctx x Q) _).mp hs⟩

/-- false のガード二つの後で外側 x=false に戻る。外側 q=True は無関係。 -/
theorem match_sem_guard_false_restores_outer :
    Sem letsSemTable (matchSemΦ true) (fun _ => some (fun _ => False))
      (matchSemEnv false True) matchSemSurface False := by
  have h := (match_sem_guards false True False (fun _ => some (fun _ => False)) rfl).1
  have he : ((False → true = true) ∧
      (¬ False → ((false = true → true = true) ∧ (¬ (false = true) → false = true)))) = False := by
    apply propext
    simp
  exact Eq.mp (congrArg (Sem letsSemTable (matchSemΦ true) (fun _ => some (fun _ => False))
    (matchSemEnv false True) matchSemSurface) he) h

/-- 真の命題ガードではパターン q=true を読む。外側 x=false/q=False を読まない。 -/
theorem match_sem_guard_true_shadows_outer :
    Sem letsSemTable (matchSemΦ true) letsSemΨ (matchSemEnv false False) matchSemSurface True := by
  have h := (match_sem_guards false False True letsSemΨ rfl).1
  have he : ((True → true = true) ∧
      (¬ True → ((false = true → true = true) ∧ (¬ (false = true) → false = true)))) = True := by
    apply propext
    simp
  exact he ▸ h

/-- パターン照合後にガードの spec 解釈が不在なら意味の証人も不在。
ガードを False に置き換えてフォールバックを成功させない。 -/
theorem match_sem_missing_guard :
    ∀ P, ¬ Sem letsSemTable (matchSemΦ true) (fun _ => none)
      (matchSemEnv false False) matchSemSurface P := by
  intro P h
  cases h with
  | matchSkip hs hp hr =>
    have hv : eval letsSemTable (matchSemΦ true) (matchSemEnv false False) letsSemFlag = some (.bool true) := rfl
    have he := hs.symm.trans hv
    cases he
    cases hr with
    | matchSkip _ hp _ => simp [matchPat] at hp
    | matchGuard _ _ hg _ _ =>
      cases hg with
      | callVal _ hr hd _ _ _ _ =>
        simp [letsSemTable] at hr
        subst hr
        simp [letsSemTable, DeclSig.value?] at hd
      | callSpec _ _ _ hF _ _ => cases hF
  | matchHit hs hp _ =>
    have hv : eval letsSemTable (matchSemΦ true) (matchSemEnv false False) letsSemFlag = some (.bool true) := rfl
    have he := hs.symm.trans hv
    cases he
    simp [matchPat] at hp

def matchSemWrongCore : Core.Expr := .match_ (.call "M.flag" []) .bool
  [.mk (.lit (.bool false)) none (.var "x"),
   .mk (.bind "q") (some (.unop "!" (.call "M.p" []))) (.var "q"),
   .mk (.bind "x") (some (.lit (.bool false) .bool)) (.var "x"),
   .mk .wild none (.var "x")]

theorem match_sem_wrong_wt :
    NaruSem.Call.wtS letsSemTable.Δ matchSemCtx matchSemWrongCore = some .prop := rfl

/-- 同じ型でも Prop ガードの否定は命題を変える。正しい Surface は True。 -/
theorem match_sem_wrong_meaning :
    NaruSem.Call.Sem letsSemTable.Δ (matchSemΦ true) letsSemΨ
      (matchSemEnv false False) matchSemWrongCore False := by
  have h : NaruSem.Call.Sem letsSemTable.Δ (matchSemΦ true) letsSemΨ
      (matchSemEnv false False) matchSemWrongCore
      ((¬ True → true = true) ∧
        (¬ (¬ True) → ((false = true → true = true) ∧ (¬ (false = true) → false = true)))) := by
    apply NaruSem.Call.Sem.matchSkip (v := .bool true) rfl (by rfl)
    apply NaruSem.Call.Sem.matchGuard (v := .bool true) (bs := [("q", .bool true)]) rfl (by rfl)
    · exact .not (.callSpec (vs := []) (F := fun _ => True) rfl rfl rfl)
    · exact .varVal (by rfl)
    · apply NaruSem.Call.Sem.matchGuard (v := .bool true) (bs := [("x", .bool true)]) rfl (by rfl)
      · exact .lit
      · exact .varVal (by rfl)
      · exact .matchHit (v := .bool true) (bs := []) rfl (by rfl) (.varVal (by rfl))
  have he : ((¬ True → true = true) ∧
      (¬ (¬ True) → ((false = true → true = true) ∧ (¬ (false = true) → false = true)))) = False := by
    apply propext
    simp
  exact he ▸ h

theorem match_sem_wrong_not_preserved :
    ¬ (Sem letsSemTable (matchSemΦ true) letsSemΨ (matchSemEnv false False) matchSemSurface True ↔
      NaruSem.Call.Sem letsSemTable.Δ (matchSemΦ true) letsSemΨ
        (matchSemEnv false False) matchSemWrongCore True) := by
  intro h
  have hc := h.mp match_sem_guard_true_shadows_outer
  have he := NaruSem.Call.Sem_unique match_sem_wrong_meaning hc
  exact he.mpr True.intro

theorem match_sem_missing_guard_core :
    ∀ P, ¬ NaruSem.Call.Sem letsSemTable.Δ (matchSemΦ true) (fun _ => none)
      (matchSemEnv false False) matchSemCore P := by
  intro P h
  exact match_sem_missing_guard P
    ((match_sem_arbitrary _ _ (match_sem_respects true) _ (match_sem_ctx _ _) P).mpr h)

def matchSemNatArms : List Arm :=
  [.mk (.lit {} (.nat 0)) none (.lit {} (.bool false)),
   .mk (.wild {}) none (.lit {} (.bool true))]
def matchSemNatCoreArms : List Core.Arm :=
  [.mk (.lit (.nat 0)) none (.lit (.bool false) .bool),
   .mk .wild none (.lit (.bool true) .bool)]

theorem match_sem_nat_wt (n : Nat) :
    wtS letsSemTable SCtx.empty (.matchE {} (.lit {} (.nat n)) matchSemNatArms) = some (.val .bool) := rfl

theorem match_sem_nat_bridge (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SpecArmsBridge letsSemTable Φ Ψ SCtx.empty .nat matchSemNatArms matchSemNatCoreArms := by
  apply SpecArmsBridge.hit (by rfl) (by rfl) (lit_bridge _ _ _ _ false)
  exact .hit (by rfl) (by rfl) (lit_bridge _ _ _ _ true) .nil

/-- Nat の 0 リテラルと任意の後続値に対する局所保存。有限入力の列挙ではない。 -/
theorem match_sem_nat_arbitrary (n : Nat) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (P : Prop) :
    Sem letsSemTable Φ Ψ SEnv.empty (.matchE {} (.lit {} (.nat n)) matchSemNatArms) P ↔
      NaruSem.Call.Sem letsSemTable.Δ Φ Ψ SEnv.empty
        (.match_ (.lit (.nat n) .nat) .nat matchSemNatCoreArms) P := by
  exact (match_sem_nat_bridge Φ Ψ).sem_iff rfl rfl rfl rfl {} P

theorem match_sem_nat_successor (n : Nat) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    Sem letsSemTable Φ Ψ SEnv.empty (.matchE {} (.lit {} (.nat (n + 1))) matchSemNatArms) (true = true) := by
  exact .matchSkip rfl (by simp [matchPat]) (.matchHit rfl (by rfl) .lit)

/-- 空の腕列に意味を補わない。両側の不在も対応に含む。 -/
theorem match_sem_empty (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (ρ : SEnv) (s : Expr) (cs : Core.Expr) (ts : TyV) (P : Prop) :
    (¬ Sem T Φ Ψ ρ (.matchE {} s []) P) ∧
      (¬ NaruSem.Call.Sem T.Δ Φ Ψ ρ (.match_ cs ts []) P) := by
  constructor <;> intro h <;> cases h

end NaruSem.Surf.Call
