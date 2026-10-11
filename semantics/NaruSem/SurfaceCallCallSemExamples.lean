import NaruSem.SurfaceCallCallSem

/-! 呼出し葉の検体。任意の解釈・名前付き引数・修飾名・UFCS・ゼロ引数と意味不在。
手組AST/Coreの検体であり、現在のcompilerから実生成Leanへの接続の代用ではない。 -/
namespace NaruSem.Surf.Call
open Naru

def callSemTable : Table :=
  { resolve := fun p => if p = ["p"] ∨ p = ["M", "p"] then some "M.p"
      else if p = ["flag"] then some "M.flag" else if p = ["value"] then some "M.value"
      else if p = ["zero"] then some "M.zero" else none
    sig := fun k => if k = "M.p" then some (.spec [("x", .nat), ("y", .nat)])
      else if k = "M.flag" then some (.input [("b", .bool)] .bool)
      else if k = "M.value" then some (.fn [("b", .bool)] .bool)
      else if k = "M.zero" then some (.input [] .bool) else none }

def callSemNamed (a b : Nat) : Expr :=
  .call {} (.var {} ["M", "p"]) [.named "y" (.lit {} (.nat a)), .named "x" (.lit {} (.nat b))]
def callSemMixed (a b : Nat) : Expr :=
  .call {} (.var {} ["p"]) [.pos (.lit {} (.nat a)), .named "y" (.lit {} (.nat b))]
def callSemUfcs (a b : Nat) : Expr :=
  .method {} (.lit {} (.nat a)) "p" [.named "y" (.lit {} (.nat b))]
def callSemPairCore (a b : Nat) : Core.Expr := .call "M.p" [.lit (.nat a) .nat, .lit (.nat b) .nat]
def callSemBool (name : String) (b : Bool) : Expr :=
  .call {} (.var {} [name]) [.pos (.lit {} (.bool b))]
def callSemBoolCore (name : String) (b : Bool) : Core.Expr := .call name [.lit (.bool b) .bool]
def callSemBoolUfcs (b : Bool) : Expr := .method {} (.lit {} (.bool b)) "flag" []
def callSemZero : Expr := .call {} (.var {} ["zero"]) []

theorem call_sem_named_wt (a b : Nat) : wtS callSemTable SCtx.empty (callSemNamed a b) = some .prop := rfl
theorem call_sem_named_lower (a b : Nat) : lowerS callSemTable SCtx.empty (callSemNamed a b) = some (callSemPairCore b a) := rfl
theorem call_sem_mixed_wt (a b : Nat) : wtS callSemTable SCtx.empty (callSemMixed a b) = some .prop := rfl
theorem call_sem_mixed_lower (a b : Nat) : lowerS callSemTable SCtx.empty (callSemMixed a b) = some (callSemPairCore a b) := rfl
theorem call_sem_ufcs_wt (a b : Nat) : wtS callSemTable SCtx.empty (callSemUfcs a b) = some .prop := rfl
theorem call_sem_ufcs_lower (a b : Nat) : lowerS callSemTable SCtx.empty (callSemUfcs a b) = some (callSemPairCore a b) := rfl

theorem call_sem_named_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (a b : Nat) :
    SpecSemEquiv callSemTable Φ Ψ SCtx.empty (callSemNamed a b) (callSemPairCore b a) :=
  lowerS_call_equiv (call_sem_named_wt a b) (call_sem_named_lower a b) hΦ

theorem call_sem_mixed_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (a b : Nat) :
    SpecSemEquiv callSemTable Φ Ψ SCtx.empty (callSemMixed a b) (callSemPairCore a b) :=
  lowerS_call_equiv (call_sem_mixed_wt a b) (call_sem_mixed_lower a b) hΦ

theorem call_sem_ufcs_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (a b : Nat) :
    SpecSemEquiv callSemTable Φ Ψ SCtx.empty (callSemUfcs a b) (callSemPairCore a b) :=
  lowerS_ufcs_equiv rfl (call_sem_ufcs_wt a b) (call_sem_ufcs_lower a b) hΦ

theorem call_sem_input_wt (b : Bool) : wtS callSemTable SCtx.empty (callSemBool "flag" b) = some (.val .bool) := rfl
theorem call_sem_input_lower (b : Bool) : lowerS callSemTable SCtx.empty (callSemBool "flag" b) = some (callSemBoolCore "M.flag" b) := rfl
theorem call_sem_fn_wt (b : Bool) : wtS callSemTable SCtx.empty (callSemBool "value" b) = some (.val .bool) := rfl
theorem call_sem_fn_lower (b : Bool) : lowerS callSemTable SCtx.empty (callSemBool "value" b) = some (callSemBoolCore "M.value" b) := rfl
theorem call_sem_input_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (b : Bool) :
    SpecSemEquiv callSemTable Φ Ψ SCtx.empty (callSemBool "flag" b) (callSemBoolCore "M.flag" b) :=
  lowerS_call_equiv (call_sem_input_wt b) (call_sem_input_lower b) hΦ
theorem call_sem_fn_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (b : Bool) :
    SpecSemEquiv callSemTable Φ Ψ SCtx.empty (callSemBool "value" b) (callSemBoolCore "M.value" b) :=
  lowerS_call_equiv (call_sem_fn_wt b) (call_sem_fn_lower b) hΦ

theorem call_sem_bool_ufcs_wt (b : Bool) : wtS callSemTable SCtx.empty (callSemBoolUfcs b) = some (.val .bool) := rfl
theorem call_sem_bool_ufcs_lower (b : Bool) : lowerS callSemTable SCtx.empty (callSemBoolUfcs b) = some (callSemBoolCore "M.flag" b) := rfl
theorem call_sem_bool_ufcs_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (b : Bool) :
    SpecSemEquiv callSemTable Φ Ψ SCtx.empty (callSemBoolUfcs b) (callSemBoolCore "M.flag" b) :=
  lowerS_ufcs_equiv rfl (call_sem_bool_ufcs_wt b) (call_sem_bool_ufcs_lower b) hΦ

theorem call_sem_zero_wt : wtS callSemTable SCtx.empty callSemZero = some (.val .bool) := rfl
theorem call_sem_zero_lower : lowerS callSemTable SCtx.empty callSemZero = some (.call "M.zero" []) := rfl
theorem call_sem_zero_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) : SpecSemEquiv callSemTable Φ Ψ SCtx.empty callSemZero (.call "M.zero" []) :=
  lowerS_call_equiv call_sem_zero_wt call_sem_zero_lower hΦ

/-- spec解釈の存在を仮定せず、不在なら両側とも意味証人がない。 -/
theorem call_sem_missing (Φ : NaruSem.Call.FEnv) (a b : Nat) (P : Prop) :
    ¬ Sem callSemTable Φ (fun _ => none) SEnv.empty (callSemMixed a b) P := by
  intro h
  cases h with
  | callVal hg hr hd => simp [callSemTable] at hr; subst hr; simp [callSemTable, DeclSig.value?] at hd
  | callSpec hg hr hd hF => simp at hF

theorem call_sem_missing_core (Φ : NaruSem.Call.FEnv) (a b : Nat) (P : Prop) :
    ¬ NaruSem.Call.Sem callSemTable.Δ Φ (fun _ => none) SEnv.empty (callSemPairCore a b) P := by
  intro h
  cases h with
  | callVal hk => simp [NaruSem.Call.isValueKey, NaruSem.Call.valueSig?, Table.Δ,
      callSemTable, DeclSig.toSig, NaruSem.Call.Sig.value?] at hk
  | callSpec hk hF => simp at hF

/-- 任意の述語Fへ名前付き引数が正しい順序で届く、非空虚な意味証人。 -/
theorem call_sem_named_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (F : List Val → Prop) (hF : Ψ "M.p" = some F) (a b : Nat) :
    Sem callSemTable Φ Ψ SEnv.empty (callSemNamed a b) (F [.nat b, .nat a]) :=
  .callSpec rfl rfl rfl hF rfl rfl

theorem call_sem_bool_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (f : List Val → Option Val) (hf : Φ "M.flag" = some f) (b c : Bool)
    (hb : f [.bool b] = some (.bool c)) :
    Sem callSemTable Φ Ψ SEnv.empty (callSemBool "flag" b) (c = true) :=
  .callVal (ps := [("b", .bool)]) (t := .bool) rfl rfl rfl hf rfl rfl hb

theorem call_sem_zero_meaning (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (f : List Val → Option Val) (hf : Φ "M.zero" = some f) (b : Bool)
    (hb : f [] = some (.bool b)) : Sem callSemTable Φ Ψ SEnv.empty callSemZero (b = true) :=
  .callVal (ps := []) (t := .bool) rfl rfl rfl hf rfl rfl hb

theorem call_sem_shadow_reject :
    wtS callSemTable (SCtx.empty.ext "p" .prop) (callSemMixed 0 1) = none := rfl
theorem call_sem_ufcs_shadow_reject :
    wtS callSemTable (SCtx.empty.ext "p" .prop) (callSemUfcs 0 1) = none := rfl
theorem call_sem_bad_named_reject :
    wtS callSemTable SCtx.empty (.call {} (.var {} ["p"]) [.named "x" (.lit {} (.nat 0)), .named "x" (.lit {} (.nat 1))]) = none := rfl
theorem call_sem_bad_type_reject :
    wtS callSemTable SCtx.empty (.call {} (.var {} ["p"]) [.pos (.lit {} (.bool false)), .pos (.lit {} (.nat 1))]) = none := rfl

/-- 同型の引数交換は適格でも、同じ正しいSurfaceの意味を保存しない。 -/
theorem call_sem_wrong_wt : NaruSem.Call.wtS callSemTable.Δ SCtx.empty (callSemPairCore 0 1) = some .prop := rfl
theorem call_sem_wrong_not_lower : lowerS callSemTable SCtx.empty (callSemNamed 0 1) ≠ some (callSemPairCore 0 1) := by
  rw [call_sem_named_lower]
  intro h
  cases h

def callSemPredicate : NaruSem.Call.PEnv := fun _ => some (fun vs => vs = [.nat 1, .nat 0])

theorem call_sem_wrong_not_preserved :
    ¬ (∀ P, Sem callSemTable (fun _ => none) callSemPredicate SEnv.empty (callSemNamed 0 1) P ↔
      NaruSem.Call.Sem callSemTable.Δ (fun _ => none) callSemPredicate SEnv.empty (callSemPairCore 0 1) P) := by
  intro h
  have hs := call_sem_named_meaning (fun _ => none) callSemPredicate _ rfl 0 1
  have hw : NaruSem.Call.Sem callSemTable.Δ (fun _ => none) callSemPredicate SEnv.empty
      (callSemPairCore 0 1) ([Val.nat 0, .nat 1] = [.nat 1, .nat 0]) :=
    .callSpec (vs := [.nat 0, .nat 1]) (F := fun vs => vs = [.nat 1, .nat 0]) rfl rfl rfl
  have hu := NaruSem.Call.Sem_unique hw ((h _).mp hs)
  exact (by decide : ¬ ([Val.nat 0, .nat 1] = [.nat 1, .nat 0])) (hu.mpr rfl)

/-- 全ての値calleeがBoolを返す表に、署名を守る解釈が実在する。 -/
def callSemFalse : NaruSem.Call.FEnv := fun _ => some (fun _ => some (.bool false))
theorem call_sem_closed_respects : callSemFalse.Respects callSemTable.Δ := by
  intro k ps t hs
  by_cases hp : k = "M.p"
  · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, DeclSig.toSig,
      NaruSem.Call.Sig.value?] at hs
  · by_cases hf : k = "M.flag"
    · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, hf, DeclSig.toSig,
        NaruSem.Call.Sig.value?] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨fun _ => some (.bool false), rfl, fun _ _ => ⟨.bool false, rfl, rfl⟩⟩
    · by_cases hv : k = "M.value"
      · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, hf, hv, DeclSig.toSig,
          NaruSem.Call.Sig.value?] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨fun _ => some (.bool false), rfl, fun _ _ => ⟨.bool false, rfl, rfl⟩⟩
      · by_cases hz : k = "M.zero"
        · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, hf, hv, hz, DeclSig.toSig,
            NaruSem.Call.Sig.value?] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact ⟨fun _ => some (.bool false), rfl, fun _ _ => ⟨.bool false, rfl, rfl⟩⟩
        · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, hf, hv, hz] at hs

theorem call_sem_closed_positive :
    Sem callSemTable callSemFalse callSemPredicate SEnv.empty (callSemNamed 0 1) True ∧
      NaruSem.Call.Sem callSemTable.Δ callSemFalse callSemPredicate SEnv.empty (callSemPairCore 1 0) True := by
  have hs := call_sem_named_meaning callSemFalse callSemPredicate _ rfl 0 1
  change Sem callSemTable callSemFalse callSemPredicate SEnv.empty (callSemNamed 0 1)
    ([Val.nat 1, .nat 0] = [.nat 1, .nat 0]) at hs
  have hs' : Sem callSemTable callSemFalse callSemPredicate SEnv.empty (callSemNamed 0 1) True :=
    (propext (by simp : ([Val.nat 1, .nat 0] = [.nat 1, .nat 0]) ↔ True)) ▸ hs
  exact ⟨hs', (call_sem_named_arbitrary callSemFalse callSemPredicate call_sem_closed_respects 0 1).iff rfl True |>.mp hs'⟩

end NaruSem.Surf.Call
