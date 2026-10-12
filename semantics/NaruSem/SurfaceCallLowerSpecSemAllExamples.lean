import NaruSem.SurfaceCallLowerSpecSemAll
import NaruSem.SurfaceCallCallSemExamples

/-! 全 spec 式の一般双方向同値の検体。命題の let・Nat の量化・呼出しの scrutinee・ガード付き match・
名前付き引数の spec 呼出し・UFCS の input 呼出し・否定・命題等値・論理演算を 1 つの式に重ね、
子式の対応を一切仮定せずに一般定理だけで Surface と Core の意味を双方向に結ぶ。
任意の署名を守る解釈での同値、非空虚な意味証人、Nat に評価されないこと、実生成 Lean の読みへの合成、
同型の誤 Core の非保存を kernel 検査する。手組 AST / Core の検体であり、現在の compiler から
実生成 Lean への接続の代用ではない。 -/
namespace NaruSem.Surf.Call
open Naru

/-- Nat の型注釈。 -/
def allSemNatTy : Ty := .named {} ["Nat"] []

/-- `{ let q = forall n: Nat { n + a >= a };
      match value(true) { true if q => q && p(y = a, x = 0), _ => !(false.flag() == q) } }` -/
def allSemExpr (a : Nat) : Expr :=
  .block {} [.letS {} "q" none (.quant {} .forall_ [{ name := "n", ty := some allSemNatTy, span := {} }]
      (.binop {} ">=" (.binop {} "+" (.var {} ["n"]) (.lit {} (.nat a))) (.lit {} (.nat a))))]
    (some (.matchE {} (.call {} (.var {} ["value"]) [.pos (.lit {} (.bool true))])
      [ .mk (.lit {} (.bool true)) (some (.var {} ["q"]))
          (.binop {} "&&" (.var {} ["q"])
            (.call {} (.var {} ["p"]) [.named "y" (.lit {} (.nat a)), .named "x" (.lit {} (.nat 0))])),
        .mk (.wild {}) none
          (.unop {} "!" (.binop {} "==" (.method {} (.lit {} (.bool false)) "flag" []) (.var {} ["q"])) ) ]))

/-- 独立 lowering の実出力(名前付き引数は仮引数順、UFCS の受け手は先頭、命題の let は注釈 `.bool`)。 -/
def allSemCore (a : Nat) : Core.Expr :=
  .let_ "q" .bool
    (.quant .forall_ [("n", .nat)]
      (.binop ">=" (.binop "+" (.var "n") (.lit (.nat a) .nat) .nat) (.lit (.nat a) .nat) .nat))
    (.match_ (.call "M.value" [.lit (.bool true) .bool]) .bool
      [ .mk (.lit (.bool true)) (some (.var "q"))
          (.binop "&&" (.var "q") (.call "M.p" [.lit (.nat 0) .nat, .lit (.nat a) .nat]) .bool),
        .mk .wild none
          (.unop "!" (.binop "==" (.call "M.flag" [.lit (.bool false) .bool]) (.var "q") .bool)) ])

theorem all_sem_wt (a : Nat) : wtS callSemTable SCtx.empty (allSemExpr a) = some .prop := rfl
theorem all_sem_lower (a : Nat) : lowerS callSemTable SCtx.empty (allSemExpr a) = some (allSemCore a) := rfl
theorem all_sem_ctyped (a : Nat) : NaruSem.Call.wtS callSemTable.Δ SCtx.empty (allSemCore a) = some .prop :=
  lowerS_wt (all_sem_wt a) (all_sem_lower a)

/-- 子式の対応を仮定せず、一般定理だけから合成式の双方向対応を得る。 -/
theorem all_sem_arbitrary (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (a : Nat) :
    SpecSemEquiv callSemTable Φ Ψ SCtx.empty (allSemExpr a) (allSemCore a) :=
  lowerS_equiv (all_sem_wt a) (all_sem_lower a) hΦ

theorem all_sem_iff (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (a : Nat) (P : Prop) :
    Sem callSemTable Φ Ψ SEnv.empty (allSemExpr a) P ↔
      NaruSem.Call.Sem callSemTable.Δ Φ Ψ SEnv.empty (allSemCore a) P :=
  lowerS_sem_iff (all_sem_wt a) (all_sem_lower a) hΦ rfl P

/-- 意味の存在(不在)も両側で一致する。spec 解釈の不在(`fun _ => none`)でも成立する。 -/
theorem all_sem_exists_iff (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (a : Nat) :
    (∃ P, Sem callSemTable Φ Ψ SEnv.empty (allSemExpr a) P) ↔
      (∃ P, NaruSem.Call.Sem callSemTable.Δ Φ Ψ SEnv.empty (allSemCore a) P) :=
  lowerS_sem_exists_iff (all_sem_wt a) (all_sem_lower a) hΦ rfl

/-- 論理の位置の合成式は、署名を守る任意の解釈で Nat に評価されない。 -/
theorem all_sem_not_nat (Φ : NaruSem.Call.FEnv) (hΦ : Φ.Respects callSemTable.Δ) (a n : Nat) :
    eval callSemTable Φ SEnv.empty (allSemExpr a) ≠ some (.nat n) :=
  eval_not_nat_of_wtS (all_sem_wt a) rfl hΦ rfl n

/-- 値の呼出し先がすべて `b` を返す解釈。 -/
def allSemConst (b : Bool) : NaruSem.Call.FEnv := fun _ => some fun _ => some (.bool b)

/-- 値の呼出し先がすべて `b` を返す解釈は表の署名を守る。 -/
theorem callSem_const_respects (b : Bool) : (allSemConst b).Respects callSemTable.Δ := by
  intro k ps t hs
  by_cases hp : k = "M.p"
  · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, DeclSig.toSig,
      NaruSem.Call.Sig.value?] at hs
  · by_cases hf : k = "M.flag"
    · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, hf, DeclSig.toSig,
        NaruSem.Call.Sig.value?] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨fun _ => some (.bool b), rfl, fun _ _ => ⟨.bool b, rfl, rfl⟩⟩
    · by_cases hv : k = "M.value"
      · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, hf, hv, DeclSig.toSig,
          NaruSem.Call.Sig.value?] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨fun _ => some (.bool b), rfl, fun _ _ => ⟨.bool b, rfl, rfl⟩⟩
      · by_cases hz : k = "M.zero"
        · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, hf, hv, hz, DeclSig.toSig,
            NaruSem.Call.Sig.value?] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact ⟨fun _ => some (.bool b), rfl, fun _ _ => ⟨.bool b, rfl, rfl⟩⟩
        · simp [NaruSem.Call.valueSig?, Table.Δ, callSemTable, hp, hf, hv, hz] at hs

/-- 非空虚な意味証人: すべての値の呼出し先が `false` を返す解釈では `value(true)` が偽で 2 つ目の腕に進み、
`false.flag()` は `false = true`、`q` は量化の命題そのもの。 -/
theorem all_sem_meaning (a : Nat) :
    Sem callSemTable callSemFalse callSemPredicate SEnv.empty (allSemExpr a)
      (¬ ((false = true) ↔ ∀ n : Nat, n + a ≥ a)) :=
  .blockLetProp rfl (.forallCons rfl fun _ => .quantNil (.cmpNat (k := .ge) rfl rfl rfl))
    (.blockTail (.matchSkip rfl rfl (.matchHit rfl rfl
      (.not (.eqForm (k := .eq) rfl
        (.ufcsVal (ps := [("b", .bool)]) (t := .bool) (b := false) rfl rfl rfl rfl rfl rfl rfl rfl)
        (.varProp rfl))))))

/-- 同じ命題が一般定理で Core の意味になる。 -/
theorem all_sem_meaning_core (a : Nat) :
    NaruSem.Call.Sem callSemTable.Δ callSemFalse callSemPredicate SEnv.empty (allSemCore a)
      (¬ ((false = true) ↔ ∀ n : Nat, n + a ≥ a)) :=
  (all_sem_iff callSemFalse callSemPredicate call_sem_closed_respects a _).mp (all_sem_meaning a)

/-- もう 1 つの非空虚な意味証人: すべての値の呼出し先が `true` を返す解釈では `value(true)` が真で 1 つ目の腕に進み、
ガード `q`・本体の `q && p(y = a, x = 0)`(名前付き引数は仮引数順 `[x, y]` で spec 解釈に届く)と、ガード不成立時の 2 つ目の腕を
前提・結論の両方向で保つ。 -/
theorem all_sem_meaning_true (a : Nat) :
    Sem callSemTable (allSemConst true) callSemPredicate SEnv.empty (allSemExpr a)
      (((∀ n : Nat, n + a ≥ a) → (∀ n : Nat, n + a ≥ a) ∧ ([Val.nat 0, .nat a] = [.nat 1, .nat 0])) ∧
        (¬ (∀ n : Nat, n + a ≥ a) → ¬ ((true = true) ↔ ∀ n : Nat, n + a ≥ a))) :=
  .blockLetProp rfl (.forallCons rfl fun _ => .quantNil (.cmpNat (k := .ge) rfl rfl rfl))
    (.blockTail (.matchGuard rfl rfl (.varProp rfl)
      (.logic (k := .and) rfl (.varProp rfl)
        (.callSpec (ps := [("x", .nat), ("y", .nat)]) (vs := [.nat 0, .nat a])
          (F := fun vs => vs = [.nat 1, .nat 0]) rfl rfl rfl rfl rfl rfl))
      (.matchHit rfl rfl (.not (.eqForm (k := .eq) rfl
        (.ufcsVal (ps := [("b", .bool)]) (t := .bool) (b := true) rfl rfl rfl rfl rfl rfl rfl rfl)
        (.varProp rfl))))))

theorem all_sem_meaning_true_core (a : Nat) :
    NaruSem.Call.Sem callSemTable.Δ (allSemConst true) callSemPredicate SEnv.empty (allSemCore a)
      (((∀ n : Nat, n + a ≥ a) → (∀ n : Nat, n + a ≥ a) ∧ ([Val.nat 0, .nat a] = [.nat 1, .nat 0])) ∧
        (¬ (∀ n : Nat, n + a ≥ a) → ¬ ((true = true) ↔ ∀ n : Nat, n + a ≥ a))) :=
  (all_sem_iff (allSemConst true) callSemPredicate (callSem_const_respects true) a _).mp
    (all_sem_meaning_true a)

theorem all_sem_predicate_defined : callSemPredicate.Defined callSemTable.Δ :=
  fun _ _ _ => ⟨_, rfl⟩

/-- 実生成 Lean の読み(`Call.denoteP`)への合成: 同じ環境での読みと Surface の意味は同値。 -/
theorem all_sem_denote (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects callSemTable.Δ) (hΨ : Ψ.Defined callSemTable.Δ) (a : Nat) {P : Prop}
    (h : Sem callSemTable Φ Ψ SEnv.empty (allSemExpr a) P) :
    P ↔ NaruSem.Call.denoteP callSemTable.Δ Φ Ψ SEnv.empty (allSemCore a) :=
  lowerS_denote (all_sem_wt a) (all_sem_lower a) rfl (NaruSem.Call.SigEnv.SubV.refl _) hΦ
    (NaruSem.Call.FEnv.Agree.refl hΦ) (NaruSem.Call.PEnv.Agree.refl hΨ) h

theorem all_sem_meaning_denote (a : Nat) :
    (¬ ((false = true) ↔ ∀ n : Nat, n + a ≥ a)) ↔
      NaruSem.Call.denoteP callSemTable.Δ callSemFalse callSemPredicate SEnv.empty (allSemCore a) :=
  all_sem_denote callSemFalse callSemPredicate call_sem_closed_respects all_sem_predicate_defined a
    (all_sem_meaning a)

/-- 同型の誤 Core(2 つ目の腕の否定を落とす)は適格だが、正しい lowering ではなく、意味も保存しない。 -/
def allSemWrong (a : Nat) : Core.Expr :=
  .let_ "q" .bool
    (.quant .forall_ [("n", .nat)]
      (.binop ">=" (.binop "+" (.var "n") (.lit (.nat a) .nat) .nat) (.lit (.nat a) .nat) .nat))
    (.match_ (.call "M.value" [.lit (.bool true) .bool]) .bool
      [ .mk (.lit (.bool true)) (some (.var "q"))
          (.binop "&&" (.var "q") (.call "M.p" [.lit (.nat 0) .nat, .lit (.nat a) .nat]) .bool),
        .mk .wild none
          (.binop "==" (.call "M.flag" [.lit (.bool false) .bool]) (.var "q") .bool) ])

theorem all_sem_wrong_wt (a : Nat) :
    NaruSem.Call.wtS callSemTable.Δ SCtx.empty (allSemWrong a) = some .prop := rfl

theorem all_sem_wrong_not_lower : lowerS callSemTable SCtx.empty (allSemExpr 0) ≠ some (allSemWrong 0) := by
  rw [all_sem_lower]
  intro h
  cases h

theorem all_sem_wrong_not_preserved :
    ¬ (∀ P, Sem callSemTable callSemFalse callSemPredicate SEnv.empty (allSemExpr 0) P ↔
      NaruSem.Call.Sem callSemTable.Δ callSemFalse callSemPredicate SEnv.empty (allSemWrong 0) P) := by
  intro h
  have hs := all_sem_meaning 0
  have hw : NaruSem.Call.Sem callSemTable.Δ callSemFalse callSemPredicate SEnv.empty (allSemWrong 0)
      ((false = true) ↔ ∀ n : Nat, n + 0 ≥ 0) :=
    .letProp rfl (.forallCons rfl fun _ => .quantNil (.cmpNat (k := .ge) rfl rfl rfl))
      (.matchSkip rfl rfl (.matchHit rfl rfl
        (.eqForm (k := .eq) rfl (.callVal (b := false) rfl rfl rfl rfl) (.varProp rfl))))
  have hu := NaruSem.Call.Sem_unique hw ((h _).mp hs)
  have hnx : ¬ ((false = true) ↔ ∀ n : Nat, n + 0 ≥ 0) := fun hx => (hu.mp hx) hx
  exact hnx (hu.mpr hnx)

end NaruSem.Surf.Call
