import NaruSem.CallTotality

/-!
# 関数・input の Core の意味論の検体(IDEAL.md C54)

`Call.lean` の対象範囲と意味の検体。`decide` / `rfl` または導出の場合分けで kernel が検査する。

- 対象範囲は空でない: fn / input / spec 宣言の呼出し(位置引数は仮引数の順)が適格で、意味が定まる。
- 不適格な Core は保証対象でない(`none`): 未解決の呼出し先、違う呼出し先の署名との不一致(引数の数・型)、phase の誤り(runtime から spec 宣言を呼ぶ、
  spec の値の位置に spec 宣言の呼出し)、循環(自己再帰・相互再帰・依存順でない宣言群)、鍵の重複。
- 評価不能は既定値に置き換えない: 署名に合わない input の解釈(Nat の署名に Bool を返す)の下では呼出しの評価が `none` になり、
  その解釈は `FEnv.RespectsInputs` を満たさない(全域性の前提が成り立たない)。
- 宣言群の意味: 2 段の呼出しと input を含む宣言群の fn の値、spec 宣言の意味。
-/

namespace NaruSem.Call
open Naru

/-! ## 署名の文脈の検体 -/

/-- `fn f(x: Nat) -> Nat`、`input k() -> Nat`、`predicate p(x: Nat)`。 -/
def Δ₀ : SigEnv := (SigEnv.empty.ext "M.f" (.fn [.nat] .nat)).ext "M.k" (.input [] .nat) |>.ext "M.p" (.spec [.nat])

/-- 仮引数 `x : Nat` の文脈。 -/
def Γx : Ctx := Ctx.ofList [("x", .nat)]

/-- 対象範囲は空でない: fn の呼出し `f(x + 1)` は Nat。 -/
example : wtR Δ₀ Γx (.call "M.f" [.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat]) = some .nat := by decide

/-- input の呼出し `k()` は Nat。 -/
example : wtR Δ₀ Γx (.call "M.k" []) = some .nat := by decide

/-- fn の呼出しの結果は値の位置(算術の被演算子)に置ける。 -/
theorem ex_wtR_call_in_arith : wtR Δ₀ Γx (.binop "+" (.call "M.f" [.var "x"]) (.call "M.k" []) .nat) = some .nat := by decide

/-- spec: spec 宣言の呼出し `p(x)` は命題、fn の Bool の呼出しは Bool の値。 -/
theorem ex_wtS_call_spec : wtS Δ₀ (SCtx.ofList [("x", .val .nat)]) (.call "M.p" [.var "x"]) = some .prop := by decide

def Δb : SigEnv := SigEnv.empty.ext "M.g" (.fn [.nat] .bool)

theorem ex_wtS_call_fn_bool : wtS Δb (SCtx.ofList [("x", .val .nat)]) (.call "M.g" [.var "x"]) = some (.val .bool) := by decide

/-- spec 宣言の呼出しは命題でしか表せない(`let` はそれを命題に束ねる)。 -/
theorem ex_proppyS_call_spec : proppyS Δ₀ (SCtx.ofList [("x", .val .nat)]) (.call "M.p" [.var "x"]) = true := by decide

theorem ex_wtS_let_call_spec :
    wtS Δ₀ (SCtx.ofList [("x", .val .nat)]) (.let_ "q" .bool (.call "M.p" [.var "x"]) (.binop "&&" (.var "q") (.var "q") .bool)) = some .prop := by decide

/-! ## 不適格な Core(保証対象でない) -/

/-- 未解決の呼出し先。 -/
theorem neg_wtR_call_unknown : wtR Δ₀ Γx (.call "M.nope" [.var "x"]) = none := by decide

/-- 引数の数が違う。 -/
theorem neg_wtR_call_arity : wtR Δ₀ Γx (.call "M.f" []) = none := by decide

theorem neg_wtR_call_arity2 : wtR Δ₀ Γx (.call "M.k" [.var "x"]) = none := by decide

/-- 引数の型が違う。 -/
theorem neg_wtR_call_type : wtR Δ₀ Γx (.call "M.f" [.lit (.bool true) .bool]) = none := by decide

/-- phase: runtime から spec 宣言を呼べない。 -/
theorem neg_wtR_call_spec_phase : wtR Δ₀ Γx (.call "M.p" [.var "x"]) = none := by decide

/-- phase: spec の値の位置(算術の被演算子)に spec 宣言の呼出しは置けない。 -/
theorem neg_wtS_call_spec_in_value :
    wtS Δ₀ (SCtx.ofList [("x", .val .nat)]) (.binop "+" (.call "M.p" [.var "x"]) (.var "x") .nat) = none := by decide

/-- spec 宣言の呼出しの実引数に命題は渡せない(実引数は値の位置)。 -/
theorem neg_wtS_call_prop_arg :
    wtS Δ₀ (SCtx.ofList [("q", .prop)]) (.call "M.p" [.var "q"]) = none := by decide

/-- 関数の値としての参照(呼出しでない)は対象外。 -/
theorem neg_wtR_global : wtR Δ₀ Γx (.global "M.f") = none := by decide

/-! ## 宣言群 -/

/-- `input k() -> Nat; fn f(x: Nat) -> Nat { x + k() }; fn g() -> Nat { f(1) }`(依存順)。 -/
def progA : Prog :=
  [ .input "M.k" [] .nat,
    .fn "M.f" [("x", .nat)] .nat (.binop "+" (.var "x") (.call "M.k" []) .nat),
    .fn "M.g" [] .nat (.call "M.f" [.lit (.nat 1) .nat]) ]

theorem ex_wtProg_A : (wtProg SigEnv.empty progA).isSome = true := by decide

theorem ex_wtProg_A_sig : (wtProg SigEnv.empty progA).bind (fun Δ => Δ "M.g") = some (.fn [] .nat) := by decide

/-- 自己再帰は不適格(呼出し先はそれより前の宣言に限る)。 -/
theorem neg_wtProg_self_recursion :
    wtProg SigEnv.empty [.fn "M.f" [("n", .nat)] .nat (.call "M.f" [.var "n"])] = none := by decide

/-- 相互再帰(循環)は不適格。 -/
theorem neg_wtProg_mutual_recursion :
    wtProg SigEnv.empty [.fn "M.f" [] .nat (.call "M.g" []), .fn "M.g" [] .nat (.call "M.f" [])] = none := by decide

/-- 依存順でない宣言群(呼出し先が後)は不適格。 -/
theorem neg_wtProg_not_ordered :
    wtProg SigEnv.empty [.fn "M.g" [] .nat (.call "M.f" [.lit (.nat 1) .nat]), .fn "M.f" [("x", .nat)] .nat (.var "x")] = none := by decide

/-- 鍵の重複は不適格。 -/
theorem neg_wtProg_duplicate :
    wtProg SigEnv.empty [.fn "M.f" [] .nat (.lit (.nat 1) .nat), .fn "M.f" [] .nat (.lit (.nat 2) .nat)] = none := by decide

/-- input の署名と合わない実引数の呼出しを含む宣言は不適格。 -/
theorem neg_wtProg_input_arity :
    wtProg SigEnv.empty [.input "M.k" [] .nat, .fn "M.f" [] .nat (.call "M.k" [.lit (.nat 1) .nat])] = none := by decide

/-- input の解釈: `k() = 41`。 -/
def I₄₁ : FEnv := FEnv.empty.ext "M.k" fun _ => some (.nat 41)

/-- 宣言群の意味: `g() = f(1) = 1 + k() = 42`。 -/
theorem ex_interp_A : ((interp I₄₁ progA).Φ "M.g").bind (fun f => f []) = some (.nat 42) := by decide

/-- 同じ宣言群を別の input の解釈で読めば別の値(解釈は環境から受け取る: 特定の束縛ではない)。 -/
theorem ex_interp_A_other : ((interp (FEnv.empty.ext "M.k" fun _ => some (.nat 0)) progA).Φ "M.g").bind (fun f => f []) = some (.nat 1) := by decide

/-- 署名に合わない input の解釈(Nat の署名に Bool を返す)の下では、呼出しの評価は行き詰まる(`none`。既定値に置き換えない)。 -/
def Iwrong : FEnv := FEnv.empty.ext "M.k" fun _ => some (.bool true)

theorem neg_interp_input_type : ((interp Iwrong progA).Φ "M.g").bind (fun f => f []) = none := by decide

/-- その解釈は input の署名を守らない(全域性の前提 `RespectsInputs` が成り立たない)。 -/
theorem neg_Iwrong_not_respects : ¬ Iwrong.RespectsInputs progA := by
  intro h
  obtain ⟨f, hf, hv⟩ := h "M.k" [] .nat (by simp [progA])
  have hf' : f = fun _ => some (.bool true) := by
    simp [Iwrong, FEnv.ext] at hf
    exact hf.symm
  obtain ⟨v, hv', hty⟩ := hv [] rfl
  subst hf'
  simp at hv'
  subst hv'
  simp [Val.ty] at hty

/-- `I₄₁` は署名を守る。 -/
theorem ex_I₄₁_respects : I₄₁.RespectsInputs progA := by
  intro k ps t h
  simp only [progA, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := Decl.input.inj h
  exact ⟨_, rfl, fun vs hvs => by
    cases vs with
    | nil => exact ⟨.nat 41, rfl, rfl⟩
    | cons v vs => simp at hvs⟩

/-- 型の合う実引数に型の合う値を返す(一般定理 `fn_total` の実例)。 -/
theorem ex_fn_total : ∃ f, (interp I₄₁ progA).Φ "M.f" = some f ∧ ∀ vs : List Val, vs.map Val.ty = [("x", Ty.nat)].map (·.2) → ∃ v, f vs = some v ∧ v.ty = .nat := by
  obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp ex_wtProg_A
  exact fn_total hΔ ex_I₄₁_respects (k := "M.f") (ps := [("x", .nat)]) (t := .nat) (body := .binop "+" (.var "x") (.call "M.k" []) .nat) (by simp [progA])

/-- spec 宣言を含む宣言群: `fn g(x: Nat) -> Bool { x > 0 }; predicate p(x: Nat) { g(x) && x < 10 }; predicate q(x: Nat) { p(x) || x == 0 }`。 -/
def progS : Prog :=
  [ .fn "M.g" [("x", .nat)] .bool (.binop ">" (.var "x") (.lit (.nat 0) .nat) .nat),
    .spec "M.p" [("x", .nat)] (.binop "&&" (.call "M.g" [.var "x"]) (.binop "<" (.var "x") (.lit (.nat 10) .nat) .nat) .bool),
    .spec "M.q" [("x", .nat)] (.binop "||" (.call "M.p" [.var "x"]) (.binop "==" (.var "x") (.lit (.nat 0) .nat) .nat) .bool) ]

theorem ex_wtProg_S : (wtProg SigEnv.empty progS).isSome = true := by decide

theorem ex_wtProg_S_sig : (wtProg SigEnv.empty progS).bind (fun Δ => Δ "M.q") = some (.spec [.nat]) := by decide

/-- spec 宣言の意味は定義されている(一般定理 `spec_defined` の実例)。 -/
theorem ex_spec_defined : ∃ F, (interp FEnv.empty progS).Ψ "M.q" = some F := by
  obtain ⟨Δ, hΔ⟩ := Option.isSome_iff_exists.mp ex_wtProg_S
  exact spec_defined hΔ (fun _ _ _ h => by simp [progS] at h) (k := "M.q") (ps := [("x", .nat)])
    (body := .binop "||" (.call "M.p" [.var "x"]) (.binop "==" (.var "x") (.lit (.nat 0) .nat) .nat) .bool) (by simp [progS])

/-- 検体の fn の意味: `g(n) = n > 0`。 -/
def gPos : List Val → Option Val
  | [.nat n] => some (.bool (decide (n > 0)))
  | _ => none

/-- fn の Bool の呼出しの意味は「結果が true である」(規則 `callVal` の実例)。 -/
theorem ex_Sem_callVal :
    Sem (SigEnv.empty.ext "M.g" (.fn [.nat] .bool)) (FEnv.empty.ext "M.g" gPos)
      PEnv.empty (SEnv.ofList [("x", .val (.nat 3))]) (.call "M.g" [.var "x"]) (decide (3 > 0) = true) :=
  .callVal (f := gPos) (by decide) (by simp [FEnv.ext]) (by rw [evalArgs_cons, evalArgs_nil]; rfl) rfl

/-- spec 宣言の呼出しの意味は、その宣言の意味に実引数の値を渡したもの(規則 `callSpec` の実例)。 -/
theorem ex_Sem_callSpec (F : List Val → Prop) :
    Sem (SigEnv.empty.ext "M.p" (.spec [.nat])) FEnv.empty (PEnv.empty.ext "M.p" F) (SEnv.ofList [("x", .val (.nat 3))])
      (.call "M.p" [.var "x"]) (F [.nat 3]) :=
  .callSpec (by decide) (by simp [PEnv.ext]) (by rw [evalArgs_cons, evalArgs_nil]; rfl)

/-- 行き詰まり: 未解決の呼出し先の評価は `none`。 -/
theorem neg_eval_call_unknown : eval FEnv.empty Env.empty (.call "M.f" []) = none := by decide

/-- 行き詰まり: 実引数が評価できなければ `none`(関数は呼ばれない)。 -/
theorem neg_eval_call_arg_stuck : eval (FEnv.empty.ext "M.f" fun _ => some (.nat 0)) Env.empty (.call "M.f" [.var "y"]) = none := by decide

/-- 行き詰まり: spec 宣言の呼出しは runtime の意味を持たない(値の環境に無い)。 -/
theorem neg_Sem_call_unknown (Φ : FEnv) (Ψ : PEnv) (ρ : SEnv) (P : Prop) (h : Sem SigEnv.empty Φ Ψ ρ (.call "M.p" []) P) : False := by
  cases h with
  | callVal hk => simp [isValueKey, valueSig?, SigEnv.empty] at hk
  | callSpec hk => simp [isSpecKey, specSig?, SigEnv.empty] at hk

end NaruSem.Call
