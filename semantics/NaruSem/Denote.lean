import NaruSem.Totality

/-!
# Model の基礎段階の保存定理(IDEAL.md C40 / C44)

生成 Model(`Backend.Model.emitE` が書く Lean)の意味を、backend の文字列とは独立に Core から直接定めた **Lean での読み**
`denoteN` / `denoteB`(Nat / Bool の総関数)で表し、適格な基礎の式と対応する環境について、独立意味論 `eval` の結果が読みの値に一致する
ことを一般定理 `denote_sound` で示す。読みは `emitE` の出力と同じ Lean の演算で書く:

| Core | 生成 Lean(`emitE`) | 読み(`denoteN` / `denoteB`) | 独立意味論(`eval`) |
|---|---|---|---|
| Nat の `+ - * / %` | `a + b` … | `ArithOp.eval`(同じ Lean の `Nat` の演算。`-` は 0 で切り詰め、`/ 0 = 0`、`% 0 = a`) | 同じ `ArithOp.eval`(等式) |
| `min` / `max` | `Min.min a b` / `Max.max a b` | `NatMethod.eval` | 同じ(等式) |
| Nat の `< <= > >=` | `Decidable.decide (a < b)` … | `CmpOp.evalNat`(`decide`) | 同じ(等式) |
| Bool の `< <= > >=` | `Ord.compare a b == .lt` / `!= .gt` / `== .gt` / `!= .lt` | `CmpOp.leanBool`(同じ形) | `CmpOp.evalBool`(`!a && b` …)— 対応関係 `CmpOp.leanBool_eq` |
| `==` / `!=` | `a == b` / `a != b`(`BEq`) | `EqOp.leanNat` / `EqOp.leanBool`(同じ形) | `decide (a = b)` / `decide (a ≠ b)` — 対応関係 `EqOp.leanNat_eq` / `EqOp.leanBool_eq` |
| `&&` / `\|\|` / `implies` / `!` | `a && b` / `a \|\| b` / `!a \|\| b` / `!a` | `LogicOp.eval` / `!` | 同じ(等式) |
| `let` / `if` / 局所名 / リテラル | `let x : T := v; b` / `if c then t else e` / `x` / `(n : Nat)` | 環境の拡張 / `if` / 環境の参照 / `n` | 同じ |

採用方式(C44、「コンパイラ意味論保存の保証方式」): **汎用翻訳方式 + 生成物ごとの接続検査**。
- 一般定理 `denote_sound`(`preserve_nat` / `preserve_bool`): 任意の基礎の適格な式 `e`(`wtR Γ e = some t`、`basic e = true`)と任意の対応する環境 `ρ`
  (`Γ = ρ.ty`)について `eval ρ e = some (denoteV ρ t e)`。backend の文字列は現れず、翻訳の正しさは仮定しない。
- 接続(`check_sound_nat` / `check_sound_bool`): 実生成宣言 `Model.M.f` について、検査プログラムが `∀ args, Model.M.f args = denoteN (Env.ofList …) core_f`
  を kernel の定義的等しさ(`rfl`)で確かめる(`core_f` は実際の compiler 経路の Core の引用で、`Quote.checkDecls` が一致を照合する)。
  この検査成功から、同じ引数で `eval (Env.ofList …) core_f = some (.nat (Model.M.f args))` を導く(`lake exe naru_test semantics`)。
  検査に失敗した宣言(読みと定義的に等しくない出力)は検証済みにならない。保証は「接続検査に成功した生成宣言」に対するもので、
  コンパイラの全入力への無条件の保存ではない。

基礎段階(C40)の範囲は `basic`(リテラル・局所名・`let`・`if`・二項演算・`!`・`min` / `max`)。`match`(C41)は読みにまだ無い
(`denoteN` / `denoteB` は既定値を返し、`basic` は `false` なので一般定理の対象にならない)。
-/

namespace NaruSem
open Naru

/-! ## 基礎段階の範囲 -/

/-- 基礎段階の構文だけから成るか(`match` と対象外の構文を含まない)。一般定理 `denote_sound` の前提。 -/
def basic : Core.Expr → Bool
  | .lit .. | .var _ => true
  | .let_ _ _ v b => basic v && basic b
  | .ite c t e => basic c && basic t && basic e
  | .binop _ l r _ => basic l && basic r
  | .unop _ a => basic a
  | .method _ _ r [a] _ => basic r && basic a
  | _ => false

/-! ## 生成 Lean の読み(演算) -/

/-- 生成 Lean の Bool の比較(`emitE`: `Ord.compare a b == .lt` / `!= .gt` / `== .gt` / `!= .lt`)。 -/
def CmpOp.leanBool : CmpOp → Bool → Bool → Bool
  | .lt, a, b => Ord.compare a b == Ordering.lt
  | .le, a, b => Ord.compare a b != Ordering.gt
  | .gt, a, b => Ord.compare a b == Ordering.gt
  | .ge, a, b => Ord.compare a b != Ordering.lt

/-- 生成 Lean の Nat の等値(`a == b` / `a != b`、`BEq`)。 -/
def EqOp.leanNat : EqOp → Nat → Nat → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b

/-- 生成 Lean の Bool の等値。 -/
def EqOp.leanBool : EqOp → Bool → Bool → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b

/-- 異なる表現の対応関係: Bool の比較(`Ord.compare` の形)は独立意味論の `evalBool`(`!a && b` …)と一致する(Bool の全要素で検査)。 -/
theorem CmpOp.leanBool_eq (k : CmpOp) (a b : Bool) : k.leanBool a b = k.evalBool a b := by
  cases k <;> cases a <;> cases b <;> rfl

/-- 異なる表現の対応関係: `BEq` の `==` / `!=` は `decide (a = b)` / `decide (a ≠ b)` と一致する(Nat)。 -/
theorem EqOp.leanNat_eq (k : EqOp) (a b : Nat) : k.leanNat a b = k.evalNat a b := by
  cases k
  · rfl
  · show (a != b) = decide (a ≠ b)
    cases h : decide (a = b) <;> simp_all

/-- 同じく Bool。 -/
theorem EqOp.leanBool_eq (k : EqOp) (a b : Bool) : k.leanBool a b = k.evalBool a b := by
  cases k <;> cases a <;> cases b <;> rfl

/-! ## 生成 Lean の読み(式) -/

mutual

/-- Nat の式の読み: `emitE` の出力の意味を Core から直接定める総関数。対象外・不適格な部分は既定値 0(一般定理は適格な式にだけ
対応を主張する)。環境の参照は `ρ x` の Nat の値。 -/
def denoteN (ρ : Env) : Core.Expr → Nat
  | .lit (.nat n) _ => n
  | .var x => match ρ x with | some (.nat n) => n | _ => 0
  | .let_ x ty v b =>
    match ty with
    | .nat => denoteN (ρ.ext x (.nat (denoteN ρ v))) b
    | .bool => denoteN (ρ.ext x (.bool (denoteB ρ v))) b
    | _ => 0
  | .ite c t e => if denoteB ρ c then denoteN ρ t else denoteN ρ e
  | .binop op l r ty =>
    match BinOp.ofString? op, TyV.toTy? ty with
    | some (.arith k), some .nat => k.eval (denoteN ρ l) (denoteN ρ r)
    | _, _ => 0
  | .method tn m r [a] _ =>
    if tn = "Nat" then
      match NatMethod.ofString? m with
      | some k => k.eval (denoteN ρ r) (denoteN ρ a)
      | none => 0
    else 0
  | _ => 0

/-- Bool の式の読み。既定値は `false`。 -/
def denoteB (ρ : Env) : Core.Expr → Bool
  | .lit (.bool b) _ => b
  | .var x => match ρ x with | some (.bool b) => b | _ => false
  | .let_ x ty v b =>
    match ty with
    | .nat => denoteB (ρ.ext x (.nat (denoteN ρ v))) b
    | .bool => denoteB (ρ.ext x (.bool (denoteB ρ v))) b
    | _ => false
  | .ite c t e => if denoteB ρ c then denoteB ρ t else denoteB ρ e
  | .binop op l r ty =>
    match BinOp.ofString? op, TyV.toTy? ty with
    | some (.cmp k), some .nat => k.evalNat (denoteN ρ l) (denoteN ρ r)
    | some (.cmp k), some .bool => k.leanBool (denoteB ρ l) (denoteB ρ r)
    | some (.eq k), some .nat => k.leanNat (denoteN ρ l) (denoteN ρ r)
    | some (.eq k), some .bool => k.leanBool (denoteB ρ l) (denoteB ρ r)
    | some (.logic k), some .bool => k.eval (denoteB ρ l) (denoteB ρ r)
    | _, _ => false
  | .unop op a => if op = "!" then !denoteB ρ a else false
  | _ => false

end

/-- 型ごとの読みを値に包む。 -/
def denoteV (ρ : Env) : Ty → Core.Expr → Val
  | .nat, e => .nat (denoteN ρ e)
  | .bool, e => .bool (denoteB ρ e)

@[simp] theorem denoteV_ty (ρ : Env) (t : Ty) (e : Core.Expr) : (denoteV ρ t e).ty = t := by
  cases t <;> rfl

/-! ## 一般定理 -/

/-- 基礎の適格な式について、独立意味論の結果は Lean での読みの値(`wtR` の関数帰納法。腕の列・腕は基礎段階では現れない)。 -/
theorem denote_sound_all :
    (∀ (Γ : Ctx) (e : Core.Expr), ∀ ρ : Env, Γ = ρ.ty → basic e = true → ∀ t, wtR Γ e = some t →
        eval ρ e = some (denoteV ρ t e)) ∧
    (∀ (_ : Ctx) (_ : Ty) (_ : List Core.Arm), True) ∧
    (∀ (_ : Ctx) (_ : Ty) (_ : Core.Arm), True) := by
  apply wtR.mutual_induct
  -- 1. Nat のリテラル
  · intro Γ n ρ _ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    simp [eval, denoteV, denoteN]
  -- 2. Bool のリテラル
  · intro Γ b ρ _ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    simp [eval, denoteV, denoteB]
  -- 3. 局所名
  · intro Γ x ρ hΓ _ t ht
    subst hΓ
    simp only [wtR, Env.ty] at ht
    cases h : ρ x with
    | none => simp [h] at ht
    | some v =>
      simp [h] at ht
      subst ht
      cases v with
      | nat n => simp [eval, h, denoteV, denoteN, Val.ty]
      | bool b => simp [eval, h, denoteV, denoteB, Val.ty]
  -- 4. let(適格)
  · intro Γ x ty v b ta hta hv ihv ihb ρ hΓ hb t ht
    simp only [wtR, hv, hta, ite_true] at ht
    simp only [basic, Bool.and_eq_true] at hb
    have hev := ihv ρ hΓ hb.1 ta hv
    have hΓ' : Γ.ext x ta = (ρ.ext x (denoteV ρ ta v)).ty := by rw [Env.ty_ext, denoteV_ty, hΓ]
    have heb := ihb _ hΓ' hb.2 t ht
    cases ty <;> simp [TyV.toTy?] at hta
    all_goals subst hta; cases t <;> simp only [denoteV] at hev heb <;> simp [eval, hev, heb, denoteV, denoteN, denoteB]
  -- 5. let(注釈と値の型が違う)
  · intro Γ x ty v b tv ta hta hv hne _ ρ _ _ t ht
    simp [wtR, hv, hta, hne] at ht
  -- 6. let(値が不適格)
  · intro Γ x ty v b hno _ ρ _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 7. if(適格)
  · intro Γ c t e te hte hc htt ihc iht ihe ρ hΓ hb t' ht'
    simp only [wtR, hc, htt, hte, ite_true, Option.some.injEq] at ht'
    subst ht'
    simp only [basic, Bool.and_eq_true] at hb
    have hec := ihc ρ hΓ hb.1.1 .bool hc
    have het := iht ρ hΓ hb.1.2 te htt
    have hee := ihe ρ hΓ hb.2 te hte
    simp only [denoteV] at hec
    cases hcb : denoteB ρ c
    all_goals cases te <;> simp [eval, hec, hcb, het, hee, denoteV, denoteN, denoteB]
  -- 8. if(分岐の型が違う)
  · intro Γ c t e tt te hte htt hc hne _ _ _ ρ _ _ t' ht'
    simp [wtR, hc, htt, hte, hne] at ht'
  -- 9. if(不適格)
  · intro Γ c t e hno _ _ _ ρ _ _ t' ht'
    simp only [wtR] at ht'
    first
      | (cases ht'; done)
      | (split at ht' <;> simp_all)
  -- 10. 二項演算(適格)
  · intro Γ op l r ty k tl tr ta hta hr hl hk ihl ihr ρ hΓ hb t ht
    simp only [wtR, hk, hl, hr, hta] at ht
    simp only [basic, Bool.and_eq_true] at hb
    have hel := ihl ρ hΓ hb.1 tl hl
    have her := ihr ρ hΓ hb.2 tr hr
    simp only [eval, hk, hel, her]
    cases k <;> cases tl <;> cases tr <;> cases ta <;> simp [BinOp.result] at ht <;> subst ht <;>
      simp [BinOp.apply, denoteV, denoteN, denoteB, hk, hta, CmpOp.leanBool_eq, EqOp.leanNat_eq, EqOp.leanBool_eq]
  -- 11. 二項演算(不適格)
  · intro Γ op l r ty hno _ _ ρ _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 12. `!`(適格)
  · intro Γ a ha iha ρ hΓ hb t ht
    simp only [wtR, ha, ite_true, Option.some.injEq] at ht
    subst ht
    simp only [basic] at hb
    have hea := iha ρ hΓ hb .bool ha
    simp only [denoteV] at hea
    simp [eval, hea, denoteV, denoteB]
  -- 13. `!`(被演算子が Bool でない)
  · intro Γ a hno _ ρ _ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 14. 対象外の単項演算子
  · intro Γ op a hne ρ _ _ t ht
    simp [wtR, hne] at ht
  -- 15. Nat の min / max(適格)
  · intro Γ m r a k ha hr hm ihr iha ρ hΓ hb t ht
    simp only [wtR, hm, hr, ha, ite_true, Option.some.injEq] at ht
    subst ht
    simp only [basic, Bool.and_eq_true] at hb
    have her := ihr ρ hΓ hb.1 .nat hr
    have hea := iha ρ hΓ hb.2 .nat ha
    simp only [denoteV] at her hea
    simp [eval, hm, her, hea, denoteV, denoteN]
  -- 16. Nat のメソッド(不適格)
  · intro Γ m r a rt hno _ _ ρ _ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 17. Nat 以外のメソッド
  · intro Γ tn m r a rt hne ρ _ _ t ht
    simp [wtR, hne] at ht
  -- 18. match(適格): 基礎段階の範囲外(`basic` が偽)
  · intro Γ s st arms tv ta hta hs hex ihs iharms ρ hΓ hb t ht
    simp [basic] at hb
  -- 19. match(型が違う / 網羅しない)
  · intro Γ s st arms tv ta hta hs hne _ ρ _ hb t ht
    simp [basic] at hb
  -- 20. match(不適格)
  · intro Γ s st arms hno _ ρ _ hb t ht
    simp [basic] at hb
  -- 21. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 ρ _ _ t ht
    rw [wtR.eq_def] at ht
    split at ht
    all_goals first
      | exact (h1 _ rfl).elim
      | exact (h2 _ rfl).elim
      | exact (h3 _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ rfl).elim
      | exact (h6 _ _ _ _ rfl).elim
      | exact (h7 _ _ rfl).elim
      | exact (h8 _ _ _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | (cases ht; done)
  -- 22〜31. 腕と腕の列(基礎段階では現れない)
  all_goals intros; trivial

/-- **基礎段階の保存(C40)**: 文脈で適格な基礎の式は、対応する環境で、独立意味論の結果が Lean での読みの値に一致する。 -/
theorem denote_sound {Γ : Ctx} {e : Core.Expr} {t : Ty} (h : wtR Γ e = some t) (hb : basic e = true) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval ρ e = some (denoteV ρ t e) :=
  denote_sound_all.1 Γ e ρ hρ hb t h

theorem preserve_nat {Γ : Ctx} {e : Core.Expr} (h : wtR Γ e = some .nat) (hb : basic e = true) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval ρ e = some (.nat (denoteN ρ e)) :=
  denote_sound h hb ρ hρ

theorem preserve_bool {Γ : Ctx} {e : Core.Expr} (h : wtR Γ e = some .bool) (hb : basic e = true) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval ρ e = some (.bool (denoteB ρ e)) :=
  denote_sound h hb ρ hρ

/-! ## 実生成宣言への接続(C44) -/

/-- 仮引数の値の列から作った環境の文脈は、その型の列の文脈。 -/
theorem Env.ty_ofList (xs : List (String × Val)) : (Env.ofList xs).ty = Ctx.ofList (xs.map fun p => (p.1, p.2.ty)) := by
  unfold Env.ofList Ctx.ofList
  rw [Env.ty_extList]
  rfl

/-- **接続検査の健全性(Nat)**: 仮引数の値 `xs` の環境で適格な基礎の式 `e` について、実生成宣言の値 `v` が読みと等しい(各宣言の接続検査
`rfl` が確かめる)なら、独立意味論の結果は `v`。 -/
theorem check_sound_nat (xs : List (String × Val)) {e : Core.Expr}
    (h : wtR (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some .nat) (hb : basic e = true)
    {v : Nat} (hv : v = denoteN (Env.ofList xs) e) : eval (Env.ofList xs) e = some (.nat v) := by
  subst hv
  exact preserve_nat h hb _ (Env.ty_ofList xs).symm

/-- 同じく Bool。 -/
theorem check_sound_bool (xs : List (String × Val)) {e : Core.Expr}
    (h : wtR (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some .bool) (hb : basic e = true)
    {v : Bool} (hv : v = denoteB (Env.ofList xs) e) : eval (Env.ofList xs) e = some (.bool v) := by
  subst hv
  exact preserve_bool h hb _ (Env.ty_ofList xs).symm

end NaruSem
