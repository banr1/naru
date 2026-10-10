import NaruSem.Totality

/-!
# Model の保存定理と実生成宣言への接続(IDEAL.md C40 / C41 / C44)

生成 Model(`Backend.Model.emitE` が書く Lean)の意味を、backend の文字列とは独立に Core から直接定めた **Lean での読み**
`denoteN` / `denoteB`(Nat / Bool の総関数)と腕の列の読み `denoteArmsN` / `denoteArmsB` で表し、適格な式と対応する環境について、
独立意味論 `eval` の結果が読みの値に一致することを一般定理 `denote_sound` で示す。読みは `emitE` の出力と同じ Lean の演算で書く:

| Core | 生成 Lean(`emitE`) | 読み(`denoteN` / `denoteB`) | 独立意味論(`eval`) |
|---|---|---|---|
| Nat の `+ - * / %` | `a + b` … | `ArithOp.eval`(同じ Lean の `Nat` の演算。`-` は 0 で切り詰め、`/ 0 = 0`、`% 0 = a`) | 同じ `ArithOp.eval`(等式) |
| `min` / `max` | `Min.min a b` / `Max.max a b` | `NatMethod.eval` | 同じ(等式) |
| Nat の `< <= > >=` | `Decidable.decide (a < b)` … | `CmpOp.evalNat`(`decide`) | 同じ(等式) |
| Bool の `< <= > >=` | `Ord.compare a b == .lt` / `!= .gt` / `== .gt` / `!= .lt` | `CmpOp.leanBool`(同じ形) | `CmpOp.evalBool`(`!a && b` …)— 対応関係 `CmpOp.leanBool_eq` |
| `==` / `!=` | `a == b` / `a != b`(`BEq`) | `EqOp.leanNat` / `EqOp.leanBool`(同じ形) | `decide (a = b)` / `decide (a ≠ b)` — 対応関係 `EqOp.leanNat_eq` / `EqOp.leanBool_eq` |
| `&&` / `\|\|` / `implies` / `!` | `a && b` / `a \|\| b` / `!a \|\| b` / `!a` | `LogicOp.eval` / `!` | 同じ(等式) |
| `let` / `if` / 局所名 / リテラル | `let x : T := v; b` / `if c then t else e` / `x` / `(n : Nat)` | 環境の拡張 / `if` / 環境の参照 / `n` | 同じ |
| `match`(C41) | `emitMatchGuarded`: ガード無しの先頭の腕は `match s with \| p => b`、ガード付きの腕 `p if g => b` は `match (match s with \| p => if g then some b else none \| _ => none) with \| some g' => g' \| none => REST`(REST は残りの腕。先頭の腕も再び含む) | 腕を前から試す(`matchPat`)。ガード付きの腕は同じ `match (if g then some b else none) with \| some g' => g' \| none => rest` の形。束縛はその腕のガードと本体だけ(`rest` は外側の環境) | `evalArms`(同じ腕の選択。`match` が網羅的で型が合えば等しい) |

採用方式(C44、「コンパイラ意味論保存の保証方式」): **汎用翻訳方式 + 生成物ごとの接続検査**。
- 一般定理 `denote_sound`(`preserve_nat` / `preserve_bool`): 任意の適格な式 `e`(`wtR Γ e = some t`)と任意の対応する環境 `ρ`(`Γ = ρ.ty`)に
  ついて `eval ρ e = some (denoteV ρ t e)`。backend の文字列は現れず、翻訳の正しさは仮定しない。腕の列・腕の一般補題は
  `denoteArms_sound` / `denoteArm_sound`、腕の選択と束縛の形は `denoteArmsV_hit` / `denoteArmsV_miss` / `denoteArmsV_guard_true` / `denoteArmsV_guard_false`。
- 接続(`check_sound_nat` / `check_sound_bool`): 実生成宣言 `Model.M.f` について、検査プログラムが `∀ args, Model.M.f args = denoteN (Env.ofList …) core_f`
  を kernel の定義的等しさで確かめる(`core_f` は実際の compiler 経路の Core の引用で、`Quote.checkDecls` が一致を照合する)。
  リテラルパターンの `match` は Lean が scrutinee の場合分け(`dite (x = k)` / `Bool.casesOn`)に展開するので、scrutinee の局所名を
  `cases` で場合分けして(Nat はリテラルの最大値 + 1 の深さ、Bool は 1 回)から `rfl`(場合分けの後は両辺が同じ形に簡約する)。
  この検査成功から、同じ引数で `eval (Env.ofList …) core_f = some (.nat (Model.M.f args))` を導く(`lake exe naru_test semantics`)。
  検査に失敗した宣言(読みと定義的に等しくない出力)は検証済みにならない。保証は「接続検査に成功した生成宣言」に対するもので、
  コンパイラの全入力への無条件の保存ではない。

段階の境界: 基礎段階(C40)の範囲は `basic`(リテラル・局所名・`let`・`if`・二項演算・`!`・`min` / `max`)、`match`(C41)はその外。
周回 42 から一般定理は `wtR` で適格な式すべて(`basic` の内外とも)を扱い、`basic` は段階の記録として残す。
-/

namespace NaruSem
open Naru

/-! ## 基礎段階の範囲(C40 の段階の境界の記録) -/

/-- 基礎段階の構文だけから成るか(`match` と対象外の構文を含まない)。C40 の段階の境界。一般定理の前提ではない(`wtR` だけ)。 -/
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

/-! ## 生成 Lean の読み(式と腕の列) -/

mutual

/-- Nat の式の読み: `emitE` の出力の意味を Core から直接定める総関数。対象外・不適格な部分は既定値 0(一般定理は適格な式にだけ
対応を主張する)。環境の参照は `ρ x` の Nat の値。`match` は scrutinee の読みの値で腕の列の読み `denoteArmsN` へ。 -/
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
  | .match_ s st arms =>
    match st with
    | .nat => denoteArmsN ρ (.nat (denoteN ρ s)) arms
    | .bool => denoteArmsN ρ (.bool (denoteB ρ s)) arms
    | _ => 0
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
  | .match_ s st arms =>
    match st with
    | .nat => denoteArmsB ρ (.nat (denoteN ρ s)) arms
    | .bool => denoteArmsB ρ (.bool (denoteB ρ s)) arms
    | _ => false
  | _ => false

/-- 腕の列の読み(Nat の本体): 腕を前から試す。パターンが一致しなければ次の腕、ガードの無い腕は束縛を足した環境で本体、
ガード付きの腕は生成形と同じ `match (if g then some b else none) with | some g' => g' | none => rest`(`rest` は外側の環境 `ρ` で:
束縛はその腕のガードと本体だけで有効)。腕が尽きれば既定値 0(適格で網羅的な `match` では起きない。`denoteArms_sound`)。 -/
def denoteArmsN (ρ : Env) (v : Val) : List Core.Arm → Nat
  | [] => 0
  | .mk p g b :: rest =>
    match matchPat p v with
    | none => denoteArmsN ρ v rest
    | some bs =>
      match g with
      | none => denoteN (ρ.extList bs) b
      | some g =>
        match (if denoteB (ρ.extList bs) g then some (denoteN (ρ.extList bs) b) else none) with
        | some g' => g'
        | none => denoteArmsN ρ v rest

/-- 腕の列の読み(Bool の本体)。 -/
def denoteArmsB (ρ : Env) (v : Val) : List Core.Arm → Bool
  | [] => false
  | .mk p g b :: rest =>
    match matchPat p v with
    | none => denoteArmsB ρ v rest
    | some bs =>
      match g with
      | none => denoteB (ρ.extList bs) b
      | some g =>
        match (if denoteB (ρ.extList bs) g then some (denoteB (ρ.extList bs) b) else none) with
        | some g' => g'
        | none => denoteArmsB ρ v rest

end

/-- 型ごとの読みを値に包む。 -/
def denoteV (ρ : Env) : Ty → Core.Expr → Val
  | .nat, e => .nat (denoteN ρ e)
  | .bool, e => .bool (denoteB ρ e)

/-- 腕の列の読みを値に包む。 -/
def denoteArmsV (ρ : Env) : Ty → Val → List Core.Arm → Val
  | .nat, v, arms => .nat (denoteArmsN ρ v arms)
  | .bool, v, arms => .bool (denoteArmsB ρ v arms)

@[simp] theorem denoteV_ty (ρ : Env) (t : Ty) (e : Core.Expr) : (denoteV ρ t e).ty = t := by
  cases t <;> rfl

@[simp] theorem denoteArmsV_ty (ρ : Env) (t : Ty) (v : Val) (arms : List Core.Arm) : (denoteArmsV ρ t v arms).ty = t := by
  cases t <;> rfl

/-! ## 腕の選択と束縛(C41) -/

/-- `denoteArmsN` の腕 1 つ分の展開(入れ子の帰納型の上の構造的再帰なので、`simp` に定義として渡さずこの補題で書き換える)。 -/
theorem denoteArmsN_cons (ρ : Env) (v : Val) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm) :
    denoteArmsN ρ v (.mk p g b :: rest) =
      match matchPat p v with
      | none => denoteArmsN ρ v rest
      | some bs =>
        match g with
        | none => denoteN (ρ.extList bs) b
        | some g =>
          match (if denoteB (ρ.extList bs) g then some (denoteN (ρ.extList bs) b) else none) with
          | some g' => g'
          | none => denoteArmsN ρ v rest :=
  denoteArmsN.eq_2 ρ v p g b rest

theorem denoteArmsB_cons (ρ : Env) (v : Val) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm) :
    denoteArmsB ρ v (.mk p g b :: rest) =
      match matchPat p v with
      | none => denoteArmsB ρ v rest
      | some bs =>
        match g with
        | none => denoteB (ρ.extList bs) b
        | some g =>
          match (if denoteB (ρ.extList bs) g then some (denoteB (ρ.extList bs) b) else none) with
          | some g' => g'
          | none => denoteArmsB ρ v rest :=
  denoteArmsB.eq_2 ρ v p g b rest

/-- 腕の選択: パターンが一致したガード無しの腕は、束縛 `bs` を足した環境での本体の読み。 -/
theorem denoteArmsV_hit (ρ : Env) (t : Ty) (v : Val) (p : Core.Pat) (b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) :
    denoteArmsV ρ t v (.mk p none b :: rest) = denoteV (ρ.extList bs) t b := by
  cases t <;> simp [denoteArmsV, denoteArmsN_cons, denoteArmsB_cons, hm, denoteV]

/-- 腕の選択: パターンが一致しない腕は飛ばして残りの腕(外側の環境 `ρ` のまま)。 -/
theorem denoteArmsV_miss (ρ : Env) (t : Ty) (v : Val) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm)
    (hm : matchPat p v = none) :
    denoteArmsV ρ t v (.mk p g b :: rest) = denoteArmsV ρ t v rest := by
  cases t <;> simp [denoteArmsV, denoteArmsN_cons, denoteArmsB_cons, hm]

/-- 腕の選択: パターンが一致しガード(束縛を足した環境で読む)が真なら、同じ環境での本体の読み。 -/
theorem denoteArmsV_guard_true (ρ : Env) (t : Ty) (v : Val) (p : Core.Pat) (g b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) (hg : denoteB (ρ.extList bs) g = true) :
    denoteArmsV ρ t v (.mk p (some g) b :: rest) = denoteV (ρ.extList bs) t b := by
  cases t <;> simp [denoteArmsV, denoteArmsN_cons, denoteArmsB_cons, hm, hg, denoteV]

/-- 腕の選択と束縛の範囲: ガードが偽なら残りの腕を **外側の環境 `ρ`** で読む(この腕の束縛 `bs` は次の腕に漏れない)。 -/
theorem denoteArmsV_guard_false (ρ : Env) (t : Ty) (v : Val) (p : Core.Pat) (g b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) (hg : denoteB (ρ.extList bs) g = false) :
    denoteArmsV ρ t v (.mk p (some g) b :: rest) = denoteArmsV ρ t v rest := by
  cases t <;> simp [denoteArmsV, denoteArmsN_cons, denoteArmsB_cons, hm, hg]

/-! ## 一般定理 -/

/-- 適格な式について、独立意味論の結果は Lean での読みの値(`wtR` の関数帰納法で、式・腕の列・腕の 3 つを同時に示す。腕の列では
`Totality.lean` と同じく網羅性の走査の状態を不変条件に持つ)。 -/
theorem denote_sound_all :
    (∀ (Γ : Ctx) (e : Core.Expr), ∀ ρ : Env, Γ = ρ.ty → ∀ t, wtR Γ e = some t →
        eval ρ e = some (denoteV ρ t e)) ∧
    (∀ (Γ : Ctx) (ts : Ty) (arms : List Core.Arm), ∀ ρ : Env, Γ = ρ.ty → ∀ t, wtArmsR Γ ts arms = some t →
        ∀ v : Val, v.ty = ts → ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        evalArms ρ v arms = some (denoteArmsV ρ t v arms)) ∧
    (∀ (Γ : Ctx) (ts : Ty) (arm : Core.Arm), ∀ p g b, arm = .mk p g b → ∀ ρ : Env, Γ = ρ.ty → ∀ t,
        wtArmR Γ ts arm = some t → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        eval (ρ.extList bs) b = some (denoteV (ρ.extList bs) t b) ∧
        (∀ g', g = some g' → eval (ρ.extList bs) g' = some (.bool (denoteB (ρ.extList bs) g')))) := by
  apply wtR.mutual_induct
  -- 1. Nat のリテラル
  · intro Γ n ρ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    simp [eval, denoteV, denoteN]
  -- 2. Bool のリテラル
  · intro Γ b ρ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    simp [eval, denoteV, denoteB]
  -- 3. 局所名
  · intro Γ x ρ hΓ t ht
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
  · intro Γ x ty v b ta hta hv ihv ihb ρ hΓ t ht
    simp only [wtR, hv, hta, ite_true] at ht
    have hev := ihv ρ hΓ ta hv
    have hΓ' : Γ.ext x ta = (ρ.ext x (denoteV ρ ta v)).ty := by rw [Env.ty_ext, denoteV_ty, hΓ]
    have heb := ihb _ hΓ' t ht
    cases ty <;> simp [TyV.toTy?] at hta
    all_goals subst hta; cases t <;> simp only [denoteV] at hev heb <;> simp [eval, hev, heb, denoteV, denoteN, denoteB]
  -- 5. let(注釈と値の型が違う)
  · intro Γ x ty v b tv ta hta hv hne _ ρ _ t ht
    simp [wtR, hv, hta, hne] at ht
  -- 6. let(値が不適格)
  · intro Γ x ty v b hno _ ρ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 7. if(適格)
  · intro Γ c t e te hte hc htt ihc iht ihe ρ hΓ t' ht'
    simp only [wtR, hc, htt, hte, ite_true, Option.some.injEq] at ht'
    subst ht'
    have hec := ihc ρ hΓ .bool hc
    have het := iht ρ hΓ te htt
    have hee := ihe ρ hΓ te hte
    simp only [denoteV] at hec
    cases hcb : denoteB ρ c
    all_goals cases te <;> simp [eval, hec, hcb, het, hee, denoteV, denoteN, denoteB]
  -- 8. if(分岐の型が違う)
  · intro Γ c t e tt te hte htt hc hne _ _ _ ρ _ t' ht'
    simp [wtR, hc, htt, hte, hne] at ht'
  -- 9. if(不適格)
  · intro Γ c t e hno _ _ _ ρ _ t' ht'
    simp only [wtR] at ht'
    first
      | (cases ht'; done)
      | (split at ht' <;> simp_all)
  -- 10. 二項演算(適格)
  · intro Γ op l r ty k tl tr ta hta hr hl hk ihl ihr ρ hΓ t ht
    simp only [wtR, hk, hl, hr, hta] at ht
    have hel := ihl ρ hΓ tl hl
    have her := ihr ρ hΓ tr hr
    simp only [eval, hk, hel, her]
    cases k <;> cases tl <;> cases tr <;> cases ta <;> simp [BinOp.result] at ht <;> subst ht <;>
      simp [BinOp.apply, denoteV, denoteN, denoteB, hk, hta, CmpOp.leanBool_eq, EqOp.leanNat_eq, EqOp.leanBool_eq]
  -- 11. 二項演算(不適格)
  · intro Γ op l r ty hno _ _ ρ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 12. `!`(適格)
  · intro Γ a ha iha ρ hΓ t ht
    simp only [wtR, ha, ite_true, Option.some.injEq] at ht
    subst ht
    have hea := iha ρ hΓ .bool ha
    simp only [denoteV] at hea
    simp [eval, hea, denoteV, denoteB]
  -- 13. `!`(被演算子が Bool でない)
  · intro Γ a hno _ ρ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 14. 対象外の単項演算子
  · intro Γ op a hne ρ _ t ht
    simp [wtR, hne] at ht
  -- 15. Nat の min / max(適格)
  · intro Γ m r a k ha hr hm ihr iha ρ hΓ t ht
    simp only [wtR, hm, hr, ha, ite_true, Option.some.injEq] at ht
    subst ht
    have her := ihr ρ hΓ .nat hr
    have hea := iha ρ hΓ .nat ha
    simp only [denoteV] at her hea
    simp [eval, hm, her, hea, denoteV, denoteN]
  -- 16. Nat のメソッド(不適格)
  · intro Γ m r a rt hno _ _ ρ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 17. Nat 以外のメソッド
  · intro Γ tn m r a rt hne ρ _ t ht
    simp [wtR, hne] at ht
  -- 18. match(適格): scrutinee の読みの値で腕の列へ(網羅性の走査は初期状態から)
  · intro Γ s st arms tv ta hta hs hex ihs iharms ρ hΓ t ht
    simp only [wtR, hs, hta, hex, ite_true] at ht
    have hv := ihs ρ hΓ tv hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hex
    obtain ⟨hteq, hexh⟩ := hex
    have hw := iharms ρ hΓ t ht (denoteV ρ tv s) (denoteV_ty ρ tv s) false false hexh (fun _ => rfl) (fun _ => rfl)
    simp only [eval, hv, hw]
    cases st <;> simp [TyV.toTy?] at hta
    all_goals subst hta; subst hteq; cases t <;> simp [denoteV, denoteArmsV, denoteN, denoteB]
  -- 19. match(型が違う / 網羅しない)
  · intro Γ s st arms tv ta hta hs hne _ ρ _ t ht
    simp [wtR, hs, hta, hne] at ht
  -- 20. match(不適格)
  · intro Γ s st arms hno _ ρ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 21. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 ρ _ t ht
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
  -- 22. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp p' g' b' heq ρ _ t ht
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp at ht
  -- 23. 腕(ガード無し): 束縛を足した環境で本体
  · intro Γ ts p b bts hp ihb p' g' b' heq ρ hΓ t ht v hv bs hm
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp only at ht
    have hΓ' : Γ.extPat bts = (ρ.extList bs).ty := by
      rw [Env.ty_extList, matchPat_types hp hv hm, hΓ]
      rfl
    refine ⟨ihb (ρ.extList bs) hΓ' t ht, ?_⟩
    intro g' hg
    cases hg
  -- 24. 腕(ガードが Bool): 束縛を足した環境でガードと本体
  · intro Γ ts p b bts hp g hg ihg ihb p' g' b' heq ρ hΓ t ht v hv bs hm
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp only [hg] at ht
    have hΓ' : Γ.extPat bts = (ρ.extList bs).ty := by
      rw [Env.ty_extList, matchPat_types hp hv hm, hΓ]
      rfl
    refine ⟨ihb (ρ.extList bs) hΓ' t ht, ?_⟩
    intro g'' hg''
    cases hg''
    have hc := ihg (ρ.extList bs) hΓ' .bool hg
    simpa [denoteV] using hc
  -- 25. 腕(ガードが Bool でない)
  · intro Γ ts p b bts hp g hno _ p' g' b' heq ρ _ t ht
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp only at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 26. 腕の列(空)
  · intro Γ ts ρ _ t ht
    simp [wtArmsR] at ht
  -- 27. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ ρ _ t ht
    simp [wtArmsR, h] at ht
  -- 28. 腕の列(最後の 1 つ): 網羅性からガード無しで必ず一致する
  · intro Γ ts arm t1 h1 ih3 ρ hΓ t ht v hv sawT sawF hex hT hF
    simp only [wtArmsR, h1, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
    have hmatch : g = none ∧ ∃ bs, matchPat p v = some bs := by
      cases g with
      | some g => simp [exhaustiveFrom] at hex
      | none =>
        refine ⟨rfl, ?_⟩
        cases p with
        | wild => exact ⟨[], rfl⟩
        | bind x => exact ⟨[(x, v)], rfl⟩
        | lit l =>
          cases l with
          | bool lb =>
            cases lb with
            | true =>
              rw [exhaustiveFrom_true] at hex
              simp only [exhaustiveFrom, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at hex
              obtain ⟨hts, hsf⟩ := hex
              subst hts
              cases v with
              | nat => simp [Val.ty] at hv
              | bool c =>
                cases c with
                | false => exact absurd (hF rfl) (by simp [hsf])
                | true => exact ⟨[], rfl⟩
            | false =>
              rw [exhaustiveFrom_false] at hex
              simp only [exhaustiveFrom, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at hex
              obtain ⟨hts, hst⟩ := hex
              subst hts
              cases v with
              | nat => simp [Val.ty] at hv
              | bool c =>
                cases c with
                | true => exact absurd (hT rfl) (by simp [hst])
                | false => exact ⟨[], rfl⟩
          | nat n => rw [exhaustiveFrom_nat] at hex; simp [exhaustiveFrom] at hex
          | str s => simp [exhaustiveFrom] at hex
          | unit => simp [exhaustiveFrom] at hex
        | tuple ps => simp [exhaustiveFrom] at hex
        | builtin n ps => simp [exhaustiveFrom] at hex
        | variant k vn ps => simp [exhaustiveFrom] at hex
    obtain ⟨hg, bs, hm⟩ := hmatch
    subst hg
    have hw := (ih3 p none b rfl ρ hΓ t1 h1 v hv bs hm).1
    rw [denoteArmsV_hit ρ t1 v p b [] bs hm]
    simp [evalArms_cons, hm, hw]
  -- 29. 腕の列(先頭の腕と残りの型が同じ): 一致すればガードの真偽で本体か残り、一致しなければ残り
  · intro Γ ts arm head tail t2 h2 h1 ih3 ih2 ρ hΓ t ht v hv sawT sawF hex hT hF
    rw [wtArmsR.eq_def] at ht
    simp only [h1, h2, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
    cases hm : matchPat p v with
    | some bs =>
      obtain ⟨hw, hguard⟩ := ih3 p g b rfl ρ hΓ t2 h1 v hv bs hm
      cases g with
      | none =>
        rw [denoteArmsV_hit ρ t2 v p b (head :: tail) bs hm]
        simp [evalArms_cons, hm, hw]
      | some g =>
        have hc := hguard g rfl
        cases hcb : denoteB (ρ.extList bs) g
        · rw [hcb] at hc
          rw [exhaustiveFrom_guard] at hex
          have hw' := ih2 ρ hΓ t2 h2 v hv sawT sawF hex hT hF
          rw [denoteArmsV_guard_false ρ t2 v p g b (head :: tail) bs hm hcb]
          simp [evalArms_cons, hm, hc, hw']
        · rw [hcb] at hc
          rw [denoteArmsV_guard_true ρ t2 v p g b (head :: tail) bs hm hcb]
          simp [evalArms_cons, hm, hc, hw]
    | none =>
      -- 一致しない: 残りの腕へ(外側の環境のまま)。網羅性の走査の状態を進める
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          evalArms ρ v (Core.Arm.mk p g b :: head :: tail) = some (denoteArmsV ρ t2 v (Core.Arm.mk p g b :: head :: tail)) := by
        intro sawT' sawF' hex' hT' hF'
        have hw' := ih2 ρ hΓ t2 h2 v hv sawT' sawF' hex' hT' hF'
        rw [denoteArmsV_miss ρ t2 v p g b (head :: tail) hm]
        simp [evalArms_cons, hm, hw']
      cases g with
      | some g =>
        rw [exhaustiveFrom_guard] at hex
        exact step sawT sawF hex hT hF
      | none =>
        cases p with
        | wild => simp [matchPat] at hm
        | bind x => simp [matchPat] at hm
        | lit l =>
          cases l with
          | bool lb =>
            cases lb with
            | true =>
              rw [exhaustiveFrom_true] at hex
              simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hex
              have hne : v ≠ .bool true := by
                intro h
                subst h
                simp [matchPat] at hm
              rcases hex with ⟨hts, hsf⟩ | hrest
              · subst hts
                cases v with
                | nat => simp [Val.ty] at hv
                | bool c =>
                  cases c with
                  | true => exact absurd rfl hne
                  | false => exact absurd (hF rfl) (by simp [hsf])
              · exact step true sawF hrest (fun h => absurd h hne) hF
            | false =>
              rw [exhaustiveFrom_false] at hex
              simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hex
              have hne : v ≠ .bool false := by
                intro h
                subst h
                simp [matchPat] at hm
              rcases hex with ⟨hts, hst⟩ | hrest
              · subst hts
                cases v with
                | nat => simp [Val.ty] at hv
                | bool c =>
                  cases c with
                  | false => exact absurd rfl hne
                  | true => exact absurd (hT rfl) (by simp [hst])
              · exact step sawT true hrest hT (fun h => absurd h hne)
          | nat n =>
            rw [exhaustiveFrom_nat] at hex
            exact step sawT sawF hex hT hF
          | str s => exact step sawT sawF (by simpa [exhaustiveFrom] using hex) hT hF
          | unit => exact step sawT sawF (by simpa [exhaustiveFrom] using hex) hT hF
        | tuple ps => exact step sawT sawF (by simpa [exhaustiveFrom] using hex) hT hF
        | builtin n ps => exact step sawT sawF (by simpa [exhaustiveFrom] using hex) hT hF
        | variant k vn ps => exact step sawT sawF (by simpa [exhaustiveFrom] using hex) hT hF
  -- 30. 腕の列(先頭の腕と残りの型が違う)
  · intro Γ ts arm t1 head tail h1 t2 hne h2 _ _ ρ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2, hne] at ht
  -- 31. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ ρ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2] at ht

/-- **Model の保存(C40 / C41)**: 文脈で適格な式(基礎の構文と非再帰の Nat / Bool の `match`)は、対応する環境で、独立意味論の結果が
Lean での読みの値に一致する。 -/
theorem denote_sound {Γ : Ctx} {e : Core.Expr} {t : Ty} (h : wtR Γ e = some t) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval ρ e = some (denoteV ρ t e) :=
  denote_sound_all.1 Γ e ρ hρ t h

theorem preserve_nat {Γ : Ctx} {e : Core.Expr} (h : wtR Γ e = some .nat) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval ρ e = some (.nat (denoteN ρ e)) :=
  denote_sound h ρ hρ

theorem preserve_bool {Γ : Ctx} {e : Core.Expr} (h : wtR Γ e = some .bool) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval ρ e = some (.bool (denoteB ρ e)) :=
  denote_sound h ρ hρ

/-- **腕の列の保存(C41)**: 適格で網羅的な腕の列と対応する環境・型の合う scrutinee の値について、腕を前から試す独立意味論の結果は
腕の列の読みの値(腕の順序、ガードの成功 / 失敗後の後続腕、束縛の範囲を含む)。 -/
theorem denoteArms_sound {Γ : Ctx} {ts t : Ty} {arms : List Core.Arm} (h : wtArmsR Γ ts arms = some t)
    (hex : exhaustive ts arms = true) (ρ : Env) (hρ : Γ = ρ.ty) (v : Val) (hv : v.ty = ts) :
    evalArms ρ v arms = some (denoteArmsV ρ t v arms) :=
  denote_sound_all.2.1 Γ ts arms ρ hρ t h v hv false false hex (fun _ => rfl) (fun _ => rfl)

/-- **腕の保存(C41)**: パターンが一致した腕のガードと本体は、束縛を足した環境で読みの値(束縛はこの腕のガードと本体だけに有効)。 -/
theorem denoteArm_sound {Γ : Ctx} {ts t : Ty} {p : Core.Pat} {g : Option Core.Expr} {b : Core.Expr}
    (h : wtArmR Γ ts (.mk p g b) = some t) (ρ : Env) (hρ : Γ = ρ.ty) {v : Val} (hv : v.ty = ts)
    {bs : List (String × Val)} (hm : matchPat p v = some bs) :
    eval (ρ.extList bs) b = some (denoteV (ρ.extList bs) t b) ∧
    (∀ g', g = some g' → eval (ρ.extList bs) g' = some (.bool (denoteB (ρ.extList bs) g'))) :=
  denote_sound_all.2.2 Γ ts (.mk p g b) p g b rfl ρ hρ t h v hv bs hm

/-! ## 実生成宣言への接続(C44) -/

/-- 仮引数の値の列から作った環境の文脈は、その型の列の文脈。 -/
theorem Env.ty_ofList (xs : List (String × Val)) : (Env.ofList xs).ty = Ctx.ofList (xs.map fun p => (p.1, p.2.ty)) := by
  unfold Env.ofList Ctx.ofList
  rw [Env.ty_extList]
  rfl

/-- **接続検査の健全性(Nat)**: 仮引数の値 `xs` の環境で適格な式 `e` について、実生成宣言の値 `v` が読みと等しい(各宣言の接続検査が
確かめる)なら、独立意味論の結果は `v`。 -/
theorem check_sound_nat (xs : List (String × Val)) {e : Core.Expr}
    (h : wtR (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some .nat)
    {v : Nat} (hv : v = denoteN (Env.ofList xs) e) : eval (Env.ofList xs) e = some (.nat v) := by
  subst hv
  exact preserve_nat h _ (Env.ty_ofList xs).symm

/-- 同じく Bool。 -/
theorem check_sound_bool (xs : List (String × Val)) {e : Core.Expr}
    (h : wtR (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some .bool)
    {v : Bool} (hv : v = denoteB (Env.ofList xs) e) : eval (Env.ofList xs) e = some (.bool v) := by
  subst hv
  exact preserve_bool h _ (Env.ty_ofList xs).symm

end NaruSem
