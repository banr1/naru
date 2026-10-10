import NaruSem.Denote
import NaruSem.SemTotality

/-!
# Statements の保存定理と実生成宣言への接続(IDEAL.md C42 / C44)

生成 Statements(`Backend.Statements.emitProp` が書く Lean の命題)の意味を、backend の文字列とは独立に Core から直接定めた **Lean での読み**
`denoteP : SEnv → Core.Expr → Prop`(命題。値の位置は Model の読み `denoteN` / `denoteB` を `ρ.vals` で)で表し、適格な式と対応する環境について、
独立意味論(評価関係 `Sem`)の命題が読みの命題と **同値** であることを一般定理 `Sem_denote` で示す。読みは `emitProp` の出力と同じ形で書く:

| Core | 生成 Lean(`emitProp`) | 読み(`denoteP`) | 独立意味論(`Sem`) |
|---|---|---|---|
| `true` / `false` | `True` / `False` | `True` / `False` | `b = true`(`lit`) |
| Bool の値の局所名 | `x = true` | 環境の値 `b` で `b = true`(命題に束ねた名前はその命題) | `b = true`(`varVal`)/ 命題(`varProp`) |
| `&&` / `\|\|` / `implies` / `!` | `∧` / `∨` / `→` / `¬` | `LogicOp.prop` / `¬` | 同じ |
| Nat の `< <= > >=`、`==` / `!=` | `a < b` …、`a = b` / `a ≠ b`(被演算子は `emitE`) | `CmpOp.propNat` / `EqOp.propNat`(被演算子は `denoteN`) | 同じ(値は `eval`) |
| Bool の `< <= > >=` | `Ord.compare a b = Ordering.lt` / `≠ .gt` / `= .gt` / `≠ .lt` | `CmpOp.leanBoolProp`(同じ形) | `CmpOp.evalBool a b = true` — `CmpOp.leanBoolProp_iff` |
| 論理の位置の `==` / `!=`、両辺が値 | `a = b` / `a ≠ b`(`proppy` が偽) | `EqOp.propBool`(`proppyS` が偽) | 両辺の命題の `↔` / `¬ (… ↔ …)` — `EqOp.propIff_bool`(値の等値と命題の同値の区別) |
| 同じく、どちらかが命題 | `P ↔ Q` / `¬ (P ↔ Q)` | `EqOp.propIff` | 同じ(C43) |
| `if`(条件が Bool の値) | `if c = true then P else Q` | `if denoteB c = true then … else …` | `(C → P) ∧ (¬ C → Q)` |
| `if`(条件が命題) | `(C → P) ∧ (¬ C → Q)` | 同じ形 | 同じ(C43) |
| 値の `let` | `let x : Nat := v; P` / `let x : Bool := v; P` | 環境の拡張(値) | 同じ |
| 命題の `let` | `let x : Prop := P; Q` | 環境の拡張(命題) | 同じ(C43) |
| `match`(非再帰) | `emitMatchGuardedProp`: ガード付きの腕は `(match s with \| p => g → b \| _ => True) ∧ (¬ (match s with \| p => g \| _ => False) → REST)` | `denoteArmsP`: 腕を前から `matchPat` で試し、同じ形(`rest` は外側の環境) | `matchSkip` / `matchHit` / `matchGuard`(C43) |
| `forall` / `exists` | `∀ (x : T), …` / `∃ (x : T), …` | `denoteQuant`(`Ty.carrier` の全要素) | `forallCons` / `existsCons`(C43) |

採用方式(C44、「コンパイラ意味論保存の保証方式」): Model と同じ **汎用翻訳方式 + 生成物ごとの接続検査**。
- 一般定理 `Sem_denote`(基礎段階、C42): 任意の適格な式 `e`(`wtS Γ e = some τ`)で基礎の構文(`basic`: リテラル・局所名・`let`・`if`・二項演算・`!`・
  `min` / `max`)だけから成り、命題の束縛の無い文脈(`SCtx.NoProp`: spec 宣言の仮引数は値)と任意の対応する環境 `ρ`(`Γ = ρ.ctx`)について、
  `Sem ρ e P → (P ↔ denoteP ρ e)`。両方向の同値で、一方向の含意ではない。`Sem_denoteP` は存在(`Sem_exists`)と合わせて `Sem ρ e (denoteP ρ e)`
  (読みは意味である。命題外延性)。
- 値 / 命題の境界 `denoteP_iff_denoteB`: 基礎の式の命題の読みは、Bool の読みが `true` であることと同値(Bool の値を「true である」命題に写す境界。
  生成 Statements が `if c = true` / `a = b` と値の形で出す所を、意味の側の `(C → P) ∧ (¬ C → Q)` / `P ↔ Q` と結ぶ)。
- 接続(`check_sound_prop`): 実生成宣言 `Statements.M.f` について、検査プログラムが `∀ args, Statements.M.f args = denoteP (SEnv.ofList …) core_f`
  (`Prop` の等式)を kernel の定義的等しさで確かめ、そこから `Sem (SEnv.ofList …) core_f (Statements.M.f args)` を導く(`lake exe naru_test semantics`)。
  検査に失敗した宣言は検証済みにならず、保証は「接続検査に成功した生成宣言」に対するもので、コンパイラの全入力への無条件の保存ではない。

段階の境界: 一般定理の前提 `basic` と `SCtx.NoProp` は C42 の段階(量化・命題の `let`・命題の条件の `if`・`match` を含まない)の記録で、読み `denoteP` 自体は
`wtS` の対象範囲すべて(C43 の構文を含む)に定めてある。読みの対象外・不適格な部分は既定値 `False`(Model の `0` / `false` と同じく、一般定理は適格な式に
だけ対応を主張する。意味の側 `Sem` は導出が無いことで「意味が定まらない」を表し、`False` で埋めない)。
-/

namespace NaruSem
open Naru

/-! ## 生成 Lean の読み(命題の演算) -/

/-- 生成 Statements の Bool の値の等値(`emitProp` の `a = b` / `a ≠ b`。論理の位置の `==` / `!=` の両辺が値のとき)。 -/
def EqOp.propBool : EqOp → Bool → Bool → Prop
  | .eq, a, b => a = b
  | .ne, a, b => a ≠ b

/-- 生成 Statements の Bool の比較(`compareProp`: `Ord.compare a b = Ordering.lt` / `≠ Ordering.gt` / `= Ordering.gt` / `≠ Ordering.lt`)。 -/
def CmpOp.leanBoolProp : CmpOp → Bool → Bool → Prop
  | .lt, a, b => Ord.compare a b = Ordering.lt
  | .le, a, b => Ord.compare a b ≠ Ordering.gt
  | .gt, a, b => Ord.compare a b = Ordering.gt
  | .ge, a, b => Ord.compare a b ≠ Ordering.lt

/-! ## 値 / 命題の境界の対応関係(Bool の全要素・`decide` の場合分けで kernel が検査) -/

/-- 異なる表現の対応関係: 生成 Statements の Bool の比較(`Ord.compare` の命題)は独立意味論の `evalBool = true` と同値。 -/
theorem CmpOp.leanBoolProp_iff (k : CmpOp) (a b : Bool) : k.leanBoolProp a b ↔ k.evalBool a b = true := by
  cases k <;> cases a <;> cases b <;> simp only [CmpOp.leanBoolProp, CmpOp.evalBool] <;> decide

/-- 同じく、生成 Model の読み(`Ord.compare a b == .lt` …)が `true` であることと同値。 -/
theorem CmpOp.leanBoolProp_iff_leanBool (k : CmpOp) (a b : Bool) : k.leanBoolProp a b ↔ k.leanBool a b = true := by
  cases k <;> cases a <;> cases b <;> simp only [CmpOp.leanBoolProp, CmpOp.leanBool] <;> decide

theorem CmpOp.propNat_iff (k : CmpOp) (a b : Nat) : k.propNat a b ↔ k.evalNat a b = true := by
  cases k <;> simp [CmpOp.propNat, CmpOp.evalNat]

theorem EqOp.propNat_iff (k : EqOp) (a b : Nat) : k.propNat a b ↔ k.evalNat a b = true := by
  cases k <;> simp [EqOp.propNat, EqOp.evalNat]

theorem EqOp.propNat_iff_leanNat (k : EqOp) (a b : Nat) : k.propNat a b ↔ k.leanNat a b = true := by
  cases k <;> simp [EqOp.propNat, EqOp.leanNat]

theorem EqOp.propBool_iff (k : EqOp) (a b : Bool) : k.propBool a b ↔ k.evalBool a b = true := by
  cases k <;> cases a <;> cases b <;> simp only [EqOp.propBool, EqOp.evalBool] <;> decide

theorem EqOp.propBool_iff_leanBool (k : EqOp) (a b : Bool) : k.propBool a b ↔ k.leanBool a b = true := by
  cases k <;> cases a <;> cases b <;> simp only [EqOp.propBool, EqOp.leanBool] <;> decide

/-- **値の等値と命題の同値の区別**: 論理の位置の `==` / `!=` の意味(両辺の命題の同値とその否定)は、両辺が Bool の値 `a` / `b` の命題 `a = true` / `b = true`
なら、生成 Statements が出す値の等値 `a = b` / `a ≠ b` と同値。 -/
theorem EqOp.propIff_bool (k : EqOp) (a b : Bool) : k.propIff (a = true) (b = true) ↔ k.propBool a b := by
  cases k <;> cases a <;> cases b <;> simp only [EqOp.propIff, EqOp.propBool] <;> decide

theorem LogicOp.prop_iff (k : LogicOp) (a b : Bool) : k.prop (a = true) (b = true) ↔ k.eval a b = true := by
  cases k <;> cases a <;> cases b <;> simp only [LogicOp.prop, LogicOp.eval] <;> decide

/-! ## 生成 Lean の読み(量化・式・腕の列) -/

/-- 量化の読み(`∀ (x : T), …` / `∃ (x : T), …`): 束縛を前から `Ty.carrier`(Nat / Bool の全要素)で束ね、束縛が尽きたら続き `k` を拡張した環境で読む。
束縛型が対象外なら `False`。 -/
def denoteQuant (q : Quant) (ρ : SEnv) : List (String × TyV) → (SEnv → Prop) → Prop
  | [], k => k ρ
  | (x, tv) :: bs, k =>
    match TyV.toTy? tv with
    | some t =>
      match q with
      | .forall_ => ∀ a : t.carrier, denoteQuant q (ρ.ext x (.val (Val.of t a))) bs k
      | .exists_ => ∃ a : t.carrier, denoteQuant q (ρ.ext x (.val (Val.of t a))) bs k
    | none => False

mutual

/-- 命題の読み: `emitProp` の出力の意味を Core から直接定める(論理の位置の式)。値の位置(比較・等値の被演算子、`if` の Bool の条件、値の `let` の値、
scrutinee)は Model の読み `denoteN` / `denoteB` を `ρ.vals`(命題に束ねた名前はスコープ外)で読む。`emitProp` と同じく、`if` の条件と `==` / `!=` の両辺は
`proppyS`(コンパイラの `proppy` と同じ構文的な区分)が真なら命題として、偽なら値として読む。対象外・不適格な部分は `False`(一般定理は適格な式にだけ
対応を主張する)。 -/
def denoteP (ρ : SEnv) : Core.Expr → Prop
  | .lit (.bool true) _ => True
  | .lit (.bool false) _ => False
  | .var x =>
    match ρ x with
    | some (.val (.bool b)) => b = true
    | some (.prop P) => P
    | _ => False
  | .let_ x ty v b =>
    match ty with
    | .nat => denoteP (ρ.ext x (.val (.nat (denoteN ρ.vals v)))) b
    | .bool =>
      match proppyS ρ.ctx v with
      | true => denoteP (ρ.ext x (.prop (denoteP ρ v))) b
      | false => denoteP (ρ.ext x (.val (.bool (denoteB ρ.vals v)))) b
    | _ => False
  | .ite c t e =>
    match proppyS ρ.ctx c with
    | true => (denoteP ρ c → denoteP ρ t) ∧ (¬ denoteP ρ c → denoteP ρ e)
    | false => if denoteB ρ.vals c = true then denoteP ρ t else denoteP ρ e
  | .binop op l r ty =>
    match BinOp.ofString? op, TyV.toTy? ty with
    | some (.logic k), some .bool => k.prop (denoteP ρ l) (denoteP ρ r)
    | some (.eq k), some .nat => k.propNat (denoteN ρ.vals l) (denoteN ρ.vals r)
    | some (.eq k), some .bool =>
      match proppyS ρ.ctx l || proppyS ρ.ctx r with
      | true => k.propIff (denoteP ρ l) (denoteP ρ r)
      | false => k.propBool (denoteB ρ.vals l) (denoteB ρ.vals r)
    | some (.cmp k), some .nat => k.propNat (denoteN ρ.vals l) (denoteN ρ.vals r)
    | some (.cmp k), some .bool => k.leanBoolProp (denoteB ρ.vals l) (denoteB ρ.vals r)
    | _, _ => False
  | .unop op a => if op = "!" then ¬ denoteP ρ a else False
  | .match_ s st arms =>
    match st with
    | .nat => denoteArmsP ρ (.nat (denoteN ρ.vals s)) arms
    | .bool => denoteArmsP ρ (.bool (denoteB ρ.vals s)) arms
    | _ => False
  | .quant q bs b => denoteQuant q ρ bs (fun ρ' => denoteP ρ' b)
  | _ => False

/-- 腕の列の読み(命題。C43 の対象): 腕を前から `matchPat` で試す。ガード無しの腕は束縛を足した環境で本体、ガード付きの腕は生成形
`emitMatchGuardedProp` と同じ `(match … with | p => g → b | _ => True) ∧ (¬ (match … with | p => g | _ => False) → rest)`(`rest` は外側の環境 `ρ` で:
束縛はその腕のガードと本体だけで有効)。腕が尽きれば `False`(生成形の `REST` が空のときと同じ。適格で網羅的な `match` では意味に現れない)。 -/
def denoteArmsP (ρ : SEnv) (v : Val) : List Core.Arm → Prop
  | [] => False
  | .mk p none b :: rest =>
    match matchPat p v with
    | some bs => denoteP (ρ.extVals bs) b
    | none => denoteArmsP ρ v rest
  | .mk p (some g) b :: rest =>
    (match matchPat p v with
     | some bs => denoteP (ρ.extVals bs) g → denoteP (ρ.extVals bs) b
     | none => True) ∧
    (¬ (match matchPat p v with
        | some bs => denoteP (ρ.extVals bs) g
        | none => False) →
      denoteArmsP ρ v rest)

end

/-! ## 基礎段階(C42)の範囲: 命題の束縛の無い文脈 -/

/-- 命題に束ねた名前の無い文脈(spec 宣言の仮引数はすべて値)。基礎段階の一般定理の前提。 -/
def SCtx.NoProp (Γ : SCtx) : Prop := ∀ y, Γ y ≠ some .prop

theorem SCtx.NoProp.ext_val {Γ : SCtx} (h : Γ.NoProp) (x : String) (t : Ty) : (Γ.ext x (.val t)).NoProp := by
  intro y
  simp only [SCtx.ext]
  split
  · simp
  · exact h y

theorem SCtx.NoProp.extList_vals {α : Type} {Γ : SCtx} (h : Γ.NoProp) (xs : List (String × α)) (f : α → Ty) :
    (Γ.extList (xs.map fun p => (p.1, STy.val (f p.2)))).NoProp := by
  induction xs generalizing Γ with
  | nil => exact h
  | cons p rest ih => exact ih (h.ext_val p.1 (f p.2))

theorem SCtx.NoProp.empty : SCtx.empty.NoProp := fun _ => by simp [SCtx.empty]

/-- 値の仮引数の並びから作った文脈には命題の束縛が無い。 -/
theorem SCtx.NoProp.ofList {α : Type} (xs : List (String × α)) (f : α → Ty) :
    (SCtx.ofList (xs.map fun p => (p.1, STy.val (f p.2)))).NoProp :=
  SCtx.NoProp.extList_vals SCtx.NoProp.empty xs f

/-- 基礎の構文の式は、命題の束縛の無い文脈では命題でしか表せない式ではない(`proppyS` が偽: `emitProp` は `if` の条件と `==` / `!=` の両辺を値として出す)。 -/
theorem basic_not_proppy : ∀ (e : Core.Expr), basic e = true → ∀ (Γ : SCtx), Γ.NoProp → proppyS Γ e = false := by
  apply basic.induct
  · intro l ty _ Γ _
    rfl
  · intro x _ Γ hΓ
    simp only [proppyS]
    cases h : Γ x with
    | none => rfl
    | some s =>
      cases s with
      | val t => rfl
      | prop => exact absurd h (hΓ x)
  · intro x ty v b ihv ihb hb Γ hΓ
    simp only [basic, Bool.and_eq_true] at hb
    simp [proppyS, ihv hb.1 Γ hΓ, ihb hb.2 _ (hΓ.ext_val x .nat)]
  · intro c t e ihc iht ihe hb Γ hΓ
    simp only [basic, Bool.and_eq_true] at hb
    simp [proppyS, ihc hb.1.1 Γ hΓ, iht hb.1.2 Γ hΓ, ihe hb.2 Γ hΓ]
  · intro op l r ty ihl ihr hb Γ hΓ
    simp only [basic, Bool.and_eq_true] at hb
    simp [proppyS, ihl hb.1 Γ hΓ, ihr hb.2 Γ hΓ]
  · intro op a iha hb Γ hΓ
    simp only [basic] at hb
    simp [proppyS, iha hb Γ hΓ]
  · intro tn m r a rt ihr iha hb Γ hΓ
    simp only [basic, Bool.and_eq_true] at hb
    simp [proppyS, ihr hb.1 Γ hΓ, iha hb.2 Γ hΓ]
  · intro e h1 h2 h3 h4 h5 h6 h7 hb Γ _
    rw [basic.eq_def] at hb
    split at hb
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ rfl).elim
      | exact (h3 _ _ _ _ rfl).elim
      | exact (h4 _ _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ rfl).elim
      | exact (h7 _ _ _ _ _ rfl).elim
      | (cases hb; done)

/-! ## 環境の値の部分 -/

/-- 値を足した環境の値の部分は、値の部分に値を足したもの。 -/
theorem SEnv.vals_ext_val (ρ : SEnv) (x : String) (v : Val) : (ρ.ext x (.val v)).vals = ρ.vals.ext x v := by
  funext y
  simp only [SEnv.vals, SEnv.ext, Env.ext]
  by_cases h : y = x <;> simp [h]

/-- 仮引数の値の列から作った環境の文脈は、その型の列の文脈。 -/
theorem SEnv.ctx_ofList (xs : List (String × SVal)) : (SEnv.ofList xs).ctx = SCtx.ofList (xs.map fun p => (p.1, p.2.ty)) := by
  unfold SEnv.ofList SCtx.ofList
  rw [SEnv.ctx_extList]
  rfl

/-! ## 値 / 命題の境界(C42) -/

/-- **値 / 命題の境界**: 基礎の構文の式を命題の束縛の無い環境で読むと、命題の読みは Bool の読み(Model の読み `denoteB`)が `true` であることと同値。
生成 Statements が値の形で出す所(`if c = true`、両辺が値の `a = b`)と命題の形の所を結ぶ。 -/
theorem denoteP_iff_denoteB : ∀ (e : Core.Expr), basic e = true → ∀ (ρ : SEnv), ρ.ctx.NoProp →
    (denoteP ρ e ↔ denoteB ρ.vals e = true) := by
  apply basic.induct
  -- リテラル
  · intro l ty _ ρ _
    cases l with
    | bool b => cases b <;> simp [denoteP, denoteB]
    | nat n => simp [denoteP, denoteB]
    | str s => simp [denoteP, denoteB]
    | unit => simp [denoteP, denoteB]
  -- 局所名
  · intro x _ ρ hΓ
    simp only [denoteP, denoteB, SEnv.vals]
    cases h : ρ x with
    | none => simp
    | some s =>
      cases s with
      | val v =>
        cases v with
        | nat n => simp
        | bool b => simp
      | prop P => exact absurd (by simp [SEnv.ctx, h, SVal.ty]) (hΓ x)
  -- let
  · intro x ty v b ihv ihb hb ρ hΓ
    simp only [basic, Bool.and_eq_true] at hb
    cases ty
    case nat =>
      simp only [denoteP, denoteB]
      rw [← SEnv.vals_ext_val]
      exact ihb hb.2 _ (by rw [SEnv.ctx_ext]; exact hΓ.ext_val x .nat)
    case bool =>
      have hp := basic_not_proppy v hb.1 ρ.ctx hΓ
      simp only [denoteP, denoteB, hp]
      rw [← SEnv.vals_ext_val]
      exact ihb hb.2 _ (by rw [SEnv.ctx_ext]; exact hΓ.ext_val x .bool)
    all_goals simp [denoteP, denoteB]
  -- if
  · intro c t e ihc iht ihe hb ρ hΓ
    simp only [basic, Bool.and_eq_true] at hb
    have hp := basic_not_proppy c hb.1.1 ρ.ctx hΓ
    simp only [denoteP, denoteB, hp]
    cases hc : denoteB ρ.vals c <;> simp [iht hb.1.2 ρ hΓ, ihe hb.2 ρ hΓ]
  -- 二項演算
  · intro op l r ty ihl ihr hb ρ hΓ
    simp only [basic, Bool.and_eq_true] at hb
    have hl := ihl hb.1 ρ hΓ
    have hr := ihr hb.2 ρ hΓ
    have hpl := basic_not_proppy l hb.1 ρ.ctx hΓ
    have hpr := basic_not_proppy r hb.2 ρ.ctx hΓ
    simp only [denoteP, denoteB, hpl, hpr, Bool.or_self]
    cases hk : BinOp.ofString? op with
    | none => simp
    | some k =>
      cases hty : TyV.toTy? ty with
      | none => cases k <;> simp
      | some t =>
        cases k <;> cases t <;>
          simp [hl, hr, LogicOp.prop_iff, EqOp.propNat_iff_leanNat, EqOp.propBool_iff_leanBool, CmpOp.propNat_iff,
            CmpOp.leanBoolProp_iff_leanBool]
  -- 単項演算
  · intro op a iha hb ρ hΓ
    simp only [basic] at hb
    by_cases h : op = "!"
    · simp [denoteP, denoteB, h, iha hb ρ hΓ]
    · simp [denoteP, denoteB, h]
  -- Nat のメソッド(値: 命題の読みは `False`、Bool の読みは `false`)
  · intro tn m r a rt _ _ _ ρ _
    simp [denoteP, denoteB]
  -- 対象外の構文
  · intro e h1 h2 h3 h4 h5 h6 h7 hb ρ _
    rw [basic.eq_def] at hb
    split at hb
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ rfl).elim
      | exact (h3 _ _ _ _ rfl).elim
      | exact (h4 _ _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ rfl).elim
      | exact (h7 _ _ _ _ _ rfl).elim
      | (cases hb; done)

/-! ## 一般定理(C42) -/

/-- 適格な基礎の式について、独立意味論の命題は Lean での読みの命題と同値(`Sem` の導出の帰納法。値の位置は Model の保存 `preserve_nat` / `preserve_bool`
で読みの値に、Bool の値の命題は境界 `denoteP_iff_denoteB` で結ぶ)。 -/
theorem Sem_denote_basic {ρ : SEnv} {e : Core.Expr} {P : Prop} (h : Sem ρ e P) :
    basic e = true → ρ.ctx.NoProp → ∀ τ, wtS ρ.ctx e = some τ → (P ↔ denoteP ρ e) := by
  induction h with
  | @lit ρ b =>
    intro _ _ τ _
    cases b <;> simp [denoteP]
  | @varVal ρ x b h =>
    intro _ _ τ _
    simp [denoteP, h]
  | @varProp ρ x P h =>
    intro _ hΓ τ _
    exact absurd (by simp [SEnv.ctx, h, SVal.ty]) (hΓ x)
  | @logic ρ op k l r P Q hk hl hr ihl ihr =>
    intro hb hΓ τ hw
    simp only [basic, Bool.and_eq_true] at hb
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtS ρ.ctx l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtS ρ.ctx r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        have el := ihl hb.1 hΓ tl hwl
        have er := ihr hb.2 hΓ tr hwr
        simp only [denoteP, hk, TyV.toTy?]
        cases k <;> simp [LogicOp.prop, el, er]
  | @eqNat ρ op k l r a b hk hl hr =>
    intro _ _ τ hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtR ρ.ctx.vals l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtR ρ.ctx.vals r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        cases tl <;> cases tr <;> simp [hwl, hwr] at hw
        have pl := preserve_nat hwl ρ.vals (SEnv.ctx_vals ρ)
        have pr := preserve_nat hwr ρ.vals (SEnv.ctx_vals ρ)
        rw [hl] at pl
        rw [hr] at pr
        cases pl
        cases pr
        simp [denoteP, hk, TyV.toTy?]
  | @eqForm ρ op k l r P Q hk hl hr ihl ihr =>
    intro hb hΓ τ hw
    simp only [basic, Bool.and_eq_true] at hb
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtS ρ.ctx l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtS ρ.ctx r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        have el := ihl hb.1 hΓ tl hwl
        have er := ihr hb.2 hΓ tr hwr
        have bl := denoteP_iff_denoteB l hb.1 ρ hΓ
        have br := denoteP_iff_denoteB r hb.2 ρ hΓ
        have hpl := basic_not_proppy l hb.1 ρ.ctx hΓ
        have hpr := basic_not_proppy r hb.2 ρ.ctx hΓ
        simp only [denoteP, hk, TyV.toTy?, hpl, hpr, Bool.or_self]
        rw [propext el, propext bl, propext er, propext br]
        exact EqOp.propIff_bool k _ _
  | @cmpNat ρ op k l r a b hk hl hr =>
    intro _ _ τ hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtR ρ.ctx.vals l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtR ρ.ctx.vals r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        cases tl <;> cases tr <;> simp [hwl, hwr] at hw
        have pl := preserve_nat hwl ρ.vals (SEnv.ctx_vals ρ)
        have pr := preserve_nat hwr ρ.vals (SEnv.ctx_vals ρ)
        rw [hl] at pl
        rw [hr] at pr
        cases pl
        cases pr
        simp [denoteP, hk, TyV.toTy?]
  | @cmpBool ρ op k l r a b hk hl hr =>
    intro _ _ τ hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtR ρ.ctx.vals l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtR ρ.ctx.vals r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        cases tl <;> cases tr <;> simp [hwl, hwr] at hw
        have pl := preserve_bool hwl ρ.vals (SEnv.ctx_vals ρ)
        have pr := preserve_bool hwr ρ.vals (SEnv.ctx_vals ρ)
        rw [hl] at pl
        rw [hr] at pr
        cases pl
        cases pr
        simp only [denoteP, hk, TyV.toTy?]
        exact (CmpOp.leanBoolProp_iff k _ _).symm
  | @not ρ a P h ih =>
    intro hb hΓ τ hw
    simp only [basic] at hb
    simp only [wtS, ite_true] at hw
    cases hwa : wtS ρ.ctx a with
    | none => simp [hwa] at hw
    | some ta =>
      have ea := ih hb hΓ ta hwa
      simp only [denoteP, ite_true]
      rw [propext ea]
  | @ite ρ c t e C P Q hc ht he ihc iht ihe =>
    intro hb hΓ τ hw
    simp only [basic, Bool.and_eq_true] at hb
    simp only [wtS] at hw
    cases hwc : wtS ρ.ctx c with
    | none => simp [hwc] at hw
    | some tc =>
      cases hwt : wtS ρ.ctx t with
      | none => simp [hwc, hwt] at hw
      | some tt =>
        cases hwe : wtS ρ.ctx e with
        | none => simp [hwc, hwt, hwe] at hw
        | some te =>
          have ec := ihc hb.1.1 hΓ tc hwc
          have et := iht hb.1.2 hΓ tt hwt
          have ee := ihe hb.2 hΓ te hwe
          have bc := denoteP_iff_denoteB c hb.1.1 ρ hΓ
          have hpc := basic_not_proppy c hb.1.1 ρ.ctx hΓ
          simp only [denoteP, hpc]
          rw [propext ec, propext bc, propext et, propext ee]
          cases denoteB ρ.vals c <;> simp
  | @letNat ρ x v b n Q hv hb ihb =>
    intro hba hΓ τ hw
    simp only [basic, Bool.and_eq_true] at hba
    simp only [wtS, TyV.toTy?] at hw
    cases hwv : wtR ρ.ctx.vals v with
    | none => simp [hwv] at hw
    | some tv =>
      cases tv with
      | bool => simp [hwv] at hw
      | nat =>
        simp only [hwv] at hw
        have pv := preserve_nat hwv ρ.vals (SEnv.ctx_vals ρ)
        rw [hv] at pv
        cases pv
        have hΓ' : (ρ.ext x (.val (.nat (denoteN ρ.vals v)))).ctx = ρ.ctx.ext x (.val .nat) := by
          rw [SEnv.ctx_ext]
          rfl
        have := ihb hba.2 (by rw [hΓ']; exact hΓ.ext_val x .nat) τ (by rw [hΓ']; exact hw)
        simpa [denoteP] using this
  | @letBoolVal ρ x v b w Q hp hv hb ihb =>
    intro hba hΓ τ hw
    simp only [basic, Bool.and_eq_true] at hba
    simp only [wtS, TyV.toTy?, hp, Bool.false_eq_true, ite_false] at hw
    cases hwv : wtR ρ.ctx.vals v with
    | none => simp [hwv] at hw
    | some tv =>
      cases tv with
      | nat => simp [hwv] at hw
      | bool =>
        simp only [hwv] at hw
        have pv := preserve_bool hwv ρ.vals (SEnv.ctx_vals ρ)
        rw [hv] at pv
        cases pv
        have hΓ' : (ρ.ext x (.val (.bool (denoteB ρ.vals v)))).ctx = ρ.ctx.ext x (.val .bool) := by
          rw [SEnv.ctx_ext]
          rfl
        have := ihb hba.2 (by rw [hΓ']; exact hΓ.ext_val x .bool) τ (by rw [hΓ']; exact hw)
        simpa [denoteP, hp] using this
  | @letProp ρ x v b P Q hp hv hb _ _ =>
    intro hba hΓ τ _
    simp only [basic, Bool.and_eq_true] at hba
    rw [basic_not_proppy v hba.1 ρ.ctx hΓ] at hp
    cases hp
  | matchSkip _ _ _ _ =>
    intro hba _ _ _
    simp [basic] at hba
  | matchHit _ _ _ _ =>
    intro hba _ _ _
    simp [basic] at hba
  | matchGuard _ _ _ _ _ _ _ _ =>
    intro hba _ _ _
    simp [basic] at hba
  | quantNil _ _ =>
    intro hba _ _ _
    simp [basic] at hba
  | forallCons _ _ _ =>
    intro hba _ _ _
    simp [basic] at hba
  | existsCons _ _ _ =>
    intro hba _ _ _
    simp [basic] at hba

/-- **Statements の基礎段階の保存(C42)**: 文脈で適格な基礎の式(リテラル・局所名・値の `let`・Bool の条件の `if`・論理・比較・等値・`!`)は、命題の束縛の
無い文脈と対応する環境で、独立意味論の命題と Lean での読みの命題が同値(両方向)。 -/
theorem Sem_denote {Γ : SCtx} {e : Core.Expr} {τ : STy} (hw : wtS Γ e = some τ) (hb : basic e = true) (hΓ : Γ.NoProp)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) {P : Prop} (h : Sem ρ e P) : P ↔ denoteP ρ e :=
  Sem_denote_basic h hb (hρ ▸ hΓ) τ (hρ ▸ hw)

/-- 読みは意味である: 適格な基礎の式の意味(存在は `Sem_exists`)は読みの命題そのもの(命題外延性)。 -/
theorem Sem_denoteP {Γ : SCtx} {e : Core.Expr} {τ : STy} (hw : wtS Γ e = some τ) (hf : τ.isForm = true) (hb : basic e = true)
    (hΓ : Γ.NoProp) (ρ : SEnv) (hρ : Γ = ρ.ctx) : Sem ρ e (denoteP ρ e) := by
  obtain ⟨P, hP⟩ := Sem_exists hw hf ρ hρ
  rw [propext (Sem_denote hw hb hΓ ρ hρ hP)] at hP
  exact hP

/-! ## 実生成宣言への接続(C44) -/

/-- **接続検査の健全性(命題)**: 仮引数の値 `xs` の環境で適格な基礎の spec の式 `e` について、実生成宣言の命題 `Q` が読みと等しい(各宣言の接続検査が
確かめる `Prop` の等式)なら、`Q` は独立意味論の意味そのもの(`Sem … e Q`。読みの命題と同値な意味が存在し、命題外延性でそれは `Q`)。 -/
theorem check_sound_prop (xs : List (String × Val)) {e : Core.Expr} {τ : STy}
    (h : wtS (SCtx.ofList (xs.map fun p => (p.1, STy.val p.2.ty))) e = some τ) (hf : τ.isForm = true) (hb : basic e = true)
    {Q : Prop} (hq : Q = denoteP (SEnv.ofList (xs.map fun p => (p.1, SVal.val p.2))) e) :
    Sem (SEnv.ofList (xs.map fun p => (p.1, SVal.val p.2))) e Q := by
  subst hq
  apply Sem_denoteP h hf hb (SCtx.NoProp.ofList xs Val.ty)
  rw [SEnv.ctx_ofList, List.map_map]
  rfl

end NaruSem
