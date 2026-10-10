import NaruSem.Denote
import NaruSem.SemTotality

/-!
# Statements の保存定理と実生成宣言への接続(IDEAL.md C42 / C43 / C44)

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
| 同じく、どちらかが命題(C43) | `P ↔ Q` / `¬ (P ↔ Q)` | `EqOp.propIff` | 同じ |
| `if`(条件が Bool の値) | `if c = true then P else Q` | `if denoteB c = true then … else …` | `(C → P) ∧ (¬ C → Q)` — `denoteP_iff_denoteB_noProp` で結ぶ |
| `if`(条件が命題、C43) | `(C → P) ∧ (¬ C → Q)` | 同じ形 | 同じ |
| 値の `let` | `let x : Nat := v; P` / `let x : Bool := v; P` | 環境の拡張(値) | 同じ |
| 命題の `let`(C43) | `let x : Prop := P; Q` | 環境の拡張(命題。以後その名前は命題で、値の `let` / 量化 / パターンの同名の束縛が隠す) | 同じ |
| `match`(非再帰、C43) | `emitMatchGuardedProp`: ガード付きの腕は `(match s with \| p => g → b \| _ => True) ∧ (¬ (match s with \| p => g \| _ => False) → REST)` | `denoteArmsP`: 腕を前から `matchPat` で試し、同じ形(`rest` は外側の環境) | `matchSkip` / `matchHit` / `matchGuard` |
| `forall` / `exists`(C43) | `∀ (x : T), …` / `∃ (x : T), …` | `denoteQuant`(`Ty.carrier`: Nat / Bool の全要素) | `forallCons` / `existsCons` |

採用方式(C44、「コンパイラ意味論保存の保証方式」): Model と同じ **汎用翻訳方式 + 生成物ごとの接続検査**。
- 一般定理 `Sem_denote`(C42 / C43): 任意の適格な式 `e`(`wtS Γ e = some τ`。量化・命題の `let` と shadowing・命題の条件の `if`・ガード付き `match` を含む)と
  任意の対応する環境 `ρ`(`Γ = ρ.ctx`。命題に束ねた名前も可)について、`Sem ρ e P → (P ↔ denoteP ρ e)`。両方向の同値で、一方向の含意ではない。
  `Sem_denoteP` は存在(`Sem_exists`)と合わせて `Sem ρ e (denoteP ρ e)`(読みは意味である。命題外延性)。
  証明は `Sem` の導出の帰納法(`Sem_denote_all`)。`match` の残りの腕(それだけでは網羅的でない)と量化の束縛の末尾(空)にも帰納法の仮定を使うため、
  仮定は `wtS` から網羅性と束縛の非空の要求を除いた `wtSNoExh`(`wtS` で適格なら `wtSNoExh` でも同じ型: `wtS_noExh`)で置く。
- 値 / 命題の境界 `denoteP_iff_denoteB_noProp`: 命題でしか表せない部分(量化・命題に束ねた局所名: `proppyS`)を含まない式の命題の読みは、Bool の読みが
  `true` であることと同値(Bool の値を「true である」命題に写す境界。生成 Statements が `if c = true` / `a = b` と値の形で出す所を、意味の側の
  `(C → P) ∧ (¬ C → Q)` / `P ↔ Q` と結ぶ)。`proppyS` は文脈の命題の束縛だけで決まる(`proppyS_congr`: 値の型は見ない)。
- 接続(`check_sound_prop`): 実生成宣言 `Statements.M.f` について、検査プログラムが `∀ args, Statements.M.f args = denoteP (SEnv.ofList …) core_f`
  (`Prop` の等式)を kernel の定義的等しさで確かめ、そこから `Sem (SEnv.ofList …) core_f (Statements.M.f args)` を導く(`lake exe naru_test semantics`)。
  検査に失敗した宣言は検証済みにならず、保証は「接続検査に成功した生成宣言」に対するもので、コンパイラの全入力への無条件の保存ではない。

段階の記録: 基礎段階(C42)の範囲 `basic` と命題の束縛の無い文脈 `SCtx.NoProp` は、一般定理の前提ではなくなった(`Sem_denote_basic` / `denoteP_iff_denoteB` は
一般定理の系)。読みの対象外・不適格な部分は既定値 `False`(Model の `0` / `false` と同じく、一般定理は適格な式にだけ対応を主張する。意味の側 `Sem` は
導出が無いことで「意味が定まらない」を表し、`False` で埋めない)。
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

/-- 腕の列の読み(命題、C43): 腕を前から `matchPat` で試す。ガード無しの腕は束縛を足した環境で本体、ガード付きの腕は生成形
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

/-! ## 文脈の命題の束縛と `proppyS` の合同(C43)

`proppyS`(命題でしか表せない式の構文的な区分)は、文脈のどの名前が命題に束ねられているかだけで決まり、値の型は見ない(`let` の束縛と変数パターンを
値の型を知らずに `.val .nat` で足すのはこのため)。 -/

/-- 名前が命題に束ねられているか。 -/
def SCtx.isProp (Γ : SCtx) (x : String) : Bool :=
  match Γ x with
  | some .prop => true
  | _ => false

theorem SCtx.isProp_ext (Γ : SCtx) (x : String) (t : STy) (y : String) :
    (Γ.ext x t).isProp y = if y = x then (match t with | .prop => true | .val _ => false) else Γ.isProp y := by
  simp only [SCtx.isProp, SCtx.ext]
  by_cases hy : y = x
  · subst hy
    simp only [ite_true]
    cases t <;> rfl
  · simp only [hy, ite_false]

/-- 値の束縛は(型が何であれ)命題の束縛を変えない。 -/
theorem SCtx.isProp_ext_val (Γ : SCtx) (x : String) (t t' : Ty) (y : String) :
    (Γ.ext x (.val t)).isProp y = (Γ.ext x (.val t')).isProp y := by
  rw [SCtx.isProp_ext, SCtx.isProp_ext]

/-- 腕の中の文脈: 変数パターンは(値の型を知らず)`.val .nat` で足す(`proppyArms` と同じ)。 -/
def SCtx.patCtx (Γ : SCtx) : Core.Pat → SCtx
  | .bind x => Γ.ext x (.val .nat)
  | _ => Γ

/-- `proppyArms` の腕 1 つ分の展開。 -/
theorem proppyArms_cons (Γ : SCtx) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm) :
    proppyArms Γ (.mk p g b :: rest) =
      ((match g with | some g => proppyS (Γ.patCtx p) g | none => false) || proppyS (Γ.patCtx p) b || proppyArms Γ rest) := by
  cases p <;> cases g <;> rfl

theorem proppyS_var (Γ : SCtx) (x : String) : proppyS Γ (.var x) = Γ.isProp x := rfl

/-- `proppyS` / `proppyArms` は文脈の命題の束縛だけで決まる(`proppyS.mutual_induct`)。 -/
theorem proppyS_congr_all :
    (∀ (Γ : SCtx) (e : Core.Expr), ∀ Γ' : SCtx, (∀ y, Γ.isProp y = Γ'.isProp y) → proppyS Γ e = proppyS Γ' e) ∧
    (∀ (Γ : SCtx) (arms : List Core.Arm), ∀ Γ' : SCtx, (∀ y, Γ.isProp y = Γ'.isProp y) → proppyArms Γ arms = proppyArms Γ' arms) := by
  apply proppyS.mutual_induct
  · intro Γ q bs b Γ' _
    rfl
  · intro Γ x _ Γ' h
    rw [proppyS_var, proppyS_var]
    exact h x
  · intro Γ x _ Γ' h
    rw [proppyS_var, proppyS_var]
    exact h x
  · intro Γ x ty v b ihv ihb Γ' h
    have h' : ∀ y, (Γ.ext x (.val .nat)).isProp y = (Γ'.ext x (.val .nat)).isProp y := by
      intro y
      rw [SCtx.isProp_ext, SCtx.isProp_ext]
      split <;> simp [h y]
    simp only [proppyS, ihv Γ' h, ihb _ h']
  · intro Γ c t e ihc iht ihe Γ' h
    simp only [proppyS, ihc Γ' h, iht Γ' h, ihe Γ' h]
  · intro Γ op l r ty ihl ihr Γ' h
    simp only [proppyS, ihl Γ' h, ihr Γ' h]
  · intro Γ op a iha Γ' h
    simp only [proppyS, iha Γ' h]
  · intro Γ s st arms ihs iharms Γ' h
    simp only [proppyS, ihs Γ' h, iharms Γ' h]
  · intro Γ tn m r a rt ihr iha Γ' h
    simp only [proppyS, ihr Γ' h, iha Γ' h]
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 Γ' _
    have e1 : ∀ Γ₀ : SCtx, proppyS Γ₀ e = false := by
      intro Γ₀
      rw [proppyS.eq_def]
      split
      all_goals first
        | exact (h1 _ _ _ rfl).elim
        | exact (h2 _ rfl).elim
        | exact (h3 _ _ _ _ rfl).elim
        | exact (h4 _ _ _ rfl).elim
        | exact (h5 _ _ _ _ rfl).elim
        | exact (h6 _ _ rfl).elim
        | exact (h7 _ _ _ rfl).elim
        | exact (h8 _ _ _ _ _ rfl).elim
        | rfl
    rw [e1, e1]
  · intro Γ Γ' _
    rfl
  · intro Γ p g b rest Γ₀ ihg ihb ihrest Γ' h
    have hΓ₀ : Γ₀ = Γ.patCtx p := by cases p <;> rfl
    clear_value Γ₀
    subst hΓ₀
    have h' : ∀ y, (Γ.patCtx p).isProp y = (Γ'.patCtx p).isProp y := by
      intro y
      cases p <;> simp only [SCtx.patCtx, h y]
      rw [SCtx.isProp_ext, SCtx.isProp_ext]
      split <;> simp [h y]
    rw [proppyArms_cons, proppyArms_cons, ihb _ h', ihrest Γ' h]
    cases g with
    | none => rfl
    | some g =>
      simp only [ihg _ h']

theorem proppyS_congr {Γ Γ' : SCtx} (h : ∀ y, Γ.isProp y = Γ'.isProp y) (e : Core.Expr) : proppyS Γ e = proppyS Γ' e :=
  proppyS_congr_all.1 Γ e Γ' h

theorem proppyArms_congr {Γ Γ' : SCtx} (h : ∀ y, Γ.isProp y = Γ'.isProp y) (arms : List Core.Arm) :
    proppyArms Γ arms = proppyArms Γ' arms :=
  proppyS_congr_all.2 Γ arms Γ' h

/-! ## 基礎段階(C42)の範囲: 命題の束縛の無い文脈(段階の記録) -/

/-- 命題に束ねた名前の無い文脈(spec 宣言の仮引数はすべて値)。基礎段階の記録(一般定理の前提ではない)。 -/
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

/-- パターンの束縛を足した環境の値の部分は、値の部分に束縛を足したもの。 -/
theorem SEnv.vals_extVals (ρ : SEnv) (bs : List (String × Val)) : (ρ.extVals bs).vals = ρ.vals.extList bs := by
  induction bs generalizing ρ with
  | nil => rfl
  | cons xv rest ih =>
    obtain ⟨x, v⟩ := xv
    simp only [SEnv.extVals, List.map_cons, SEnv.extList, Env.extList]
    rw [← SEnv.vals_ext_val]
    exact ih _

/-- 仮引数の値の列から作った環境の文脈は、その型の列の文脈。 -/
theorem SEnv.ctx_ofList (xs : List (String × SVal)) : (SEnv.ofList xs).ctx = SCtx.ofList (xs.map fun p => (p.1, p.2.ty)) := by
  unfold SEnv.ofList SCtx.ofList
  rw [SEnv.ctx_extList]
  rfl

/-! ## 読みの形(C43): 局所束縛・条件・`==`、腕の選択と束縛、量化 -/

/-- 命題の `let`: 以後その名前は命題(読みの命題)に束ねる。 -/
theorem denoteP_let_prop (ρ : SEnv) (x : String) (v b : Core.Expr) (hp : proppyS ρ.ctx v = true) :
    denoteP ρ (.let_ x .bool v b) = denoteP (ρ.ext x (.prop (denoteP ρ v))) b := by
  simp [denoteP, hp]

/-- Bool の値の `let`: 名前は値に束ねる(同名の命題の束縛を隠す)。 -/
theorem denoteP_let_bool (ρ : SEnv) (x : String) (v b : Core.Expr) (hp : proppyS ρ.ctx v = false) :
    denoteP ρ (.let_ x .bool v b) = denoteP (ρ.ext x (.val (.bool (denoteB ρ.vals v)))) b := by
  simp [denoteP, hp]

/-- 命題の条件の `if` は `(C → P) ∧ (¬ C → Q)`(生成形と同じ)。 -/
theorem denoteP_ite_prop (ρ : SEnv) (c t e : Core.Expr) (hp : proppyS ρ.ctx c = true) :
    denoteP ρ (.ite c t e) = ((denoteP ρ c → denoteP ρ t) ∧ (¬ denoteP ρ c → denoteP ρ e)) := by
  simp [denoteP, hp]

/-- Bool の値の条件の `if` は Lean の `if c = true then … else …`。 -/
theorem denoteP_ite_bool (ρ : SEnv) (c t e : Core.Expr) (hp : proppyS ρ.ctx c = false) :
    denoteP ρ (.ite c t e) = (if denoteB ρ.vals c = true then denoteP ρ t else denoteP ρ e) := by
  simp [denoteP, hp]

/-- 命題を含む両辺の `==` / `!=` は同値とその否定(値の等値 `a = b` ではない)。 -/
theorem denoteP_eq_prop (ρ : SEnv) (op : String) (k : EqOp) (l r : Core.Expr) (hk : BinOp.ofString? op = some (.eq k))
    (hp : (proppyS ρ.ctx l || proppyS ρ.ctx r) = true) :
    denoteP ρ (.binop op l r .bool) = k.propIff (denoteP ρ l) (denoteP ρ r) := by
  simp [denoteP, hk, TyV.toTy?, hp]

/-- 両辺が値の `==` / `!=` は値の等値 `a = b` / `a ≠ b`。 -/
theorem denoteP_eq_bool (ρ : SEnv) (op : String) (k : EqOp) (l r : Core.Expr) (hk : BinOp.ofString? op = some (.eq k))
    (hp : (proppyS ρ.ctx l || proppyS ρ.ctx r) = false) :
    denoteP ρ (.binop op l r .bool) = k.propBool (denoteB ρ.vals l) (denoteB ρ.vals r) := by
  simp [denoteP, hk, TyV.toTy?, hp]

/-- 腕の選択: パターンが一致したガード無しの腕は、束縛 `bs` を足した環境での本体の読み。 -/
theorem denoteArmsP_hit (ρ : SEnv) (v : Val) (p : Core.Pat) (b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) :
    denoteArmsP ρ v (.mk p none b :: rest) = denoteP (ρ.extVals bs) b := by
  rw [denoteArmsP.eq_2]
  simp [hm]

/-- 腕の選択: パターンが一致しない腕は飛ばして残りの腕(外側の環境 `ρ` のまま)。 -/
theorem denoteArmsP_miss (ρ : SEnv) (v : Val) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm)
    (hm : matchPat p v = none) :
    denoteArmsP ρ v (.mk p g b :: rest) ↔ denoteArmsP ρ v rest := by
  cases g with
  | none => rw [denoteArmsP.eq_2]; simp [hm]
  | some g => rw [denoteArmsP.eq_3]; simp [hm]

/-- 腕の選択と束縛の範囲: 一致したガード付きの腕は `(G → B) ∧ (¬ G → R)`。ガードと本体は束縛 `bs` を足した環境、残りの腕 `R` は **外側の環境 `ρ`**
(この腕の束縛は次の腕に漏れない)。 -/
theorem denoteArmsP_guard (ρ : SEnv) (v : Val) (p : Core.Pat) (g b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) :
    denoteArmsP ρ v (.mk p (some g) b :: rest) ↔
      ((denoteP (ρ.extVals bs) g → denoteP (ρ.extVals bs) b) ∧ (¬ denoteP (ρ.extVals bs) g → denoteArmsP ρ v rest)) := by
  rw [denoteArmsP.eq_3]
  simp [hm]

/-- ガード(Bool の値でも命題でも)が成り立てば本体。 -/
theorem denoteArmsP_guard_true (ρ : SEnv) (v : Val) (p : Core.Pat) (g b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) (hg : denoteP (ρ.extVals bs) g) :
    denoteArmsP ρ v (.mk p (some g) b :: rest) ↔ denoteP (ρ.extVals bs) b := by
  rw [denoteArmsP_guard ρ v p g b rest bs hm]
  simp [hg]

/-- ガードが成り立たなければ残りの腕を外側の環境で。 -/
theorem denoteArmsP_guard_false (ρ : SEnv) (v : Val) (p : Core.Pat) (g b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) (hg : ¬ denoteP (ρ.extVals bs) g) :
    denoteArmsP ρ v (.mk p (some g) b :: rest) ↔ denoteArmsP ρ v rest := by
  rw [denoteArmsP_guard ρ v p g b rest bs hm]
  simp [hg]

theorem denoteQuant_nil (q : Quant) (ρ : SEnv) (k : SEnv → Prop) : denoteQuant q ρ [] k = k ρ := rfl

/-- `forall x: T { … }` の読みは `T` の全要素(`Ty.carrier`)についての `∀`。 -/
theorem denoteQuant_forall_cons (ρ : SEnv) (x : String) (tv : TyV) (t : Ty) (bs : List (String × TyV)) (k : SEnv → Prop)
    (ht : TyV.toTy? tv = some t) :
    denoteQuant .forall_ ρ ((x, tv) :: bs) k = ∀ a : t.carrier, denoteQuant .forall_ (ρ.ext x (.val (Val.of t a))) bs k := by
  simp [denoteQuant, ht]

/-- `exists x: T { … }` の読みは `T` の全要素についての `∃`。 -/
theorem denoteQuant_exists_cons (ρ : SEnv) (x : String) (tv : TyV) (t : Ty) (bs : List (String × TyV)) (k : SEnv → Prop)
    (ht : TyV.toTy? tv = some t) :
    denoteQuant .exists_ ρ ((x, tv) :: bs) k = ∃ a : t.carrier, denoteQuant .exists_ (ρ.ext x (.val (Val.of t a))) bs k := by
  simp [denoteQuant, ht]

/-! ## 値 / 命題の境界(C42 / C43) -/

/-- **値 / 命題の境界(一般形)**: 命題でしか表せない部分(量化・命題に束ねた局所名: `proppyS`)を含まない式(`let`・`if`・`match` を含んでよい)を読むと、
命題の読みは Bool の読み(Model の読み `denoteB`)が `true` であることと同値。生成 Statements が値の形で出す所(`if c = true`、両辺が値の `a = b`)と
命題の形の所を結ぶ。`denoteP.mutual_induct`(式と腕の列を同時に)。 -/
theorem denoteP_iff_denoteB_all :
    (∀ (ρ : SEnv) (e : Core.Expr), proppyS ρ.ctx e = false → (denoteP ρ e ↔ denoteB ρ.vals e = true)) ∧
    (∀ (ρ : SEnv) (v : Val) (arms : List Core.Arm), proppyArms ρ.ctx arms = false →
        (denoteArmsP ρ v arms ↔ denoteArmsB ρ.vals v arms = true)) := by
  apply denoteP.mutual_induct
  -- 1. true
  · intro ρ ty _
    simp [denoteP, denoteB]
  -- 2. false
  · intro ρ ty _
    simp [denoteP, denoteB]
  -- 3. Bool の値の局所名
  · intro ρ x b h _
    simp [denoteP, denoteB, SEnv.vals, h]
  -- 4. 命題の局所名(命題でしか表せない)
  · intro ρ x P h hp
    simp [proppyS_var, SCtx.isProp, SEnv.ctx, h, SVal.ty] at hp
  -- 5. その他の局所名(Nat の値・スコープ外)
  · intro ρ x h1 h2 _
    simp only [denoteP, denoteB, SEnv.vals]
    cases hx : ρ x with
    | none => simp
    | some s =>
      cases s with
      | prop P => exact absurd hx (h2 P)
      | val v =>
        cases v with
        | nat n => simp
        | bool b => exact absurd hx (h1 b)
  -- 6. Nat の let
  · intro ρ x v b ih hp
    simp only [proppyS, Bool.or_eq_false_iff] at hp
    have hΓ : (ρ.ext x (.val (.nat (denoteN ρ.vals v)))).ctx = ρ.ctx.ext x (.val .nat) := by
      rw [SEnv.ctx_ext]; rfl
    simp only [denoteP, denoteB]
    rw [← SEnv.vals_ext_val]
    exact ih (by rw [hΓ]; exact hp.2)
  -- 7. Bool の let、値が命題(命題でしか表せない)
  · intro ρ x v b hpv _ _ hp
    simp [proppyS, hpv] at hp
  -- 8. Bool の let、値が値(`proppyS` は束縛を `.val .nat` で足すので、合同で `.val .bool` の文脈へ)
  · intro ρ x v b hpv ih hp
    simp only [proppyS, Bool.or_eq_false_iff] at hp
    have hΓ : (ρ.ext x (.val (.bool (denoteB ρ.vals v)))).ctx = ρ.ctx.ext x (.val .bool) := by
      rw [SEnv.ctx_ext]; rfl
    have hb : proppyS (ρ.ctx.ext x (.val .bool)) b = false := by
      rw [proppyS_congr (fun y => SCtx.isProp_ext_val ρ.ctx x .bool .nat y)]
      exact hp.2
    simp only [denoteP, denoteB, hpv]
    rw [← SEnv.vals_ext_val]
    exact ih (by rw [hΓ]; exact hb)
  -- 9. let(注釈が対象外)
  · intro ρ x ty v b h1 h2 _
    cases ty with
    | nat => exact (h1 rfl).elim
    | bool => exact (h2 rfl).elim
    | _ => simp [denoteP, denoteB]
  -- 10. if、条件が命題(命題でしか表せない)
  · intro ρ c t e hpc _ _ _ hp
    simp [proppyS, hpc] at hp
  -- 11. if、条件が値で真
  · intro ρ c t e hpc hc ih hp
    simp only [proppyS, Bool.or_eq_false_iff] at hp
    simp only [denoteP, denoteB, hpc, hc, ite_true]
    exact ih hp.1.2
  -- 12. if、条件が値で偽
  · intro ρ c t e hpc hc ih hp
    simp only [proppyS, Bool.or_eq_false_iff] at hp
    simp only [Bool.not_eq_true] at hc
    simp only [denoteP, denoteB, hpc, hc, Bool.false_eq_true, ite_false]
    exact ih hp.2
  -- 13. 論理演算
  · intro ρ op l r ty k hty hk ihl ihr hp
    simp only [proppyS, Bool.or_eq_false_iff] at hp
    simp only [denoteP, denoteB, hk, hty]
    rw [propext (ihl hp.1), propext (ihr hp.2)]
    exact LogicOp.prop_iff k _ _
  -- 14. Nat の == / !=
  · intro ρ op l r ty k hty hk _
    simp only [denoteP, denoteB, hk, hty]
    exact EqOp.propNat_iff_leanNat k _ _
  -- 15. 論理の位置の == / != で、どちらかが命題(命題でしか表せない)
  · intro ρ op l r ty k hty hk hpp _ _ hp
    simp [proppyS, hpp] at hp
  -- 16. 論理の位置の == / != で、両辺が値
  · intro ρ op l r ty k hty hk hpp _
    simp only [denoteP, denoteB, hk, hty, hpp]
    exact EqOp.propBool_iff_leanBool k _ _
  -- 17. Nat の比較
  · intro ρ op l r ty k hty hk _
    simp only [denoteP, denoteB, hk, hty]
    exact CmpOp.propNat_iff k _ _
  -- 18. Bool の比較
  · intro ρ op l r ty k hty hk _
    simp only [denoteP, denoteB, hk, hty]
    exact CmpOp.leanBoolProp_iff_leanBool k _ _
  -- 19. 対象外の二項演算
  · intro ρ op l r ty h1 h2 h3 h4 h5 _
    simp only [denoteP, denoteB]
    cases hk : BinOp.ofString? op with
    | none => simp
    | some k =>
      cases hty : TyV.toTy? ty with
      | none => cases k <;> simp
      | some t =>
        cases k <;> cases t
        all_goals first
          | exact (h1 _ hk hty).elim
          | exact (h2 _ hk hty).elim
          | exact (h3 _ hk hty).elim
          | exact (h4 _ hk hty).elim
          | exact (h5 _ hk hty).elim
          | simp
  -- 20. `!`
  · intro ρ a ih hp
    simp only [proppyS] at hp
    simp only [denoteP, denoteB, ite_true]
    rw [propext (ih hp)]
    simp
  -- 21. 対象外の単項演算子
  · intro ρ op a hne _
    simp [denoteP, denoteB, hne]
  -- 22. Nat の match
  · intro ρ s arms ih hp
    simp only [proppyS, Bool.or_eq_false_iff] at hp
    simp only [denoteP, denoteB]
    exact ih hp.2
  -- 23. Bool の match
  · intro ρ s arms ih hp
    simp only [proppyS, Bool.or_eq_false_iff] at hp
    simp only [denoteP, denoteB]
    exact ih hp.2
  -- 24. match(scrutinee の型が対象外)
  · intro ρ s st arms h1 h2 _
    cases st with
    | nat => exact (h1 rfl).elim
    | bool => exact (h2 rfl).elim
    | _ => simp [denoteP, denoteB]
  -- 25. 量化(命題でしか表せない)
  · intro ρ q bs b _ hp
    simp [proppyS] at hp
  -- 26. 対象外の構文
  · intro e ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 _
    cases e with
    | lit l ty =>
      cases l with
      | bool b =>
        cases b with
        | true => exact (h1 _ rfl).elim
        | false => exact (h2 _ rfl).elim
      | _ => simp [denoteP, denoteB]
    | var x => exact (h3 _ rfl).elim
    | let_ x ty v b => exact (h4 _ _ _ _ rfl).elim
    | ite c t e => exact (h5 _ _ _ rfl).elim
    | binop op l r ty => exact (h6 _ _ _ _ rfl).elim
    | unop op a => exact (h7 _ _ rfl).elim
    | match_ s st arms => exact (h8 _ _ _ rfl).elim
    | quant q bs b => exact (h9 _ _ _ rfl).elim
    | _ => simp [denoteP, denoteB]
  -- 27. 腕の列(空)
  · intro ρ v _
    rw [denoteArmsP.eq_1, denoteArmsB.eq_1]
    simp
  -- 28. 腕(ガード無し、一致): 束縛を足した環境で本体(変数パターンの束縛は合同で `.val .nat` の文脈から)
  · intro ρ v p b rest bs hm ih hp
    rw [proppyArms_cons] at hp
    simp only [Bool.or_eq_false_iff] at hp
    have hb : proppyS (ρ.extVals bs).ctx b = false := by
      rw [SEnv.ctx_extVals]
      cases p with
      | bind x =>
        simp only [matchPat, Option.some.injEq] at hm
        subst hm
        simp only [SCtx.patCtx] at hp
        simp only [List.map_cons, List.map_nil, SCtx.extVals, SCtx.extList]
        rw [proppyS_congr (fun y => SCtx.isProp_ext_val ρ.ctx x v.ty .nat y)]
        exact hp.1.2
      | wild =>
        simp only [matchPat, Option.some.injEq] at hm
        subst hm
        exact hp.1.2
      | lit l =>
        have hbs : bs = [] := by
          cases l <;> cases v <;> simp only [matchPat] at hm <;> (try split at hm) <;> cases hm <;> rfl
        subst hbs
        exact hp.1.2
      | tuple ps => simp [matchPat] at hm
      | builtin n ps => simp [matchPat] at hm
      | variant k vn ps => simp [matchPat] at hm
    rw [denoteArmsP.eq_2, denoteArmsB_cons]
    simp only [hm]
    rw [← SEnv.vals_extVals]
    exact ih hb
  -- 29. 腕(ガード無し、不一致)
  · intro ρ v p b rest hm ih hp
    rw [proppyArms_cons] at hp
    simp only [Bool.or_eq_false_iff] at hp
    rw [denoteArmsP.eq_2, denoteArmsB_cons]
    simp only [hm]
    exact ih hp.2
  -- 30. 腕(ガード付き): 一致しなければ残りの腕、一致すればガードの真偽で本体か残りの腕(外側の環境)
  · intro ρ v p g b rest ihg ihb ihrest hp
    rw [proppyArms_cons] at hp
    simp only [Bool.or_eq_false_iff] at hp
    rw [denoteArmsP.eq_3, denoteArmsB_cons]
    cases hm : matchPat p v with
    | none =>
      simp only []
      rw [propext (ihrest hp.2)]
      simp
    | some bs =>
      have hctx : ∀ e, proppyS (ρ.ctx.patCtx p) e = false → proppyS (ρ.extVals bs).ctx e = false := by
        intro e he
        rw [SEnv.ctx_extVals]
        cases p with
        | bind x =>
          simp only [matchPat, Option.some.injEq] at hm
          subst hm
          simp only [SCtx.patCtx] at he
          simp only [List.map_cons, List.map_nil, SCtx.extVals, SCtx.extList]
          rw [proppyS_congr (fun y => SCtx.isProp_ext_val ρ.ctx x v.ty .nat y)]
          exact he
        | wild =>
          simp only [matchPat, Option.some.injEq] at hm
          subst hm
          exact he
        | lit l =>
          have hbs : bs = [] := by
            cases l <;> cases v <;> simp only [matchPat] at hm <;> (try split at hm) <;> cases hm <;> rfl
          subst hbs
          exact he
        | tuple ps => simp [matchPat] at hm
        | builtin n ps => simp [matchPat] at hm
        | variant k vn ps => simp [matchPat] at hm
      have eg := ihg bs (hctx g hp.1.1)
      have eb := ihb bs (hctx b hp.1.2)
      have er := ihrest hp.2
      rw [SEnv.vals_extVals] at eg eb
      simp only []
      rw [propext eg, propext eb, propext er]
      cases denoteB (ρ.vals.extList bs) g <;> simp

/-- **値 / 命題の境界**(任意の環境・任意の `proppyS` が偽の式)。 -/
theorem denoteP_iff_denoteB_noProp (e : Core.Expr) (ρ : SEnv) (hp : proppyS ρ.ctx e = false) :
    denoteP ρ e ↔ denoteB ρ.vals e = true :=
  denoteP_iff_denoteB_all.1 ρ e hp

/-- 基礎段階(C42)の形: 基礎の式を命題の束縛の無い環境で読む場合(一般形の系)。 -/
theorem denoteP_iff_denoteB (e : Core.Expr) (hb : basic e = true) (ρ : SEnv) (hΓ : ρ.ctx.NoProp) :
    denoteP ρ e ↔ denoteB ρ.vals e = true :=
  denoteP_iff_denoteB_noProp e ρ (basic_not_proppy e hb ρ.ctx hΓ)

/-! ## 網羅性と量化の束縛の非空を要求しない型付け(帰納法の仮定のため) -/

/-- `wtS` から `match` の網羅性と量化の束縛の非空の要求を除いた型付け。`Sem` の導出があるとき、残りの腕(それだけでは網羅的でない)と量化の束縛の
末尾(空)にも同値定理の帰納法の仮定を使うための仮定で、保証の前提は `wtS`(`wtS_noExh` で写す)。 -/
def wtSNoExh (Γ : SCtx) : Core.Expr → Option STy
  | .match_ s st arms =>
    match wtR Γ.vals s, TyV.toTy? st with
    | some ts, some ta => if ts = ta then wtArmsS Γ ts arms else none
    | _, _ => none
  | .quant _ bs b =>
    match Γ.extBinders bs with
    | some Γ' =>
      match wtS Γ' b with
      | some t => if t.isForm then some .prop else none
      | none => none
    | none => none
  | e => wtS Γ e

theorem wtS_noExh {Γ : SCtx} {e : Core.Expr} {τ : STy} (h : wtS Γ e = some τ) : wtSNoExh Γ e = some τ := by
  cases e with
  | match_ s st arms =>
    simp only [wtS] at h
    simp only [wtSNoExh]
    cases hs : wtR Γ.vals s with
    | none => simp [hs] at h
    | some ts =>
      cases hta : TyV.toTy? st with
      | none => simp [hs, hta] at h
      | some ta =>
        simp only [hs, hta] at h ⊢
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨hts, _⟩ := hc
          subst hts
          simp [h]
        · cases h
  | quant q bs b =>
    simp only [wtS] at h
    simp only [wtSNoExh]
    cases bs with
    | nil => cases h
    | cons xt rest => exact h
  | _ => exact h

/-- 腕の列の先頭の腕は適格。 -/
theorem wtArmsS_head {Γ : SCtx} {ts : Ty} {arm : Core.Arm} {rest : List Core.Arm} {τ : STy}
    (h : wtArmsS Γ ts (arm :: rest) = some τ) : ∃ t1, wtArmS Γ ts arm = some t1 := by
  rw [wtArmsS.eq_def] at h
  cases h1 : wtArmS Γ ts arm with
  | none => simp [h1] at h
  | some t1 => exact ⟨t1, rfl⟩

/-- 腕の列の残り(空でなければ)は適格。 -/
theorem wtArmsS_tail {Γ : SCtx} {ts : Ty} {arm a2 : Core.Arm} {rest : List Core.Arm} {τ : STy}
    (h : wtArmsS Γ ts (arm :: a2 :: rest) = some τ) : ∃ t2, wtArmsS Γ ts (a2 :: rest) = some t2 := by
  rw [wtArmsS.eq_def] at h
  cases h1 : wtArmS Γ ts arm with
  | none => simp [h1] at h
  | some t1 =>
    simp only [h1] at h
    cases h2 : wtArmsS Γ ts (a2 :: rest) with
    | none => simp [h2] at h
    | some t2 => exact ⟨t2, rfl⟩

/-! ## 一般定理(C42 / C43) -/

/-- 適格な式について、独立意味論の命題は Lean での読みの命題と同値(`Sem` の導出の帰納法。値の位置は Model の保存 `preserve_nat` / `preserve_bool` /
`denote_sound` で読みの値に、Bool の値の条件・両辺が値の `==` は境界 `denoteP_iff_denoteB_noProp` で、命題の `let` は命題外延性で環境を揃え、
`match` は腕の選択と束縛の形、量化は束縛ごとの同値で結ぶ)。 -/
theorem Sem_denote_all {ρ : SEnv} {e : Core.Expr} {P : Prop} (h : Sem ρ e P) :
    ∀ τ, wtSNoExh ρ.ctx e = some τ → (P ↔ denoteP ρ e) := by
  induction h with
  | @lit ρ b =>
    intro τ _
    cases b <;> simp [denoteP]
  | @varVal ρ x b h =>
    intro τ _
    simp [denoteP, h]
  | @varProp ρ x P h =>
    intro τ _
    simp [denoteP, h]
  | @logic ρ op k l r P Q hk hl hr ihl ihr =>
    intro τ hw
    replace hw : wtS ρ.ctx (.binop op l r .bool) = some τ := hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtS ρ.ctx l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtS ρ.ctx r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        have el := ihl tl (wtS_noExh hwl)
        have er := ihr tr (wtS_noExh hwr)
        simp only [denoteP, hk, TyV.toTy?]
        cases k <;> simp [LogicOp.prop, el, er]
  | @eqNat ρ op k l r a b hk hl hr =>
    intro τ hw
    replace hw : wtS ρ.ctx (.binop op l r .nat) = some τ := hw
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
    intro τ hw
    replace hw : wtS ρ.ctx (.binop op l r .bool) = some τ := hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtS ρ.ctx l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtS ρ.ctx r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        have el := ihl tl (wtS_noExh hwl)
        have er := ihr tr (wtS_noExh hwr)
        simp only [denoteP, hk, TyV.toTy?]
        cases hpp : (proppyS ρ.ctx l || proppyS ρ.ctx r)
        · -- 両辺が値: 値の等値(境界で命題の同値と結ぶ)
          simp only [Bool.or_eq_false_iff] at hpp
          have bl := denoteP_iff_denoteB_noProp l ρ hpp.1
          have br := denoteP_iff_denoteB_noProp r ρ hpp.2
          simp only []
          rw [propext el, propext bl, propext er, propext br]
          exact EqOp.propIff_bool k _ _
        · -- どちらかが命題: 命題の同値とその否定
          simp only []
          rw [propext el, propext er]
  | @cmpNat ρ op k l r a b hk hl hr =>
    intro τ hw
    replace hw : wtS ρ.ctx (.binop op l r .nat) = some τ := hw
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
    intro τ hw
    replace hw : wtS ρ.ctx (.binop op l r .bool) = some τ := hw
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
    intro τ hw
    replace hw : wtS ρ.ctx (.unop "!" a) = some τ := hw
    simp only [wtS, ite_true] at hw
    cases hwa : wtS ρ.ctx a with
    | none => simp [hwa] at hw
    | some ta =>
      have ea := ih ta (wtS_noExh hwa)
      simp only [denoteP, ite_true]
      rw [propext ea]
  | @ite ρ c t e C P Q hc ht he ihc iht ihe =>
    intro τ hw
    replace hw : wtS ρ.ctx (.ite c t e) = some τ := hw
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
          have ec := ihc tc (wtS_noExh hwc)
          have et := iht tt (wtS_noExh hwt)
          have ee := ihe te (wtS_noExh hwe)
          simp only [denoteP]
          cases hpc : proppyS ρ.ctx c
          · -- Bool の値の条件: `if c = true then … else …`(境界で `(C → P) ∧ (¬ C → Q)` と結ぶ)
            have bc := denoteP_iff_denoteB_noProp c ρ hpc
            simp only []
            rw [propext ec, propext bc, propext et, propext ee]
            cases denoteB ρ.vals c <;> simp
          · -- 命題の条件: 同じ形
            simp only []
            rw [propext ec, propext et, propext ee]
  | @letNat ρ x v b n Q hv hb ihb =>
    intro τ hw
    replace hw : wtS ρ.ctx (.let_ x .nat v b) = some τ := hw
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
        have := ihb τ (by rw [hΓ']; exact wtS_noExh hw)
        simpa [denoteP] using this
  | @letBoolVal ρ x v b w Q hp hv hb ihb =>
    intro τ hw
    replace hw : wtS ρ.ctx (.let_ x .bool v b) = some τ := hw
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
        have := ihb τ (by rw [hΓ']; exact wtS_noExh hw)
        simpa [denoteP, hp] using this
  | @letProp ρ x v b P Q hp hv hb ihv ihb =>
    -- 命題の `let`: 値の意味 `P` と読み `denoteP ρ v` は同値 → 命題外延性で環境を揃える
    intro τ hw
    replace hw : wtS ρ.ctx (.let_ x .bool v b) = some τ := hw
    simp only [wtS, TyV.toTy?, hp, ite_true] at hw
    cases hwv : wtS ρ.ctx v with
    | none => simp [hwv] at hw
    | some tv =>
      cases tv with
      | val t => simp [hwv] at hw
      | prop =>
        simp only [hwv] at hw
        have ev := ihv .prop (wtS_noExh hwv)
        have hΓ' : (ρ.ext x (.prop P)).ctx = ρ.ctx.ext x .prop := by
          rw [SEnv.ctx_ext]
          rfl
        have eb := ihb τ (by rw [hΓ']; exact wtS_noExh hw)
        simp only [denoteP, hp]
        rw [propext ev] at eb
        exact eb
  | @matchSkip ρ s st p g b rest v P hs hp hr ihr =>
    -- 先頭の腕が一致しない: 残りの腕(外側の環境)。残りは単独では網羅的でなくてよい(`wtSNoExh`)
    intro τ hw
    simp only [wtSNoExh] at hw
    cases hws : wtR ρ.ctx.vals s with
    | none => simp [hws] at hw
    | some ts =>
      cases hst : TyV.toTy? st with
      | none => simp [hws, hst] at hw
      | some ta =>
        simp only [hws, hst] at hw
        split at hw
        · rename_i hts
          subst hts
          cases rest with
          | nil => cases hr
          | cons a2 rest2 =>
            obtain ⟨t2, hw2⟩ := wtArmsS_tail hw
            have er := ihr t2 (by simp [wtSNoExh, hws, hst, hw2])
            have pv := denote_sound hws ρ.vals (SEnv.ctx_vals ρ)
            rw [hs] at pv
            cases pv
            rw [er]
            cases ts <;> cases st <;> simp [TyV.toTy?] at hst
            all_goals
              simp only [denoteP]
              simp only [denoteV] at hp
              cases g <;> first
                | (rw [denoteArmsP.eq_2]; simp [hp])
                | (rw [denoteArmsP.eq_3]; simp [hp])
        · cases hw
  | @matchHit ρ s st p b rest v bs P hs hp hb ihb =>
    -- ガード無しの腕が一致: 束縛を足した環境で本体
    intro τ hw
    simp only [wtSNoExh] at hw
    cases hws : wtR ρ.ctx.vals s with
    | none => simp [hws] at hw
    | some ts =>
      cases hst : TyV.toTy? st with
      | none => simp [hws, hst] at hw
      | some ta =>
        simp only [hws, hst] at hw
        split at hw
        · rename_i hts
          subst hts
          obtain ⟨t1, hw1⟩ := wtArmsS_head hw
          rw [wtArmS_mk] at hw1
          cases hpat : wtPat ts p with
          | none => simp [hpat] at hw1
          | some bts =>
            simp only [hpat] at hw1
            cases hwb : wtS (ρ.ctx.extVals bts) b with
            | none => simp [hwb] at hw1
            | some tb =>
              have pv := denote_sound hws ρ.vals (SEnv.ctx_vals ρ)
              rw [hs] at pv
              cases pv
              have hv : (denoteV ρ.vals ts s).ty = ts := denoteV_ty ρ.vals ts s
              have hΓ' : (ρ.extVals bs).ctx = ρ.ctx.extVals bts := by
                rw [SEnv.ctx_extVals, matchPat_types hpat hv hp]
              have eb := ihb tb (by rw [hΓ']; exact wtS_noExh hwb)
              rw [eb]
              cases ts <;> cases st <;> simp [TyV.toTy?] at hst
              all_goals
                simp only [denoteP]
                simp only [denoteV] at hp
                rw [denoteArmsP.eq_2]
                simp [hp]
        · cases hw
  | @matchGuard ρ s st p g b rest v bs G P R hs hp hg hb hr ihg ihb ihr =>
    -- ガード付きの腕が一致: `(G → B) ∧ (¬ G → R)`。ガードと本体は束縛を足した環境、残りの腕は外側の環境
    intro τ hw
    simp only [wtSNoExh] at hw
    cases hws : wtR ρ.ctx.vals s with
    | none => simp [hws] at hw
    | some ts =>
      cases hst : TyV.toTy? st with
      | none => simp [hws, hst] at hw
      | some ta =>
        simp only [hws, hst] at hw
        split at hw
        · rename_i hts
          subst hts
          obtain ⟨t1, hw1⟩ := wtArmsS_head hw
          rw [wtArmS_mk] at hw1
          cases hpat : wtPat ts p with
          | none => simp [hpat] at hw1
          | some bts =>
            simp only [hpat] at hw1
            cases hwg : wtS (ρ.ctx.extVals bts) g with
            | none => simp [hwg] at hw1
            | some tg =>
              cases hwb : wtS (ρ.ctx.extVals bts) b with
              | none => simp [hwg, hwb] at hw1
              | some tb =>
                cases rest with
                | nil => cases hr
                | cons a2 rest2 =>
                  obtain ⟨t2, hw2⟩ := wtArmsS_tail hw
                  have er := ihr t2 (by simp [wtSNoExh, hws, hst, hw2])
                  have pv := denote_sound hws ρ.vals (SEnv.ctx_vals ρ)
                  rw [hs] at pv
                  cases pv
                  have hv : (denoteV ρ.vals ts s).ty = ts := denoteV_ty ρ.vals ts s
                  have hΓ' : (ρ.extVals bs).ctx = ρ.ctx.extVals bts := by
                    rw [SEnv.ctx_extVals, matchPat_types hpat hv hp]
                  have eg := ihg tg (by rw [hΓ']; exact wtS_noExh hwg)
                  have eb := ihb tb (by rw [hΓ']; exact wtS_noExh hwb)
                  rw [propext eg, propext eb, propext er]
                  cases ts <;> cases st <;> simp [TyV.toTy?] at hst
                  all_goals
                    simp only [denoteP]
                    simp only [denoteV] at hp
                    rw [denoteArmsP.eq_3]
                    simp [hp]
        · cases hw
  | @quantNil ρ q b P h ih =>
    intro τ hw
    simp only [wtSNoExh, SCtx.extBinders] at hw
    cases hwb : wtS ρ.ctx b with
    | none => simp [hwb] at hw
    | some t =>
      have := ih t (wtS_noExh hwb)
      simpa [denoteP, denoteQuant] using this
  | @forallCons ρ x tv t bs b F ht h ih =>
    -- `T` の全要素 `a` について、束縛を足した環境での同値を `∀` で束ねる
    intro τ hw
    simp only [wtSNoExh, SCtx.extBinders, ht] at hw
    have hw' : ∀ a : t.carrier, wtSNoExh (ρ.ext x (.val (Val.of t a))).ctx (.quant .forall_ bs b) = some τ := by
      intro a
      rw [SEnv.ctx_ext]
      simp only [SVal.ty, Val.ty_of]
      simp only [wtSNoExh]
      exact hw
    simp only [denoteP, denoteQuant, ht]
    exact forall_congr' fun a => (ih a τ (hw' a)).trans (by simp only [denoteP])
  | @existsCons ρ x tv t bs b F ht h ih =>
    intro τ hw
    simp only [wtSNoExh, SCtx.extBinders, ht] at hw
    have hw' : ∀ a : t.carrier, wtSNoExh (ρ.ext x (.val (Val.of t a))).ctx (.quant .exists_ bs b) = some τ := by
      intro a
      rw [SEnv.ctx_ext]
      simp only [SVal.ty, Val.ty_of]
      simp only [wtSNoExh]
      exact hw
    simp only [denoteP, denoteQuant, ht]
    exact exists_congr fun a => (ih a τ (hw' a)).trans (by simp only [denoteP])

/-- **Statements の保存(C42 / C43)**: 文脈で適格な spec の式(リテラル・局所名(値 / 命題)・Bool / 命題の `let` と shadowing・Bool / 命題の条件の `if`・
論理・比較・等値(値の `==` と命題の `↔`)・`!`・Nat / Bool の `forall` / `exists`・非再帰の Nat / Bool のガード付き `match`)は、対応する環境で、
独立意味論の命題と Lean での読みの命題が同値(両方向)。 -/
theorem Sem_denote {Γ : SCtx} {e : Core.Expr} {τ : STy} (hw : wtS Γ e = some τ) (ρ : SEnv) (hρ : Γ = ρ.ctx)
    {P : Prop} (h : Sem ρ e P) : P ↔ denoteP ρ e :=
  Sem_denote_all h τ (wtS_noExh (hρ ▸ hw))

/-- 基礎段階(C42)の形(一般定理の系): 基礎の式と命題の束縛の無い文脈。 -/
theorem Sem_denote_basic {Γ : SCtx} {e : Core.Expr} {τ : STy} (hw : wtS Γ e = some τ) (_hb : basic e = true) (_hΓ : Γ.NoProp)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) {P : Prop} (h : Sem ρ e P) : P ↔ denoteP ρ e :=
  Sem_denote hw ρ hρ h

/-- 読みは意味である: 適格な式の意味(存在は `Sem_exists`)は読みの命題そのもの(命題外延性)。 -/
theorem Sem_denoteP {Γ : SCtx} {e : Core.Expr} {τ : STy} (hw : wtS Γ e = some τ) (hf : τ.isForm = true)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) : Sem ρ e (denoteP ρ e) := by
  obtain ⟨P, hP⟩ := Sem_exists hw hf ρ hρ
  rw [propext (Sem_denote hw ρ hρ hP)] at hP
  exact hP

/-! ## 実生成宣言への接続(C44) -/

/-- **接続検査の健全性(命題)**: 仮引数の値 `xs` の環境で適格な spec の式 `e` について、実生成宣言の命題 `Q` が読みと等しい(各宣言の接続検査が
確かめる `Prop` の等式)なら、`Q` は独立意味論の意味そのもの(`Sem … e Q`。読みの命題と同値な意味が存在し、命題外延性でそれは `Q`)。 -/
theorem check_sound_prop (xs : List (String × Val)) {e : Core.Expr} {τ : STy}
    (h : wtS (SCtx.ofList (xs.map fun p => (p.1, STy.val p.2.ty))) e = some τ) (hf : τ.isForm = true)
    {Q : Prop} (hq : Q = denoteP (SEnv.ofList (xs.map fun p => (p.1, SVal.val p.2))) e) :
    Sem (SEnv.ofList (xs.map fun p => (p.1, SVal.val p.2))) e Q := by
  subst hq
  apply Sem_denoteP h hf
  rw [SEnv.ctx_ofList, List.map_map]
  rfl

end NaruSem
