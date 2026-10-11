import NaruSem.CallTotality
import NaruSem.Denote

/-!
# 関数・input を含む Model の保存と実生成宣言への接続(IDEAL.md C55 / C56 / C57、runtime)

`Call.lean` の Core(呼出しを含む)について、生成 Model(`Backend.Model.emitE` が書く Lean。呼出しは実生成の呼出し先の定数への適用、input は
関数の先頭の引数)の意味を、backend の文字列とは独立に Core から直接定めた **Lean での読み** `denoteN` / `denoteB`(+ 実引数の列 `denoteArgs`、
腕の列 `denoteArmsN` / `denoteArmsB`)で表す。`Denote.lean` の読みに `.call k args` の場合を加えたもの: 署名の文脈 `Δ` から仮引数の型を取り、
実引数をその型で読んだ値の列を、関数環境 `Φ` の鍵 `k` の関数に渡し、結果の値を取り出す(鍵・関数・結果が無ければ既定値。一般定理は適格な式にだけ
対応を主張する)。

- **一般定理 `denote_sound`**: 署名 `Δ` と文脈 `Γ` で適格な式 `e` と対応する局所環境 `ρ`(`Γ = ρ.ty`)について、独立意味論 `eval Φ ρ e` の結果は
  読み `denoteV Δ' Φ' ρ t e` の値。読みの側の環境 `Φ'`(実生成定数の環境)は型付けの側の環境 `Φ`(宣言群の意味 `interp`)と **署名の鍵で一致**すれば
  よい(`FEnv.Agree Φ Φ' Δ`: fn / input の鍵には両方に関数があり、型の合う実引数に同じ結果を返す)。読みの署名 `Δ'` は型付けの署名を含めばよい
  (`SigEnv.SubV Δ Δ'`)。`Φ = Φ'` の形は系 `denote_sound_self`。翻訳の正しさも呼出し先の正しさも仮定しない(呼出し先の値は環境の関数の結果)。
- **実生成定数の環境**: 実生成の fn / input は Lean の関数(カリー化。`Fn ps t`)で、`wrap ps t g` が値の列の上の関数に包む(型の合う実引数には
  `some` の値、合わなければ `none`。`wrap_respects`: 署名を守る)。実生成宣言の表 `Gen`(鍵・fn / input・仮引数の型・戻り型・関数。input の引数は適用済み)
  から関数環境 `FEnv.ofGens` と署名 `SigEnv.ofShapes` を作る(`ofGens_respects`: 表から作った環境は表の署名を守る)。
- **宣言群の意味と実生成定数の一致 `interp_agree`**: 適格な宣言群 `P`、input の署名を守る任意の解釈 `I`、実生成定数の環境 `Φ'` について、
  (a) `Φ'` が署名を守り、(b) input の鍵で `I` と `Φ'` が同じ(`SameInputs`: 同じ input 解釈)、(c) 各 fn に接続の証拠(`Evidence`: 型の合う任意の実引数で
  実生成定数の値 = 仮引数に実引数を束ねた環境での本体の読み。`FnConn`)があれば、宣言群の意味 `(interp I P).Φ` は `Φ'` と署名の鍵で一致する。
  証明は宣言群の帰納法: 各 fn の本体の `eval` を、それより前の宣言の意味と `Φ'` の一致(帰納法の仮定)と `denote_sound` で実生成定数の値に結び、
  呼出し先の証拠を呼出し側へ合成する。系 `fn_value`: 各 fn の意味は型の合う任意の実引数で実生成定数の値。
- **接続の証拠の形**: 実生成宣言ごとの検査は `conn_<f> : ∀ args, Model.M.f inputs args = denoteN Δ' Φ' (Env.ofList …) core_f`(kernel の定義的等しさ。
  `Curried` の形)で、`fnConn_of_curried` が `FnConn` に写す。`SubV_of_cover`: 宣言群の各 fn / input の署名が表にあれば `wtProg` の署名を含む。

採用方式(「コンパイラ意味論保存の保証方式」): 汎用翻訳方式(一般定理 `denote_sound` / `interp_agree`)+ 生成物ごとの接続検査(`conn_<f>`)。
保証は「接続検査に成功した実生成宣言」の宣言群に対するもので、呼出し先を含む必要な証拠が欠けた宣言は検証済みにならない。spec の式の読みと一般同値は `CallDenoteProp.lean`。
宣言群の spec 合成は `CallComposeProp.lean`。Surface AST からの合成は未完了。
-/

namespace NaruSem.Call
open Naru

/-! ## 生成 Lean の読み(呼出しを含む) -/

mutual

/-- Nat の式の読み: `Denote.lean` の `denoteN` に呼出しを加えたもの。`.call k args` は、署名 `Δ` の仮引数の型で実引数を読んだ値の列を関数環境 `Φ` の
鍵 `k` の関数に渡し、Nat の結果を取り出す(無ければ既定値 0)。 -/
def denoteN (Δ : SigEnv) (Φ : FEnv) (ρ : Env) : Core.Expr → Nat
  | .lit (.nat n) _ => n
  | .var x => match ρ x with | some (.nat n) => n | _ => 0
  | .call k args =>
    match valueSig? Δ k, Φ k with
    | some (ps, _), some f =>
      match f (denoteArgs Δ Φ ρ args ps) with
      | some (.nat n) => n
      | _ => 0
    | _, _ => 0
  | .let_ x ty v b =>
    match ty with
    | .nat => denoteN Δ Φ (ρ.ext x (.nat (denoteN Δ Φ ρ v))) b
    | .bool => denoteN Δ Φ (ρ.ext x (.bool (denoteB Δ Φ ρ v))) b
    | _ => 0
  | .ite c t e => if denoteB Δ Φ ρ c then denoteN Δ Φ ρ t else denoteN Δ Φ ρ e
  | .binop op l r ty =>
    match BinOp.ofString? op, TyV.toTy? ty with
    | some (.arith k), some .nat => k.eval (denoteN Δ Φ ρ l) (denoteN Δ Φ ρ r)
    | _, _ => 0
  | .method tn m r [a] _ =>
    if tn = "Nat" then
      match NatMethod.ofString? m with
      | some k => k.eval (denoteN Δ Φ ρ r) (denoteN Δ Φ ρ a)
      | none => 0
    else 0
  | .match_ s st arms =>
    match st with
    | .nat => denoteArmsN Δ Φ ρ (.nat (denoteN Δ Φ ρ s)) arms
    | .bool => denoteArmsN Δ Φ ρ (.bool (denoteB Δ Φ ρ s)) arms
    | _ => 0
  | _ => 0

/-- Bool の式の読み。既定値は `false`。 -/
def denoteB (Δ : SigEnv) (Φ : FEnv) (ρ : Env) : Core.Expr → Bool
  | .lit (.bool b) _ => b
  | .var x => match ρ x with | some (.bool b) => b | _ => false
  | .call k args =>
    match valueSig? Δ k, Φ k with
    | some (ps, _), some f =>
      match f (denoteArgs Δ Φ ρ args ps) with
      | some (.bool b) => b
      | _ => false
    | _, _ => false
  | .let_ x ty v b =>
    match ty with
    | .nat => denoteB Δ Φ (ρ.ext x (.nat (denoteN Δ Φ ρ v))) b
    | .bool => denoteB Δ Φ (ρ.ext x (.bool (denoteB Δ Φ ρ v))) b
    | _ => false
  | .ite c t e => if denoteB Δ Φ ρ c then denoteB Δ Φ ρ t else denoteB Δ Φ ρ e
  | .binop op l r ty =>
    match BinOp.ofString? op, TyV.toTy? ty with
    | some (.cmp k), some .nat => k.evalNat (denoteN Δ Φ ρ l) (denoteN Δ Φ ρ r)
    | some (.cmp k), some .bool => k.leanBool (denoteB Δ Φ ρ l) (denoteB Δ Φ ρ r)
    | some (.eq k), some .nat => k.leanNat (denoteN Δ Φ ρ l) (denoteN Δ Φ ρ r)
    | some (.eq k), some .bool => k.leanBool (denoteB Δ Φ ρ l) (denoteB Δ Φ ρ r)
    | some (.logic k), some .bool => k.eval (denoteB Δ Φ ρ l) (denoteB Δ Φ ρ r)
    | _, _ => false
  | .unop op a => if op = "!" then !denoteB Δ Φ ρ a else false
  | .match_ s st arms =>
    match st with
    | .nat => denoteArmsB Δ Φ ρ (.nat (denoteN Δ Φ ρ s)) arms
    | .bool => denoteArmsB Δ Φ ρ (.bool (denoteB Δ Φ ρ s)) arms
    | _ => false
  | _ => false

/-- 実引数の列の読み: 仮引数の型の列に従って順に Nat / Bool の値に。数が合わない残りは落とす(適格なら合う)。 -/
def denoteArgs (Δ : SigEnv) (Φ : FEnv) (ρ : Env) : List Core.Expr → List Ty → List Val
  | a :: as, .nat :: ts => .nat (denoteN Δ Φ ρ a) :: denoteArgs Δ Φ ρ as ts
  | a :: as, .bool :: ts => .bool (denoteB Δ Φ ρ a) :: denoteArgs Δ Φ ρ as ts
  | _, _ => []

/-- 腕の列の読み(Nat の本体)。`Denote.lean` の `denoteArmsN` と同じ形(束縛はその腕のガードと本体だけ、`rest` は外側の環境)。 -/
def denoteArmsN (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (v : Val) : List Core.Arm → Nat
  | [] => 0
  | .mk p g b :: rest =>
    match matchPat p v with
    | none => denoteArmsN Δ Φ ρ v rest
    | some bs =>
      match g with
      | none => denoteN Δ Φ (ρ.extList bs) b
      | some g =>
        match (if denoteB Δ Φ (ρ.extList bs) g then some (denoteN Δ Φ (ρ.extList bs) b) else none) with
        | some g' => g'
        | none => denoteArmsN Δ Φ ρ v rest

/-- 腕の列の読み(Bool の本体)。 -/
def denoteArmsB (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (v : Val) : List Core.Arm → Bool
  | [] => false
  | .mk p g b :: rest =>
    match matchPat p v with
    | none => denoteArmsB Δ Φ ρ v rest
    | some bs =>
      match g with
      | none => denoteB Δ Φ (ρ.extList bs) b
      | some g =>
        match (if denoteB Δ Φ (ρ.extList bs) g then some (denoteB Δ Φ (ρ.extList bs) b) else none) with
        | some g' => g'
        | none => denoteArmsB Δ Φ ρ v rest

end

/-- 型ごとの読みを値に包む。 -/
def denoteV (Δ : SigEnv) (Φ : FEnv) (ρ : Env) : Ty → Core.Expr → Val
  | .nat, e => .nat (denoteN Δ Φ ρ e)
  | .bool, e => .bool (denoteB Δ Φ ρ e)

/-- 型ごとの読み(型の担い手の値)。 -/
def denoteT (Δ : SigEnv) (Φ : FEnv) (ρ : Env) : (t : Ty) → Core.Expr → t.carrier
  | .nat, e => denoteN Δ Φ ρ e
  | .bool, e => denoteB Δ Φ ρ e

/-- 腕の列の読みを値に包む。 -/
def denoteArmsV (Δ : SigEnv) (Φ : FEnv) (ρ : Env) : Ty → Val → List Core.Arm → Val
  | .nat, v, arms => .nat (denoteArmsN Δ Φ ρ v arms)
  | .bool, v, arms => .bool (denoteArmsB Δ Φ ρ v arms)

@[simp] theorem denoteV_ty (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (t : Ty) (e : Core.Expr) : (denoteV Δ Φ ρ t e).ty = t := by
  cases t <;> rfl

@[simp] theorem denoteArmsV_ty (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (t : Ty) (v : Val) (arms : List Core.Arm) :
    (denoteArmsV Δ Φ ρ t v arms).ty = t := by
  cases t <;> rfl

theorem Val.of_denoteT (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (t : Ty) (e : Core.Expr) : Val.of t (denoteT Δ Φ ρ t e) = denoteV Δ Φ ρ t e := by
  cases t <;> rfl

/-! ## 展開の補題 -/

theorem denoteArgs_nil (Δ : SigEnv) (Φ : FEnv) (ρ : Env) : denoteArgs Δ Φ ρ [] [] = [] := by
  rw [denoteArgs.eq_def]

theorem denoteArgs_cons (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (a : Core.Expr) (as : List Core.Expr) (t : Ty) (ts : List Ty) :
    denoteArgs Δ Φ ρ (a :: as) (t :: ts) = denoteV Δ Φ ρ t a :: denoteArgs Δ Φ ρ as ts := by
  cases t
  · exact denoteArgs.eq_1 Δ Φ ρ a as ts
  · exact denoteArgs.eq_2 Δ Φ ρ a as ts

theorem denoteArmsN_cons (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (v : Val) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm) :
    denoteArmsN Δ Φ ρ v (.mk p g b :: rest) =
      match matchPat p v with
      | none => denoteArmsN Δ Φ ρ v rest
      | some bs =>
        match g with
        | none => denoteN Δ Φ (ρ.extList bs) b
        | some g =>
          match (if denoteB Δ Φ (ρ.extList bs) g then some (denoteN Δ Φ (ρ.extList bs) b) else none) with
          | some g' => g'
          | none => denoteArmsN Δ Φ ρ v rest :=
  denoteArmsN.eq_2 Δ Φ ρ v p g b rest

theorem denoteArmsB_cons (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (v : Val) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm) :
    denoteArmsB Δ Φ ρ v (.mk p g b :: rest) =
      match matchPat p v with
      | none => denoteArmsB Δ Φ ρ v rest
      | some bs =>
        match g with
        | none => denoteB Δ Φ (ρ.extList bs) b
        | some g =>
          match (if denoteB Δ Φ (ρ.extList bs) g then some (denoteB Δ Φ (ρ.extList bs) b) else none) with
          | some g' => g'
          | none => denoteArmsB Δ Φ ρ v rest :=
  denoteArmsB.eq_2 Δ Φ ρ v p g b rest

/-! ## 腕の選択と束縛 -/

theorem denoteArmsV_hit (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (t : Ty) (v : Val) (p : Core.Pat) (b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) :
    denoteArmsV Δ Φ ρ t v (.mk p none b :: rest) = denoteV Δ Φ (ρ.extList bs) t b := by
  cases t <;> simp [denoteArmsV, denoteArmsN_cons, denoteArmsB_cons, hm, denoteV]

theorem denoteArmsV_miss (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (t : Ty) (v : Val) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr)
    (rest : List Core.Arm) (hm : matchPat p v = none) :
    denoteArmsV Δ Φ ρ t v (.mk p g b :: rest) = denoteArmsV Δ Φ ρ t v rest := by
  cases t <;> simp [denoteArmsV, denoteArmsN_cons, denoteArmsB_cons, hm]

theorem denoteArmsV_guard_true (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (t : Ty) (v : Val) (p : Core.Pat) (g b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) (hg : denoteB Δ Φ (ρ.extList bs) g = true) :
    denoteArmsV Δ Φ ρ t v (.mk p (some g) b :: rest) = denoteV Δ Φ (ρ.extList bs) t b := by
  cases t <;> simp [denoteArmsV, denoteArmsN_cons, denoteArmsB_cons, hm, hg, denoteV]

theorem denoteArmsV_guard_false (Δ : SigEnv) (Φ : FEnv) (ρ : Env) (t : Ty) (v : Val) (p : Core.Pat) (g b : Core.Expr) (rest : List Core.Arm)
    (bs : List (String × Val)) (hm : matchPat p v = some bs) (hg : denoteB Δ Φ (ρ.extList bs) g = false) :
    denoteArmsV Δ Φ ρ t v (.mk p (some g) b :: rest) = denoteArmsV Δ Φ ρ t v rest := by
  cases t <;> simp [denoteArmsV, denoteArmsN_cons, denoteArmsB_cons, hm, hg]

/-! ## 環境と署名の対応 -/

/-- 2 つの関数環境が署名の鍵で一致する: fn / input の署名のある鍵には両方に関数があり、型の合う実引数に同じ結果を返す。
`interp` の意味(呼出し先の本体を評価する閉包)と実生成定数の環境の対応に使う。 -/
def FEnv.Agree (Φ Φ' : FEnv) (Δ : SigEnv) : Prop :=
  ∀ k ps t, valueSig? Δ k = some (ps, t) →
    ∃ f f', Φ k = some f ∧ Φ' k = some f' ∧ ∀ vs : List Val, vs.map Val.ty = ps → f vs = f' vs

/-- 署名の文脈の包含(fn / input の署名について)。 -/
def SigEnv.SubV (Δ Δ' : SigEnv) : Prop :=
  ∀ k ps t, valueSig? Δ k = some (ps, t) → valueSig? Δ' k = some (ps, t)

theorem SigEnv.SubV.refl (Δ : SigEnv) : SigEnv.SubV Δ Δ := fun _ _ _ h => h

/-- 署名を守る環境は自分自身と一致する。 -/
theorem FEnv.Agree.refl {Φ : FEnv} {Δ : SigEnv} (h : Φ.Respects Δ) : FEnv.Agree Φ Φ Δ := by
  intro k ps t hk
  obtain ⟨f, hf, _⟩ := h k ps t hk
  exact ⟨f, f, hf, hf, fun _ _ => rfl⟩

/-- 署名を守る環境と署名の鍵で一致する環境は署名を守る。 -/
theorem FEnv.Agree.respects {Φ Φ' : FEnv} {Δ Δ' : SigEnv} (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hA : FEnv.Agree Φ Φ' Δ) :
    Φ.Respects Δ := by
  intro k ps t hk
  obtain ⟨f, f', hf, hf', hag⟩ := hA k ps t hk
  obtain ⟨f'', hf'', hfv⟩ := hΦ' k ps t (hΔ k ps t hk)
  rw [hf'] at hf''
  cases hf''
  refine ⟨f, hf, fun vs hvs => ?_⟩
  rw [hag vs hvs]
  exact hfv vs hvs

/-- 包含の下で署名を守ることは保たれる(小さい署名でも守る)。 -/
theorem FEnv.Respects.mono {Φ : FEnv} {Δ Δ' : SigEnv} (hΔ : SigEnv.SubV Δ Δ') (h : Φ.Respects Δ') : Φ.Respects Δ :=
  fun k ps t hk => h k ps t (hΔ k ps t hk)

/-! ## 一般定理 -/

/-- 適格な式について、独立意味論の結果は Lean での読みの値(`wtR` の関数帰納法で、式・腕の列・腕・実引数の列の 4 つを同時に示す)。読みの環境
`Φ'` と署名 `Δ'` は、評価の環境 `Φ` と型付けの署名 `Δ` と署名の鍵で一致していればよい。 -/
theorem denote_sound_all (Δ Δ' : SigEnv) (Φ Φ' : FEnv) (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hA : FEnv.Agree Φ Φ' Δ) :
    (∀ (Γ : Ctx) (e : Core.Expr), ∀ ρ : Env, Γ = ρ.ty → ∀ t, wtR Δ Γ e = some t →
        eval Φ ρ e = some (denoteV Δ' Φ' ρ t e)) ∧
    (∀ (Γ : Ctx) (ts : Ty) (arms : List Core.Arm), ∀ ρ : Env, Γ = ρ.ty → ∀ t, wtArmsR Δ Γ ts arms = some t →
        ∀ v : Val, v.ty = ts → ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        evalArms Φ ρ v arms = some (denoteArmsV Δ' Φ' ρ t v arms)) ∧
    (∀ (Γ : Ctx) (ts : Ty) (arm : Core.Arm), ∀ p g b, arm = .mk p g b → ∀ ρ : Env, Γ = ρ.ty → ∀ t,
        wtArmR Δ Γ ts arm = some t → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        eval Φ (ρ.extList bs) b = some (denoteV Δ' Φ' (ρ.extList bs) t b) ∧
        (∀ g', g = some g' → eval Φ (ρ.extList bs) g' = some (.bool (denoteB Δ' Φ' (ρ.extList bs) g')))) ∧
    (∀ (Γ : Ctx) (args : List Core.Expr) (ps : List Ty), ∀ ρ : Env, Γ = ρ.ty → wtArgs Δ Γ args ps = true →
        evalArgs Φ ρ args = some (denoteArgs Δ' Φ' ρ args ps) ∧ (denoteArgs Δ' Φ' ρ args ps).map Val.ty = ps) := by
  apply wtR.mutual_induct Δ
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
  -- 4. 呼出し(適格): 実引数の読みの列を、一致する関数環境の関数に渡す
  · intro Γ k args ps t hk hargs ih4 ρ hΓ t' ht
    simp only [wtR, hk, hargs, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨f, f', hf, hf', hag⟩ := hA k ps t hk
    have hk' := hΔ k ps t hk
    obtain ⟨f'', hf'', hfv⟩ := hΦ' k ps t hk'
    rw [hf'] at hf''
    cases hf''
    obtain ⟨hargsEq, hty⟩ := ih4 ρ hΓ hargs
    obtain ⟨v, hv, hvt⟩ := hfv _ hty
    have hfvs : f (denoteArgs Δ' Φ' ρ args ps) = some v := by rw [hag _ hty]; exact hv
    cases t <;> cases v <;> simp [Val.ty] at hvt <;> simp [eval, hf, hargsEq, hfvs, denoteV, denoteN, denoteB, hk', hf', hv]
  -- 5. 呼出し(実引数が合わない)
  · intro Γ k args ps t hk hno _ ρ _ t' ht
    simp [wtR, hk, hno] at ht
  -- 6. 呼出し(fn / input の署名が無い)
  · intro Γ k args hk ρ _ t ht
    simp [wtR, hk] at ht
  -- 7. let(適格)
  · intro Γ x ty v b ta hta hv ihv ihb ρ hΓ t ht
    simp only [wtR, hv, hta, ite_true] at ht
    have hev := ihv ρ hΓ ta hv
    have hΓ' : Γ.ext x ta = (ρ.ext x (denoteV Δ' Φ' ρ ta v)).ty := by rw [Env.ty_ext, denoteV_ty, hΓ]
    have heb := ihb _ hΓ' t ht
    cases ty <;> simp [TyV.toTy?] at hta
    all_goals subst hta; cases t <;> simp only [denoteV] at hev heb <;> simp [eval, hev, heb, denoteV, denoteN, denoteB]
  -- 8. let(注釈と値の型が違う)
  · intro Γ x ty v b tv ta hta hv hne _ ρ _ t ht
    simp [wtR, hv, hta, hne] at ht
  -- 9. let(値が不適格)
  · intro Γ x ty v b hno _ ρ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 10. if(適格)
  · intro Γ c t e te hte hc htt ihc iht ihe ρ hΓ t' ht'
    simp only [wtR, hc, htt, hte, ite_true, Option.some.injEq] at ht'
    subst ht'
    have hec := ihc ρ hΓ .bool hc
    have het := iht ρ hΓ te htt
    have hee := ihe ρ hΓ te hte
    simp only [denoteV] at hec
    cases hcb : denoteB Δ' Φ' ρ c
    all_goals cases te <;> simp [eval, hec, hcb, het, hee, denoteV, denoteN, denoteB]
  -- 11. if(分岐の型が違う)
  · intro Γ c t e tt te hte htt hc hne _ _ _ ρ _ t' ht'
    simp [wtR, hc, htt, hte, hne] at ht'
  -- 12. if(不適格)
  · intro Γ c t e hno _ _ _ ρ _ t' ht'
    simp only [wtR] at ht'
    first
      | (cases ht'; done)
      | (split at ht' <;> simp_all)
  -- 13. 二項演算(適格)
  · intro Γ op l r ty k tl tr ta hta hr hl hk ihl ihr ρ hΓ t ht
    simp only [wtR, hk, hl, hr, hta] at ht
    have hel := ihl ρ hΓ tl hl
    have her := ihr ρ hΓ tr hr
    simp only [eval, hk, hel, her]
    cases k <;> cases tl <;> cases tr <;> cases ta <;> simp [BinOp.result] at ht <;> subst ht <;>
      simp [BinOp.apply, denoteV, denoteN, denoteB, hk, hta, CmpOp.leanBool_eq, EqOp.leanNat_eq, EqOp.leanBool_eq]
  -- 14. 二項演算(不適格)
  · intro Γ op l r ty hno _ _ ρ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 15. `!`(適格)
  · intro Γ a ha iha ρ hΓ t ht
    simp only [wtR, ha, ite_true, Option.some.injEq] at ht
    subst ht
    have hea := iha ρ hΓ .bool ha
    simp only [denoteV] at hea
    simp [eval, hea, denoteV, denoteB]
  -- 16. `!`(被演算子が Bool でない)
  · intro Γ a hno _ ρ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 17. 対象外の単項演算子
  · intro Γ op a hne ρ _ t ht
    simp [wtR, hne] at ht
  -- 18. Nat の min / max(適格)
  · intro Γ m r a k ha hr hm ihr iha ρ hΓ t ht
    simp only [wtR, hm, hr, ha, ite_true, Option.some.injEq] at ht
    subst ht
    have her := ihr ρ hΓ .nat hr
    have hea := iha ρ hΓ .nat ha
    simp only [denoteV] at her hea
    simp [eval, hm, her, hea, denoteV, denoteN]
  -- 19. Nat のメソッド(不適格)
  · intro Γ m r a rt hno _ _ ρ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 20. Nat 以外のメソッド
  · intro Γ tn m r a rt hne ρ _ t ht
    simp [wtR, hne] at ht
  -- 21. match(適格)
  · intro Γ s st arms tv ta hta hs hex ihs iharms ρ hΓ t ht
    simp only [wtR, hs, hta, hex, ite_true] at ht
    have hv := ihs ρ hΓ tv hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hex
    obtain ⟨hteq, hexh⟩ := hex
    have hw := iharms ρ hΓ t ht (denoteV Δ' Φ' ρ tv s) (denoteV_ty Δ' Φ' ρ tv s) false false hexh (fun _ => rfl) (fun _ => rfl)
    simp only [eval, hv, hw]
    cases st <;> simp [TyV.toTy?] at hta
    all_goals subst hta; subst hteq; cases t <;> simp [denoteV, denoteArmsV, denoteN, denoteB]
  -- 22. match(型が違う / 網羅しない)
  · intro Γ s st arms tv ta hta hs hne _ ρ _ t ht
    simp [wtR, hs, hta, hne] at ht
  -- 23. match(不適格)
  · intro Γ s st arms hno _ ρ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 24. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ρ _ t ht
    rw [wtR.eq_def] at ht
    split at ht
    all_goals first
      | exact (h1 _ rfl).elim
      | exact (h2 _ rfl).elim
      | exact (h3 _ rfl).elim
      | exact (h4 _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ _ rfl).elim
      | exact (h7 _ _ _ _ rfl).elim
      | exact (h8 _ _ rfl).elim
      | exact (h9 _ _ _ _ _ rfl).elim
      | exact (h10 _ _ _ rfl).elim
      | (cases ht; done)
  -- 25. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp p' g' b' heq ρ _ t ht
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp at ht
  -- 26. 腕(ガード無し)
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
  -- 27. 腕(ガードが Bool)
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
  -- 28. 腕(ガードが Bool でない)
  · intro Γ ts p b bts hp g hno _ p' g' b' heq ρ _ t ht
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp only at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 29. 実引数の列(空)
  · intro Γ ρ _ _
    rw [evalArgs_nil, denoteArgs_nil]
    exact ⟨rfl, rfl⟩
  -- 30. 実引数の列(先頭と残り)
  · intro Γ a as t ts iha ihas ρ hΓ hw
    rw [wtArgs_cons] at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨ha, has⟩ := hw
    have hv := iha ρ hΓ t ha
    obtain ⟨hvs, hty⟩ := ihas ρ hΓ has
    rw [denoteArgs_cons]
    refine ⟨?_, ?_⟩
    · rw [evalArgs_cons, hv, hvs]
    · simp [hty]
  -- 31. 実引数の列(数が合わない)
  · intro args Γ ps h1 h2 ρ _ hw
    rw [wtArgs.eq_def] at hw
    split at hw
    all_goals first
      | exact (h1 rfl rfl).elim
      | exact (h2 _ _ _ _ rfl rfl).elim
      | (cases hw; done)
  -- 32. 腕の列(空)
  · intro Γ ts ρ _ t ht
    simp [wtArmsR] at ht
  -- 33. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ ρ _ t ht
    simp [wtArmsR, h] at ht
  -- 34. 腕の列(最後の 1 つ): 網羅性からガード無しで必ず一致する
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
    rw [denoteArmsV_hit Δ' Φ' ρ t1 v p b [] bs hm]
    simp [evalArms_cons, hm, hw]
  -- 35. 腕の列(先頭の腕と残りの型が同じ)
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
        rw [denoteArmsV_hit Δ' Φ' ρ t2 v p b (head :: tail) bs hm]
        simp [evalArms_cons, hm, hw]
      | some g =>
        have hc := hguard g rfl
        cases hcb : denoteB Δ' Φ' (ρ.extList bs) g
        · rw [hcb] at hc
          rw [exhaustiveFrom_guard] at hex
          have hw' := ih2 ρ hΓ t2 h2 v hv sawT sawF hex hT hF
          rw [denoteArmsV_guard_false Δ' Φ' ρ t2 v p g b (head :: tail) bs hm hcb]
          simp [evalArms_cons, hm, hc, hw']
        · rw [hcb] at hc
          rw [denoteArmsV_guard_true Δ' Φ' ρ t2 v p g b (head :: tail) bs hm hcb]
          simp [evalArms_cons, hm, hc, hw]
    | none =>
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          evalArms Φ ρ v (Core.Arm.mk p g b :: head :: tail) = some (denoteArmsV Δ' Φ' ρ t2 v (Core.Arm.mk p g b :: head :: tail)) := by
        intro sawT' sawF' hex' hT' hF'
        have hw' := ih2 ρ hΓ t2 h2 v hv sawT' sawF' hex' hT' hF'
        rw [denoteArmsV_miss Δ' Φ' ρ t2 v p g b (head :: tail) hm]
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
  -- 36. 腕の列(先頭の腕と残りの型が違う)
  · intro Γ ts arm t1 head tail h1 t2 hne h2 _ _ ρ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2, hne] at ht
  -- 37. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ ρ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2] at ht

/-- **Model の保存(呼出しを含む、C55)**: 署名 `Δ` と文脈 `Γ` で適格な式は、対応する局所環境 `ρ` と、読みの環境 `Φ'`(署名 `Δ'` を守る)と署名の鍵で
一致する関数環境 `Φ` について、独立意味論の結果が読みの値に一致する。 -/
theorem denote_sound {Δ Δ' : SigEnv} {Φ Φ' : FEnv} (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hA : FEnv.Agree Φ Φ' Δ)
    {Γ : Ctx} {e : Core.Expr} {t : Ty} (h : wtR Δ Γ e = some t) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval Φ ρ e = some (denoteV Δ' Φ' ρ t e) :=
  (denote_sound_all Δ Δ' Φ Φ' hΔ hΦ' hA).1 Γ e ρ hρ t h

/-- 同じ環境での形(系): 署名を守る関数環境の下で、独立意味論の結果はその環境での読みの値。 -/
theorem denote_sound_self {Δ : SigEnv} {Φ : FEnv} (hΦ : Φ.Respects Δ) {Γ : Ctx} {e : Core.Expr} {t : Ty} (h : wtR Δ Γ e = some t)
    (ρ : Env) (hρ : Γ = ρ.ty) : eval Φ ρ e = some (denoteV Δ Φ ρ t e) :=
  denote_sound (SigEnv.SubV.refl Δ) hΦ (FEnv.Agree.refl hΦ) h ρ hρ

theorem preserve_nat {Δ Δ' : SigEnv} {Φ Φ' : FEnv} (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hA : FEnv.Agree Φ Φ' Δ)
    {Γ : Ctx} {e : Core.Expr} (h : wtR Δ Γ e = some .nat) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval Φ ρ e = some (.nat (denoteN Δ' Φ' ρ e)) :=
  denote_sound hΔ hΦ' hA h ρ hρ

theorem preserve_bool {Δ Δ' : SigEnv} {Φ Φ' : FEnv} (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hA : FEnv.Agree Φ Φ' Δ)
    {Γ : Ctx} {e : Core.Expr} (h : wtR Δ Γ e = some .bool) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval Φ ρ e = some (.bool (denoteB Δ' Φ' ρ e)) :=
  denote_sound hΔ hΦ' hA h ρ hρ

/-- **腕の列の保存**: 適格で網羅的な腕の列と対応する環境・型の合う scrutinee の値について、腕を前から試す独立意味論の結果は腕の列の読みの値。 -/
theorem denoteArms_sound {Δ Δ' : SigEnv} {Φ Φ' : FEnv} (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hA : FEnv.Agree Φ Φ' Δ)
    {Γ : Ctx} {ts t : Ty} {arms : List Core.Arm} (h : wtArmsR Δ Γ ts arms = some t) (hex : exhaustive ts arms = true) (ρ : Env) (hρ : Γ = ρ.ty)
    (v : Val) (hv : v.ty = ts) : evalArms Φ ρ v arms = some (denoteArmsV Δ' Φ' ρ t v arms) :=
  (denote_sound_all Δ Δ' Φ Φ' hΔ hΦ' hA).2.1 Γ ts arms ρ hρ t h v hv false false hex (fun _ => rfl) (fun _ => rfl)

/-- **接続検査の健全性(Nat)**: 仮引数の値 `xs` の環境で適格な式 `e` について、実生成宣言の値 `v` が実生成定数の環境 `Φ'` での読みと等しい(各宣言の
接続検査 `conn_<f>` が確かめる)なら、`Φ'` と署名の鍵で一致する任意の環境 `Φ` での独立意味論の結果は `v`。 -/
theorem check_sound_nat {Δ Δ' : SigEnv} {Φ Φ' : FEnv} (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hA : FEnv.Agree Φ Φ' Δ)
    (xs : List (String × Val)) {e : Core.Expr} (h : wtR Δ (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some .nat)
    {v : Nat} (hv : v = denoteN Δ' Φ' (Env.ofList xs) e) : eval Φ (Env.ofList xs) e = some (.nat v) := by
  subst hv
  exact preserve_nat hΔ hΦ' hA h _ (Env.ty_ofList xs).symm

/-- 同じく Bool。 -/
theorem check_sound_bool {Δ Δ' : SigEnv} {Φ Φ' : FEnv} (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hA : FEnv.Agree Φ Φ' Δ)
    (xs : List (String × Val)) {e : Core.Expr} (h : wtR Δ (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some .bool)
    {v : Bool} (hv : v = denoteB Δ' Φ' (Env.ofList xs) e) : eval Φ (Env.ofList xs) e = some (.bool v) := by
  subst hv
  exact preserve_bool hΔ hΦ' hA h _ (Env.ty_ofList xs).symm

/-! ## 実生成定数の環境 -/

/-- 仮引数の型の列と戻り型から、実生成の fn / input の Lean の型(カリー化): `Fn [Nat, Bool] Nat = Nat → Bool → Nat`。 -/
def Fn : List Ty → Ty → Type
  | [], t => t.carrier
  | p :: ps, t => p.carrier → Fn ps t

/-- 実生成の関数を値の列の上の関数に包む: 型の合う実引数には結果の値、数や型が合わなければ `none`。 -/
def wrap : (ps : List Ty) → (t : Ty) → Fn ps t → List Val → Option Val
  | [], t, g, [] => some (Val.of t g)
  | .nat :: ps, t, g, .nat n :: vs => wrap ps t (g n) vs
  | .bool :: ps, t, g, .bool b :: vs => wrap ps t (g b) vs
  | _, _, _, _ => none

theorem wrap_nil (t : Ty) (g : Fn [] t) : wrap [] t g [] = some (Val.of t g) := by
  rw [wrap.eq_def]

theorem wrap_nat (ps : List Ty) (t : Ty) (g : Fn (.nat :: ps) t) (n : Nat) (vs : List Val) :
    wrap (.nat :: ps) t g (.nat n :: vs) = wrap ps t (g n) vs := by
  rw [wrap.eq_def]

theorem wrap_bool (ps : List Ty) (t : Ty) (g : Fn (.bool :: ps) t) (b : Bool) (vs : List Val) :
    wrap (.bool :: ps) t g (.bool b :: vs) = wrap ps t (g b) vs := by
  rw [wrap.eq_def]

theorem Val.of_ty (t : Ty) (a : t.carrier) : (Val.of t a).ty = t := by
  cases t <;> rfl

/-- 包んだ関数は署名を守る: 型の合う任意の実引数に戻り型の値を返す(input の任意の全域関数の解釈もこの形)。 -/
theorem wrap_respects : ∀ (ps : List Ty) (t : Ty) (g : Fn ps t) (vs : List Val), vs.map Val.ty = ps →
    ∃ v, wrap ps t g vs = some v ∧ v.ty = t
  | [], t, g, [], _ => ⟨Val.of t g, wrap_nil t g, Val.of_ty t g⟩
  | [], _, _, _ :: _, h => by simp at h
  | _ :: _, _, _, [], h => by simp at h
  | .nat :: ps, t, g, v :: vs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hv, hvs⟩ := h
    cases v with
    | bool => simp [Val.ty] at hv
    | nat n =>
      rw [wrap_nat]
      exact wrap_respects ps t (g n) vs hvs
  | .bool :: ps, t, g, v :: vs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hv, hvs⟩ := h
    cases v with
    | nat => simp [Val.ty] at hv
    | bool b =>
      rw [wrap_bool]
      exact wrap_respects ps t (g b) vs hvs

/-- 実生成宣言の形: 鍵、input か(fn でなければ input)、仮引数の型、戻り型。 -/
structure Shape where
  key : String
  input : Bool
  ps : List Ty
  t : Ty
deriving DecidableEq, Repr

/-- 形の署名(Core 側)。 -/
def Shape.sig (s : Shape) : Sig := if s.input then .input s.ps s.t else .fn s.ps s.t

theorem Shape.sig_value? (s : Shape) : s.sig.value? = some (s.ps, s.t) := by
  unfold Shape.sig
  split <;> rfl

/-- 実生成宣言の表の項目: 形と、実生成の Lean の関数(fn は生成定数に input の引数を適用したもの、input はその解釈の Lean の値)。 -/
structure Gen where
  shape : Shape
  fn : Fn shape.ps shape.t

/-- 項目の関数を値の列の上の関数に包んだもの。 -/
def Gen.wrapped (g : Gen) : List Val → Option Val := wrap g.shape.ps g.shape.t g.fn

/-- 形の表の署名の文脈。 -/
def SigEnv.ofShapes (ss : List Shape) : SigEnv := fun k => (ss.find? fun s => s.key == k).map Shape.sig

/-- 実生成宣言の表の関数環境。 -/
def FEnv.ofGens (gs : List Gen) : FEnv := fun k => (gs.find? fun g => g.shape.key == k).map Gen.wrapped

theorem find?_map_shape (gs : List Gen) (k : String) :
    (gs.map Gen.shape).find? (fun s => s.key == k) = (gs.find? fun g => g.shape.key == k).map Gen.shape := by
  induction gs with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.map_cons, List.find?_cons]
    split <;> simp_all

/-- **表から作った環境は表の署名を守る**(C56: 任意の型に合う input 解釈も含む)。 -/
theorem ofGens_respects (gs : List Gen) : (FEnv.ofGens gs).Respects (SigEnv.ofShapes (gs.map Gen.shape)) := by
  intro k ps t hk
  simp only [valueSig?, SigEnv.ofShapes, find?_map_shape] at hk
  cases hfind : gs.find? (fun g => g.shape.key == k) with
  | none => simp [hfind] at hk
  | some g =>
    simp only [hfind, Option.map_some, Option.bind_some, Shape.sig_value?, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨g.wrapped, by simp [FEnv.ofGens, hfind], fun vs hvs => wrap_respects g.shape.ps g.shape.t g.fn vs hvs⟩

/-! ## 宣言群の意味と実生成定数の一致 -/

/-- 接続の証拠(fn 1 つ): 型の合う任意の実引数で、実生成定数の環境 `Φ'` の鍵 `k` の関数の値は、仮引数に実引数を束ねた環境での本体の読み。 -/
def FnConn (Δ' : SigEnv) (Φ' : FEnv) (k : String) (ps : List (String × Ty)) (t : Ty) (body : Core.Expr) : Prop :=
  ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) →
    ∃ f', Φ' k = some f' ∧ f' vs = some (denoteV Δ' Φ' (Env.ofList ((ps.map (·.1)).zip vs)) t body)

/-- 宣言 1 つの接続の証拠(fn 以外は要らない)。 -/
def DeclConn (Δ' : SigEnv) (Φ' : FEnv) : Decl → Prop
  | .fn k ps t body => FnConn Δ' Φ' k ps t body
  | _ => True

/-- 宣言群の接続の証拠: 各 fn に接続の証拠がある。 -/
def Evidence (Δ' : SigEnv) (Φ' : FEnv) (P : Prog) : Prop := ∀ d ∈ P, DeclConn Δ' Φ' d

/-- 同じ input 解釈: 宣言群の各 input の鍵で 2 つの関数環境が同じ。 -/
def SameInputs (I Φ' : FEnv) (P : Prog) : Prop := ∀ k ps t, Decl.input k ps t ∈ P → I k = Φ' k

theorem Interp.step_Φ_input (m : Interp) (k : String) (ps : List (String × Ty)) (t : Ty) : (m.step (.input k ps t)).Φ = m.Φ := rfl

theorem FEnv.ext_self (Φ : FEnv) (k : String) (f : List Val → Option Val) : (Φ.ext k f) k = some f := by
  simp [FEnv.ext]

theorem Interp.step_Φ_fn (m : Interp) (k : String) (ps : List (String × Ty)) (t : Ty) (body : Core.Expr) :
    (m.step (.fn k ps t body)).Φ k = some fun vs => match bindParams ps vs with | some ρ => eval m.Φ ρ body | none => none :=
  FEnv.ext_self m.Φ k _

/-- 署名の包含は `wtProg` の始めの文脈から結果へ。 -/
theorem SubV_of_wtProg {Δ₀ Δ : SigEnv} (P : Prog) (h : wtProg Δ₀ P = some Δ) : SigEnv.SubV Δ₀ Δ := by
  intro k ps t hk
  simp only [valueSig?] at hk ⊢
  cases h0 : Δ₀ k with
  | none => simp [h0] at hk
  | some s =>
    rw [h0] at hk
    rw [wtProg_mono P h k s h0]
    exact hk

/-- 宣言群の意味は実生成定数の環境と署名の鍵で一致する(宣言群の帰納法。各 fn の本体の評価を、それより前の宣言についての一致と `denote_sound` で
実生成定数の値に結ぶ)。 -/
theorem interpFrom_agree (Δ' : SigEnv) (Φ' : FEnv) (hΦ' : Φ'.Respects Δ') :
    ∀ (P : Prog) (m : Interp) {Δ : SigEnv}, wtProg m.Δ P = some Δ → m.Φ.Respects m.Δ → m.Φ.RespectsInputs P → m.Ψ.Defined m.Δ →
      SigEnv.SubV Δ Δ' → SameInputs m.Φ Φ' P → Evidence Δ' Φ' P → FEnv.Agree m.Φ Φ' m.Δ → FEnv.Agree (interpFrom m P).Φ Φ' Δ
  | [], m, Δ, h, _, _, _, _, _, _, hag => by
    simp only [wtProg, Option.some.injEq] at h
    subst h
    simpa [interpFrom] using hag
  | d :: rest, m, Δ, h, hΦ, hI, hΨ, hsub, hin, hev, hag => by
    obtain ⟨hfresh, hwt, hrest⟩ := wtProg_cons h
    obtain ⟨hΦs, hIs, hΨs⟩ := Interp.step_inv m d rest hfresh hwt hrest hΦ hI hΨ
    have hrestFresh : ∀ k ps t, Decl.input k ps t ∈ rest → k ≠ d.key := by
      intro k ps t hin' he
      have := wtProg_fresh rest hrest _ hin'
      change (m.Δ.ext d.key d.sig) k = none at this
      rw [he, SigEnv.ext_self] at this
      cases this
    have hsubm : SigEnv.SubV m.Δ Δ' := fun k ps t hk => hsub k ps t (SubV_of_wtProg (d :: rest) h k ps t hk)
    have hsigd : Δ d.key = some d.sig := wtProg_sig (d :: rest) h d (List.mem_cons_self ..)
    have hag' : FEnv.Agree (m.step d).Φ Φ' (m.step d).Δ := by
      intro y ps t hy
      rw [Interp.step_Δ] at hy
      by_cases hk : y = d.key
      · subst hk
        rw [valueSig?, SigEnv.ext_self] at hy
        cases d with
        | fn k ps' t' body =>
          simp only [Decl.sig, Sig.value?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hy
          obtain ⟨hps, ht⟩ := hy
          subst hps ht
          have hconn : FnConn Δ' Φ' k ps' t' body := hev _ (List.mem_cons_self ..)
          have hΔk : valueSig? Δ' k = some (ps'.map (·.2), t') :=
            hsub k _ t' (valueSig?_fn (by simpa [Decl.key, Decl.sig] using hsigd))
          obtain ⟨f', hf', _⟩ := hΦ' k _ t' hΔk
          refine ⟨fun vs => match bindParams ps' vs with | some ρ => eval m.Φ ρ body | none => none, f', Interp.step_Φ_fn m k ps' t' body, hf', ?_⟩
          intro vs hvs
          obtain ⟨hb, hty⟩ := bindParams_ty hvs
          simp only [hb]
          obtain ⟨f'', hf'', hval⟩ := hconn vs hvs
          rw [hf'] at hf''
          cases hf''
          rw [hval]
          simp only [wtDecl, decide_eq_true_eq] at hwt
          exact denote_sound hsubm hΦ' hag hwt _ hty.symm
        | spec k ps' body => simp [Decl.sig, Sig.value?] at hy
        | input k ps' t' =>
          simp only [Decl.sig, Sig.value?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hy
          obtain ⟨hps, ht⟩ := hy
          subst hps ht
          have hsame : m.Φ k = Φ' k := hin k ps' t' (List.mem_cons_self ..)
          have hΔk : valueSig? Δ' k = some (ps'.map (·.2), t') :=
            hsub k _ t' (valueSig?_input (by simpa [Decl.key, Decl.sig] using hsigd))
          obtain ⟨f', hf', _⟩ := hΦ' k _ t' hΔk
          refine ⟨f', f', ?_, hf', fun _ _ => rfl⟩
          show m.Φ k = some f'
          rw [hsame]
          exact hf'
      · rw [valueSig?, SigEnv.ext_ne _ _ _ hk] at hy
        obtain ⟨f, f', hf, hf', hagree⟩ := hag y ps t hy
        exact ⟨f, f', by rw [Interp.step_Φ_ne _ _ hk]; exact hf, hf', hagree⟩
    have hin' : SameInputs (m.step d).Φ Φ' rest := by
      intro k ps t hk
      rw [Interp.step_Φ_ne _ _ (hrestFresh k ps t hk)]
      exact hin k ps t (List.mem_cons_of_mem _ hk)
    have hev' : Evidence Δ' Φ' rest := fun d' hd' => hev d' (List.mem_cons_of_mem _ hd')
    simp only [interpFrom]
    exact interpFrom_agree Δ' Φ' hΦ' rest (m.step d) (by rw [Interp.step_Δ]; exact hrest) hΦs hIs hΨs hsub hin' hev' hag'

/-- **宣言群の意味と実生成定数の一致(C55 / C56 / C57)**: 適格な宣言群 `P` と input の署名を守る任意の解釈 `I`、署名 `Δ'`(宣言群の署名を含む)を守る
実生成定数の環境 `Φ'` について、input の鍵で `I` と `Φ'` が同じ(同じ input 解釈)で、各 fn に接続の証拠(型の合う任意の実引数で実生成定数の値 = 本体の読み)
があれば、宣言群の意味 `(interp I P).Φ` は `Φ'` と署名の鍵で一致する — 各 fn / input の意味は型の合う任意の実引数で実生成定数の値。 -/
theorem interp_agree {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ) {I : FEnv} (hI : I.RespectsInputs P)
    {Δ' : SigEnv} {Φ' : FEnv} (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hin : SameInputs I Φ' P) (hev : Evidence Δ' Φ' P) :
    FEnv.Agree (interp I P).Φ Φ' Δ :=
  interpFrom_agree Δ' Φ' hΦ' P (Interp.init I) hP (Interp.init_respects I) hI (Interp.init_defined I) hΔ hin hev
    (fun k ps t h => by simp [Interp.init, valueSig?, SigEnv.empty] at h)

/-- **fn の意味は実生成定数の値**(系): 宣言群の各 fn `k` について、実生成定数の環境の関数 `f'` が型の合う実引数 `vs` に `v` を返すなら、
宣言群の意味の関数も `vs` に `v` を返す。 -/
theorem fn_value {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ) {I : FEnv} (hI : I.RespectsInputs P)
    {Δ' : SigEnv} {Φ' : FEnv} (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hin : SameInputs I Φ' P) (hev : Evidence Δ' Φ' P)
    {k : String} {ps : List (String × Ty)} {t : Ty} {body : Core.Expr} (hd : Decl.fn k ps t body ∈ P)
    {f' : List Val → Option Val} (hf' : Φ' k = some f') {vs : List Val} (hvs : vs.map Val.ty = ps.map (·.2)) {v : Val} (hv : f' vs = some v) :
    ∃ f, (interp I P).Φ k = some f ∧ f vs = some v := by
  have hsig := wtProg_sig P hP _ hd
  simp only [Decl.key, Decl.sig] at hsig
  obtain ⟨f, f'', hf, hf'', hag⟩ := interp_agree hP hI hΔ hΦ' hin hev k _ t (valueSig?_fn hsig)
  rw [hf'] at hf''
  cases hf''
  exact ⟨f, hf, by rw [hag vs hvs]; exact hv⟩

/-! ## 署名の包含と接続の証拠の形 -/

/-- `wtProg` の署名の鍵は、始めの文脈か宣言群の宣言のもの。 -/
theorem wtProg_keys : ∀ {Δ₀ Δ : SigEnv} (P : Prog), wtProg Δ₀ P = some Δ → ∀ k s, Δ k = some s →
    Δ₀ k = some s ∨ ∃ d ∈ P, d.key = k ∧ d.sig = s
  | _, _, [], h, k, s, hk => by
    simp only [wtProg, Option.some.injEq] at h
    subst h
    exact Or.inl hk
  | Δ₀, Δ, d :: rest, h, k, s, hk => by
    obtain ⟨_, _, hrest⟩ := wtProg_cons h
    rcases wtProg_keys rest hrest k s hk with h0 | ⟨d', hd', hk', hs⟩
    · by_cases he : k = d.key
      · subst he
        rw [SigEnv.ext_self] at h0
        cases h0
        exact Or.inr ⟨d, List.mem_cons_self .., rfl, rfl⟩
      · rw [SigEnv.ext_ne _ _ _ he] at h0
        exact Or.inl h0
    · exact Or.inr ⟨d', List.mem_cons_of_mem _ hd', hk', hs⟩

/-- 宣言群の各 fn / input の署名が表 `Δ'` にあれば、`wtProg` の署名は `Δ'` に含まれる(検査プログラムは `hcov` を `decide` で確かめる)。 -/
theorem SubV_of_cover {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ) {Δ' : SigEnv}
    (hcov : ∀ d ∈ P, d.sig.value?.isSome = true → Δ' d.key = some d.sig) : SigEnv.SubV Δ Δ' := by
  intro k ps t hk
  simp only [valueSig?] at hk
  cases hΔ : Δ k with
  | none => simp [hΔ] at hk
  | some s =>
    simp only [hΔ, Option.bind_some] at hk
    rcases wtProg_keys P hP k s hΔ with h0 | ⟨d, hd, rfl, rfl⟩
    · simp [SigEnv.empty] at h0
    · have := hcov d hd (by simp [hk])
      simp [valueSig?, this, hk]

/-- 接続の定理の形(カリー化): 仮引数ごとに量化し、実生成の関数に実引数を渡した値が、実引数を束ねた環境での本体の読みに等しい。
検査プログラムの `conn_<f> : ∀ («x» : Nat) …, Model.M.f inputs «x» … = denoteN Δ' Φ' (Env.ofList [("x", .nat «x»), …]) core_f` はこの形。 -/
def Curried (Δ : SigEnv) (Φ : FEnv) (t : Ty) (body : Core.Expr) :
    (ps : List (String × Ty)) → Fn (ps.map (·.2)) t → List (String × Val) → Prop
  | [], g, acc => g = denoteT Δ Φ (Env.ofList acc) t body
  | (x, .nat) :: ps, g, acc => ∀ n : Nat, Curried Δ Φ t body ps (g n) (acc ++ [(x, .nat n)])
  | (x, .bool) :: ps, g, acc => ∀ b : Bool, Curried Δ Φ t body ps (g b) (acc ++ [(x, .bool b)])

/-- カリー化の形の接続から、包んだ関数の値の列の上の接続。 -/
theorem curried_wrap (Δ : SigEnv) (Φ : FEnv) (t : Ty) (body : Core.Expr) :
    ∀ (ps : List (String × Ty)) (g : Fn (ps.map (·.2)) t) (acc : List (String × Val)), Curried Δ Φ t body ps g acc →
      ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) →
        wrap (ps.map (·.2)) t g vs = some (denoteV Δ Φ (Env.ofList (acc ++ (ps.map (·.1)).zip vs)) t body)
  | [], g, acc, h, vs, hvs => by
    cases vs with
    | nil =>
      simp only [Curried] at h
      subst h
      show wrap [] t (denoteT Δ Φ (Env.ofList acc) t body) [] = some (denoteV Δ Φ (Env.ofList (acc ++ [])) t body)
      rw [List.append_nil]
      exact (wrap_nil t (denoteT Δ Φ (Env.ofList acc) t body)).trans (congrArg some (Val.of_denoteT Δ Φ (Env.ofList acc) t body))
    | cons v vs => simp at hvs
  | (x, .nat) :: ps, g, acc, h, vs, hvs => by
    cases vs with
    | nil => simp at hvs
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at hvs
      obtain ⟨hv, hvs⟩ := hvs
      cases v with
      | bool => simp [Val.ty] at hv
      | nat n =>
        simp only [Curried] at h
        have := curried_wrap Δ Φ t body ps (g n) (acc ++ [(x, .nat n)]) (h n) vs hvs
        rw [List.append_assoc, List.singleton_append] at this
        show wrap (.nat :: ps.map (fun p : String × Ty => p.2)) t g (.nat n :: vs) =
          some (denoteV Δ Φ (Env.ofList (acc ++ (x, .nat n) :: (ps.map (fun p : String × Ty => p.1)).zip vs)) t body)
        rw [wrap_nat]
        exact this
  | (x, .bool) :: ps, g, acc, h, vs, hvs => by
    cases vs with
    | nil => simp at hvs
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at hvs
      obtain ⟨hv, hvs⟩ := hvs
      cases v with
      | nat => simp [Val.ty] at hv
      | bool b =>
        simp only [Curried] at h
        have := curried_wrap Δ Φ t body ps (g b) (acc ++ [(x, .bool b)]) (h b) vs hvs
        rw [List.append_assoc, List.singleton_append] at this
        show wrap (.bool :: ps.map (fun p : String × Ty => p.2)) t g (.bool b :: vs) =
          some (denoteV Δ Φ (Env.ofList (acc ++ (x, .bool b) :: (ps.map (fun p : String × Ty => p.1)).zip vs)) t body)
        rw [wrap_bool]
        exact this

/-- 実生成宣言ごとの接続検査(`conn_<f>`、カリー化の形)と、実生成定数の環境の鍵 `k` がその関数を包んだものであることから、接続の証拠 `FnConn`。 -/
theorem fnConn_of_curried (Δ : SigEnv) (Φ : FEnv) (k : String) (ps : List (String × Ty)) (t : Ty) (body : Core.Expr)
    (g : Fn (ps.map (·.2)) t) (h : Curried Δ Φ t body ps g []) (hΦ : Φ k = some (wrap (ps.map (·.2)) t g)) : FnConn Δ Φ k ps t body := by
  intro vs hvs
  refine ⟨_, hΦ, ?_⟩
  have := curried_wrap Δ Φ t body ps g [] h vs hvs
  simpa using this

end NaruSem.Call
