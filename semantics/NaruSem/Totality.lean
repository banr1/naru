import NaruSem.Sem

/-!
# 適格な式と環境には意味が定まる(IDEAL.md C39)

- runtime(表示的意味論 `eval`): 文脈 `Γ` で適格(`wtR Γ e = some t`)な式は、`Γ` に対応する環境(`Γ = ρ.ty`: 各名前の値の型が文脈の型)で
  必ず値を持ち(`eval_total`)、その値の型は `t`。値は関数の結果なので一意(`Eval_unique`)。
- spec(評価関係 `Sem`): 文脈 `Γ` で適格(`wtS Γ e = some τ`)な式は、対応する環境(`Γ = ρ.ctx`)で意味(命題)が存在し(`Sem_exists`)、
  意味は一意(`Sem_unique`。量化の意味は束縛ごとの意味を `∀` / `∃` で束ねるので、一意性は関数外延性と命題外延性で `=` になる)。

型付け・スコープ・網羅性(`Scope.lean`)は仮定(適格性の前提)で、翻訳の正しさは仮定しない(backend の出力は現れない)。
-/

namespace NaruSem
open Naru

/-! ## 環境と文脈の対応(runtime) -/

/-- 環境に対応する文脈: 各名前の値の型。 -/
def Env.ty (ρ : Env) : Ctx := fun x => (ρ x).map Val.ty

@[simp] theorem Val.ty_of (t : Ty) (a : t.carrier) : (Val.of t a).ty = t := by
  cases t <;> rfl

theorem Env.ty_ext (ρ : Env) (x : String) (v : Val) : (ρ.ext x v).ty = ρ.ty.ext x v.ty := by
  funext y
  simp only [Env.ty, Env.ext, Ctx.ext]
  split <;> rfl

theorem Env.ty_extList (ρ : Env) (bs : List (String × Val)) :
    (ρ.extList bs).ty = ρ.ty.extList (bs.map fun (x, v) => (x, v.ty)) := by
  induction bs generalizing ρ with
  | nil => rfl
  | cons xv rest ih =>
    obtain ⟨x, v⟩ := xv
    simp [Env.extList, Ctx.extList, ih, Env.ty_ext]

/-- パターンの照合が成功すれば、束縛する値の型は型付けが与える束縛の型。 -/
theorem matchPat_types {t : Ty} {p : Core.Pat} {v : Val} {bs : List (String × Val)} {bts : List (String × Ty)}
    (hp : wtPat t p = some bts) (hv : v.ty = t) (hm : matchPat p v = some bs) :
    bs.map (fun (x, w) => (x, w.ty)) = bts := by
  cases p with
  | wild => simp_all [wtPat, matchPat]
  | bind x =>
    simp only [wtPat, matchPat, Option.some.injEq] at hp hm
    subst hp hm
    simp [hv]
  | lit l =>
    cases l <;> cases v <;> simp_all [wtPat, matchPat, Val.ty] <;> split at hm <;> simp_all
  | tuple => simp_all [wtPat]
  | builtin => simp_all [wtPat]
  | variant => simp_all [wtPat]

/-- 必ず一致するパターンは照合に成功する。 -/
theorem matchPat_irrefutable {p : Core.Pat} (h : irrefutable p = true) (v : Val) : ∃ bs, matchPat p v = some bs := by
  cases p <;> simp_all [irrefutable, matchPat]

theorem exhaustiveFrom_guard (t : Ty) (sawT sawF : Bool) (p : Core.Pat) (g b : Core.Expr) (rest : List Core.Arm) :
    exhaustiveFrom t sawT sawF (.mk p (some g) b :: rest) = exhaustiveFrom t sawT sawF rest := by
  simp [exhaustiveFrom]

theorem exhaustiveFrom_true (t : Ty) (sawT sawF : Bool) (b : Core.Expr) (rest : List Core.Arm) :
    exhaustiveFrom t sawT sawF (.mk (.lit (.bool true)) none b :: rest) =
      ((decide (t = .bool) && sawF) || exhaustiveFrom t true sawF rest) := by
  simp [exhaustiveFrom]

theorem exhaustiveFrom_false (t : Ty) (sawT sawF : Bool) (b : Core.Expr) (rest : List Core.Arm) :
    exhaustiveFrom t sawT sawF (.mk (.lit (.bool false)) none b :: rest) =
      ((decide (t = .bool) && sawT) || exhaustiveFrom t sawT true rest) := by
  simp [exhaustiveFrom]

theorem exhaustiveFrom_nat (t : Ty) (sawT sawF : Bool) (n : Nat) (b : Core.Expr) (rest : List Core.Arm) :
    exhaustiveFrom t sawT sawF (.mk (.lit (.nat n)) none b :: rest) = exhaustiveFrom t sawT sawF rest := by
  simp [exhaustiveFrom]

/-- `evalArms` の腕 1 つ分の展開。入れ子の帰納型の上の構造的再帰の等式は、`simp` に定義として渡さず(kernel の定義展開が
失敗する)、この補題を通して書き換える。 -/
theorem evalArms_cons (ρ : Env) (v : Val) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm) :
    evalArms ρ v (.mk p g b :: rest) =
      match matchPat p v with
      | none => evalArms ρ v rest
      | some bs =>
        match g with
        | none => eval (ρ.extList bs) b
        | some g =>
          match eval (ρ.extList bs) g with
          | some (.bool true) => eval (ρ.extList bs) b
          | some (.bool false) => evalArms ρ v rest
          | _ => none :=
  evalArms.eq_2 ρ v p g b rest

/-! ## runtime の全域性 -/

/-- `wtR` / `wtArmsR` / `wtArmR` の関数帰納法で、式・腕の列・腕の 3 つを同時に示す。腕の列では、網羅性の走査の状態
(`sawT` / `sawF`: 既に見た Bool のリテラルの腕)と、値がそのリテラルならもう前の腕で一致している(`v = true → sawT = false` …)
ことを不変条件に持つ。 -/
theorem wtR_total_all :
    (∀ (Γ : Ctx) (e : Core.Expr), ∀ ρ : Env, Γ = ρ.ty → ∀ t, wtR Γ e = some t →
        ∃ v, eval ρ e = some v ∧ v.ty = t) ∧
    (∀ (Γ : Ctx) (ts : Ty) (arms : List Core.Arm), ∀ ρ : Env, Γ = ρ.ty → ∀ t, wtArmsR Γ ts arms = some t →
        ∀ v : Val, v.ty = ts → ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        ∃ w, evalArms ρ v arms = some w ∧ w.ty = t) ∧
    (∀ (Γ : Ctx) (ts : Ty) (arm : Core.Arm), ∀ p g b, arm = .mk p g b → ∀ ρ : Env, Γ = ρ.ty → ∀ t,
        wtArmR Γ ts arm = some t → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        (∃ w, eval (ρ.extList bs) b = some w ∧ w.ty = t) ∧
        (∀ g', g = some g' → ∃ c : Bool, eval (ρ.extList bs) g' = some (.bool c))) := by
  apply wtR.mutual_induct
  -- 1. Nat のリテラル
  · intro Γ n ρ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨.nat n, by simp [eval], rfl⟩
  -- 2. Bool のリテラル
  · intro Γ b ρ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨.bool b, by simp [eval], rfl⟩
  -- 3. 局所名
  · intro Γ x ρ hΓ t ht
    subst hΓ
    simp only [wtR, Env.ty] at ht
    cases h : ρ x with
    | none => simp [h] at ht
    | some v =>
      simp [h] at ht
      exact ⟨v, by simp [eval, h], ht⟩
  -- 4. let(適格)
  · intro Γ x ty v b ta hta hv ihv ihb ρ hΓ t ht
    simp only [wtR, hv, hta, ite_true] at ht
    obtain ⟨w, hw, hwt⟩ := ihv ρ hΓ ta hv
    obtain ⟨u, hu, hut⟩ := ihb (ρ.ext x w) (by rw [Env.ty_ext, hwt, hΓ]) t ht
    exact ⟨u, by simp [eval, hw, hu], hut⟩
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
    obtain ⟨vc, hvc, hvct⟩ := ihc ρ hΓ .bool hc
    cases vc with
    | nat => simp [Val.ty] at hvct
    | bool bc =>
      cases bc with
      | true =>
        obtain ⟨w, hw, hwt⟩ := iht ρ hΓ te htt
        exact ⟨w, by simp [eval, hvc, hw], hwt⟩
      | false =>
        obtain ⟨w, hw, hwt⟩ := ihe ρ hΓ te hte
        exact ⟨w, by simp [eval, hvc, hw], hwt⟩
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
    obtain ⟨a, ha, hat⟩ := ihl ρ hΓ tl hl
    obtain ⟨b, hb, hbt⟩ := ihr ρ hΓ tr hr
    simp only [eval, hk, ha, hb]
    subst hat hbt
    cases k <;> cases a <;> cases b <;> cases ta <;> simp_all [BinOp.result, BinOp.apply, Val.ty]
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
    obtain ⟨va, hva, hvat⟩ := iha ρ hΓ .bool ha
    cases va with
    | nat => simp [Val.ty] at hvat
    | bool ba => exact ⟨.bool (!ba), by simp [eval, hva], rfl⟩
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
    obtain ⟨x, hx, hxt⟩ := ihr ρ hΓ .nat hr
    obtain ⟨y, hy, hyt⟩ := iha ρ hΓ .nat ha
    cases x with
    | bool => simp [Val.ty] at hxt
    | nat x =>
      cases y with
      | bool => simp [Val.ty] at hyt
      | nat y => exact ⟨.nat (k.eval x y), by simp [eval, hm, hx, hy], rfl⟩
  -- 16. Nat のメソッド(不適格)
  · intro Γ m r a rt hno _ _ ρ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 17. Nat 以外のメソッド
  · intro Γ tn m r a rt hne ρ _ t ht
    simp [wtR, hne] at ht
  -- 18. match(適格)
  · intro Γ s st arms tv ta hta hs hex ihs iharms ρ hΓ t ht
    simp only [wtR, hs, hta, hex, ite_true] at ht
    obtain ⟨v, hv, hvt⟩ := ihs ρ hΓ tv hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hex
    obtain ⟨w, hw, hwt⟩ := iharms ρ hΓ t ht v hvt false false hex.2 (fun _ => rfl) (fun _ => rfl)
    exact ⟨w, by simp [eval, hv, hw], hwt⟩
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
  -- 23. 腕(ガード無し)
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
  -- 24. 腕(ガードが Bool)
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
    obtain ⟨c, hc, hct⟩ := ihg (ρ.extList bs) hΓ' .bool hg
    cases c with
    | nat => simp [Val.ty] at hct
    | bool cb => exact ⟨cb, hc⟩
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
  -- 28. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 ρ hΓ t ht v hv sawT sawF hex hT hF
    simp only [wtArmsR, h1, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
    cases g with
    | some g => simp [exhaustiveFrom] at hex
    | none =>
      cases p with
      | wild =>
        obtain ⟨w, hw, hwt⟩ := (ih3 .wild none b rfl ρ hΓ t1 h1 v hv [] rfl).1
        exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
      | bind x =>
        obtain ⟨w, hw, hwt⟩ := (ih3 (.bind x) none b rfl ρ hΓ t1 h1 v hv [(x, v)] rfl).1
        exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
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
              | true =>
                obtain ⟨w, hw, hwt⟩ := (ih3 (.lit (.bool true)) none b rfl ρ hΓ t1 h1 (.bool true) hv [] rfl).1
                exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
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
              | false =>
                obtain ⟨w, hw, hwt⟩ := (ih3 (.lit (.bool false)) none b rfl ρ hΓ t1 h1 (.bool false) hv [] rfl).1
                exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
        | nat n => rw [exhaustiveFrom_nat] at hex; simp [exhaustiveFrom] at hex
        | str s => simp [exhaustiveFrom] at hex
        | unit => simp [exhaustiveFrom] at hex
      | tuple ps => simp [exhaustiveFrom] at hex
      | builtin n ps => simp [exhaustiveFrom] at hex
      | variant k vn ps => simp [exhaustiveFrom] at hex
  -- 29. 腕の列(先頭の腕と残りの型が同じ)
  · intro Γ ts arm head tail t2 h2 h1 ih3 ih2 ρ hΓ t ht v hv sawT sawF hex hT hF
    rw [wtArmsR.eq_def] at ht
    simp only [h1, h2, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
    -- 先頭の腕のパターンの照合
    cases hm : matchPat p v with
    | some bs =>
      obtain ⟨⟨w, hw, hwt⟩, hguard⟩ := ih3 p g b rfl ρ hΓ t2 h1 v hv bs hm
      cases g with
      | none => exact ⟨w, by simp [evalArms_cons, hm, hw], hwt⟩
      | some g =>
        obtain ⟨c, hc⟩ := hguard g rfl
        cases c with
        | true => exact ⟨w, by simp [evalArms_cons, hm, hc, hw], hwt⟩
        | false =>
          rw [exhaustiveFrom_guard] at hex
          obtain ⟨w', hw', hwt'⟩ := ih2 ρ hΓ t2 h2 v hv sawT sawF hex hT hF
          exact ⟨w', by simp [evalArms_cons, hm, hc, hw'], hwt'⟩
    | none =>
      -- 一致しない: 残りの腕へ。網羅性の走査の状態を進める
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          ∃ w, evalArms ρ v (Core.Arm.mk p g b :: head :: tail) = some w ∧ w.ty = t2 := by
        intro sawT' sawF' hex' hT' hF'
        obtain ⟨w', hw', hwt'⟩ := ih2 ρ hΓ t2 h2 v hv sawT' sawF' hex' hT' hF'
        exact ⟨w', by simp [evalArms_cons, hm, hw'], hwt'⟩
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

/-- **runtime の全域性**: 文脈で適格な式は、対応する環境で必ず値を持ち、その型は型付けの型。 -/
theorem eval_total {Γ : Ctx} {e : Core.Expr} {t : Ty} (h : wtR Γ e = some t) (ρ : Env) (hρ : Γ = ρ.ty) :
    ∃ v, eval ρ e = some v ∧ v.ty = t :=
  wtR_total_all.1 Γ e ρ hρ t h

/-- **runtime の一意性**: 評価関係(`Eval ρ e v := eval ρ e = some v`)の結果は一意。 -/
theorem Eval_unique {ρ : Env} {e : Core.Expr} {v w : Val} (hv : Eval ρ e v) (hw : Eval ρ e w) : v = w := by
  unfold Eval at hv hw
  rw [hv] at hw
  exact Option.some.inj hw

end NaruSem
