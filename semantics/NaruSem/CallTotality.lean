import NaruSem.Call

/-!
# 関数・input を含む適格な式と宣言群には意味が定まる(IDEAL.md C54)

`Call.lean` の意味論について:

- runtime: 署名の文脈 `Δ` と局所の文脈 `Γ` で適格(`wtR Δ Γ e = some t`)な式は、`Γ` に対応する局所環境(`Γ = ρ.ty`)と `Δ` の署名を守る関数環境
  (`Φ.Respects Δ`: fn / input の鍵には型の合う実引数に型の合う結果を返す関数がある)で必ず値を持ち(`eval_total`)、その型は `t`。値は一意(`Eval_unique`)。
  実引数の列も同じ(`evalArgs_total`)。
- spec: 適格(`wtS Δ Γ e = some τ`、`τ` は論理の位置の型)な式は、対応する環境(`Γ = ρ.ctx`、`Φ.Respects Δ`、spec 宣言の環境が定義されている `Ψ.Defined Δ`)で
  意味(命題)が存在し(`Sem_exists`)、一意(`Sem_unique`。fn / input の呼出しの規則と spec 宣言の呼出しの規則は署名の phase で排他)。
- 宣言群: 適格な宣言群(`wtProg SigEnv.empty P = some Δ`)と input の署名を守る任意の解釈 `I` について、宣言群の意味 `interp I P` は `Δ` の署名を守る
  (`interp_respects`: 各 fn の意味は型の合う実引数に型の合う値を返す = `fn_total`)、spec 宣言の意味は定義され(`interp_defined` / `spec_defined`)、
  その命題は本体の意味そのもの(`spec_meaning`: 適格なら本体の意味は存在して一意なので、`Interp.step` の `∃ P, Sem … P ∧ P` はその意味と同値)。
  適格な宣言群の各宣言の署名は結果の文脈にあり(`wtProg_sig`)、鍵は重複しない(`wtProg_fresh`)。

型付け・スコープ・網羅性・署名・依存順(`Call.lean`)は仮定(適格性の前提)で、翻訳の正しさと呼出し先の正しさは仮定しない(backend の出力は現れない。
呼出し先の fn の意味は宣言群の意味の構成そのもの)。
-/

namespace NaruSem.Call
open Naru

/-! ## 展開の補題(入れ子の帰納型の上の構造的再帰は等式補題を通して書き換える) -/

theorem wtArgs_nil (Δ : SigEnv) (Γ : Ctx) : wtArgs Δ Γ [] [] = true := wtArgs.eq_1 Δ Γ

theorem wtArgs_cons (Δ : SigEnv) (Γ : Ctx) (a : Core.Expr) (as : List Core.Expr) (t : Ty) (ts : List Ty) :
    wtArgs Δ Γ (a :: as) (t :: ts) = (decide (wtR Δ Γ a = some t) && wtArgs Δ Γ as ts) := wtArgs.eq_2 Δ Γ a as t ts

theorem evalArgs_nil (Φ : FEnv) (ρ : Env) : evalArgs Φ ρ [] = some [] := evalArgs.eq_1 Φ ρ

theorem evalArgs_cons (Φ : FEnv) (ρ : Env) (a : Core.Expr) (as : List Core.Expr) :
    evalArgs Φ ρ (a :: as) =
      match eval Φ ρ a, evalArgs Φ ρ as with
      | some v, some vs => some (v :: vs)
      | _, _ => none := evalArgs.eq_2 Φ ρ a as

theorem evalArms_cons (Φ : FEnv) (ρ : Env) (v : Val) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) (rest : List Core.Arm) :
    evalArms Φ ρ v (.mk p g b :: rest) =
      match matchPat p v with
      | none => evalArms Φ ρ v rest
      | some bs =>
        match g with
        | none => eval Φ (ρ.extList bs) b
        | some g =>
          match eval Φ (ρ.extList bs) g with
          | some (.bool true) => eval Φ (ρ.extList bs) b
          | some (.bool false) => evalArms Φ ρ v rest
          | _ => none :=
  evalArms.eq_2 Φ ρ v p g b rest

theorem wtArmS_mk (Δ : SigEnv) (Γ : SCtx) (ts : Ty) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) :
    wtArmS Δ Γ ts (.mk p g b) =
      match wtPat ts p with
      | none => none
      | some bs =>
        match g with
        | none =>
          match wtS Δ (Γ.extVals bs) b with
          | some t => if t.isForm then some t else none
          | none => none
        | some g =>
          match wtS Δ (Γ.extVals bs) g, wtS Δ (Γ.extVals bs) b with
          | some tg, some tb => tg.join tb
          | _, _ => none :=
  wtArmS.eq_1 Δ Γ ts p g b

/-! ## 署名の補題 -/

/-- fn / input の鍵と spec 宣言の鍵は排他(署名は 1 つ)。 -/
theorem not_value_and_spec {Δ : SigEnv} {k : String} (hv : isValueKey Δ k = true) (hs : isSpecKey Δ k = true) : False := by
  simp only [isValueKey, isSpecKey, valueSig?, specSig?] at hv hs
  cases h : Δ k with
  | none => simp [h] at hv
  | some s => cases s <;> simp [h, Sig.value?, Sig.spec?] at hv hs

theorem valueSig?_fn {Δ : SigEnv} {k : String} {ps : List Ty} {t : Ty} (h : Δ k = some (.fn ps t)) : valueSig? Δ k = some (ps, t) := by
  simp [valueSig?, h, Sig.value?]

theorem valueSig?_input {Δ : SigEnv} {k : String} {ps : List Ty} {t : Ty} (h : Δ k = some (.input ps t)) : valueSig? Δ k = some (ps, t) := by
  simp [valueSig?, h, Sig.value?]

theorem specSig?_spec {Δ : SigEnv} {k : String} {ps : List Ty} (h : Δ k = some (.spec ps)) : specSig? Δ k = some ps := by
  simp [specSig?, h, Sig.spec?]

theorem isValueKey_of_valueSig? {Δ : SigEnv} {k : String} {ps : List Ty} {t : Ty} (h : valueSig? Δ k = some (ps, t)) : isValueKey Δ k = true := by
  simp [isValueKey, h]

theorem isSpecKey_of_specSig? {Δ : SigEnv} {k : String} {ps : List Ty} (h : specSig? Δ k = some ps) : isSpecKey Δ k = true := by
  simp [isSpecKey, h]

/-! ## runtime の全域性 -/

/-- `wtR` / `wtArmsR` / `wtArmR` / `wtArgs` の関数帰納法で、式・腕の列・腕・実引数の列の 4 つを同時に示す。腕の列の不変条件は `Totality.lean` と同じ。
実引数の列は、型の列に順に合えば順に値を持ち、値の型の列は仮引数の型の列。 -/
theorem wtR_total_all (Δ : SigEnv) :
    (∀ (Γ : Ctx) (e : Core.Expr), ∀ (Φ : FEnv) (ρ : Env), Γ = ρ.ty → Φ.Respects Δ → ∀ t, wtR Δ Γ e = some t →
        ∃ v, eval Φ ρ e = some v ∧ v.ty = t) ∧
    (∀ (Γ : Ctx) (ts : Ty) (arms : List Core.Arm), ∀ (Φ : FEnv) (ρ : Env), Γ = ρ.ty → Φ.Respects Δ → ∀ t, wtArmsR Δ Γ ts arms = some t →
        ∀ v : Val, v.ty = ts → ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        ∃ w, evalArms Φ ρ v arms = some w ∧ w.ty = t) ∧
    (∀ (Γ : Ctx) (ts : Ty) (arm : Core.Arm), ∀ p g b, arm = .mk p g b → ∀ (Φ : FEnv) (ρ : Env), Γ = ρ.ty → Φ.Respects Δ → ∀ t,
        wtArmR Δ Γ ts arm = some t → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        (∃ w, eval Φ (ρ.extList bs) b = some w ∧ w.ty = t) ∧
        (∀ g', g = some g' → ∃ c : Bool, eval Φ (ρ.extList bs) g' = some (.bool c))) ∧
    (∀ (Γ : Ctx) (args : List Core.Expr) (ps : List Ty), ∀ (Φ : FEnv) (ρ : Env), Γ = ρ.ty → Φ.Respects Δ →
        wtArgs Δ Γ args ps = true → ∃ vs, evalArgs Φ ρ args = some vs ∧ vs.map Val.ty = ps) := by
  apply wtR.mutual_induct Δ
  -- 1. Nat のリテラル
  · intro Γ n Φ ρ _ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨.nat n, by simp [eval], rfl⟩
  -- 2. Bool のリテラル
  · intro Γ b Φ ρ _ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨.bool b, by simp [eval], rfl⟩
  -- 3. 局所名
  · intro Γ x Φ ρ hΓ _ t ht
    subst hΓ
    simp only [wtR, Env.ty] at ht
    cases h : ρ x with
    | none => simp [h] at ht
    | some v =>
      simp [h] at ht
      exact ⟨v, by simp [eval, h], ht⟩
  -- 4. 呼出し(適格): 署名を守る関数環境の関数に、順に評価した実引数を渡す
  · intro Γ k args ps t hk hargs ih4 Φ ρ hΓ hΦ t' ht
    simp only [wtR, hk, hargs, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨f, hf, hfv⟩ := hΦ k ps t hk
    obtain ⟨vs, hvs, hvt⟩ := ih4 Φ ρ hΓ hΦ hargs
    obtain ⟨v, hv, hvty⟩ := hfv vs hvt
    exact ⟨v, by simp [eval, hf, hvs, hv], hvty⟩
  -- 5. 呼出し(実引数が合わない)
  · intro Γ k args ps t hk hno _ Φ ρ _ _ t' ht
    simp [wtR, hk, hno] at ht
  -- 6. 呼出し(fn / input の署名が無い: 未解決・spec 宣言・input でない)
  · intro Γ k args hk Φ ρ _ _ t ht
    simp [wtR, hk] at ht
  -- 7. let(適格)
  · intro Γ x ty v b ta hta hv ihv ihb Φ ρ hΓ hΦ t ht
    simp only [wtR, hv, hta, ite_true] at ht
    obtain ⟨w, hw, hwt⟩ := ihv Φ ρ hΓ hΦ ta hv
    obtain ⟨u, hu, hut⟩ := ihb Φ (ρ.ext x w) (by rw [Env.ty_ext, hwt, hΓ]) hΦ t ht
    exact ⟨u, by simp [eval, hw, hu], hut⟩
  -- 8. let(注釈と値の型が違う)
  · intro Γ x ty v b tv ta hta hv hne _ Φ ρ _ _ t ht
    simp [wtR, hv, hta, hne] at ht
  -- 9. let(値が不適格)
  · intro Γ x ty v b hno _ Φ ρ _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 10. if(適格)
  · intro Γ c t e te hte hc htt ihc iht ihe Φ ρ hΓ hΦ t' ht'
    simp only [wtR, hc, htt, hte, ite_true, Option.some.injEq] at ht'
    subst ht'
    obtain ⟨vc, hvc, hvct⟩ := ihc Φ ρ hΓ hΦ .bool hc
    cases vc with
    | nat => simp [Val.ty] at hvct
    | bool bc =>
      cases bc with
      | true =>
        obtain ⟨w, hw, hwt⟩ := iht Φ ρ hΓ hΦ te htt
        exact ⟨w, by simp [eval, hvc, hw], hwt⟩
      | false =>
        obtain ⟨w, hw, hwt⟩ := ihe Φ ρ hΓ hΦ te hte
        exact ⟨w, by simp [eval, hvc, hw], hwt⟩
  -- 11. if(分岐の型が違う)
  · intro Γ c t e tt te hte htt hc hne _ _ _ Φ ρ _ _ t' ht'
    simp [wtR, hc, htt, hte, hne] at ht'
  -- 12. if(不適格)
  · intro Γ c t e hno _ _ _ Φ ρ _ _ t' ht'
    simp only [wtR] at ht'
    first
      | (cases ht'; done)
      | (split at ht' <;> simp_all)
  -- 13. 二項演算(適格)
  · intro Γ op l r ty k tl tr ta hta hr hl hk ihl ihr Φ ρ hΓ hΦ t ht
    simp only [wtR, hk, hl, hr, hta] at ht
    obtain ⟨a, ha, hat⟩ := ihl Φ ρ hΓ hΦ tl hl
    obtain ⟨b, hb, hbt⟩ := ihr Φ ρ hΓ hΦ tr hr
    simp only [eval, hk, ha, hb]
    subst hat hbt
    cases k <;> cases a <;> cases b <;> cases ta <;> simp_all [BinOp.result, BinOp.apply, Val.ty]
  -- 14. 二項演算(不適格)
  · intro Γ op l r ty hno _ _ Φ ρ _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 15. `!`(適格)
  · intro Γ a ha iha Φ ρ hΓ hΦ t ht
    simp only [wtR, ha, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨va, hva, hvat⟩ := iha Φ ρ hΓ hΦ .bool ha
    cases va with
    | nat => simp [Val.ty] at hvat
    | bool ba => exact ⟨.bool (!ba), by simp [eval, hva], rfl⟩
  -- 16. `!`(被演算子が Bool でない)
  · intro Γ a hno _ Φ ρ _ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 17. 対象外の単項演算子
  · intro Γ op a hne Φ ρ _ _ t ht
    simp [wtR, hne] at ht
  -- 18. Nat の min / max(適格)
  · intro Γ m r a k ha hr hm ihr iha Φ ρ hΓ hΦ t ht
    simp only [wtR, hm, hr, ha, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨x, hx, hxt⟩ := ihr Φ ρ hΓ hΦ .nat hr
    obtain ⟨y, hy, hyt⟩ := iha Φ ρ hΓ hΦ .nat ha
    cases x with
    | bool => simp [Val.ty] at hxt
    | nat x =>
      cases y with
      | bool => simp [Val.ty] at hyt
      | nat y => exact ⟨.nat (k.eval x y), by simp [eval, hm, hx, hy], rfl⟩
  -- 19. Nat のメソッド(不適格)
  · intro Γ m r a rt hno _ _ Φ ρ _ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 20. Nat 以外のメソッド
  · intro Γ tn m r a rt hne Φ ρ _ _ t ht
    simp [wtR, hne] at ht
  -- 21. match(適格)
  · intro Γ s st arms tv ta hta hs hex ihs iharms Φ ρ hΓ hΦ t ht
    simp only [wtR, hs, hta, hex, ite_true] at ht
    obtain ⟨v, hv, hvt⟩ := ihs Φ ρ hΓ hΦ tv hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hex
    obtain ⟨w, hw, hwt⟩ := iharms Φ ρ hΓ hΦ t ht v hvt false false hex.2 (fun _ => rfl) (fun _ => rfl)
    exact ⟨w, by simp [eval, hv, hw], hwt⟩
  -- 22. match(型が違う / 網羅しない)
  · intro Γ s st arms tv ta hta hs hne _ Φ ρ _ _ t ht
    simp [wtR, hs, hta, hne] at ht
  -- 23. match(不適格)
  · intro Γ s st arms hno _ Φ ρ _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 24. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 Φ ρ _ _ t ht
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
  · intro Γ ts p g b hp p' g' b' heq Φ ρ _ _ t ht
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp at ht
  -- 26. 腕(ガード無し)
  · intro Γ ts p b bts hp ihb p' g' b' heq Φ ρ hΓ hΦ t ht v hv bs hm
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp only at ht
    have hΓ' : Γ.extPat bts = (ρ.extList bs).ty := by
      rw [Env.ty_extList, matchPat_types hp hv hm, hΓ]
      rfl
    refine ⟨ihb Φ (ρ.extList bs) hΓ' hΦ t ht, ?_⟩
    intro g' hg
    cases hg
  -- 27. 腕(ガードが Bool)
  · intro Γ ts p b bts hp g hg ihg ihb p' g' b' heq Φ ρ hΓ hΦ t ht v hv bs hm
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp only [hg] at ht
    have hΓ' : Γ.extPat bts = (ρ.extList bs).ty := by
      rw [Env.ty_extList, matchPat_types hp hv hm, hΓ]
      rfl
    refine ⟨ihb Φ (ρ.extList bs) hΓ' hΦ t ht, ?_⟩
    intro g'' hg''
    cases hg''
    obtain ⟨c, hc, hct⟩ := ihg Φ (ρ.extList bs) hΓ' hΦ .bool hg
    cases c with
    | nat => simp [Val.ty] at hct
    | bool cb => exact ⟨cb, hc⟩
  -- 28. 腕(ガードが Bool でない)
  · intro Γ ts p b bts hp g hno _ p' g' b' heq Φ ρ _ _ t ht
    cases heq
    rw [wtArmR.eq_1, hp] at ht
    simp only at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 29. 実引数の列(空)
  · intro Γ Φ ρ _ _ _
    exact ⟨[], by rw [evalArgs_nil], rfl⟩
  -- 30. 実引数の列(先頭と残り)
  · intro Γ a as t ts iha ihas Φ ρ hΓ hΦ hw
    rw [wtArgs_cons] at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨ha, has⟩ := hw
    obtain ⟨v, hv, hvt⟩ := iha Φ ρ hΓ hΦ t ha
    obtain ⟨vs, hvs, hvst⟩ := ihas Φ ρ hΓ hΦ has
    exact ⟨v :: vs, by rw [evalArgs_cons, hv, hvs], by simp [hvt, hvst]⟩
  -- 31. 実引数の列(数が合わない)
  · intro args Γ ps h1 h2 Φ ρ _ _ hw
    rw [wtArgs.eq_def] at hw
    split at hw
    all_goals first
      | exact (h1 rfl rfl).elim
      | exact (h2 _ _ _ _ rfl rfl).elim
      | (cases hw; done)
  -- 32. 腕の列(空)
  · intro Γ ts Φ ρ _ _ t ht
    simp [wtArmsR] at ht
  -- 33. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ Φ ρ _ _ t ht
    simp [wtArmsR, h] at ht
  -- 34. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 Φ ρ hΓ hΦ t ht v hv sawT sawF hex hT hF
    simp only [wtArmsR, h1, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
    cases g with
    | some g => simp [exhaustiveFrom] at hex
    | none =>
      cases p with
      | wild =>
        obtain ⟨w, hw, hwt⟩ := (ih3 .wild none b rfl Φ ρ hΓ hΦ t1 h1 v hv [] rfl).1
        exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
      | bind x =>
        obtain ⟨w, hw, hwt⟩ := (ih3 (.bind x) none b rfl Φ ρ hΓ hΦ t1 h1 v hv [(x, v)] rfl).1
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
                obtain ⟨w, hw, hwt⟩ := (ih3 (.lit (.bool true)) none b rfl Φ ρ hΓ hΦ t1 h1 (.bool true) hv [] rfl).1
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
                obtain ⟨w, hw, hwt⟩ := (ih3 (.lit (.bool false)) none b rfl Φ ρ hΓ hΦ t1 h1 (.bool false) hv [] rfl).1
                exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
        | nat n => rw [exhaustiveFrom_nat] at hex; simp [exhaustiveFrom] at hex
        | str s => simp [exhaustiveFrom] at hex
        | unit => simp [exhaustiveFrom] at hex
      | tuple ps => simp [exhaustiveFrom] at hex
      | builtin n ps => simp [exhaustiveFrom] at hex
      | variant k vn ps => simp [exhaustiveFrom] at hex
  -- 35. 腕の列(先頭の腕と残りの型が同じ)
  · intro Γ ts arm head tail t2 h2 h1 ih3 ih2 Φ ρ hΓ hΦ t ht v hv sawT sawF hex hT hF
    rw [wtArmsR.eq_def] at ht
    simp only [h1, h2, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
    cases hm : matchPat p v with
    | some bs =>
      obtain ⟨⟨w, hw, hwt⟩, hguard⟩ := ih3 p g b rfl Φ ρ hΓ hΦ t2 h1 v hv bs hm
      cases g with
      | none => exact ⟨w, by simp [evalArms_cons, hm, hw], hwt⟩
      | some g =>
        obtain ⟨c, hc⟩ := hguard g rfl
        cases c with
        | true => exact ⟨w, by simp [evalArms_cons, hm, hc, hw], hwt⟩
        | false =>
          rw [exhaustiveFrom_guard] at hex
          obtain ⟨w', hw', hwt'⟩ := ih2 Φ ρ hΓ hΦ t2 h2 v hv sawT sawF hex hT hF
          exact ⟨w', by simp [evalArms_cons, hm, hc, hw'], hwt'⟩
    | none =>
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          ∃ w, evalArms Φ ρ v (Core.Arm.mk p g b :: head :: tail) = some w ∧ w.ty = t2 := by
        intro sawT' sawF' hex' hT' hF'
        obtain ⟨w', hw', hwt'⟩ := ih2 Φ ρ hΓ hΦ t2 h2 v hv sawT' sawF' hex' hT' hF'
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
  -- 36. 腕の列(先頭の腕と残りの型が違う)
  · intro Γ ts arm t1 head tail h1 t2 hne h2 _ _ Φ ρ _ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2, hne] at ht
  -- 37. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ Φ ρ _ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2] at ht

/-- **runtime の全域性**: 署名と文脈で適格な式は、対応する局所環境と署名を守る関数環境で必ず値を持ち、その型は型付けの型。 -/
theorem eval_total {Δ : SigEnv} {Γ : Ctx} {e : Core.Expr} {t : Ty} (h : wtR Δ Γ e = some t) (Φ : FEnv) (ρ : Env) (hρ : Γ = ρ.ty)
    (hΦ : Φ.Respects Δ) : ∃ v, eval Φ ρ e = some v ∧ v.ty = t :=
  (wtR_total_all Δ).1 Γ e Φ ρ hρ hΦ t h

/-- 実引数の列の全域性: 型の列に合う実引数の列は順に値を持ち、値の型の列は仮引数の型の列。 -/
theorem evalArgs_total {Δ : SigEnv} {Γ : Ctx} {args : List Core.Expr} {ps : List Ty} (h : wtArgs Δ Γ args ps = true) (Φ : FEnv) (ρ : Env)
    (hρ : Γ = ρ.ty) (hΦ : Φ.Respects Δ) : ∃ vs, evalArgs Φ ρ args = some vs ∧ vs.map Val.ty = ps :=
  (wtR_total_all Δ).2.2.2 Γ args ps Φ ρ hρ hΦ h

/-- **runtime の一意性**: 評価関係の結果は一意。 -/
theorem Eval_unique {Φ : FEnv} {ρ : Env} {e : Core.Expr} {v w : Val} (hv : Eval Φ ρ e v) (hw : Eval Φ ρ e w) : v = w := by
  unfold Eval at hv hw
  rw [hv] at hw
  exact Option.some.inj hw

/-! ## spec の意味の存在 -/

/-- 値の位置の式: 文脈の値の部分で適格なら、環境の値の部分で値を持つ。 -/
theorem evalS_total {Δ : SigEnv} {Γ : SCtx} {e : Core.Expr} {t : Ty} (h : wtR Δ Γ.vals e = some t) (Φ : FEnv) (ρ : SEnv) (hρ : Γ = ρ.ctx)
    (hΦ : Φ.Respects Δ) : ∃ v, eval Φ ρ.vals e = some v ∧ v.ty = t :=
  eval_total h Φ ρ.vals (by rw [hρ, SEnv.ctx_vals]) hΦ

theorem evalArgsS_total {Δ : SigEnv} {Γ : SCtx} {args : List Core.Expr} {ps : List Ty} (h : wtArgs Δ Γ.vals args ps = true) (Φ : FEnv)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) (hΦ : Φ.Respects Δ) : ∃ vs, evalArgs Φ ρ.vals args = some vs ∧ vs.map Val.ty = ps :=
  evalArgs_total h Φ ρ.vals (by rw [hρ, SEnv.ctx_vals]) hΦ

theorem Sem_exists_all (Δ : SigEnv) :
    (∀ (Γ : SCtx) (e : Core.Expr), ∀ (Φ : FEnv) (Ψ : PEnv) (ρ : SEnv), Γ = ρ.ctx → Φ.Respects Δ → Ψ.Defined Δ →
        ∀ τ, wtS Δ Γ e = some τ → τ.isForm = true → ∃ P, Sem Δ Φ Ψ ρ e P) ∧
    (∀ (Γ : SCtx) (ts : Ty) (arms : List Core.Arm), ∀ (Φ : FEnv) (Ψ : PEnv) (ρ : SEnv), Γ = ρ.ctx → Φ.Respects Δ → Ψ.Defined Δ →
        ∀ τ, wtArmsS Δ Γ ts arms = some τ →
        ∀ (s : Core.Expr) (st : TyV) (v : Val), eval Φ ρ.vals s = some v → v.ty = ts →
        ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        ∃ P, Sem Δ Φ Ψ ρ (.match_ s st arms) P) ∧
    (∀ (Γ : SCtx) (ts : Ty) (arm : Core.Arm), ∀ p g b, arm = .mk p g b → ∀ (Φ : FEnv) (Ψ : PEnv) (ρ : SEnv), Γ = ρ.ctx → Φ.Respects Δ →
        Ψ.Defined Δ → ∀ τ, wtArmS Δ Γ ts arm = some τ → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        (∃ P, Sem Δ Φ Ψ (ρ.extVals bs) b P) ∧
        (∀ g', g = some g' → ∃ G, Sem Δ Φ Ψ (ρ.extVals bs) g' G)) := by
  apply wtS.mutual_induct Δ
  -- 1. Nat のリテラル(値: 論理の位置ではない)
  · intro Γ n Φ Ψ ρ _ _ _ τ hτ hf
    simp only [wtS, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 2. Bool のリテラル
  · intro Γ b Φ Ψ ρ _ _ _ τ _ _
    exact ⟨b = true, .lit⟩
  -- 3. 局所名
  · intro Γ x Φ Ψ ρ hΓ _ _ τ hτ hf
    subst hΓ
    simp only [wtS, SEnv.ctx] at hτ
    cases h : ρ x with
    | none => simp [h] at hτ
    | some s =>
      simp only [h, Option.map_some, Option.some.injEq] at hτ
      subst hτ
      cases s with
      | prop P => exact ⟨P, .varProp h⟩
      | val v =>
        cases v with
        | nat n => simp [SVal.ty, Val.ty, STy.isForm] at hf
        | bool b => exact ⟨b = true, .varVal h⟩
  -- 4. spec 宣言の呼出し(適格): 宣言の意味に実引数の値を渡す
  · intro Γ k args ps hk hargs Φ Ψ ρ hΓ hΦ hΨ τ _ _
    obtain ⟨F, hF⟩ := hΨ k ps (specSig?_spec hk)
    obtain ⟨vs, hvs, _⟩ := evalArgsS_total hargs Φ ρ hΓ hΦ
    exact ⟨F vs, .callSpec (isSpecKey_of_specSig? (specSig?_spec hk)) hF hvs⟩
  -- 5. spec 宣言の呼出し(実引数が合わない)
  · intro Γ k args ps hk hno Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hk, hno] at hτ
  -- 6. fn の呼出し(適格): Bool の結果を命題に写す(Nat の結果は論理の位置の型でない)
  · intro Γ k args ps t hk hargs Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    simp only [wtS, hk, hargs, ite_true, Option.some.injEq] at hτ
    subst hτ
    cases t with
    | nat => simp [STy.isForm] at hf
    | bool =>
      obtain ⟨f, hf', hfv⟩ := hΦ k ps .bool (valueSig?_fn hk)
      obtain ⟨vs, hvs, hvt⟩ := evalArgsS_total hargs Φ ρ hΓ hΦ
      obtain ⟨v, hv, hvty⟩ := hfv vs hvt
      cases v with
      | nat => simp [Val.ty] at hvty
      | bool b => exact ⟨b = true, .callVal (isValueKey_of_valueSig? (valueSig?_fn hk)) hf' hvs hv⟩
  -- 7. fn の呼出し(実引数が合わない)
  · intro Γ k args ps t hk hno Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hk, hno] at hτ
  -- 8. input の呼出し(適格)
  · intro Γ k args ps t hk hargs Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    simp only [wtS, hk, hargs, ite_true, Option.some.injEq] at hτ
    subst hτ
    cases t with
    | nat => simp [STy.isForm] at hf
    | bool =>
      obtain ⟨f, hf', hfv⟩ := hΦ k ps .bool (valueSig?_input hk)
      obtain ⟨vs, hvs, hvt⟩ := evalArgsS_total hargs Φ ρ hΓ hΦ
      obtain ⟨v, hv, hvty⟩ := hfv vs hvt
      cases v with
      | nat => simp [Val.ty] at hvty
      | bool b => exact ⟨b = true, .callVal (isValueKey_of_valueSig? (valueSig?_input hk)) hf' hvs hv⟩
  -- 9. input の呼出し(実引数が合わない)
  · intro Γ k args ps t hk hno Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hk, hno] at hτ
  -- 10. 呼出し(署名が無い: 未解決)
  · intro Γ k args hk Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hk] at hτ
  -- 11. let(Nat、適格)
  · intro Γ x ty v b hty hv ihb Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    simp only [wtS, hty, hv] at hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨w, hw, hwt⟩ := evalS_total hv Φ ρ hΓ hΦ
    cases w with
    | bool => simp [Val.ty] at hwt
    | nat n =>
      obtain ⟨Q, hQ⟩ := ihb Φ Ψ (ρ.ext x (.val (.nat n))) (by rw [SEnv.ctx_ext, hΓ]; rfl) hΦ hΨ τ hτ hf
      exact ⟨Q, .letNat hw hQ⟩
  -- 12. let(Nat、値が不適格)
  · intro Γ x ty v b hty hno Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 13. let(Bool、命題に束ねる)
  · intro Γ x ty v b hty hp hv ihv ihb Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    simp only [wtS, hty, hp, hv, ite_true] at hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨P, hP⟩ := ihv Φ Ψ ρ hΓ hΦ hΨ .prop hv rfl
    obtain ⟨Q, hQ⟩ := ihb Φ Ψ (ρ.ext x (.prop P)) (by rw [SEnv.ctx_ext, hΓ]; rfl) hΦ hΨ τ hτ hf
    exact ⟨Q, .letProp (by rw [← hΓ]; exact hp) hP hQ⟩
  -- 14. let(Bool、命題だが不適格)
  · intro Γ x ty v b hty hp hno _ Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS, hty, hp, ite_true] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 15. let(Bool、値に束ねる)
  · intro Γ x ty v b hty hp hv ihb Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    simp only [wtS, hty, hv, Bool.not_eq_true] at hτ
    simp only [Bool.not_eq_true] at hp
    simp only [hp, Bool.false_eq_true, ite_false] at hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨w, hw, hwt⟩ := evalS_total hv Φ ρ hΓ hΦ
    cases w with
    | nat => simp [Val.ty] at hwt
    | bool wb =>
      obtain ⟨Q, hQ⟩ := ihb Φ Ψ (ρ.ext x (.val (.bool wb))) (by rw [SEnv.ctx_ext, hΓ]; rfl) hΦ hΨ τ hτ hf
      exact ⟨Q, .letBoolVal (by rw [← hΓ]; exact hp) hw hQ⟩
  -- 16. let(Bool、値が不適格)
  · intro Γ x ty v b hty hp hno Φ Ψ ρ _ _ _ τ hτ _
    simp only [Bool.not_eq_true] at hp
    simp only [wtS, hty, hp, Bool.false_eq_true, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 17. let(注釈が対象外の型)
  · intro Γ x ty v b hty Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hty] at hτ
  -- 18. if(適格)
  · intro Γ c t e tc tt te hte htt hc j hj ihc iht ihe Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    obtain ⟨hcf, htf, hjf⟩ := STy.join_isForm hj
    simp only [wtS, hc, htt, hte, hj] at hτ
    obtain ⟨_, hef, _⟩ := STy.join_isForm hτ
    obtain ⟨C, hC⟩ := ihc Φ Ψ ρ hΓ hΦ hΨ tc hc hcf
    obtain ⟨P, hP⟩ := iht Φ Ψ ρ hΓ hΦ hΨ tt htt htf
    obtain ⟨Q, hQ⟩ := ihe Φ Ψ ρ hΓ hΦ hΨ te hte hef
    exact ⟨(C → P) ∧ (¬ C → Q), .ite hC hP hQ⟩
  -- 19. if(条件と then の結びが無い)
  · intro Γ c t e tc tt te hte htt hc hj _ _ _ Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hc, htt, hte, hj] at hτ
  -- 20. if(不適格)
  · intro Γ c t e hno _ _ _ Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 21. 論理演算(適格)
  · intro Γ op l r ty k hty hk tl tr hr hl ihl ihr Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    simp only [wtS, hk, hty, hl, hr] at hτ
    obtain ⟨hlf, hrf, _⟩ := STy.join_isForm hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨P, hP⟩ := ihl Φ Ψ ρ hΓ hΦ hΨ tl hl hlf
    obtain ⟨Q, hQ⟩ := ihr Φ Ψ ρ hΓ hΦ hΨ tr hr hrf
    exact ⟨k.prop P Q, .logic hk hP hQ⟩
  -- 22. 論理演算(被演算子が不適格)
  · intro Γ op l r ty k hty hk hno _ _ Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 23. 論理の位置の == / !=(適格)
  · intro Γ op l r ty k hty hk tl tr hr hl ihl ihr Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    simp only [wtS, hk, hty, hl, hr] at hτ
    obtain ⟨hlf, hrf, _⟩ := STy.join_isForm hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨P, hP⟩ := ihl Φ Ψ ρ hΓ hΦ hΨ tl hl hlf
    obtain ⟨Q, hQ⟩ := ihr Φ Ψ ρ hΓ hΦ hΨ tr hr hrf
    exact ⟨k.propIff P Q, .eqForm hk hP hQ⟩
  -- 24. 論理の位置の == / !=(被演算子が不適格)
  · intro Γ op l r ty k hty hk hno _ _ Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 25. Nat の == / !=(適格)
  · intro Γ op l r ty k hty hk hr hl Φ Ψ ρ hΓ hΦ hΨ τ _ _
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨a, ha, hat⟩ := evalS_total hl Φ ρ hΓ hΦ
    obtain ⟨b, hb, hbt⟩ := evalS_total hr Φ ρ hΓ hΦ
    cases a with
    | bool => simp [Val.ty] at hat
    | nat a =>
      cases b with
      | bool => simp [Val.ty] at hbt
      | nat b => exact ⟨k.propNat a b, .eqNat hk ha hb⟩
  -- 26. Nat の == / !=(被演算子が不適格)
  · intro Γ op l r ty k hty hk hno Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 27. 比較(適格)
  · intro Γ op l r ty k ta hty hk tv ta1 hr hl hdec Φ Ψ ρ hΓ hΦ hΨ τ _ _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
    obtain ⟨h1, h2⟩ := hdec
    subst h1 h2
    obtain ⟨a, ha, hat⟩ := evalS_total hl Φ ρ hΓ hΦ
    obtain ⟨b, hb, hbt⟩ := evalS_total hr Φ ρ hΓ hΦ
    cases ty <;> simp [TyV.toTy?] at hty
    · subst hty
      cases a with
      | nat a => simp [Val.ty] at hat
      | bool a =>
        cases b with
        | nat b => simp [Val.ty] at hbt
        | bool b => exact ⟨k.evalBool a b = true, .cmpBool hk ha hb⟩
    · subst hty
      cases a with
      | bool a => simp [Val.ty] at hat
      | nat a =>
        cases b with
        | bool b => simp [Val.ty] at hbt
        | nat b => exact ⟨k.propNat a b, .cmpNat hk ha hb⟩
  -- 28. 比較(被演算子の型が注釈と違う)
  · intro Γ op l r ty k ta hty hk tv ta1 hr hl hne Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hk, hty, hl, hr, hne] at hτ
  -- 29. 比較(被演算子が不適格)
  · intro Γ op l r ty k ta hty hk hno Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 30. 算術(値: 論理の位置ではない)
  · intro Γ op l r ty k hty hk hr hl Φ Ψ ρ _ _ _ τ hτ hf
    simp only [wtS, hk, hty, hl, hr, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 31. 算術(被演算子が不適格)
  · intro Γ op l r ty k hty hk hno Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 32. 対象外の演算子・注釈
  · intro Γ op l r ty h1 h2 h3 h4 h5 Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 33. `!`(適格)
  · intro Γ a j hj hjf iha Φ Ψ ρ hΓ hΦ hΨ τ _ _
    obtain ⟨P, hP⟩ := iha Φ Ψ ρ hΓ hΦ hΨ j hj hjf
    exact ⟨¬ P, .not hP⟩
  -- 34. `!`(被演算子が論理の位置の型でない)
  · intro Γ a j hj hjf _ Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hj, hjf] at hτ
  -- 35. `!`(被演算子が不適格)
  · intro Γ a hj _ Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hj] at hτ
  -- 36. 対象外の単項演算子
  · intro Γ op a hne Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hne] at hτ
  -- 37. Nat の min / max(値)
  · intro Γ m r a k ha hr hm Φ Ψ ρ _ _ _ τ hτ hf
    simp only [wtS, hm, hr, ha, ite_true, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 38. Nat のメソッド(不適格)
  · intro Γ m r a rt hno Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS, ite_true] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 39. Nat 以外のメソッド
  · intro Γ tn m r a rt hne Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hne] at hτ
  -- 40. match(適格)
  · intro Γ s st arms tv ta hta hs hex ih2 Φ Ψ ρ hΓ hΦ hΨ τ hτ _
    simp only [wtS, hs, hta, hex, ite_true] at hτ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hex
    obtain ⟨v, hv, hvt⟩ := evalS_total hs Φ ρ hΓ hΦ
    exact ih2 Φ Ψ ρ hΓ hΦ hΨ τ hτ s st v hv hvt false false hex.2 (fun _ => rfl) (fun _ => rfl)
  -- 41. match(型が違う / 網羅しない)
  · intro Γ s st arms tv ta hta hs hne Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS, hs, hta, hne] at hτ
  -- 42. match(scrutinee が不適格)
  · intro Γ s st arms hno Φ Ψ ρ _ _ _ τ hτ _
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 43. 量化(束縛なし: 対象外)
  · intro Γ q b Φ Ψ ρ _ _ _ τ hτ _
    simp [wtS] at hτ
  -- 44. 量化(適格)
  · intro Γ q bs b Γ' hb j hj hjf _ ih Φ Ψ ρ hΓ hΦ hΨ τ _ _
    have aux : ∀ (bs' : List (String × TyV)) (Γ₀ : SCtx) (ρ₀ : SEnv), Γ₀ = ρ₀.ctx → Γ₀.extBinders bs' = some Γ' →
        ∃ P, Sem Δ Φ Ψ ρ₀ (.quant q bs' b) P := by
      intro bs'
      induction bs' with
      | nil =>
        intro Γ₀ ρ₀ h0 hb0
        simp only [SCtx.extBinders, Option.some.injEq] at hb0
        subst hb0
        obtain ⟨P, hP⟩ := ih Φ Ψ ρ₀ h0 hΦ hΨ j hj hjf
        exact ⟨P, .quantNil hP⟩
      | cons xt rest ihr =>
        obtain ⟨x, tv⟩ := xt
        intro Γ₀ ρ₀ h0 hb0
        simp only [SCtx.extBinders] at hb0
        cases htv : TyV.toTy? tv with
        | none => simp [htv] at hb0
        | some t =>
          simp only [htv] at hb0
          have hall : ∀ a : t.carrier, ∃ P, Sem Δ Φ Ψ (ρ₀.ext x (.val (Val.of t a))) (.quant q rest b) P := fun a =>
            ihr (Γ₀.ext x (.val t)) (ρ₀.ext x (.val (Val.of t a))) (by rw [SEnv.ctx_ext, h0]; simp [SVal.ty]) hb0
          have hF : ∀ a, Sem Δ Φ Ψ (ρ₀.ext x (.val (Val.of t a))) (.quant q rest b) (Classical.choose (hall a)) :=
            fun a => Classical.choose_spec (hall a)
          cases q with
          | forall_ => exact ⟨∀ a, Classical.choose (hall a), .forallCons htv hF⟩
          | exists_ => exact ⟨∃ a, Classical.choose (hall a), .existsCons htv hF⟩
    exact aux bs Γ ρ hΓ hb
  -- 45. 量化(本体が論理の位置の型でない)
  · intro Γ q bs b Γ' hb j hj hjf hne _ Φ Ψ ρ _ _ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj, hjf] at hτ
  -- 46. 量化(本体が不適格)
  · intro Γ q bs b Γ' hb hj hne _ Φ Ψ ρ _ _ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj] at hτ
  -- 47. 量化(束縛の型が対象外)
  · intro Γ q bs b hb hne Φ Ψ ρ _ _ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb] at hτ
  -- 48. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    split at hτ
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
      | exact (h11 _ _ _ rfl).elim
      | (cases hτ; done)
  -- 49. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp p' g' b' heq Φ Ψ ρ _ _ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp at hτ
  -- 50. 腕(ガード無し、適格)
  · intro Γ ts p b bts hp j hj hjf ihb p' g' b' heq Φ Ψ ρ hΓ hΦ hΨ τ hτ v hv bs hm
    cases heq
    have hΓ' : Γ.extVals bts = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb Φ Ψ (ρ.extVals bs) hΓ' hΦ hΨ j hj hjf, ?_⟩
    intro g' hg
    cases hg
  -- 51. 腕(ガード無し、本体が論理の位置の型でない)
  · intro Γ ts p b bts hp j hj hjf _ p' g' b' heq Φ Ψ ρ _ _ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj, hjf] at hτ
  -- 52. 腕(ガード無し、本体が不適格)
  · intro Γ ts p b bts hp hj _ p' g' b' heq Φ Ψ ρ _ _ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj] at hτ
  -- 53. 腕(ガード付き、適格)
  · intro Γ ts p b bts hp g tl tr hb hg ihg ihb p' g' b' heq Φ Ψ ρ hΓ hΦ hΨ τ hτ v hv bs hm
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only [hg, hb] at hτ
    obtain ⟨hgf, hbf, _⟩ := STy.join_isForm hτ
    have hΓ' : Γ.extVals bts = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb Φ Ψ (ρ.extVals bs) hΓ' hΦ hΨ tr hb hbf, ?_⟩
    intro g'' hg''
    cases hg''
    exact ihg Φ Ψ (ρ.extVals bs) hΓ' hΦ hΨ tl hg hgf
  -- 54. 腕(ガード付き、不適格)
  · intro Γ ts p b bts hp g hno _ _ p' g' b' heq Φ Ψ ρ _ _ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 55. 腕の列(空)
  · intro Γ ts Φ Ψ ρ _ _ _ τ hτ
    simp [wtArmsS] at hτ
  -- 56. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ Φ Ψ ρ _ _ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h] at hτ
  -- 57. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 Φ Ψ ρ hΓ hΦ hΨ τ hτ s st v hs hv sawT sawF hex hT hF
    obtain ⟨p, g, b⟩ := arm
    cases g with
    | some g => simp [exhaustiveFrom] at hex
    | none =>
      cases p with
      | wild =>
        obtain ⟨P, hP⟩ := (ih3 .wild none b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 v hv [] rfl).1
        exact ⟨P, .matchHit hs rfl hP⟩
      | bind x =>
        obtain ⟨P, hP⟩ := (ih3 (.bind x) none b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 v hv [(x, v)] rfl).1
        exact ⟨P, .matchHit hs rfl hP⟩
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
                obtain ⟨P, hP⟩ := (ih3 (.lit (.bool true)) none b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 (.bool true) hv [] rfl).1
                exact ⟨P, .matchHit hs rfl hP⟩
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
                obtain ⟨P, hP⟩ := (ih3 (.lit (.bool false)) none b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 (.bool false) hv [] rfl).1
                exact ⟨P, .matchHit hs rfl hP⟩
        | nat n => rw [exhaustiveFrom_nat] at hex; simp [exhaustiveFrom] at hex
        | str s => simp [exhaustiveFrom] at hex
        | unit => simp [exhaustiveFrom] at hex
      | tuple ps => simp [exhaustiveFrom] at hex
      | builtin n ps => simp [exhaustiveFrom] at hex
      | variant k vn ps => simp [exhaustiveFrom] at hex
  -- 58. 腕の列(先頭の腕と残りがともに適格)
  · intro Γ ts arm t1 head tail h1 j hj ih3 ih2 Φ Ψ ρ hΓ hΦ hΨ τ hτ s st v hs hv sawT sawF hex hT hF
    obtain ⟨p, g, b⟩ := arm
    cases hm : matchPat p v with
    | some bs =>
      obtain ⟨⟨P, hP⟩, hguard⟩ := ih3 p g b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 v hv bs hm
      cases g with
      | none => exact ⟨P, .matchHit hs hm hP⟩
      | some g =>
        obtain ⟨G, hG⟩ := hguard g rfl
        rw [exhaustiveFrom_guard] at hex
        obtain ⟨R, hR⟩ := ih2 Φ Ψ ρ hΓ hΦ hΨ j hj s st v hs hv sawT sawF hex hT hF
        exact ⟨(G → P) ∧ (¬ G → R), .matchGuard hs hm hG hP hR⟩
    | none =>
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          ∃ P, Sem Δ Φ Ψ ρ (.match_ s st (Core.Arm.mk p g b :: head :: tail)) P := by
        intro sawT' sawF' hex' hT' hF'
        obtain ⟨R, hR⟩ := ih2 Φ Ψ ρ hΓ hΦ hΨ j hj s st v hs hv sawT' sawF' hex' hT' hF'
        exact ⟨R, .matchSkip hs hm hR⟩
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
  -- 59. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ Φ Ψ ρ _ _ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h1, h2] at hτ

/-- **spec の意味の存在**: 署名と文脈で論理の位置で適格な式は、対応する環境(局所環境・署名を守る関数環境・定義された spec 宣言の環境)で意味を持つ。 -/
theorem Sem_exists {Δ : SigEnv} {Γ : SCtx} {e : Core.Expr} {τ : STy} (h : wtS Δ Γ e = some τ) (hf : τ.isForm = true)
    (Φ : FEnv) (Ψ : PEnv) (ρ : SEnv) (hρ : Γ = ρ.ctx) (hΦ : Φ.Respects Δ) (hΨ : Ψ.Defined Δ) : ∃ P, Sem Δ Φ Ψ ρ e P :=
  (Sem_exists_all Δ).1 Γ e Φ Ψ ρ hρ hΦ hΨ τ h hf

/-! ## spec の意味の一意性 -/

/-- **spec の意味の一意性**: 同じ環境・式の意味は等しい。fn / input の呼出しと spec 宣言の呼出しの規則は署名の phase で排他。 -/
theorem Sem_unique {Δ : SigEnv} {Φ : FEnv} {Ψ : PEnv} {ρ : SEnv} {e : Core.Expr} {P : Prop} (h : Sem Δ Φ Ψ ρ e P) :
    ∀ {Q : Prop}, Sem Δ Φ Ψ ρ e Q → P = Q := by
  induction h with
  | lit =>
    intro Q hQ
    cases hQ
    rfl
  | varVal h =>
    intro Q hQ
    cases hQ with
    | varVal h' => rw [h] at h'; cases h'; rfl
    | varProp h' => rw [h] at h'; cases h'
  | varProp h =>
    intro Q hQ
    cases hQ with
    | varVal h' => rw [h] at h'; cases h'
    | varProp h' => rw [h] at h'; cases h'; rfl
  | callVal hk hf ha hv =>
    intro Q hQ
    cases hQ with
    | callVal hk' hf' ha' hv' => rw [hf] at hf'; cases hf'; rw [ha] at ha'; cases ha'; rw [hv] at hv'; cases hv'; rfl
    | callSpec hk' => exact (not_value_and_spec hk hk').elim
  | callSpec hk hF ha =>
    intro Q hQ
    cases hQ with
    | callVal hk' => exact (not_value_and_spec hk' hk).elim
    | callSpec hk' hF' ha' => rw [hF] at hF'; cases hF'; rw [ha] at ha'; cases ha'; rfl
  | logic hk hl hr ihl ihr =>
    intro Q hQ
    cases hQ with
    | logic hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [ihl hl', ihr hr']
    | eqForm hk' => rw [hk] at hk'; cases hk'
    | cmpBool hk' => rw [hk] at hk'; cases hk'
  | eqNat hk hl hr =>
    intro Q hQ
    cases hQ with
    | eqNat hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [hl] at hl'; cases hl'; rw [hr] at hr'; cases hr'; rfl
    | cmpNat hk' => rw [hk] at hk'; cases hk'
  | eqForm hk hl hr ihl ihr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqForm hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [ihl hl', ihr hr']
    | cmpBool hk' => rw [hk] at hk'; cases hk'
  | cmpNat hk hl hr =>
    intro Q hQ
    cases hQ with
    | eqNat hk' => rw [hk] at hk'; cases hk'
    | cmpNat hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [hl] at hl'; cases hl'; rw [hr] at hr'; cases hr'; rfl
  | cmpBool hk hl hr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqForm hk' => rw [hk] at hk'; cases hk'
    | cmpBool hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [hl] at hl'; cases hl'; rw [hr] at hr'; cases hr'; rfl
  | not h ih =>
    intro Q hQ
    cases hQ with
    | not h' => rw [ih h']
  | ite hc ht he ihc iht ihe =>
    intro Q hQ
    cases hQ with
    | ite hc' ht' he' => rw [ihc hc', iht ht', ihe he']
  | letNat hv hb ihb =>
    intro Q hQ
    cases hQ with
    | letNat hv' hb' => rw [hv] at hv'; cases hv'; exact ihb hb'
  | letBoolVal hp hv hb ihb =>
    intro Q hQ
    cases hQ with
    | letBoolVal hp' hv' hb' => rw [hv] at hv'; cases hv'; exact ihb hb'
    | letProp hp' => rw [hp] at hp'; cases hp'
  | letProp hp hv hb ihv ihb =>
    intro Q hQ
    cases hQ with
    | letBoolVal hp' => rw [hp] at hp'; cases hp'
    | letProp hp' hv' hb' =>
      have := ihv hv'
      subst this
      exact ihb hb'
  | matchSkip hs hp hr ihr =>
    intro Q hQ
    cases hQ with
    | matchSkip hs' hp' hr' => rw [hs] at hs'; cases hs'; exact ihr hr'
    | matchHit hs' hp' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
    | matchGuard hs' hp' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
  | matchHit hs hp hb ihb =>
    intro Q hQ
    cases hQ with
    | matchSkip hs' hp' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
    | matchHit hs' hp' hb' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'; exact ihb hb'
  | matchGuard hs hp hg hb hr ihg ihb ihr =>
    intro Q hQ
    cases hQ with
    | matchSkip hs' hp' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
    | matchGuard hs' hp' hg' hb' hr' =>
      rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
      rw [ihg hg', ihb hb', ihr hr']
  | quantNil h ih =>
    intro Q hQ
    cases hQ with
    | quantNil h' => exact ih h'
  | forallCons ht h ih =>
    intro Q hQ
    cases hQ with
    | forallCons ht' h' =>
      rw [ht] at ht'
      cases ht'
      have hF : _ = _ := funext fun a => ih a (h' a)
      rw [hF]
  | existsCons ht h ih =>
    intro Q hQ
    cases hQ with
    | existsCons ht' h' =>
      rw [ht] at ht'
      cases ht'
      have hF : _ = _ := funext fun a => ih a (h' a)
      rw [hF]

/-! ## 宣言群 -/

theorem SigEnv.ext_self (Δ : SigEnv) (k : String) (s : Sig) : (Δ.ext k s) k = some s := by
  simp [SigEnv.ext]

theorem SigEnv.ext_ne (Δ : SigEnv) (k : String) (s : Sig) {y : String} (h : y ≠ k) : (Δ.ext k s) y = Δ y := by
  simp [SigEnv.ext, h]

theorem FEnv.ext_ne (Φ : FEnv) (k : String) (f : List Val → Option Val) {y : String} (h : y ≠ k) : (Φ.ext k f) y = Φ y := by
  simp [FEnv.ext, h]

theorem PEnv.ext_ne (Ψ : PEnv) (k : String) (F : List Val → Prop) {y : String} (h : y ≠ k) : (Ψ.ext k F) y = Ψ y := by
  simp [PEnv.ext, h]

theorem wtProg_cons {Δ : SigEnv} {d : Decl} {rest : Prog} {Δ' : SigEnv} (h : wtProg Δ (d :: rest) = some Δ') :
    Δ d.key = none ∧ wtDecl Δ d = true ∧ wtProg (Δ.ext d.key d.sig) rest = some Δ' := by
  simp only [wtProg] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    exact ⟨hc.1, hc.2, h⟩
  · cases h

/-- 適格な宣言群の各宣言の鍵は、始めの文脈に無い(重複しない)。 -/
theorem wtProg_fresh : ∀ {Δ₀ Δ : SigEnv} (P : Prog), wtProg Δ₀ P = some Δ → ∀ d ∈ P, Δ₀ d.key = none
  | _, _, [], _, _, hd => by simp at hd
  | Δ₀, Δ, d :: rest, h, d', hd' => by
    obtain ⟨hfresh, _, hrest⟩ := wtProg_cons h
    simp only [List.mem_cons] at hd'
    rcases hd' with rfl | hd'
    · exact hfresh
    · have := wtProg_fresh rest hrest d' hd'
      by_cases hk : d'.key = d.key
      · rw [hk, SigEnv.ext_self] at this
        cases this
      · rwa [SigEnv.ext_ne _ _ _ hk] at this

/-- 始めの文脈の署名は結果の文脈に残る。 -/
theorem wtProg_mono : ∀ {Δ₀ Δ : SigEnv} (P : Prog), wtProg Δ₀ P = some Δ → ∀ k s, Δ₀ k = some s → Δ k = some s
  | _, _, [], h, k, s, hk => by
    simp only [wtProg, Option.some.injEq] at h
    subst h
    exact hk
  | Δ₀, Δ, d :: rest, h, k, s, hk => by
    obtain ⟨hfresh, _, hrest⟩ := wtProg_cons h
    have hne : k ≠ d.key := by
      intro he
      rw [he, hfresh] at hk
      cases hk
    exact wtProg_mono rest hrest k s (by rw [SigEnv.ext_ne _ _ _ hne]; exact hk)

/-- 適格な宣言群の各宣言の署名は結果の文脈にある。 -/
theorem wtProg_sig : ∀ {Δ₀ Δ : SigEnv} (P : Prog), wtProg Δ₀ P = some Δ → ∀ d ∈ P, Δ d.key = some d.sig
  | _, _, [], _, _, hd => by simp at hd
  | Δ₀, Δ, d :: rest, h, d', hd' => by
    obtain ⟨_, _, hrest⟩ := wtProg_cons h
    simp only [List.mem_cons] at hd'
    rcases hd' with rfl | hd'
    · exact wtProg_mono rest hrest _ _ (SigEnv.ext_self Δ₀ d'.key d'.sig)
    · exact wtProg_sig rest hrest d' hd'

theorem Interp.step_Δ (m : Interp) (d : Decl) : (m.step d).Δ = m.Δ.ext d.key d.sig := by
  cases d <;> rfl

theorem Interp.step_Ψ_ne (m : Interp) (d : Decl) {k : String} (h : k ≠ d.key) : (m.step d).Ψ k = m.Ψ k := by
  cases d with
  | fn => rfl
  | spec => exact PEnv.ext_ne _ _ _ h
  | input => rfl

theorem Interp.step_Φ_ne (m : Interp) (d : Decl) {k : String} (h : k ≠ d.key) : (m.step d).Φ k = m.Φ k := by
  cases d with
  | fn => exact FEnv.ext_ne _ _ _ h
  | spec => rfl
  | input => rfl

/-- 宣言群の意味の署名は `wtProg` の署名。 -/
theorem interpFrom_Δ : ∀ (P : Prog) (m : Interp) {Δ : SigEnv}, wtProg m.Δ P = some Δ → (interpFrom m P).Δ = Δ
  | [], m, Δ, h => by
    simp only [wtProg, Option.some.injEq] at h
    simpa [interpFrom] using h
  | d :: rest, m, Δ, h => by
    obtain ⟨_, _, hrest⟩ := wtProg_cons h
    simp only [interpFrom]
    exact interpFrom_Δ rest (m.step d) (by rw [Interp.step_Δ]; exact hrest)

/-- 既に署名のある鍵の意味は、以後の宣言で変わらない(鍵は重複しない)。 -/
theorem interpFrom_stable : ∀ (P : Prog) (m : Interp) {Δ : SigEnv}, wtProg m.Δ P = some Δ → ∀ k s, m.Δ k = some s →
    (interpFrom m P).Φ k = m.Φ k ∧ (interpFrom m P).Ψ k = m.Ψ k
  | [], m, _, _, _, _, _ => ⟨rfl, rfl⟩
  | d :: rest, m, Δ, h, k, s, hk => by
    obtain ⟨hfresh, _, hrest⟩ := wtProg_cons h
    have hne : k ≠ d.key := by
      intro he
      rw [he, hfresh] at hk
      cases hk
    simp only [interpFrom]
    have hk' : (m.step d).Δ k = some s := by rw [Interp.step_Δ, SigEnv.ext_ne _ _ _ hne]; exact hk
    obtain ⟨h1, h2⟩ := interpFrom_stable rest (m.step d) (by rw [Interp.step_Δ]; exact hrest) k s hk'
    exact ⟨by rw [h1, Interp.step_Φ_ne _ _ hne], by rw [h2, Interp.step_Ψ_ne _ _ hne]⟩

/-- 環境の文脈の補題: `Env.ofList` の文脈。 -/
theorem Env.ty_ofList' (xs : List (String × Val)) : (Env.ofList xs).ty = Ctx.ofList (xs.map fun p => (p.1, p.2.ty)) := by
  unfold Env.ofList Ctx.ofList
  rw [Env.ty_extList]
  rfl

theorem zip_ty_eq : ∀ (ps : List (String × Ty)) (vs : List Val), vs.map Val.ty = ps.map (·.2) →
    (((ps.map (·.1)).zip vs).map fun p => (p.1, p.2.ty)) = ps
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | (x, t) :: ps, v :: vs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp [zip_ty_eq ps vs h.2, h.1]

/-- 実引数の束縛は仮引数の文脈に対応する環境を作る。 -/
theorem bindParams_ty {ps : List (String × Ty)} {vs : List Val} (h : vs.map Val.ty = ps.map (·.2)) :
    bindParams ps vs = some (Env.ofList ((ps.map (·.1)).zip vs)) ∧ (Env.ofList ((ps.map (·.1)).zip vs)).ty = paramCtx ps := by
  refine ⟨by simp [bindParams, h], ?_⟩
  rw [Env.ty_ofList', zip_ty_eq ps vs h]
  rfl

theorem bindParams_some {ps : List (String × Ty)} {vs : List Val} {ρ : Env} (h : bindParams ps vs = some ρ) :
    vs.map Val.ty = ps.map (·.2) ∧ ρ = Env.ofList ((ps.map (·.1)).zip vs) := by
  simp only [bindParams] at h
  split at h
  · rename_i hty
    cases h
    exact ⟨hty, rfl⟩
  · cases h

theorem Env.toSEnv_vals (ρ : Env) : (Env.toSEnv ρ).vals = ρ := by
  funext x
  simp only [SEnv.vals, Env.toSEnv]
  cases ρ x <;> rfl

theorem SCtx.extList_vals (Γ : Ctx) (xs : List (String × Ty)) :
    SCtx.extList (fun y => (Γ y).map STy.val) (xs.map fun (x, t) => (x, STy.val t)) = fun y => (Γ.extList xs y).map STy.val := by
  induction xs generalizing Γ with
  | nil => rfl
  | cons xt rest ih =>
    obtain ⟨x, t⟩ := xt
    simp only [List.map_cons, SCtx.extList, Ctx.extList]
    rw [← ih (Γ.ext x t)]
    congr 1
    funext y
    simp only [SCtx.ext, Ctx.ext]
    split <;> rfl

/-- 値だけの環境の文脈は、値の文脈を値に写したもの。 -/
theorem Env.toSEnv_ctx (ρ : Env) : (Env.toSEnv ρ).ctx = fun y => (ρ.ty y).map STy.val := by
  funext y
  simp only [SEnv.ctx, Env.toSEnv, Env.ty]
  cases ρ y <;> rfl

theorem paramSCtx_eq (ps : List (String × Ty)) : paramSCtx ps = fun y => (paramCtx ps y).map STy.val := by
  unfold paramSCtx paramCtx SCtx.ofList Ctx.ofList
  have : SCtx.empty = fun y => (Ctx.empty y).map STy.val := by funext y; rfl
  rw [this, SCtx.extList_vals]

/-- 宣言 1 つの意味を足す段の不変条件: 署名を守る関数環境・input の解釈・定義された spec 宣言の環境は保たれる。 -/
theorem Interp.step_inv (m : Interp) (d : Decl) (rest : Prog) {Δ : SigEnv}
    (hfresh : m.Δ d.key = none) (hwt : wtDecl m.Δ d = true) (hrest : wtProg (m.Δ.ext d.key d.sig) rest = some Δ)
    (hΦ : m.Φ.Respects m.Δ) (hI : m.Φ.RespectsInputs (d :: rest)) (hΨ : m.Ψ.Defined m.Δ) :
    (m.step d).Φ.Respects (m.step d).Δ ∧ (m.step d).Φ.RespectsInputs rest ∧ (m.step d).Ψ.Defined (m.step d).Δ := by
  -- rest の input の鍵は d の鍵と異なる(重複しない)
  have hrestFresh : ∀ k ps t, Decl.input k ps t ∈ rest → k ≠ d.key := by
    intro k ps t hin he
    have := wtProg_fresh rest hrest _ hin
    change (m.Δ.ext d.key d.sig) k = none at this
    rw [he, SigEnv.ext_self] at this
    cases this
  refine ⟨?_, ?_, ?_⟩
  · -- 関数環境が署名を守る
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
        refine ⟨fun vs => match bindParams ps' vs with | some ρ => eval m.Φ ρ body | none => none, ?_, ?_⟩
        · simp [Interp.step, FEnv.ext, Decl.key] <;> rfl
        intro vs hvs
        obtain ⟨hb, hty⟩ := bindParams_ty hvs
        simp only [hb]
        simp only [wtDecl, decide_eq_true_eq] at hwt
        exact eval_total hwt m.Φ _ hty.symm hΦ
      | spec k ps' body => simp [Decl.sig, Sig.value?] at hy
      | input k ps' t' =>
        simp only [Decl.sig, Sig.value?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hy
        obtain ⟨hps, ht⟩ := hy
        subst hps ht
        obtain ⟨f, hf, hfv⟩ := hI k ps' t' (List.mem_cons_self ..)
        exact ⟨f, by simpa [Interp.step, Decl.key] using hf, hfv⟩
    · rw [valueSig?, SigEnv.ext_ne _ _ _ hk] at hy
      obtain ⟨f, hf, hfv⟩ := hΦ y ps t hy
      exact ⟨f, by rw [Interp.step_Φ_ne _ _ hk]; exact hf, hfv⟩
  · -- input の解釈は保たれる
    intro k ps t hin
    obtain ⟨f, hf, hfv⟩ := hI k ps t (List.mem_cons_of_mem _ hin)
    exact ⟨f, by rw [Interp.step_Φ_ne _ _ (hrestFresh k ps t hin)]; exact hf, hfv⟩
  · -- spec 宣言の環境は定義されている
    intro y ps hy
    rw [Interp.step_Δ] at hy
    by_cases hk : y = d.key
    · subst hk
      rw [specSig?, SigEnv.ext_self] at hy
      cases d with
      | fn k ps' t' body => simp [Decl.sig, Sig.spec?] at hy
      | spec k ps' body =>
        exact ⟨fun vs => ∃ ρ, bindParams ps' vs = some ρ ∧ ∃ P, Sem m.Δ m.Φ m.Ψ (Env.toSEnv ρ) body P ∧ P,
          by simp [Interp.step, PEnv.ext, Decl.key]⟩
      | input k ps' t' => simp [Decl.sig, Sig.spec?] at hy
    · rw [specSig?, SigEnv.ext_ne _ _ _ hk] at hy
      obtain ⟨F, hF⟩ := hΨ y ps hy
      exact ⟨F, by rw [Interp.step_Ψ_ne _ _ hk]; exact hF⟩

/-- 適格な宣言群の意味は、その署名を守り(fn の意味は型の合う実引数に型の合う値を返す)、spec 宣言の意味は定義されている。 -/
theorem interpFrom_inv : ∀ (P : Prog) (m : Interp) {Δ : SigEnv}, wtProg m.Δ P = some Δ → m.Φ.Respects m.Δ → m.Φ.RespectsInputs P →
    m.Ψ.Defined m.Δ → (interpFrom m P).Φ.Respects Δ ∧ (interpFrom m P).Ψ.Defined Δ
  | [], m, Δ, h, hΦ, _, hΨ => by
    simp only [wtProg, Option.some.injEq] at h
    subst h
    exact ⟨hΦ, hΨ⟩
  | d :: rest, m, Δ, h, hΦ, hI, hΨ => by
    obtain ⟨hfresh, hwt, hrest⟩ := wtProg_cons h
    obtain ⟨hΦ', hI', hΨ'⟩ := Interp.step_inv m d rest hfresh hwt hrest hΦ hI hΨ
    simp only [interpFrom]
    exact interpFrom_inv rest (m.step d) (by rw [Interp.step_Δ]; exact hrest) hΦ' hI' hΨ'

theorem Interp.init_respects (I : FEnv) : (Interp.init I).Φ.Respects (Interp.init I).Δ := by
  intro k ps t h
  simp [Interp.init, valueSig?, SigEnv.empty] at h

theorem Interp.init_defined (I : FEnv) : (Interp.init I).Ψ.Defined (Interp.init I).Δ := by
  intro k ps h
  simp [Interp.init, specSig?, SigEnv.empty] at h

/-- **宣言群の意味は署名を守る**: 適格な宣言群と input の署名を守る任意の解釈について、各 fn / input の鍵の関数は型の合う実引数に型の合う値を返す。 -/
theorem interp_respects {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ) {I : FEnv} (hI : I.RespectsInputs P) :
    (interp I P).Φ.Respects Δ :=
  (interpFrom_inv P (Interp.init I) hP (Interp.init_respects I) hI (Interp.init_defined I)).1

/-- **spec 宣言の意味は定義されている**。 -/
theorem interp_defined {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ) {I : FEnv} (hI : I.RespectsInputs P) :
    (interp I P).Ψ.Defined Δ :=
  (interpFrom_inv P (Interp.init I) hP (Interp.init_respects I) hI (Interp.init_defined I)).2

theorem interp_Δ {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ) (I : FEnv) : (interp I P).Δ = Δ :=
  interpFrom_Δ P (Interp.init I) hP

/-- **fn の全域性**: 適格な宣言群の各 fn は、型の合う任意の実引数に対して値を持ち、その型は戻り型。 -/
theorem fn_total {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ) {I : FEnv} (hI : I.RespectsInputs P)
    {k : String} {ps : List (String × Ty)} {t : Ty} {body : Core.Expr} (hd : Decl.fn k ps t body ∈ P) :
    ∃ f, (interp I P).Φ k = some f ∧ ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) → ∃ v, f vs = some v ∧ v.ty = t := by
  have hsig := wtProg_sig P hP _ hd
  simp only [Decl.key, Decl.sig] at hsig
  exact interp_respects hP hI k _ t (valueSig?_fn hsig)

/-- **spec 宣言の意味の存在**: 適格な宣言群の各 spec 宣言には意味(実引数の値の列 → 命題)がある。 -/
theorem spec_defined {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ) {I : FEnv} (hI : I.RespectsInputs P)
    {k : String} {ps : List (String × Ty)} {body : Core.Expr} (hd : Decl.spec k ps body ∈ P) :
    ∃ F, (interp I P).Ψ k = some F := by
  have hsig := wtProg_sig P hP _ hd
  simp only [Decl.key, Decl.sig] at hsig
  exact interp_defined hP hI k _ (specSig?_spec hsig)

/-- **spec 宣言の意味は本体の意味**: 適格な宣言群の spec 宣言 `k` の意味 `F` は、型の合う任意の実引数 `vs` について、実引数を束ねた環境での本体の
(それより前の宣言の意味 `m'` の下の)意味 `Q` と同値(`F vs ↔ Q`)。本体の意味は存在して一意(`Sem_exists` / `Sem_unique`)なので、
`Interp.step` の `∃ P, Sem … P ∧ P` は既定値や `False` で埋めたものではなく本体の意味そのもの。 -/
theorem interpFrom_spec_meaning : ∀ (P : Prog) (m : Interp) {Δ : SigEnv}, wtProg m.Δ P = some Δ → m.Φ.Respects m.Δ → m.Φ.RespectsInputs P →
    m.Ψ.Defined m.Δ → ∀ {k : String} {ps : List (String × Ty)} {body : Core.Expr}, Decl.spec k ps body ∈ P →
    ∃ F, (interpFrom m P).Ψ k = some F ∧ ∃ m' : Interp, m'.Φ.Respects m'.Δ ∧ m'.Ψ.Defined m'.Δ ∧
      (∃ τ, wtS m'.Δ (paramSCtx ps) body = some τ ∧ τ.isForm = true) ∧
      ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) → ∃ ρ Q, bindParams ps vs = some ρ ∧ Sem m'.Δ m'.Φ m'.Ψ (Env.toSEnv ρ) body Q ∧ (F vs ↔ Q)
  | [], _, _, _, _, _, _, _, _, _, hd => by simp at hd
  | d :: rest, m, Δ, h, hΦ, hI, hΨ, k, ps, body, hd => by
    obtain ⟨hfresh, hwt, hrest⟩ := wtProg_cons h
    obtain ⟨hΦ', hI', hΨ'⟩ := Interp.step_inv m d rest hfresh hwt hrest hΦ hI hΨ
    simp only [List.mem_cons] at hd
    simp only [interpFrom]
    rcases hd with rfl | hd
    · -- この宣言: 意味は `step` が足したもので、以後変わらない
      have hstable := interpFrom_stable rest (m.step (.spec k ps body)) (by rw [Interp.step_Δ]; exact hrest) k (.spec (ps.map (·.2)))
        (by rw [Interp.step_Δ]; exact SigEnv.ext_self _ _ _)
      refine ⟨fun vs => ∃ ρ, bindParams ps vs = some ρ ∧ ∃ P, Sem m.Δ m.Φ m.Ψ (Env.toSEnv ρ) body P ∧ P, ?_, m, hΦ, hΨ, ?_, ?_⟩
      · rw [hstable.2]
        simp [Interp.step, PEnv.ext]
      · simp only [wtDecl] at hwt
        split at hwt
        · rename_i τ hτ
          exact ⟨τ, hτ, hwt⟩
        · cases hwt
      · intro vs hvs
        obtain ⟨hb, hty⟩ := bindParams_ty hvs
        simp only [wtDecl] at hwt
        split at hwt
        · rename_i τ hτ
          have hctx : paramSCtx ps = (Env.toSEnv (Env.ofList ((ps.map (·.1)).zip vs))).ctx := by
            rw [Env.toSEnv_ctx, hty, paramSCtx_eq]
          obtain ⟨Q, hQ⟩ := Sem_exists hτ hwt m.Φ m.Ψ _ hctx hΦ hΨ
          refine ⟨_, Q, hb, hQ, ?_⟩
          constructor
          · rintro ⟨ρ', hρ', P', hP', hp⟩
            rw [hb] at hρ'
            cases hρ'
            rw [← Sem_unique hP' hQ]
            exact hp
          · intro hq
            exact ⟨_, hb, Q, hQ, hq⟩
        · cases hwt
    · exact interpFrom_spec_meaning rest (m.step d) (by rw [Interp.step_Δ]; exact hrest) hΦ' hI' hΨ' hd

theorem spec_meaning {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ) {I : FEnv} (hI : I.RespectsInputs P)
    {k : String} {ps : List (String × Ty)} {body : Core.Expr} (hd : Decl.spec k ps body ∈ P) :
    ∃ F, (interp I P).Ψ k = some F ∧ ∃ m' : Interp, m'.Φ.Respects m'.Δ ∧ m'.Ψ.Defined m'.Δ ∧
      (∃ τ, wtS m'.Δ (paramSCtx ps) body = some τ ∧ τ.isForm = true) ∧
      ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) → ∃ ρ Q, bindParams ps vs = some ρ ∧ Sem m'.Δ m'.Φ m'.Ψ (Env.toSEnv ρ) body Q ∧ (F vs ↔ Q) :=
  interpFrom_spec_meaning P (Interp.init I) hP (Interp.init_respects I) hI (Interp.init_defined I) hd

end NaruSem.Call
