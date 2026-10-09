import NaruSem.Totality

/-!
# spec の意味の存在と一意性(IDEAL.md C39)

`Sem_exists`: 文脈 `Γ` で適格(`wtS Γ e = some τ`、`τ` は論理の位置の型)な spec の式は、対応する環境(`Γ = ρ.ctx`)で意味(命題)を持つ。
値の位置の部分式(算術・比較・Nat の等値の被演算子、`match` の scrutinee、`let` の値)は runtime の全域性 `eval_total` で値を得る。
量化は束縛ごとの意味の存在から `Classical.choose` で関数 `F : carrier → Prop` を取り出す。
`Sem_unique`: 導出は決定的なので意味は一意。量化は `F = G`(関数外延性)から `(∀ a, F a) = (∀ a, G a)`。
-/

namespace NaruSem
open Naru

/-! ## 環境と文脈の対応(spec) -/

theorem SEnv.ctx_ext (ρ : SEnv) (x : String) (s : SVal) : (ρ.ext x s).ctx = ρ.ctx.ext x s.ty := by
  funext y
  simp only [SEnv.ctx, SEnv.ext, SCtx.ext]
  split <;> rfl

theorem SEnv.ctx_extList (ρ : SEnv) (bs : List (String × SVal)) :
    (ρ.extList bs).ctx = ρ.ctx.extList (bs.map fun (x, s) => (x, s.ty)) := by
  induction bs generalizing ρ with
  | nil => rfl
  | cons xs rest ih =>
    obtain ⟨x, s⟩ := xs
    simp [SEnv.extList, SCtx.extList, ih, SEnv.ctx_ext]

theorem SEnv.ctx_extVals (ρ : SEnv) (bs : List (String × Val)) :
    (ρ.extVals bs).ctx = ρ.ctx.extVals (bs.map fun (x, v) => (x, v.ty)) := by
  simp [SEnv.extVals, SCtx.extVals, SEnv.ctx_extList, List.map_map, Function.comp_def, SVal.ty]

/-- 値の位置から見た文脈は、値の位置から見た環境の文脈。 -/
theorem SEnv.ctx_vals (ρ : SEnv) : ρ.ctx.vals = ρ.vals.ty := by
  funext x
  simp only [SEnv.ctx, SCtx.vals, SEnv.vals, Env.ty]
  cases ρ x with
  | none => rfl
  | some s => cases s <;> rfl

/-- 値の位置の式: 文脈の値の部分で適格なら、環境の値の部分で値を持つ。 -/
theorem evalS_total {Γ : SCtx} {e : Core.Expr} {t : Ty} (h : wtR Γ.vals e = some t) (ρ : SEnv) (hρ : Γ = ρ.ctx) :
    ∃ v, eval ρ.vals e = some v ∧ v.ty = t :=
  eval_total h ρ.vals (by rw [hρ, SEnv.ctx_vals])

theorem STy.join_isForm {a b j : STy} (h : a.join b = some j) : a.isForm = true ∧ b.isForm = true ∧ j.isForm = true := by
  rcases a with ta | _ <;> rcases b with tb | _ <;> (try cases ta) <;> (try cases tb) <;> simp only [STy.join] at h <;>
    cases h <;> simp [STy.isForm]

/-- `wtArmsS` / `wtArmS` の展開(入れ子の帰納型の上の構造的再帰の等式は補題を通して書き換える)。 -/
theorem wtArmS_mk (Γ : SCtx) (ts : Ty) (p : Core.Pat) (g : Option Core.Expr) (b : Core.Expr) :
    wtArmS Γ ts (.mk p g b) =
      match wtPat ts p with
      | none => none
      | some bs =>
        match g with
        | none =>
          match wtS (Γ.extVals bs) b with
          | some t => if t.isForm then some t else none
          | none => none
        | some g =>
          match wtS (Γ.extVals bs) g, wtS (Γ.extVals bs) b with
          | some tg, some tb => tg.join tb
          | _, _ => none :=
  wtArmS.eq_1 Γ ts p g b

/-! ## 存在 -/

theorem Sem_exists_all :
    (∀ (Γ : SCtx) (e : Core.Expr), ∀ ρ : SEnv, Γ = ρ.ctx → ∀ τ, wtS Γ e = some τ → τ.isForm = true →
        ∃ P, Sem ρ e P) ∧
    (∀ (Γ : SCtx) (ts : Ty) (arms : List Core.Arm), ∀ ρ : SEnv, Γ = ρ.ctx → ∀ τ, wtArmsS Γ ts arms = some τ →
        ∀ (s : Core.Expr) (st : TyV) (v : Val), eval ρ.vals s = some v → v.ty = ts →
        ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        ∃ P, Sem ρ (.match_ s st arms) P) ∧
    (∀ (Γ : SCtx) (ts : Ty) (arm : Core.Arm), ∀ p g b, arm = .mk p g b → ∀ ρ : SEnv, Γ = ρ.ctx → ∀ τ,
        wtArmS Γ ts arm = some τ → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        (∃ P, Sem (ρ.extVals bs) b P) ∧
        (∀ g', g = some g' → ∃ G, Sem (ρ.extVals bs) g' G)) := by
  apply wtS.mutual_induct
  -- 1. Nat のリテラル(値: 論理の位置ではない)
  · intro Γ n ρ _ τ hτ hf
    simp only [wtS, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 2. Bool のリテラル
  · intro Γ b ρ _ τ _ _
    exact ⟨b = true, .lit⟩
  -- 3. 局所名
  · intro Γ x ρ hΓ τ hτ hf
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
  -- 4. let(Nat、適格)
  · intro Γ x ty v b hty hv ihb ρ hΓ τ hτ hf
    simp only [wtS, hty, hv] at hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨w, hw, hwt⟩ := evalS_total hv ρ hΓ
    cases w with
    | bool => simp [Val.ty] at hwt
    | nat n =>
      obtain ⟨Q, hQ⟩ := ihb (ρ.ext x (.val (.nat n))) (by rw [SEnv.ctx_ext, hΓ]; rfl) τ hτ hf
      exact ⟨Q, .letNat hw hQ⟩
  -- 5. let(Nat、値が不適格)
  · intro Γ x ty v b hty hno ρ _ τ hτ _
    simp only [wtS, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 6. let(Bool、命題に束ねる)
  · intro Γ x ty v b hty hp hv ihv ihb ρ hΓ τ hτ hf
    simp only [wtS, hty, hp, hv, ite_true] at hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨P, hP⟩ := ihv ρ hΓ .prop hv rfl
    obtain ⟨Q, hQ⟩ := ihb (ρ.ext x (.prop P)) (by rw [SEnv.ctx_ext, hΓ]; rfl) τ hτ hf
    exact ⟨Q, .letProp (by rw [← hΓ]; exact hp) hP hQ⟩
  -- 7. let(Bool、命題だが不適格)
  · intro Γ x ty v b hty hp hno _ ρ _ τ hτ _
    simp only [wtS, hty, hp, ite_true] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 8. let(Bool、値に束ねる)
  · intro Γ x ty v b hty hp hv ihb ρ hΓ τ hτ hf
    simp only [wtS, hty, hv, Bool.not_eq_true] at hτ
    simp only [Bool.not_eq_true] at hp
    simp only [hp, Bool.false_eq_true, ite_false] at hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨w, hw, hwt⟩ := evalS_total hv ρ hΓ
    cases w with
    | nat => simp [Val.ty] at hwt
    | bool wb =>
      obtain ⟨Q, hQ⟩ := ihb (ρ.ext x (.val (.bool wb))) (by rw [SEnv.ctx_ext, hΓ]; rfl) τ hτ hf
      exact ⟨Q, .letBoolVal (by rw [← hΓ]; exact hp) hw hQ⟩
  -- 9. let(Bool、値が不適格)
  · intro Γ x ty v b hty hp hno ρ _ τ hτ _
    simp only [Bool.not_eq_true] at hp
    simp only [wtS, hty, hp, Bool.false_eq_true, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 10. let(注釈が対象外の型)
  · intro Γ x ty v b hty ρ _ τ hτ _
    simp [wtS, hty] at hτ
  -- 11. if(適格)
  · intro Γ c t e tc tt te hte htt hc j hj ihc iht ihe ρ hΓ τ hτ hf
    obtain ⟨hcf, htf, hjf⟩ := STy.join_isForm hj
    simp only [wtS, hc, htt, hte, hj] at hτ
    obtain ⟨_, hef, _⟩ := STy.join_isForm hτ
    obtain ⟨C, hC⟩ := ihc ρ hΓ tc hc hcf
    obtain ⟨P, hP⟩ := iht ρ hΓ tt htt htf
    obtain ⟨Q, hQ⟩ := ihe ρ hΓ te hte hef
    exact ⟨(C → P) ∧ (¬ C → Q), .ite hC hP hQ⟩
  -- 12. if(条件と then の結びが無い)
  · intro Γ c t e tc tt te hte htt hc hj _ _ _ ρ _ τ hτ _
    simp [wtS, hc, htt, hte, hj] at hτ
  -- 13. if(不適格)
  · intro Γ c t e hno _ _ _ ρ _ τ hτ _
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 14. 論理演算(適格)
  · intro Γ op l r ty k hty hk tl tr hr hl ihl ihr ρ hΓ τ hτ hf
    simp only [wtS, hk, hty, hl, hr] at hτ
    obtain ⟨hlf, hrf, _⟩ := STy.join_isForm hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨P, hP⟩ := ihl ρ hΓ tl hl hlf
    obtain ⟨Q, hQ⟩ := ihr ρ hΓ tr hr hrf
    exact ⟨k.prop P Q, .logic hk hP hQ⟩
  -- 15. 論理演算(被演算子が不適格)
  · intro Γ op l r ty k hty hk hno _ _ ρ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 16. 論理の位置の == / !=(適格)
  · intro Γ op l r ty k hty hk tl tr hr hl ihl ihr ρ hΓ τ hτ hf
    simp only [wtS, hk, hty, hl, hr] at hτ
    obtain ⟨hlf, hrf, _⟩ := STy.join_isForm hτ
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨P, hP⟩ := ihl ρ hΓ tl hl hlf
    obtain ⟨Q, hQ⟩ := ihr ρ hΓ tr hr hrf
    exact ⟨k.propIff P Q, .eqForm hk hP hQ⟩
  -- 17. 論理の位置の == / !=(被演算子が不適格)
  · intro Γ op l r ty k hty hk hno _ _ ρ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 18. Nat の == / !=(適格)
  · intro Γ op l r ty k hty hk hr hl ρ hΓ τ _ _
    cases ty <;> simp [TyV.toTy?] at hty
    obtain ⟨a, ha, hat⟩ := evalS_total hl ρ hΓ
    obtain ⟨b, hb, hbt⟩ := evalS_total hr ρ hΓ
    cases a with
    | bool => simp [Val.ty] at hat
    | nat a =>
      cases b with
      | bool => simp [Val.ty] at hbt
      | nat b => exact ⟨k.propNat a b, .eqNat hk ha hb⟩
  -- 19. Nat の == / !=(被演算子が不適格)
  · intro Γ op l r ty k hty hk hno ρ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 20. 比較(適格)
  · intro Γ op l r ty k ta hty hk tv ta1 hr hl hdec ρ hΓ τ _ _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
    obtain ⟨h1, h2⟩ := hdec
    subst h1 h2
    obtain ⟨a, ha, hat⟩ := evalS_total hl ρ hΓ
    obtain ⟨b, hb, hbt⟩ := evalS_total hr ρ hΓ
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
  -- 21. 比較(被演算子の型が注釈と違う)
  · intro Γ op l r ty k ta hty hk tv ta1 hr hl hne ρ _ τ hτ _
    simp [wtS, hk, hty, hl, hr, hne] at hτ
  -- 22. 比較(被演算子が不適格)
  · intro Γ op l r ty k ta hty hk hno ρ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 23. 算術(値: 論理の位置ではない)
  · intro Γ op l r ty k hty hk hr hl ρ _ τ hτ hf
    simp only [wtS, hk, hty, hl, hr, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 24. 算術(被演算子が不適格)
  · intro Γ op l r ty k hty hk hno ρ _ τ hτ _
    simp only [wtS, hk, hty] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 25. 対象外の演算子・注釈
  · intro Γ op l r ty h1 h2 h3 h4 h5 ρ _ τ hτ _
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 26. `!`(適格)
  · intro Γ a j hj hjf iha ρ hΓ τ _ _
    obtain ⟨P, hP⟩ := iha ρ hΓ j hj hjf
    exact ⟨¬ P, .not hP⟩
  -- 27. `!`(被演算子が論理の位置の型でない)
  · intro Γ a j hj hjf _ ρ _ τ hτ _
    simp [wtS, hj, hjf] at hτ
  -- 28. `!`(被演算子が不適格)
  · intro Γ a hj _ ρ _ τ hτ _
    simp [wtS, hj] at hτ
  -- 29. 対象外の単項演算子
  · intro Γ op a hne ρ _ τ hτ _
    simp [wtS, hne] at hτ
  -- 30. Nat の min / max(値)
  · intro Γ m r a k ha hr hm ρ _ τ hτ hf
    simp only [wtS, hm, hr, ha, ite_true, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 31. Nat のメソッド(不適格)
  · intro Γ m r a rt hno ρ _ τ hτ _
    simp only [wtS, ite_true] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 32. Nat 以外のメソッド
  · intro Γ tn m r a rt hne ρ _ τ hτ _
    simp [wtS, hne] at hτ
  -- 33. match(適格)
  · intro Γ s st arms tv ta hta hs hex ih2 ρ hΓ τ hτ _
    simp only [wtS, hs, hta, hex, ite_true] at hτ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hex
    obtain ⟨v, hv, hvt⟩ := evalS_total hs ρ hΓ
    exact ih2 ρ hΓ τ hτ s st v hv hvt false false hex.2 (fun _ => rfl) (fun _ => rfl)
  -- 34. match(型が違う / 網羅しない)
  · intro Γ s st arms tv ta hta hs hne ρ _ τ hτ _
    simp [wtS, hs, hta, hne] at hτ
  -- 35. match(scrutinee が不適格)
  · intro Γ s st arms hno ρ _ τ hτ _
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 36. 量化(束縛なし: 対象外)
  · intro Γ q b ρ _ τ hτ _
    simp [wtS] at hτ
  -- 37. 量化(適格)
  · intro Γ q bs b Γ' hb j hj hjf _ ih ρ hΓ τ _ _
    have aux : ∀ (bs' : List (String × TyV)) (Γ₀ : SCtx) (ρ₀ : SEnv), Γ₀ = ρ₀.ctx → Γ₀.extBinders bs' = some Γ' →
        ∃ P, Sem ρ₀ (.quant q bs' b) P := by
      intro bs'
      induction bs' with
      | nil =>
        intro Γ₀ ρ₀ h0 hb0
        simp only [SCtx.extBinders, Option.some.injEq] at hb0
        subst hb0
        obtain ⟨P, hP⟩ := ih ρ₀ h0 j hj hjf
        exact ⟨P, .quantNil hP⟩
      | cons xt rest ihr =>
        obtain ⟨x, tv⟩ := xt
        intro Γ₀ ρ₀ h0 hb0
        simp only [SCtx.extBinders] at hb0
        cases htv : TyV.toTy? tv with
        | none => simp [htv] at hb0
        | some t =>
          simp only [htv] at hb0
          have hall : ∀ a : t.carrier, ∃ P, Sem (ρ₀.ext x (.val (Val.of t a))) (.quant q rest b) P := fun a =>
            ihr (Γ₀.ext x (.val t)) (ρ₀.ext x (.val (Val.of t a))) (by rw [SEnv.ctx_ext, h0]; simp [SVal.ty]) hb0
          have hF : ∀ a, Sem (ρ₀.ext x (.val (Val.of t a))) (.quant q rest b) (Classical.choose (hall a)) :=
            fun a => Classical.choose_spec (hall a)
          cases q with
          | forall_ => exact ⟨∀ a, Classical.choose (hall a), .forallCons htv hF⟩
          | exists_ => exact ⟨∃ a, Classical.choose (hall a), .existsCons htv hF⟩
    exact aux bs Γ ρ hΓ hb
  -- 38. 量化(本体が論理の位置の型でない)
  · intro Γ q bs b Γ' hb j hj hjf hne _ ρ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj, hjf] at hτ
  -- 39. 量化(本体が不適格)
  · intro Γ q bs b Γ' hb hj hne _ ρ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj] at hτ
  -- 40. 量化(束縛の型が対象外)
  · intro Γ q bs b hb hne ρ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb] at hτ
  -- 41. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ρ _ τ hτ _
    rw [wtS.eq_def] at hτ
    split at hτ
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
      | exact (h10 _ _ _ rfl).elim
      | (cases hτ; done)
  -- 42. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp p' g' b' heq ρ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp at hτ
  -- 43. 腕(ガード無し、適格)
  · intro Γ ts p b bts hp j hj hjf ihb p' g' b' heq ρ hΓ τ hτ v hv bs hm
    cases heq
    have hΓ' : Γ.extVals bts = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb (ρ.extVals bs) hΓ' j hj hjf, ?_⟩
    intro g' hg
    cases hg
  -- 44. 腕(ガード無し、本体が論理の位置の型でない)
  · intro Γ ts p b bts hp j hj hjf _ p' g' b' heq ρ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj, hjf] at hτ
  -- 45. 腕(ガード無し、本体が不適格)
  · intro Γ ts p b bts hp hj _ p' g' b' heq ρ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj] at hτ
  -- 46. 腕(ガード付き、適格)
  · intro Γ ts p b bts hp g tl tr hb hg ihg ihb p' g' b' heq ρ hΓ τ hτ v hv bs hm
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only [hg, hb] at hτ
    obtain ⟨hgf, hbf, _⟩ := STy.join_isForm hτ
    have hΓ' : Γ.extVals bts = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb (ρ.extVals bs) hΓ' tr hb hbf, ?_⟩
    intro g'' hg''
    cases hg''
    exact ihg (ρ.extVals bs) hΓ' tl hg hgf
  -- 47. 腕(ガード付き、不適格)
  · intro Γ ts p b bts hp g hno _ _ p' g' b' heq ρ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 48. 腕の列(空)
  · intro Γ ts ρ _ τ hτ
    simp [wtArmsS] at hτ
  -- 49. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ ρ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h] at hτ
  -- 50. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 ρ hΓ τ hτ s st v hs hv sawT sawF hex hT hF
    obtain ⟨p, g, b⟩ := arm
    cases g with
    | some g => simp [exhaustiveFrom] at hex
    | none =>
      cases p with
      | wild =>
        obtain ⟨P, hP⟩ := (ih3 .wild none b rfl ρ hΓ t1 h1 v hv [] rfl).1
        exact ⟨P, .matchHit hs rfl hP⟩
      | bind x =>
        obtain ⟨P, hP⟩ := (ih3 (.bind x) none b rfl ρ hΓ t1 h1 v hv [(x, v)] rfl).1
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
                obtain ⟨P, hP⟩ := (ih3 (.lit (.bool true)) none b rfl ρ hΓ t1 h1 (.bool true) hv [] rfl).1
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
                obtain ⟨P, hP⟩ := (ih3 (.lit (.bool false)) none b rfl ρ hΓ t1 h1 (.bool false) hv [] rfl).1
                exact ⟨P, .matchHit hs rfl hP⟩
        | nat n => rw [exhaustiveFrom_nat] at hex; simp [exhaustiveFrom] at hex
        | str s => simp [exhaustiveFrom] at hex
        | unit => simp [exhaustiveFrom] at hex
      | tuple ps => simp [exhaustiveFrom] at hex
      | builtin n ps => simp [exhaustiveFrom] at hex
      | variant k vn ps => simp [exhaustiveFrom] at hex
  -- 51. 腕の列(先頭の腕と残りがともに適格)
  · intro Γ ts arm t1 head tail h1 j hj ih3 ih2 ρ hΓ τ hτ s st v hs hv sawT sawF hex hT hF
    obtain ⟨p, g, b⟩ := arm
    cases hm : matchPat p v with
    | some bs =>
      obtain ⟨⟨P, hP⟩, hguard⟩ := ih3 p g b rfl ρ hΓ t1 h1 v hv bs hm
      cases g with
      | none => exact ⟨P, .matchHit hs hm hP⟩
      | some g =>
        obtain ⟨G, hG⟩ := hguard g rfl
        rw [exhaustiveFrom_guard] at hex
        obtain ⟨R, hR⟩ := ih2 ρ hΓ j hj s st v hs hv sawT sawF hex hT hF
        exact ⟨(G → P) ∧ (¬ G → R), .matchGuard hs hm hG hP hR⟩
    | none =>
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          ∃ P, Sem ρ (.match_ s st (Core.Arm.mk p g b :: head :: tail)) P := by
        intro sawT' sawF' hex' hT' hF'
        obtain ⟨R, hR⟩ := ih2 ρ hΓ j hj s st v hs hv sawT' sawF' hex' hT' hF'
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
  -- 52. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ ρ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h1, h2] at hτ

/-- **spec の意味の存在**: 論理の位置で適格な式は、対応する環境で意味(命題)を持つ。 -/
theorem Sem_exists {Γ : SCtx} {e : Core.Expr} {τ : STy} (h : wtS Γ e = some τ) (hf : τ.isForm = true)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) : ∃ P, Sem ρ e P :=
  Sem_exists_all.1 Γ e ρ hρ τ h hf

/-! ## 一意性 -/

/-- **spec の意味の一意性**: 同じ環境・式の意味は等しい。 -/
theorem Sem_unique {ρ : SEnv} {e : Core.Expr} {P : Prop} (h : Sem ρ e P) : ∀ {Q : Prop}, Sem ρ e Q → P = Q := by
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

end NaruSem
