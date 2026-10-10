import NaruSem.SurfaceEval
import NaruSem.SemTotality

/-!
# 適格な Surface AST と環境には意味が定まる(IDEAL.md C48)

- runtime(表示的意味論 `Surf.eval`): 文脈 `Γ` で適格(`Surf.wtR Γ e = some t`)な式は、対応する環境(`Γ = ρ.ty`)で必ず値を持ち(`Surf.eval_total`)、
  その値の型は `t`。値は関数の結果なので一意(`Surf.Eval_unique`)。
- spec(評価関係 `Surf.Sem`): 文脈 `Γ` で適格(`Surf.wtS Γ e = some τ`、`τ` は論理の位置の型)な式は、対応する環境(`Γ = ρ.ctx`)で意味(命題)が
  存在し(`Surf.Sem_exists`)、意味は一意(`Surf.Sem_unique`)。注釈の無い `==` / `!=` の 2 つの規則(値の等しさ / 命題の同値)が重ならないことは、
  「論理の位置の式(`Sem` の導出のある式)は Nat の値に評価されない」(`Surf.Sem_not_nat`。評価の単調性 `Surf.eval_mono` を使う)から導く。

型付け・スコープ・網羅性(`Surface.lean`)は仮定(適格性の前提)で、frontend の変換の正しさは仮定しない(Core は現れない)。
-/

namespace NaruSem.Surf
open Naru

/-! ## 展開の補題(入れ子の帰納型の上の構造的再帰の等式は、`simp` に定義として渡さずこれらで書き換える) -/

theorem evalArms_cons (ρ : Env) (v : Val) (p : Pat) (g : Option Expr) (b : Expr) (rest : List Arm) :
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

theorem evalStmts_cons (ρ : Env) (sp : Span) (x : String) (ty : Option Ty) (v : Expr) (rest : List Stmt) :
    evalStmts ρ (.letS sp x ty v :: rest) =
      match eval ρ v with
      | some w => evalStmts (ρ.ext x w) rest
      | none => none :=
  evalStmts.eq_2 ρ sp x ty v rest

theorem wtArmR_mk (Γ : Ctx) (ts : NaruSem.Ty) (p : Pat) (g : Option Expr) (b : Expr) :
    wtArmR Γ ts (.mk p g b) =
      match wtPat ts p with
      | none => none
      | some bs =>
        match g with
        | none => wtR (Γ.extPat bs) b
        | some g =>
          match wtR (Γ.extPat bs) g with
          | some .bool => wtR (Γ.extPat bs) b
          | _ => none :=
  wtArmR.eq_1 Γ ts p g b

theorem wtArmS_mk (Γ : SCtx) (ts : NaruSem.Ty) (p : Pat) (g : Option Expr) (b : Expr) :
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

/-- ブロックの `let` 1 つ分の評価の形(末尾式があってもなくても成り立つ)。 -/
theorem eval_block_cons (ρ : Env) (sp lsp : Span) (x : String) (ty : Option Ty) (v : Expr) (rest : List Stmt) (tail : Option Expr) :
    eval ρ (.block sp (.letS lsp x ty v :: rest) tail) =
      match eval ρ v with
      | some w => eval (ρ.ext x w) (.block sp rest tail)
      | none => none := by
  cases tail with
  | none =>
    simp only [eval]
    split <;> rfl
  | some e =>
    simp only [eval, evalStmts_cons]
    cases eval ρ v <;> simp

theorem eval_block_nil (ρ : Env) (sp : Span) (e : Expr) : eval ρ (.block sp [] (some e)) = eval ρ e := by
  simp [eval, evalStmts]

theorem eval_match (ρ : Env) (sp : Span) (s : Expr) (arms : List Arm) (v : Val) (hs : eval ρ s = some v) :
    eval ρ (.matchE sp s arms) = evalArms ρ v arms := by
  simp [eval, hs]

/-! ## パターンと網羅性の補題 -/

/-- パターンの照合が成功すれば、束縛する値の型は型付けが与える束縛の型。 -/
theorem matchPat_types {t : NaruSem.Ty} {p : Pat} {v : Val} {bs : List (String × Val)} {bts : List (String × NaruSem.Ty)}
    (hp : wtPat t p = some bts) (hv : v.ty = t) (hm : matchPat p v = some bs) :
    bs.map (fun (x, w) => (x, w.ty)) = bts := by
  cases p with
  | wild => simp_all [wtPat, matchPat]
  | bind _ x =>
    simp only [wtPat, matchPat, Option.some.injEq] at hp hm
    subst hp hm
    simp [hv]
  | lit _ l =>
    cases l <;> cases v <;> simp_all [wtPat, matchPat, Val.ty] <;> split at hm <;> simp_all

theorem exhaustiveFrom_guard (t : NaruSem.Ty) (sawT sawF : Bool) (p : Pat) (g b : Expr) (rest : List Arm) :
    exhaustiveFrom t sawT sawF (.mk p (some g) b :: rest) = exhaustiveFrom t sawT sawF rest := by
  simp [exhaustiveFrom]

theorem exhaustiveFrom_true (t : NaruSem.Ty) (sawT sawF : Bool) (sp : Span) (b : Expr) (rest : List Arm) :
    exhaustiveFrom t sawT sawF (.mk (.lit sp (.bool true)) none b :: rest) =
      ((decide (t = .bool) && sawF) || exhaustiveFrom t true sawF rest) := by
  simp [exhaustiveFrom]

theorem exhaustiveFrom_false (t : NaruSem.Ty) (sawT sawF : Bool) (sp : Span) (b : Expr) (rest : List Arm) :
    exhaustiveFrom t sawT sawF (.mk (.lit sp (.bool false)) none b :: rest) =
      ((decide (t = .bool) && sawT) || exhaustiveFrom t sawT true rest) := by
  simp [exhaustiveFrom]

theorem exhaustiveFrom_nat (t : NaruSem.Ty) (sawT sawF : Bool) (sp : Span) (n : Nat) (b : Expr) (rest : List Arm) :
    exhaustiveFrom t sawT sawF (.mk (.lit sp (.nat n)) none b :: rest) = exhaustiveFrom t sawT sawF rest := by
  simp [exhaustiveFrom]

theorem annot_eq {ty : Option Ty} {tv t : NaruSem.Ty} (h : annot ty tv = some t) : t = tv := by
  unfold annot at h
  cases ty with
  | none => simp_all
  | some τ =>
    cases hτ : τ.toTy? with
    | none => simp [hτ] at h
    | some ta =>
      simp only [hτ] at h
      split at h <;> simp_all

/-! ## runtime の全域性 -/

/-- `wtR` / `wtStmtsR` / `wtArmsR` / `wtArmR` の関数帰納法で、式・`let` の列・腕の列・腕の 4 つを同時に示す。腕の列では網羅性の走査の状態
(`sawT` / `sawF`)と、値がそのリテラルならもう前の腕で一致していることを不変条件に持つ(Core の `wtR_total_all` と同じ)。 -/
theorem wtR_total_all :
    (∀ (Γ : Ctx) (e : Expr), ∀ ρ : Env, Γ = ρ.ty → ∀ t, wtR Γ e = some t →
        ∃ v, eval ρ e = some v ∧ v.ty = t) ∧
    (∀ (Γ : Ctx) (stmts : List Stmt), ∀ ρ : Env, Γ = ρ.ty → ∀ Γ', wtStmtsR Γ stmts = some Γ' →
        ∃ ρ', evalStmts ρ stmts = some ρ' ∧ Γ' = ρ'.ty) ∧
    (∀ (Γ : Ctx) (ts : NaruSem.Ty) (arms : List Arm), ∀ ρ : Env, Γ = ρ.ty → ∀ t, wtArmsR Γ ts arms = some t →
        ∀ v : Val, v.ty = ts → ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        ∃ w, evalArms ρ v arms = some w ∧ w.ty = t) ∧
    (∀ (Γ : Ctx) (ts : NaruSem.Ty) (arm : Arm), ∀ p g b, arm = .mk p g b → ∀ ρ : Env, Γ = ρ.ty → ∀ t,
        wtArmR Γ ts arm = some t → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        (∃ w, eval (ρ.extList bs) b = some w ∧ w.ty = t) ∧
        (∀ g', g = some g' → ∃ c : Bool, eval (ρ.extList bs) g' = some (.bool c))) := by
  apply wtR.mutual_induct
  -- 1. Nat のリテラル
  · intro Γ _ n ρ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨.nat n, by simp [eval], rfl⟩
  -- 2. Bool のリテラル
  · intro Γ _ b ρ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨.bool b, by simp [eval], rfl⟩
  -- 3. 局所名
  · intro Γ _ x ρ hΓ t ht
    subst hΓ
    simp only [wtR, Env.ty] at ht
    cases h : ρ x with
    | none => simp [h] at ht
    | some v =>
      simp [h] at ht
      exact ⟨v, by simp [eval, h], ht⟩
  -- 4. 二項演算(適格)
  · intro Γ _ op l r k tl tr hr hl hk ihl ihr ρ hΓ t ht
    simp only [wtR, hk, hl, hr] at ht
    obtain ⟨a, ha, hat⟩ := ihl ρ hΓ tl hl
    obtain ⟨b, hb, hbt⟩ := ihr ρ hΓ tr hr
    simp only [eval, hk, ha, hb]
    subst hat hbt
    cases k <;> cases a <;> cases b <;> simp_all [binopResult, BinOp.apply, Val.ty]
  -- 5. 二項演算(不適格)
  · intro Γ _ op l r hno _ _ ρ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 6. `!`(適格)
  · intro Γ _ a ha iha ρ hΓ t ht
    simp only [wtR, ha, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨va, hva, hvat⟩ := iha ρ hΓ .bool ha
    cases va with
    | nat => simp [Val.ty] at hvat
    | bool ba => exact ⟨.bool (!ba), by simp [eval, hva], rfl⟩
  -- 7. `!`(被演算子が Bool でない)
  · intro Γ _ a hno _ ρ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 8. 対象外の単項演算子
  · intro Γ _ op a hne ρ _ t ht
    simp [wtR, hne] at ht
  -- 9. Nat の min / max(適格)
  · intro Γ _ r m a k ha hr hm ihr iha ρ hΓ t ht
    simp only [wtR, hm, hr, ha, Option.some.injEq] at ht
    subst ht
    obtain ⟨x, hx, hxt⟩ := ihr ρ hΓ .nat hr
    obtain ⟨y, hy, hyt⟩ := iha ρ hΓ .nat ha
    cases x with
    | bool => simp [Val.ty] at hxt
    | nat x =>
      cases y with
      | bool => simp [Val.ty] at hyt
      | nat y => exact ⟨.nat (k.eval x y), by simp [eval, hm, hx, hy], rfl⟩
  -- 10. Nat のメソッド(不適格)
  · intro Γ _ r m a hno _ _ ρ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 11. if(適格)
  · intro Γ _ c t e te hte hc htt ihc iht ihe ρ hΓ t' ht'
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
  -- 12. if(分岐の型が違う)
  · intro Γ _ c t e tt te hte htt hc hne _ _ _ ρ _ t' ht'
    simp [wtR, hc, htt, hte, hne] at ht'
  -- 13. if(不適格)
  · intro Γ _ c t e hno _ _ _ ρ _ t' ht'
    simp only [wtR] at ht'
    first
      | (cases ht'; done)
      | (split at ht' <;> simp_all)
  -- 14. match(適格)
  · intro Γ _ s arms ta hs hex ihs iharms ρ hΓ t ht
    simp only [wtR, hs, hex, ite_true] at ht
    obtain ⟨v, hv, hvt⟩ := ihs ρ hΓ ta hs
    obtain ⟨w, hw, hwt⟩ := iharms ρ hΓ t ht v hvt false false hex (fun _ => rfl) (fun _ => rfl)
    exact ⟨w, by simp [eval, hv, hw], hwt⟩
  -- 15. match(網羅しない)
  · intro Γ _ s arms ta hs hne _ ρ _ t ht
    simp [wtR, hs, hne] at ht
  -- 16. match(scrutinee が不適格)
  · intro Γ _ s arms hs _ ρ _ t ht
    simp [wtR, hs] at ht
  -- 17. ブロック(適格)
  · intro Γ _ stmts e Γ' hst ihst ihe ρ hΓ t ht
    simp only [wtR, hst] at ht
    obtain ⟨ρ', hρ', hΓ'⟩ := ihst ρ hΓ Γ' hst
    obtain ⟨w, hw, hwt⟩ := ihe ρ' hΓ' t ht
    exact ⟨w, by simp [eval, hρ', hw], hwt⟩
  -- 18. ブロック(let の列が不適格)
  · intro Γ _ stmts e hst _ ρ _ t ht
    simp [wtR, hst] at ht
  -- 19. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 ρ _ t ht
    rw [wtR.eq_def] at ht
    split at ht
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ rfl).elim
      | exact (h6 _ _ _ _ rfl).elim
      | exact (h7 _ _ _ _ rfl).elim
      | exact (h8 _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | (cases ht; done)
  -- 20. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp p' g' b' heq ρ _ t ht
    cases heq
    rw [wtArmR_mk, hp] at ht
    simp at ht
  -- 21. 腕(ガード無し)
  · intro Γ ts p b bts hp ihb p' g' b' heq ρ hΓ t ht v hv bs hm
    cases heq
    rw [wtArmR_mk, hp] at ht
    simp only at ht
    have hΓ' : Γ.extPat bts = (ρ.extList bs).ty := by
      rw [Env.ty_extList, matchPat_types hp hv hm, hΓ]
      rfl
    refine ⟨ihb (ρ.extList bs) hΓ' t ht, ?_⟩
    intro g' hg
    cases hg
  -- 22. 腕(ガードが Bool)
  · intro Γ ts p b bts hp g hg ihg ihb p' g' b' heq ρ hΓ t ht v hv bs hm
    cases heq
    rw [wtArmR_mk, hp] at ht
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
  -- 23. 腕(ガードが Bool でない)
  · intro Γ ts p b bts hp g hno _ p' g' b' heq ρ _ t ht
    cases heq
    rw [wtArmR_mk, hp] at ht
    simp only at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 24. 腕の列(空)
  · intro Γ ts ρ _ t ht
    simp [wtArmsR] at ht
  -- 25. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ ρ _ t ht
    simp [wtArmsR, h] at ht
  -- 26. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 ρ hΓ t ht v hv sawT sawF hex hT hF
    simp only [wtArmsR, h1, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
    cases g with
    | some g => simp [exhaustiveFrom] at hex
    | none =>
      cases p with
      | wild sp =>
        obtain ⟨w, hw, hwt⟩ := (ih3 (.wild sp) none b rfl ρ hΓ t1 h1 v hv [] rfl).1
        exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
      | bind sp x =>
        obtain ⟨w, hw, hwt⟩ := (ih3 (.bind sp x) none b rfl ρ hΓ t1 h1 v hv [(x, v)] rfl).1
        exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
      | lit sp l =>
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
                obtain ⟨w, hw, hwt⟩ := (ih3 (.lit sp (.bool true)) none b rfl ρ hΓ t1 h1 (.bool true) hv [] rfl).1
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
                obtain ⟨w, hw, hwt⟩ := (ih3 (.lit sp (.bool false)) none b rfl ρ hΓ t1 h1 (.bool false) hv [] rfl).1
                exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
        | nat n => rw [exhaustiveFrom_nat] at hex; simp [exhaustiveFrom] at hex
        | str s => simp [exhaustiveFrom] at hex
        | unit => simp [exhaustiveFrom] at hex
  -- 27. 腕の列(先頭の腕と残りの型が同じ)
  · intro Γ ts arm head tail t2 h2 h1 ih3 ih2 ρ hΓ t ht v hv sawT sawF hex hT hF
    rw [wtArmsR.eq_def] at ht
    simp only [h1, h2, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
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
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          ∃ w, evalArms ρ v (Arm.mk p g b :: head :: tail) = some w ∧ w.ty = t2 := by
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
        | bind => simp [matchPat] at hm
        | lit sp l =>
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
  -- 28. 腕の列(先頭の腕と残りの型が違う)
  · intro Γ ts arm t1 head tail h1 t2 hne h2 _ _ ρ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2, hne] at ht
  -- 29. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ ρ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2] at ht
  -- 30. let の列(空)
  · intro Γ ρ hΓ Γ' h
    simp only [wtStmtsR, Option.some.injEq] at h
    subst h
    exact ⟨ρ, rfl, hΓ⟩
  -- 31. let の列(適格)
  · intro Γ _ x ty v rest ta hv t hann ihv ihrest ρ hΓ Γ' h
    simp only [wtStmtsR, hv, hann] at h
    obtain ⟨w, hw, hwt⟩ := ihv ρ hΓ ta hv
    have ht : t = ta := annot_eq hann
    subst ht
    obtain ⟨ρ', hρ', hΓ'⟩ := ihrest (ρ.ext x w) (by rw [Env.ty_ext, hwt, hΓ]) Γ' h
    exact ⟨ρ', by simp [evalStmts_cons, hw, hρ'], hΓ'⟩
  -- 32. let の列(注釈が合わない)
  · intro Γ _ x ty v rest ta hv hann _ ρ _ Γ' h
    simp [wtStmtsR, hv, hann] at h
  -- 33. let の列(値が不適格)
  · intro Γ _ x ty v rest hv _ ρ _ Γ' h
    simp [wtStmtsR, hv] at h

/-- **runtime の全域性**: 文脈で適格な Surface AST の式は、対応する環境で必ず値を持ち、その型は型付けの型。 -/
theorem eval_total {Γ : Ctx} {e : Expr} {t : NaruSem.Ty} (h : wtR Γ e = some t) (ρ : Env) (hρ : Γ = ρ.ty) :
    ∃ v, eval ρ e = some v ∧ v.ty = t :=
  wtR_total_all.1 Γ e ρ hρ t h

/-- **runtime の一意性**: 評価関係(`Eval ρ e v := eval ρ e = some v`)の結果は一意。 -/
theorem Eval_unique {ρ : Env} {e : Expr} {v w : Val} (hv : Eval ρ e v) (hw : Eval ρ e w) : v = w := by
  unfold Eval at hv hw
  rw [hv] at hw
  exact Option.some.inj hw

/-! ## 評価の単調性 -/

/-- 環境の包含: `ρ₁` の束縛はすべて `ρ₂` にもある。 -/
def Env.Sub (ρ₁ ρ₂ : Env) : Prop := ∀ x v, ρ₁ x = some v → ρ₂ x = some v

theorem Env.Sub.refl (ρ : Env) : Env.Sub ρ ρ := fun _ _ h => h

theorem Env.Sub.ext {ρ₁ ρ₂ : Env} (h : Env.Sub ρ₁ ρ₂) (x : String) (v : Val) : Env.Sub (ρ₁.ext x v) (ρ₂.ext x v) := by
  intro y w hy
  simp only [NaruSem.Env.ext] at hy ⊢
  by_cases hyx : y = x
  · simp only [hyx, ite_true] at hy ⊢
    exact hy
  · simp only [hyx, ite_false] at hy ⊢
    exact h y w hy

theorem Env.Sub.extList {ρ₁ ρ₂ : Env} (h : Env.Sub ρ₁ ρ₂) (bs : List (String × Val)) : Env.Sub (ρ₁.extList bs) (ρ₂.extList bs) := by
  induction bs generalizing ρ₁ ρ₂ with
  | nil => exact h
  | cons xv rest ih =>
    obtain ⟨x, v⟩ := xv
    exact ih (h.ext x v)

/-- **評価の単調性**: 環境を広げても、定まっていた値は変わらない(束縛の無い名前に値を足しても、既に値のある式の評価は同じ)。 -/
theorem eval_mono_all :
    (∀ (ρ : Env) (e : Expr), ∀ ρ₂, Env.Sub ρ ρ₂ → ∀ v, eval ρ e = some v → eval ρ₂ e = some v) ∧
    (∀ (ρ : Env) (stmts : List Stmt), ∀ ρ₂, Env.Sub ρ ρ₂ → ∀ ρ', evalStmts ρ stmts = some ρ' →
        ∃ ρ₂', evalStmts ρ₂ stmts = some ρ₂' ∧ Env.Sub ρ' ρ₂') ∧
    (∀ (ρ : Env) (v : Val) (arms : List Arm), ∀ ρ₂, Env.Sub ρ ρ₂ → ∀ w, evalArms ρ v arms = some w → evalArms ρ₂ v arms = some w) := by
  apply eval.mutual_induct
  -- 1. Nat のリテラル
  · intro ρ _ n ρ₂ _ v h
    simpa [eval] using h
  -- 2. Bool のリテラル
  · intro ρ _ b ρ₂ _ v h
    simpa [eval] using h
  -- 3. 局所名
  · intro ρ _ x ρ₂ hsub v h
    simp only [eval] at h ⊢
    exact hsub x v h
  -- 4. 二項演算(両辺に値)
  · intro ρ _ op l r k a b hr hl hk ihl ihr ρ₂ hsub v h
    simp only [eval, hk, hl, hr] at h
    simp [eval, hk, ihl ρ₂ hsub a hl, ihr ρ₂ hsub b hr, h]
  -- 5. 二項演算(値が無い)
  · intro ρ _ op l r hno _ _ ρ₂ _ v h
    simp only [eval] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 6. `!`(Bool の値)
  · intro ρ _ a x ha iha ρ₂ hsub v h
    simp only [eval, ha, ite_true] at h
    simp [eval, iha ρ₂ hsub _ ha, h]
  -- 7. `!`(値が Bool でない)
  · intro ρ _ a hno _ ρ₂ _ v h
    simp only [eval, ite_true] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 8. 対象外の単項演算子
  · intro ρ _ op a hne ρ₂ _ v h
    simp [eval, hne] at h
  -- 9. min / max(値あり)
  · intro ρ _ r m a k x y ha hr hm ihr iha ρ₂ hsub v h
    simp only [eval, hm, hr, ha] at h
    simp [eval, hm, ihr ρ₂ hsub _ hr, iha ρ₂ hsub _ ha, h]
  -- 10. min / max(値なし)
  · intro ρ _ r m a hno _ _ ρ₂ _ v h
    simp only [eval] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 11. if(真)
  · intro ρ _ c t e hc ihc iht ρ₂ hsub v h
    simp only [eval, hc] at h
    simp [eval, ihc ρ₂ hsub _ hc, iht ρ₂ hsub v h]
  -- 12. if(偽)
  · intro ρ _ c t e hc ihc ihe ρ₂ hsub v h
    simp only [eval, hc] at h
    simp [eval, ihc ρ₂ hsub _ hc, ihe ρ₂ hsub v h]
  -- 13. if(条件に Bool の値が無い)
  · intro ρ _ c t e hnt hnf _ ρ₂ _ v h
    simp only [eval] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 14. match(scrutinee に値)
  · intro ρ _ s arms w hs ihs iharms ρ₂ hsub v h
    simp only [eval, hs] at h
    simp [eval, ihs ρ₂ hsub w hs, iharms ρ₂ hsub v h]
  -- 15. match(scrutinee に値が無い)
  · intro ρ _ s arms hs _ ρ₂ _ v h
    simp [eval, hs] at h
  -- 16. ブロック(let の列に値)
  · intro ρ _ stmts e ρ' hst ihst ihe ρ₂ hsub v h
    simp only [eval, hst] at h
    obtain ⟨ρ₂', hρ₂', hsub'⟩ := ihst ρ₂ hsub ρ' hst
    simp [eval, hρ₂', ihe ρ₂' hsub' v h]
  -- 17. ブロック(let の列に値が無い)
  · intro ρ _ stmts e hst _ ρ₂ _ v h
    simp [eval, hst] at h
  -- 18. 対象外の構文
  · intro e ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 ρ₂ _ v h
    rw [eval.eq_def] at h
    split at h
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ rfl).elim
      | exact (h6 _ _ _ _ rfl).elim
      | exact (h7 _ _ _ _ rfl).elim
      | exact (h8 _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | (cases h; done)
  -- 19. 腕の列(空)
  · intro ρ v ρ₂ _ w h
    simp [evalArms] at h
  -- 20. 腕の列(一致しない)
  · intro ρ v p g b rest hm ih ρ₂ hsub w h
    rw [evalArms_cons, hm] at h ⊢
    exact ih ρ₂ hsub w h
  -- 21. 腕の列(一致、ガード無し)
  · intro ρ v p b rest bs hm ih ρ₂ hsub w h
    rw [evalArms_cons, hm] at h ⊢
    exact ih (ρ₂.extList bs) (hsub.extList bs) w h
  -- 22. 腕の列(一致、ガード真)
  · intro ρ v p b rest bs hm g hg ihg ihb ρ₂ hsub w h
    rw [evalArms_cons, hm] at h ⊢
    simp only [hg] at h
    simp only [ihg (ρ₂.extList bs) (hsub.extList bs) _ hg]
    exact ihb (ρ₂.extList bs) (hsub.extList bs) w h
  -- 23. 腕の列(一致、ガード偽)
  · intro ρ v p b rest bs hm g hg ihg ihrest ρ₂ hsub w h
    rw [evalArms_cons, hm] at h ⊢
    simp only [hg] at h
    simp only [ihg (ρ₂.extList bs) (hsub.extList bs) _ hg]
    exact ihrest ρ₂ hsub w h
  -- 24. 腕の列(一致、ガードに Bool の値が無い)
  · intro ρ v p b rest bs hm g hnt hnf _ ρ₂ _ w h
    rw [evalArms_cons, hm] at h
    simp only at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 25. let の列(空)
  · intro ρ ρ₂ hsub ρ' h
    simp only [evalStmts, Option.some.injEq] at h
    subst h
    exact ⟨ρ₂, rfl, hsub⟩
  -- 26. let の列(値あり)
  · intro ρ _ x ty v rest w hv ihv ihrest ρ₂ hsub ρ' h
    rw [evalStmts_cons, hv] at h
    obtain ⟨ρ₂', hρ₂', hsub'⟩ := ihrest (ρ₂.ext x w) (hsub.ext x w) ρ' h
    exact ⟨ρ₂', by rw [evalStmts_cons, ihv ρ₂ hsub w hv]; exact hρ₂', hsub'⟩
  -- 27. let の列(値なし)
  · intro ρ _ x ty v rest hv _ ρ₂ _ ρ' h
    rw [evalStmts_cons, hv] at h
    cases h

theorem eval_mono {ρ ρ₂ : Env} (hsub : Env.Sub ρ ρ₂) {e : Expr} {v : Val} (h : eval ρ e = some v) : eval ρ₂ e = some v :=
  eval_mono_all.1 ρ e ρ₂ hsub v h

/-! ## 論理の位置の式は Nat の値に評価されない -/

/-- 評価の環境 `ρe` と spec の環境 `ρ` の対応: `ρ` の値の束縛は `ρe` にもあり、`ρ` が命題に束ねた名前は `ρe` で Nat の値を持たない。 -/
def Agree (ρe : Env) (ρ : SEnv) : Prop :=
  (∀ x w, ρ.vals x = some w → ρe x = some w) ∧ (∀ x (P : Prop) n, ρ x = some (.prop P) → ρe x ≠ some (.nat n))

theorem Agree.vals (ρ : SEnv) : Agree ρ.vals ρ := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro x P n hx h
  simp [SEnv.vals, hx] at h

theorem Agree.sub {ρe : Env} {ρ : SEnv} (h : Agree ρe ρ) : Env.Sub ρ.vals ρe := h.1

theorem Agree.ext_val {ρe : Env} {ρ : SEnv} (h : Agree ρe ρ) (x : String) (w : Val) : Agree (ρe.ext x w) (ρ.ext x (.val w)) := by
  refine ⟨?_, ?_⟩
  · intro y u hy
    simp only [SEnv.vals, SEnv.ext, NaruSem.Env.ext] at hy ⊢
    by_cases hyx : y = x
    · simp only [hyx, ite_true] at hy ⊢
      exact hy
    · simp only [hyx, ite_false] at hy ⊢
      exact h.1 y u hy
  · intro y P n hy
    simp only [SEnv.ext, NaruSem.Env.ext] at hy ⊢
    by_cases hyx : y = x
    · simp [hyx] at hy
    · simp only [hyx, ite_false] at hy ⊢
      exact h.2 y P n hy

theorem Agree.ext_prop {ρe : Env} {ρ : SEnv} (h : Agree ρe ρ) (x : String) (w : Val) (hw : ∀ n, w ≠ .nat n) (P : Prop) :
    Agree (ρe.ext x w) (ρ.ext x (.prop P)) := by
  refine ⟨?_, ?_⟩
  · intro y u hy
    simp only [SEnv.vals, SEnv.ext, NaruSem.Env.ext] at hy ⊢
    by_cases hyx : y = x
    · simp [hyx] at hy
    · simp only [hyx, ite_false] at hy ⊢
      exact h.1 y u hy
  · intro y Q n hy
    simp only [SEnv.ext, NaruSem.Env.ext] at hy ⊢
    by_cases hyx : y = x
    · simp only [hyx, ite_true]
      intro heq
      exact hw n (Option.some.inj heq)
    · simp only [hyx, ite_false] at hy ⊢
      exact h.2 y Q n hy

/-- 論理の位置でない演算(論理・等値・比較)の値は Nat でない。 -/
theorem BinOp.apply_not_nat (k : BinOp) (hk : ∀ j, k ≠ .arith j) (a b : Val) (n : Nat) : k.apply a b ≠ some (.nat n) := by
  cases k with
  | arith j => exact (hk j rfl).elim
  | cmp j => cases a <;> cases b <;> simp [BinOp.apply]
  | eq j => cases a <;> cases b <;> simp [BinOp.apply]
  | logic j => cases a <;> cases b <;> simp [BinOp.apply]

/-- 論理・等値・比較の二項演算の評価は Nat の値にならない。 -/
theorem eval_binop_not_nat (ρe : Env) (sp : Span) (op : String) (l r : Expr) (k : BinOp) (hk : BinOp.ofString? op = some k)
    (hna : ∀ j, k ≠ .arith j) (n : Nat) : eval ρe (.binop sp op l r) ≠ some (.nat n) := by
  simp only [eval, hk]
  cases eval ρe l with
  | none => simp
  | some a =>
    cases eval ρe r with
    | none => simp
    | some b =>
      simp only
      exact BinOp.apply_not_nat k hna a b n

theorem Agree.extVals {ρe : Env} {ρ : SEnv} (h : Agree ρe ρ) (bs : List (String × Val)) : Agree (ρe.extList bs) (ρ.extVals bs) := by
  induction bs generalizing ρe ρ with
  | nil => exact h
  | cons xv rest ih =>
    obtain ⟨x, v⟩ := xv
    exact ih (h.ext_val x v)

/-- **論理の位置の式は Nat の値に評価されない**: `Sem` の導出のある式は、対応する評価の環境で Nat の値を持たない(`==` / `!=` の 2 つの規則の排他性)。 -/
theorem Sem_not_nat {ρ : SEnv} {e : Expr} {P : Prop} (h : Sem ρ e P) : ∀ ρe, Agree ρe ρ → ∀ n, eval ρe e ≠ some (.nat n) := by
  induction h with
  | lit => intro ρe _ n; simp [eval]
  | @varVal _ _ x b hx =>
    intro ρe ha n
    have hb : ρe x = some (.bool b) := ha.1 x _ (by simp [SEnv.vals, hx])
    simp [eval, hb]
  | @varProp _ _ x _ hx =>
    intro ρe ha n
    simp only [eval]
    exact ha.2 x _ n hx
  | logic hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | eqNat hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | eqForm hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | cmpNat hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | cmpBool hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | not _ =>
    intro ρe _ n
    simp only [eval, ite_true]
    split <;> simp
  | ite _ _ _ _ iht ihe =>
    intro ρe ha n
    simp only [eval]
    split
    · exact iht ρe ha n
    · exact ihe ρe ha n
    · simp
  | blockTail _ ih =>
    intro ρe ha n
    rw [eval_block_nil]
    exact ih ρe ha n
  | blockLetVal hp hv _ ih =>
    intro ρe ha n
    rw [eval_block_cons, eval_mono ha.sub hv]
    exact ih (ρe.ext _ _) (ha.ext_val _ _) n
  | blockLetProp hp _ _ ihv ih =>
    intro ρe ha n
    rw [eval_block_cons]
    cases hw : eval ρe _ with
    | none => simp
    | some w =>
      simp only
      exact ih (ρe.ext _ w) (ha.ext_prop _ w (fun m heq => ihv ρe ha m (heq ▸ hw)) _) n
  | matchSkip hs hp _ ih =>
    intro ρe ha n
    have hrest := ih ρe ha n
    rw [eval_match _ _ _ _ _ (eval_mono ha.sub hs)] at hrest ⊢
    rw [evalArms_cons, hp]
    exact hrest
  | matchHit hs hp _ ih =>
    intro ρe ha n
    rw [eval_match _ _ _ _ _ (eval_mono ha.sub hs), evalArms_cons, hp]
    exact ih (ρe.extList _) (ha.extVals _) n
  | matchGuard hs hp _ _ _ ihg ihb ihr =>
    intro ρe ha n
    have hrest := ihr ρe ha n
    rw [eval_match _ _ _ _ _ (eval_mono ha.sub hs)] at hrest ⊢
    rw [evalArms_cons, hp]
    simp only
    cases hg : eval (ρe.extList _) _ with
    | none => simp
    | some c =>
      cases c with
      | nat m => exact absurd hg (ihg (ρe.extList _) (ha.extVals _) m)
      | bool cb =>
        cases cb with
        | true => exact ihb (ρe.extList _) (ha.extVals _) n
        | false => exact hrest
  | quantNil _ => intro ρe _ n; simp [eval]
  | forallCons _ _ => intro ρe _ n; simp [eval]
  | existsCons _ _ => intro ρe _ n; simp [eval]

/-! ## spec の意味の存在 -/

theorem evalS_total {Γ : SCtx} {e : Expr} {t : NaruSem.Ty} (h : wtR Γ.vals e = some t) (ρ : SEnv) (hρ : Γ = ρ.ctx) :
    ∃ v, eval ρ.vals e = some v ∧ v.ty = t :=
  eval_total h ρ.vals (by rw [hρ, SEnv.ctx_vals])

theorem Sem_exists_all :
    (∀ (Γ : SCtx) (e : Expr), ∀ ρ : SEnv, Γ = ρ.ctx → ∀ τ, wtS Γ e = some τ → τ.isForm = true →
        ∃ P, Sem ρ e P) ∧
    (∀ (Γ : SCtx) (stmts : List Stmt), ∀ ρ : SEnv, Γ = ρ.ctx → ∀ Γ', wtStmtsS Γ stmts = some Γ' →
        ∀ (sp : Span) (tail : Option Expr), (∀ ρ' : SEnv, Γ' = ρ'.ctx → ∃ P, Sem ρ' (.block sp [] tail) P) →
        ∃ P, Sem ρ (.block sp stmts tail) P) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arms : List Arm), ∀ ρ : SEnv, Γ = ρ.ctx → ∀ τ, wtArmsS Γ ts arms = some τ →
        ∀ (sp : Span) (s : Expr) (v : Val), eval ρ.vals s = some v → v.ty = ts →
        ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        ∃ P, Sem ρ (.matchE sp s arms) P) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arm : Arm), ∀ p g b, arm = .mk p g b → ∀ ρ : SEnv, Γ = ρ.ctx → ∀ τ,
        wtArmS Γ ts arm = some τ → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        (∃ P, Sem (ρ.extVals bs) b P) ∧
        (∀ g', g = some g' → ∃ G, Sem (ρ.extVals bs) g' G)) := by
  apply wtS.mutual_induct
  -- 1. Nat のリテラル(値: 論理の位置ではない)
  · intro Γ _ n ρ _ τ hτ hf
    simp only [wtS, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 2. Bool のリテラル
  · intro Γ _ b ρ _ τ _ _
    exact ⟨b = true, .lit⟩
  -- 3. 局所名
  · intro Γ _ x ρ hΓ τ hτ hf
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
  -- 4. if(適格)
  · intro Γ _ c t e tc tt te hte htt hc j hj ihc iht ihe ρ hΓ τ hτ hf
    obtain ⟨hcf, htf, hjf⟩ := STy.join_isForm hj
    simp only [wtS, hc, htt, hte, hj] at hτ
    obtain ⟨_, hef, _⟩ := STy.join_isForm hτ
    obtain ⟨C, hC⟩ := ihc ρ hΓ tc hc hcf
    obtain ⟨P, hP⟩ := iht ρ hΓ tt htt htf
    obtain ⟨Q, hQ⟩ := ihe ρ hΓ te hte hef
    exact ⟨(C → P) ∧ (¬ C → Q), .ite hC hP hQ⟩
  -- 5. if(条件と then の結びが無い)
  · intro Γ _ c t e tc tt te hte htt hc hj _ _ _ ρ _ τ hτ _
    simp [wtS, hc, htt, hte, hj] at hτ
  -- 6. if(不適格)
  · intro Γ _ c t e hno _ _ _ ρ _ τ hτ _
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 7. 論理演算(適格)
  · intro Γ _ op l r k hk tl tr hr hl ihl ihr ρ hΓ τ hτ hf
    simp only [wtS, hk, hl, hr] at hτ
    obtain ⟨hlf, hrf, _⟩ := STy.join_isForm hτ
    obtain ⟨P, hP⟩ := ihl ρ hΓ tl hl hlf
    obtain ⟨Q, hQ⟩ := ihr ρ hΓ tr hr hrf
    exact ⟨k.prop P Q, .logic hk hP hQ⟩
  -- 8. 論理演算(被演算子が不適格)
  · intro Γ _ op l r k hk hno _ _ ρ _ τ hτ _
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 9. == / !=(両辺が Nat の値)
  · intro Γ _ op l r k hk hnn ρ hΓ τ _ _
    obtain ⟨a, ha, hat⟩ := evalS_total hnn.1 ρ hΓ
    obtain ⟨b, hb, hbt⟩ := evalS_total hnn.2 ρ hΓ
    cases a with
    | bool => simp [Val.ty] at hat
    | nat a =>
      cases b with
      | bool => simp [Val.ty] at hbt
      | nat b => exact ⟨k.propNat a b, .eqNat hk ha hb⟩
  -- 10. == / !=(論理の位置、適格)
  · intro Γ _ op l r k hk hnn tl tr hr hl ihl ihr ρ hΓ τ hτ hf
    simp only [wtS, hk, hnn, ite_false, hl, hr] at hτ
    obtain ⟨hlf, hrf, _⟩ := STy.join_isForm hτ
    obtain ⟨P, hP⟩ := ihl ρ hΓ tl hl hlf
    obtain ⟨Q, hQ⟩ := ihr ρ hΓ tr hr hrf
    exact ⟨k.propIff P Q, .eqForm hk hP hQ⟩
  -- 11. == / !=(論理の位置、被演算子が不適格)
  · intro Γ _ op l r k hk hnn hno _ _ ρ _ τ hτ _
    simp only [wtS, hk, hnn, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 12. 比較(適格)
  · intro Γ _ op l r k hk tr hr hl ρ hΓ τ _ _
    obtain ⟨a, ha, hat⟩ := evalS_total hl ρ hΓ
    obtain ⟨b, hb, hbt⟩ := evalS_total hr ρ hΓ
    cases tr with
    | bool =>
      cases a with
      | nat a => simp [Val.ty] at hat
      | bool a =>
        cases b with
        | nat b => simp [Val.ty] at hbt
        | bool b => exact ⟨k.evalBool a b = true, .cmpBool hk ha hb⟩
    | nat =>
      cases a with
      | bool a => simp [Val.ty] at hat
      | nat a =>
        cases b with
        | bool b => simp [Val.ty] at hbt
        | nat b => exact ⟨k.propNat a b, .cmpNat hk ha hb⟩
  -- 13. 比較(被演算子の型が違う)
  · intro Γ _ op l r k hk tl tr hr hl hne ρ _ τ hτ _
    simp [wtS, hk, hl, hr, hne] at hτ
  -- 14. 比較(被演算子が不適格)
  · intro Γ _ op l r k hk hno ρ _ τ hτ _
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 15. 算術(値: 論理の位置ではない)
  · intro Γ _ op l r k hk hr hl ρ _ τ hτ hf
    simp only [wtS, hk, hl, hr, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 16. 算術(被演算子が不適格)
  · intro Γ _ op l r k hk hno ρ _ τ hτ _
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 17. 対象外の演算子
  · intro Γ _ op l r hk ρ _ τ hτ _
    simp [wtS, hk] at hτ
  -- 18. `!`(適格)
  · intro Γ _ a j hj hjf iha ρ hΓ τ _ _
    obtain ⟨P, hP⟩ := iha ρ hΓ j hj hjf
    exact ⟨¬ P, .not hP⟩
  -- 19. `!`(被演算子が論理の位置の型でない)
  · intro Γ _ a j hj hjf _ ρ _ τ hτ _
    simp [wtS, hj, hjf] at hτ
  -- 20. `!`(被演算子が不適格)
  · intro Γ _ a hj _ ρ _ τ hτ _
    simp [wtS, hj] at hτ
  -- 21. 対象外の単項演算子
  · intro Γ _ op a hne ρ _ τ hτ _
    simp [wtS, hne] at hτ
  -- 22. Nat の min / max(値)
  · intro Γ _ r m a k ha hr hm ρ _ τ hτ hf
    simp only [wtS, hm, hr, ha, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 23. Nat のメソッド(不適格)
  · intro Γ _ r m a hno ρ _ τ hτ _
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 24. match(適格)
  · intro Γ _ s arms ta hs hex ih2 ρ hΓ τ hτ _
    simp only [wtS, hs, hex, ite_true] at hτ
    obtain ⟨v, hv, hvt⟩ := evalS_total hs ρ hΓ
    exact ih2 ρ hΓ τ hτ _ s v hv hvt false false hex (fun _ => rfl) (fun _ => rfl)
  -- 25. match(網羅しない)
  · intro Γ _ s arms ta hs hne ρ _ τ hτ _
    simp [wtS, hs, hne] at hτ
  -- 26. match(scrutinee が不適格)
  · intro Γ _ s arms hs ρ _ τ hτ _
    simp [wtS, hs] at hτ
  -- 27. ブロック(適格)
  · intro Γ sp stmts e Γ' hst ihst ihe ρ hΓ τ hτ hf
    simp only [wtS, hst] at hτ
    refine ihst ρ hΓ Γ' hst sp (some e) ?_
    intro ρ' hρ'
    obtain ⟨P, hP⟩ := ihe ρ' hρ' τ hτ hf
    exact ⟨P, .blockTail hP⟩
  -- 28. ブロック(let の列が不適格)
  · intro Γ _ stmts e hst _ ρ _ τ hτ _
    simp [wtS, hst] at hτ
  -- 29. 量化(束縛なし: 対象外)
  · intro Γ _ q b ρ _ τ hτ _
    simp [wtS] at hτ
  -- 30. 量化(適格)
  · intro Γ sp q bs b Γ' hb j hj hjf _ ih ρ hΓ τ _ _
    have aux : ∀ (bs' : List Binder) (Γ₀ : SCtx) (ρ₀ : SEnv), Γ₀ = ρ₀.ctx → SCtx.extBinders Γ₀ bs' = some Γ' →
        ∃ P, Sem ρ₀ (.quant sp q bs' b) P := by
      intro bs'
      induction bs' with
      | nil =>
        intro Γ₀ ρ₀ h0 hb0
        simp only [SCtx.extBinders, Option.some.injEq] at hb0
        subst hb0
        obtain ⟨P, hP⟩ := ih ρ₀ h0 j hj hjf
        exact ⟨P, .quantNil hP⟩
      | cons bd rest ihr =>
        obtain ⟨x, ty, bsp⟩ := bd
        intro Γ₀ ρ₀ h0 hb0
        simp only [SCtx.extBinders] at hb0
        cases ty with
        | none => simp at hb0
        | some ty =>
          simp only at hb0
          cases htv : ty.toTy? with
          | none => simp [htv] at hb0
          | some t =>
            simp only [htv] at hb0
            have hall : ∀ a : t.carrier, ∃ P, Sem (ρ₀.ext x (.val (Val.of t a))) (.quant sp q rest b) P := fun a =>
              ihr (Γ₀.ext x (.val t)) (ρ₀.ext x (.val (Val.of t a))) (by rw [SEnv.ctx_ext, h0]; simp [SVal.ty]) hb0
            have hF : ∀ a, Sem (ρ₀.ext x (.val (Val.of t a))) (.quant sp q rest b) (Classical.choose (hall a)) :=
              fun a => Classical.choose_spec (hall a)
            cases q with
            | forall_ => exact ⟨∀ a, Classical.choose (hall a), .forallCons htv hF⟩
            | exists_ => exact ⟨∃ a, Classical.choose (hall a), .existsCons htv hF⟩
    exact aux bs Γ ρ hΓ hb
  -- 31. 量化(本体が論理の位置の型でない)
  · intro Γ _ q bs b Γ' hb j hj hjf hne _ ρ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj, hjf] at hτ
  -- 32. 量化(本体が不適格)
  · intro Γ _ q bs b Γ' hb hj hne _ ρ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj] at hτ
  -- 33. 量化(束縛の型が対象外)
  · intro Γ _ q bs b hb hne ρ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb] at hτ
  -- 34. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ρ _ τ hτ _
    rw [wtS.eq_def] at hτ
    split at hτ
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ _ rfl).elim
      | exact (h7 _ _ _ _ rfl).elim
      | exact (h8 _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | exact (h10 _ _ _ _ rfl).elim
      | (cases hτ; done)
  -- 35. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp p' g' b' heq ρ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp at hτ
  -- 36. 腕(ガード無し、適格)
  · intro Γ ts p b bs' hp j hj hjf ihb p' g' b' heq ρ hΓ τ hτ v hv bs hm
    cases heq
    have hΓ' : Γ.extVals bs' = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb (ρ.extVals bs) hΓ' j hj hjf, ?_⟩
    intro g' hg
    cases hg
  -- 37. 腕(ガード無し、本体が論理の位置の型でない)
  · intro Γ ts p b bs' hp j hj hjf _ p' g' b' heq ρ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj, hjf] at hτ
  -- 38. 腕(ガード無し、本体が不適格)
  · intro Γ ts p b bs' hp hj _ p' g' b' heq ρ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj] at hτ
  -- 39. 腕(ガード付き、適格)
  · intro Γ ts p b bs' hp g tl tr hb hg ihg ihb p' g' b' heq ρ hΓ τ hτ v hv bs hm
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only [hg, hb] at hτ
    obtain ⟨hgf, hbf, _⟩ := STy.join_isForm hτ
    have hΓ' : Γ.extVals bs' = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb (ρ.extVals bs) hΓ' tr hb hbf, ?_⟩
    intro g'' hg''
    cases hg''
    exact ihg (ρ.extVals bs) hΓ' tl hg hgf
  -- 40. 腕(ガード付き、不適格)
  · intro Γ ts p b bs' hp g hno _ _ p' g' b' heq ρ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 41. 腕の列(空)
  · intro Γ ts ρ _ τ hτ
    simp [wtArmsS] at hτ
  -- 42. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ ρ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h] at hτ
  -- 43. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 ρ hΓ τ hτ sp s v hs hv sawT sawF hex hT hF
    obtain ⟨p, g, b⟩ := arm
    cases g with
    | some g => simp [exhaustiveFrom] at hex
    | none =>
      cases p with
      | wild psp =>
        obtain ⟨P, hP⟩ := (ih3 (.wild psp) none b rfl ρ hΓ t1 h1 v hv [] rfl).1
        exact ⟨P, .matchHit hs rfl hP⟩
      | bind psp x =>
        obtain ⟨P, hP⟩ := (ih3 (.bind psp x) none b rfl ρ hΓ t1 h1 v hv [(x, v)] rfl).1
        exact ⟨P, .matchHit hs rfl hP⟩
      | lit psp l =>
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
                obtain ⟨P, hP⟩ := (ih3 (.lit psp (.bool true)) none b rfl ρ hΓ t1 h1 (.bool true) hv [] rfl).1
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
                obtain ⟨P, hP⟩ := (ih3 (.lit psp (.bool false)) none b rfl ρ hΓ t1 h1 (.bool false) hv [] rfl).1
                exact ⟨P, .matchHit hs rfl hP⟩
        | nat n => rw [exhaustiveFrom_nat] at hex; simp [exhaustiveFrom] at hex
        | str s => simp [exhaustiveFrom] at hex
        | unit => simp [exhaustiveFrom] at hex
  -- 44. 腕の列(先頭の腕と残りがともに適格)
  · intro Γ ts arm t1 head tail h1 j hj ih3 ih2 ρ hΓ τ hτ sp s v hs hv sawT sawF hex hT hF
    obtain ⟨p, g, b⟩ := arm
    cases hm : matchPat p v with
    | some bs =>
      obtain ⟨⟨P, hP⟩, hguard⟩ := ih3 p g b rfl ρ hΓ t1 h1 v hv bs hm
      cases g with
      | none => exact ⟨P, .matchHit hs hm hP⟩
      | some g =>
        obtain ⟨G, hG⟩ := hguard g rfl
        rw [exhaustiveFrom_guard] at hex
        obtain ⟨R, hR⟩ := ih2 ρ hΓ j hj sp s v hs hv sawT sawF hex hT hF
        exact ⟨(G → P) ∧ (¬ G → R), .matchGuard hs hm hG hP hR⟩
    | none =>
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          ∃ P, Sem ρ (.matchE sp s (Arm.mk p g b :: head :: tail)) P := by
        intro sawT' sawF' hex' hT' hF'
        obtain ⟨R, hR⟩ := ih2 ρ hΓ j hj sp s v hs hv sawT' sawF' hex' hT' hF'
        exact ⟨R, .matchSkip hs hm hR⟩
      cases g with
      | some g =>
        rw [exhaustiveFrom_guard] at hex
        exact step sawT sawF hex hT hF
      | none =>
        cases p with
        | wild => simp [matchPat] at hm
        | bind => simp [matchPat] at hm
        | lit psp l =>
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
  -- 45. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ ρ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h1, h2] at hτ
  -- 46. let の列(空)
  · intro Γ ρ hΓ Γ' h sp tail hk
    simp only [wtStmtsS, Option.some.injEq] at h
    subst h
    exact hk ρ hΓ
  -- 47. let の列(命題に束ねる、適格)
  · intro Γ _ x ty v rest hp hann hv ihv ihrest ρ hΓ Γ' h sp tail hk
    simp only [wtStmtsS, hp, hann, hv, ite_true] at h
    obtain ⟨P, hP⟩ := ihv ρ hΓ .prop hv rfl
    obtain ⟨Q, hQ⟩ := ihrest (ρ.ext x (.prop P)) (by rw [SEnv.ctx_ext, hΓ]; rfl) Γ' h sp tail hk
    exact ⟨Q, .blockLetProp (by rw [← hΓ]; exact hp) hP hQ⟩
  -- 48. let の列(命題だが不適格)
  · intro Γ _ x ty v rest hp hann hno _ ρ _ Γ' h sp tail _
    simp only [wtStmtsS, hp, hann, ite_true] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 49. let の列(命題だが注釈が Bool でない)
  · intro Γ _ x ty v rest hp hann ρ _ Γ' h sp tail _
    simp [wtStmtsS, hp, hann] at h
  -- 50. let の列(値に束ねる、適格)
  · intro Γ _ x ty v rest hp ta hv t hann ihrest ρ hΓ Γ' h sp tail hk
    simp only [Bool.not_eq_true] at hp
    simp only [wtStmtsS, hp, Bool.false_eq_true, ite_false, hv, hann] at h
    obtain ⟨w, hw, hwt⟩ := evalS_total hv ρ hΓ
    have ht : t = ta := annot_eq hann
    subst ht
    obtain ⟨Q, hQ⟩ := ihrest (ρ.ext x (.val w)) (by rw [SEnv.ctx_ext, hΓ]; simp [SVal.ty, hwt]) Γ' h sp tail hk
    exact ⟨Q, .blockLetVal (by rw [← hΓ]; exact hp) hw hQ⟩
  -- 51. let の列(値に束ねる、注釈が合わない)
  · intro Γ _ x ty v rest hp ta hv hann ρ _ Γ' h sp tail _
    simp only [Bool.not_eq_true] at hp
    simp [wtStmtsS, hp, hv, hann] at h
  -- 52. let の列(値が不適格)
  · intro Γ _ x ty v rest hp hv ρ _ Γ' h sp tail _
    simp only [Bool.not_eq_true] at hp
    simp [wtStmtsS, hp, hv] at h

/-- **spec の意味の存在**: 論理の位置で適格な Surface AST の式は、対応する環境で意味(命題)を持つ。 -/
theorem Sem_exists {Γ : SCtx} {e : Expr} {τ : STy} (h : wtS Γ e = some τ) (hf : τ.isForm = true)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) : ∃ P, Sem ρ e P :=
  Sem_exists_all.1 Γ e ρ hρ τ h hf

/-! ## spec の意味の一意性 -/

/-- **spec の意味の一意性**: 同じ環境・式の意味は等しい(`==` / `!=` の 2 つの規則は `Sem_not_nat` で排他)。 -/
theorem Sem_unique {ρ : SEnv} {e : Expr} {P : Prop} (h : Sem ρ e P) : ∀ {Q : Prop}, Sem ρ e Q → P = Q := by
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
    | eqNat hk' => rw [hk] at hk'; cases hk'
    | eqForm hk' => rw [hk] at hk'; cases hk'
    | cmpNat hk' => rw [hk] at hk'; cases hk'
    | cmpBool hk' => rw [hk] at hk'; cases hk'
  | eqNat hk hl hr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqNat hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [hl] at hl'; cases hl'; rw [hr] at hr'; cases hr'; rfl
    | eqForm hk' hl' hr' => exact absurd hl (Sem_not_nat hl' _ (Agree.vals _) _)
    | cmpNat hk' => rw [hk] at hk'; cases hk'
    | cmpBool hk' => rw [hk] at hk'; cases hk'
  | eqForm hk hl hr ihl ihr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqNat hk' hl' hr' => exact absurd hl' (Sem_not_nat hl _ (Agree.vals _) _)
    | eqForm hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [ihl hl', ihr hr']
    | cmpNat hk' => rw [hk] at hk'; cases hk'
    | cmpBool hk' => rw [hk] at hk'; cases hk'
  | cmpNat hk hl hr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqNat hk' => rw [hk] at hk'; cases hk'
    | eqForm hk' => rw [hk] at hk'; cases hk'
    | cmpNat hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [hl] at hl'; cases hl'; rw [hr] at hr'; cases hr'; rfl
    | cmpBool hk' hl' hr' => rw [hl] at hl'; cases hl'
  | cmpBool hk hl hr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqNat hk' => rw [hk] at hk'; cases hk'
    | eqForm hk' => rw [hk] at hk'; cases hk'
    | cmpNat hk' hl' hr' => rw [hl] at hl'; cases hl'
    | cmpBool hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [hl] at hl'; cases hl'; rw [hr] at hr'; cases hr'; rfl
  | not h ih =>
    intro Q hQ
    cases hQ with
    | not h' => rw [ih h']
  | ite hc ht he ihc iht ihe =>
    intro Q hQ
    cases hQ with
    | ite hc' ht' he' => rw [ihc hc', iht ht', ihe he']
  | blockTail h ih =>
    intro Q hQ
    cases hQ with
    | blockTail h' => exact ih h'
  | blockLetVal hp hv hb ihb =>
    intro Q hQ
    cases hQ with
    | blockLetVal hp' hv' hb' => rw [hv] at hv'; cases hv'; exact ihb hb'
    | blockLetProp hp' => rw [hp] at hp'; cases hp'
  | blockLetProp hp hv hb ihv ihb =>
    intro Q hQ
    cases hQ with
    | blockLetVal hp' => rw [hp] at hp'; cases hp'
    | blockLetProp hp' hv' hb' =>
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

end NaruSem.Surf
