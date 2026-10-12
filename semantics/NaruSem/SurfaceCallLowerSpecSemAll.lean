import NaruSem.SurfaceCallCallSem
import NaruSem.CallDenoteProp

/-!
# 呼出しを含む全 spec 式の一般双方向意味保存(IDEAL.md C55、用語「関数・input の保存対象」)

`Surf.Call.wtS.mutual_induct` で式・let 列・腕列・腕を同時に帰納し、既存の局所合成
(let 列 `SpecLetsBridge`、腕列 `SpecArmsBridge`、量化 `lowerS_quant_equiv`、論理 / 否定 / if、
Nat / Bool の比較・値等値・命題等値、通常呼出し / UFCS の葉)を子式の帰納結果で結ぶ。
局所合成が明示的な前提にしていた子式の `SpecSemEquiv` は、ここで型付けの帰納から導く。
命題等値の左子式が Nat を評価しないことは、spec 解釈をすべて補った環境での意味の存在
(`Sem_exists`)と `Sem_not_nat` から導く(評価は spec 解釈に依らない)。

結論 `lowerS_sem_iff`: 任意の宣言表・文脈で論理の位置で適格な spec の Surface 式と、独立 lowering
`lowerS` の実出力の Core について、署名を守る任意の関数 / input 解釈 `Φ`・任意の spec 解釈 `Ψ`
(不在を含む)・型付け文脈と一致する任意の環境 `ρ` で、同じ命題が Surface の意味であることと
Core の意味であることは同値。意味の存在や `Ψ.Defined` は仮定しない(意味の不在も両側で保つ)。
`lowerS_denote` は C44 / C55 の Core → 実生成 Lean の読み(`Call.denoteP`)まで合成する。

Surface / Core の宣言群からの callee 環境の対応(`Φ` / `Ψ` が宣言群の意味であること)と、
現在の実生成 Statements 宣言への接続は別の義務で、この定理はそれらを前提にも結論にもしない。
-/
namespace NaruSem.Surf.Call
open Naru

/-- 論理の位置で適格な式は、署名を守る任意の関数 / input 解釈の下で Nat の値に評価されない。
spec 解釈をすべて補った環境で意味が存在し(`Sem_exists`)、論理の位置の式は Nat に評価されない
(`Sem_not_nat`)。評価は spec 解釈に依らないので、任意の `Ψ`(不在を含む)で使える。 -/
theorem eval_not_nat_of_wtS {T : Table} {Γ : SCtx} {e : Expr} {τ : STy}
    (hw : wtS T Γ e = some τ) (hf : τ.isForm = true)
    {Φ : NaruSem.Call.FEnv} (hΦ : Φ.Respects T.Δ) {ρ : SEnv} (hΓ : Γ = ρ.ctx) (n : Nat) :
    eval T Φ ρ e ≠ some (.nat n) := by
  obtain ⟨P, hP⟩ := Sem_exists hw hf Φ (fun _ => some fun _ => True) ρ hΓ hΦ
    (fun _ _ _ => ⟨fun _ => True, rfl⟩)
  exact Sem_not_nat hP ρ (Agree.refl ρ) n

/-- **全 4 構文群の spec の双方向意味保存**: 式は `SpecSemEquiv`、let 列は末尾の対応から
`SpecLetsBridge`、腕列は `SpecArmsBridge`、腕は後続の腕列の証明書を 1 つ伸ばす。
関数 / input 環境は署名を守る任意の解釈、spec 環境は任意。 -/
theorem lowerS_sem_all (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (hΦ : Φ.Respects T.Δ) :
    (∀ (Γ : SCtx) (e : Expr), ∀ τ, wtS T Γ e = some τ →
      ∀ c, lowerS T Γ e = some c → SpecSemEquiv T Φ Ψ Γ e c) ∧
    (∀ (Γ : SCtx) (stmts : List Stmt), ∀ Γ', wtStmtsS T Γ stmts = some Γ' →
      ∀ binds, lowerStmtsS T Γ stmts = some binds →
      ∀ (e : Expr) (c : Core.Expr), SpecSemEquiv T Φ Ψ Γ' e c →
        SpecLetsBridge T Φ Ψ Γ stmts binds e c) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arms : List Arm), ∀ τ, wtArmsS T Γ ts arms = some τ →
      ∀ cas, lowerArmsS T Γ ts arms = some cas → SpecArmsBridge T Φ Ψ Γ ts arms cas) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arm : Arm), ∀ τ, wtArmS T Γ ts arm = some τ →
      ∀ ca, lowerArmS T Γ ts arm = some ca →
      ∀ (rest : List Arm) (cas : List Core.Arm), SpecArmsBridge T Φ Ψ Γ ts rest cas →
        SpecArmsBridge T Φ Ψ Γ ts (arm :: rest) (ca :: cas)) := by
  apply wtS.mutual_induct T
  -- 1. Nat のリテラル(値): どちらの側にも意味の導出が無い
  · intro Γ _ n τ hτ c hc
    simp only [lowerS, Option.some.injEq] at hc
    subst hc
    intro ρ _ P
    constructor
    · intro h; cases h
    · intro h; cases h
  -- 2. Bool のリテラル
  · intro Γ _ b τ hτ c hc
    simp only [lowerS, Option.some.injEq] at hc
    subst hc
    apply SpecSemEquiv.of_iff
    intro ρ _ P
    constructor
    · intro h; cases h; exact .lit
    · intro h; cases h; exact .lit
  -- 3. 局所名
  · intro Γ _ x τ hτ c hc
    simp only [lowerS, Option.some.injEq] at hc
    subst hc
    apply SpecSemEquiv.of_iff
    intro ρ _ P
    constructor
    · intro h
      cases h with
      | varVal h => exact .varVal h
      | varProp h => exact .varProp h
    · intro h
      cases h with
      | varVal h => exact .varVal h
      | varProp h => exact .varProp h
  -- 4. 呼出し(頭が局所名に隠される)
  · intro Γ _ _ path args hb τ hτ
    simp [wtS, hb] at hτ
  -- 5. 呼出し(適格): 呼出し葉の双方向保存
  · intro Γ _ _ path args hnb tys hargs τ hτ c hc
    exact lowerS_call_equiv hτ hc hΦ
  -- 6. 呼出し(実引数が不適格)
  · intro Γ _ _ path args hnb hargs τ hτ
    simp only [Bool.not_eq_true] at hnb
    simp [wtS, hnb, hargs] at hτ
  -- 7. if(適格)
  · intro Γ _ c t e tc tt te hte htt hc j hj ihc iht ihe τ hτ d hd
    obtain ⟨cc, hcc⟩ := lowerS_total hc
    obtain ⟨ct, hct⟩ := lowerS_total htt
    obtain ⟨ce, hce⟩ := lowerS_total hte
    have he : d = .ite cc ct ce := by
      simpa only [lowerS, hcc, hct, hce, Option.some.injEq] using hd.symm
    subst he
    exact lowerS_ite_equiv (ihc tc hc cc hcc) (iht tt htt ct hct) (ihe te hte ce hce)
  -- 8. if(条件と then の結びが無い)
  · intro Γ _ c t e tc tt te hte htt hc hj _ _ _ τ hτ
    simp [wtS, hc, htt, hte, hj] at hτ
  -- 9. if(不適格)
  · intro Γ _ c t e hno _ _ _ τ hτ
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 10. 論理演算(適格)
  · intro Γ _ op l r k hk tl tr hr hl ihl ihr τ hτ d hd
    obtain ⟨cl, hcl⟩ := lowerS_total hl
    obtain ⟨cr, hcr⟩ := lowerS_total hr
    have he : d = .binop op cl cr .bool := by
      simpa only [lowerS, hk, hcl, hcr, Option.some.injEq] using hd.symm
    subst he
    exact lowerS_logic_equiv hk (ihl tl hl cl hcl) (ihr tr hr cr hcr)
  -- 11. 論理演算(被演算子が不適格)
  · intro Γ _ op l r k hk hno _ _ τ hτ
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 12. == / !=(両辺が Nat の値: 値の等値、注釈 `.nat`)
  · intro Γ _ op l r k hk hnn τ hτ d hd
    obtain ⟨cl, hcl⟩ := lower_total hnn.1
    obtain ⟨cr, hcr⟩ := lower_total hnn.2
    have he : d = .binop op cl cr .nat := by
      simpa only [lowerS, hk, hnn.1, hnn.2, and_self, ite_true, hcl, hcr,
        Option.some.injEq] using hd.symm
    subst he
    exact lowerS_eqNat_equiv hk hnn.1 hnn.2 hcl hcr hΦ
  -- 13. == / !=(論理の位置、適格: 注釈 `.bool`)。左子式が Nat を評価しないことは帰納の外で導く
  · intro Γ _ op l r k hk hnn tl tr hr hl ihl ihr τ hτ d hd
    simp only [wtS, hk, hnn, ite_false, hl, hr] at hτ
    obtain ⟨cl, hcl⟩ := lowerS_total hl
    obtain ⟨cr, hcr⟩ := lowerS_total hr
    have he : d = .binop op cl cr .bool := by
      simpa only [lowerS, hk, hnn, ite_false, hcl, hcr, Option.some.injEq] using hd.symm
    subst he
    have hform : tl.isForm = true := (STy.join_isForm hτ).1
    exact lowerS_eqForm_equiv hk (fun _ hΓ n => eval_not_nat_of_wtS hl hform hΦ hΓ n)
      (ihl tl hl cl hcl) (ihr tr hr cr hcr)
  -- 14. == / !=(論理の位置、被演算子が不適格)
  · intro Γ _ op l r k hk hnn hno _ _ τ hτ
    simp only [wtS, hk, hnn, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 15. 比較(適格: 注釈は被演算子の型)
  · intro Γ _ op l r k hk tr hr hl τ hτ d hd
    obtain ⟨cl, hcl⟩ := lower_total hl
    obtain ⟨cr, hcr⟩ := lower_total hr
    have he : d = .binop op cl cr tr.toTyV := by
      simpa only [lowerS, hk, hl, hcl, hcr, Option.some.injEq] using hd.symm
    subst he
    exact lowerS_cmp_equiv hk hl hr hcl hcr hΦ
  -- 16. 比較(被演算子の型が違う)
  · intro Γ _ op l r k hk tl tr hr hl hne τ hτ
    simp [wtS, hk, hl, hr, hne] at hτ
  -- 17. 比較(被演算子が不適格)
  · intro Γ _ op l r k hk hno τ hτ
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 18. 算術(値): どちらの側にも意味の導出が無い
  · intro Γ _ op l r k hk hr hl τ hτ d hd
    obtain ⟨cl, hcl⟩ := lower_total hl
    obtain ⟨cr, hcr⟩ := lower_total hr
    have he : d = .binop op cl cr .nat := by
      simpa only [lowerS, hk, hcl, hcr, Option.some.injEq] using hd.symm
    subst he
    intro ρ _ P
    constructor
    · intro h
      cases h with
      | logic hk' => rw [hk] at hk'; cases hk'
      | eqNat hk' => rw [hk] at hk'; cases hk'
      | eqForm hk' => rw [hk] at hk'; cases hk'
      | cmpNat hk' => rw [hk] at hk'; cases hk'
      | cmpBool hk' => rw [hk] at hk'; cases hk'
    · intro h
      cases h with
      | eqNat hk' => rw [hk] at hk'; cases hk'
      | cmpNat hk' => rw [hk] at hk'; cases hk'
  -- 19. 算術(被演算子が不適格)
  · intro Γ _ op l r k hk hno τ hτ
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 20. 対象外の演算子
  · intro Γ _ op l r hk τ hτ
    simp [wtS, hk] at hτ
  -- 21. `!`(適格)
  · intro Γ _ a j hj hjf iha τ hτ d hd
    obtain ⟨ca, hca⟩ := lowerS_total hj
    have he : d = .unop "!" ca := by
      simpa only [lowerS, ite_true, hca, Option.some.injEq] using hd.symm
    subst he
    exact lowerS_not_equiv (iha j hj ca hca)
  -- 22. `!`(被演算子が論理の位置の型でない)
  · intro Γ _ a j hj hjf _ τ hτ
    simp [wtS, hj, hjf] at hτ
  -- 23. `!`(被演算子が不適格)
  · intro Γ _ a hj _ τ hτ
    simp [wtS, hj] at hτ
  -- 24. 対象外の単項演算子
  · intro Γ _ op a hne τ hτ
    simp [wtS, hne] at hτ
  -- 25. UFCS(適格): 呼出し葉の双方向保存
  · intro Γ _ r m args hu tr tys hargs hr τ hτ d hd
    exact lowerS_ufcs_equiv hu hτ hd hΦ
  -- 26. UFCS(受け手か実引数が不適格)
  · intro Γ _ r m args hu hno τ hτ
    rw [wtS.eq_def] at hτ
    simp only [hu, ite_true] at hτ
    cases hr : wtR T Γ r with
    | none => simp at hτ
    | some tr =>
      cases ha : wtArgs T Γ args with
      | none => simp at hτ
      | some tys => exact (hno tr tys hr ha).elim
  -- 27. Nat の min / max(値): どちらの側にも意味の導出が無い
  · intro Γ sp r m hnu a k ha hr hm τ hτ d hd
    simp only [Bool.not_eq_true] at hnu
    obtain ⟨cr, hcr⟩ := lower_total hr
    obtain ⟨ca, hca⟩ := lower_total ha
    have hd' : lowerS T Γ (.method sp r m [.pos a]) = some (.method "Nat" m cr [ca] .nat) := by
      simp [lowerS, hnu, hm, hcr, hca]
    have hdd := Option.some.inj (hd'.symm.trans hd)
    subst hdd
    intro ρ hΓ P
    constructor
    · intro h
      cases h with
      | ufcsVal hu' => rw [← ufcs_ctx T ρ m, ← hΓ, hnu] at hu'; cases hu'
      | ufcsSpec hu' => rw [← ufcs_ctx T ρ m, ← hΓ, hnu] at hu'; cases hu'
    · intro h
      cases h
  -- 28. Nat の min / max(受け手か実引数が不適格)
  · intro Γ _ r m hnu a hno τ hτ
    simp only [Bool.not_eq_true] at hnu
    rw [wtS.eq_def] at hτ
    simp only [hnu, Bool.false_eq_true, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 29. メソッド(実引数の形が対象外)
  · intro Γ _ r m args hnu hne τ hτ
    simp only [Bool.not_eq_true] at hnu
    rw [wtS.eq_def] at hτ
    simp only [hnu, Bool.false_eq_true, ite_false] at hτ
    cases args with
    | nil => simp at hτ
    | cons a rest =>
      cases a with
      | named n e => simp at hτ
      | pos e =>
        cases rest with
        | nil => exact (hne e rfl).elim
        | cons b rest' => simp at hτ
  -- 30. match(適格): 腕列の証明書を帰納から得て局所合成に渡す
  · intro Γ _ s arms ta hs hex ih2 τ hτ d hd
    simp only [wtS, hs, hex, ite_true] at hτ
    obtain ⟨cs, hcs⟩ := lower_total hs
    obtain ⟨cas, hcas, -⟩ := (lowerS_typed_all T).2.2.1 Γ ta arms τ hτ
    exact SpecSemEquiv.of_iff fun _ hΓ P =>
      lowerS_match_sem_iff hs hcs hd (ih2 τ hτ cas hcas) hΦ hΓ P
  -- 31. match(網羅しない)
  · intro Γ _ s arms ta hs hne τ hτ
    simp [wtS, hs, hne] at hτ
  -- 32. match(scrutinee が不適格)
  · intro Γ _ s arms hs τ hτ
    simp [wtS, hs] at hτ
  -- 33. ブロック(適格): let 列の証明書を帰納から得て局所合成に渡す
  · intro Γ sp stmts e Γ' hst ihst ihe τ hτ d hd
    simp only [wtS, hst] at hτ
    obtain ⟨c, hc⟩ := lowerS_total hτ
    obtain ⟨binds, hlb, -⟩ := (lowerS_typed_all T).2.1 Γ stmts Γ' hst
    exact SpecSemEquiv.of_iff fun _ hΓ Q =>
      lowerS_block_sem_iff hst hτ hc hd (ihst Γ' hst binds hlb e c (ihe τ hτ c hc)) hΦ hΓ Q
  -- 34. ブロック(let の列が不適格)
  · intro Γ _ stmts e hst _ τ hτ
    simp [wtS, hst] at hτ
  -- 35. 量化(束縛なし: 対象外)
  · intro Γ _ q b τ hτ
    simp [wtS] at hτ
  -- 36. 量化(適格)
  · intro Γ sp q bs b Γ' hb j hj hjf hne ih τ hτ d hd
    obtain ⟨cbs, hcbs, -⟩ := lowerBinders_sound bs hb
    obtain ⟨cb, hcb⟩ := lowerS_total hj
    exact SpecSemEquiv.of_iff fun _ hΓ P =>
      lowerS_quant_sem_iff hb hcbs hj hcb hd (ih j hj cb hcb) hΓ P
  -- 37. 量化(本体が論理の位置の型でない)
  · intro Γ _ q bs b Γ' hb j hj hjf hne _ τ hτ
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj, hjf] at hτ
  -- 38. 量化(本体が不適格)
  · intro Γ _ q bs b Γ' hb hj hne _ τ hτ
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj] at hτ
  -- 39. 量化(束縛の型が対象外)
  · intro Γ _ q bs b hb hne τ hτ
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb] at hτ
  -- 40. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 τ hτ
    rw [wtS.eq_def] at hτ
    split at hτ
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ _ _ rfl).elim
      | exact (h7 _ _ _ rfl).elim
      | exact (h8 _ _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | exact (h10 _ _ _ rfl).elim
      | exact (h11 _ _ _ _ rfl).elim
      | (cases hτ; done)
  -- 41. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp τ hτ
    rw [wtArmS.eq_1, hp] at hτ
    simp at hτ
  -- 42. 腕(ガード無し、適格)
  · intro Γ ts p b bs' hp j hj hjf ihb τ hτ ca hca rest cas hrest
    obtain ⟨cb, hcb⟩ := lowerS_total hj
    have hca' : lowerArmS T Γ ts (.mk p none b) = some (.mk (Surf.lowerPat p) none cb) := by
      rw [lowerArmS.eq_1, hp]
      simp [hcb]
    have hcc := Option.some.inj (hca'.symm.trans hca)
    subst hcc
    exact .hit hp hcb (ihb j hj cb hcb) hrest
  -- 43. 腕(ガード無し、本体が論理の位置の型でない)
  · intro Γ ts p b bs' hp j hj hjf _ τ hτ
    rw [wtArmS.eq_1, hp] at hτ
    simp [hj, hjf] at hτ
  -- 44. 腕(ガード無し、本体が不適格)
  · intro Γ ts p b bs' hp hj _ τ hτ
    rw [wtArmS.eq_1, hp] at hτ
    simp [hj] at hτ
  -- 45. 腕(ガード付き、適格)
  · intro Γ ts p b bs' hp g tl tr hb hg ihg ihb τ hτ ca hca rest cas hrest
    obtain ⟨cg, hcg⟩ := lowerS_total hg
    obtain ⟨cb, hcb⟩ := lowerS_total hb
    have hca' : lowerArmS T Γ ts (.mk p (some g) b) =
        some (.mk (Surf.lowerPat p) (some cg) cb) := by
      rw [lowerArmS.eq_1, hp]
      simp [hcg, hcb]
    have hcc := Option.some.inj (hca'.symm.trans hca)
    subst hcc
    exact .guard hp hcg hcb (ihg tl hg cg hcg) (ihb tr hb cb hcb) hrest
  -- 46. 腕(ガード付き、不適格)
  · intro Γ ts p b bs' hp g hno _ _ τ hτ
    rw [wtArmS.eq_1, hp] at hτ
    simp only at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 47. 腕の列(空)
  · intro Γ ts τ hτ
    simp [wtArmsS] at hτ
  -- 48. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h] at hτ
  -- 49. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 τ hτ cas hcas
    rw [lowerArmsS.eq_2] at hcas
    cases hca : lowerArmS T Γ ts arm with
    | none => simp [hca] at hcas
    | some ca =>
      rw [hca, lowerArmsS.eq_1] at hcas
      simp only [Option.some.injEq] at hcas
      subst hcas
      exact ih3 t1 h1 ca hca [] [] .nil
  -- 50. 腕の列(先頭の腕と残りがともに適格)
  · intro Γ ts arm t1 head tail h1 j hj ih3 ih2 τ hτ cas hcas
    rw [lowerArmsS.eq_2] at hcas
    cases hca : lowerArmS T Γ ts arm with
    | none => simp [hca] at hcas
    | some ca =>
      cases hcs : lowerArmsS T Γ ts (head :: tail) with
      | none => simp [hca, hcs] at hcas
      | some cas' =>
        rw [hca, hcs] at hcas
        simp only [Option.some.injEq] at hcas
        subst hcas
        exact ih3 t1 h1 ca hca _ _ (ih2 j hj cas' hcs)
  -- 51. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h1, h2] at hτ
  -- 52. let の列(空)
  · intro Γ Γ' h binds hb e c hec
    simp only [wtStmtsS, Option.some.injEq] at h
    subst h
    simp only [lowerStmtsS, Option.some.injEq] at hb
    subst hb
    exact .nil hec
  -- 53. let の列(命題に束ねる、適格)
  · intro Γ sp x ty v rest hp hann hv ihv ihrest Γ' h binds hb e c hec
    simp only [wtStmtsS, hp, hann, hv, ite_true] at h
    obtain ⟨cv, hcv⟩ := lowerS_total hv
    obtain ⟨binds', hlb, -⟩ := (lowerS_typed_all T).2.1 _ rest Γ' h
    have hb' : lowerStmtsS T Γ (.letS sp x ty v :: rest) = some ((x, .bool, cv) :: binds') := by
      rw [lowerStmtsS.eq_2]
      simp [hp, hcv, hlb]
    have hbb := Option.some.inj (hb'.symm.trans hb)
    subst hbb
    exact .prop hp hv hcv (ihv .prop hv cv hcv) (ihrest Γ' h binds' hlb e c hec)
  -- 54. let の列(命題だが不適格)
  · intro Γ _ x ty v rest hp hann hno _ Γ' h
    simp only [wtStmtsS, hp, hann, ite_true] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 55. let の列(命題だが注釈が Bool でない)
  · intro Γ _ x ty v rest hp hann Γ' h
    simp [wtStmtsS, hp, hann] at h
  -- 56. let の列(値に束ねる、適格)
  · intro Γ sp x ty v rest hp ta hv t hann ihrest Γ' h binds hb e c hec
    simp only [Bool.not_eq_true] at hp
    simp only [wtStmtsS, hp, Bool.false_eq_true, ite_false, hv, hann] at h
    have ht : t = ta := annot_eq hann
    subst ht
    obtain ⟨cv, hcv⟩ := lower_total hv
    obtain ⟨binds', hlb, -⟩ := (lowerS_typed_all T).2.1 _ rest Γ' h
    have hb' : lowerStmtsS T Γ (.letS sp x ty v :: rest) = some ((x, t.toTyV, cv) :: binds') := by
      rw [lowerStmtsS.eq_2]
      simp [hp, hv, hcv, hlb]
    have hbb := Option.some.inj (hb'.symm.trans hb)
    subst hbb
    exact .value hp hv hcv (ihrest Γ' h binds' hlb e c hec)
  -- 57. let の列(値に束ねる、注釈が合わない)
  · intro Γ _ x ty v rest hp ta hv hann Γ' h
    simp only [Bool.not_eq_true] at hp
    simp [wtStmtsS, hp, hv, hann] at h
  -- 58. let の列(値が不適格)
  · intro Γ _ x ty v rest hp hv Γ' h
    simp only [Bool.not_eq_true] at hp
    simp [wtStmtsS, hp, hv] at h

/-- 任意の適格な spec 式と独立 lowering の実出力について、子式の対応を仮定しない双方向の意味対応。 -/
theorem lowerS_equiv {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {e : Expr} {τ : STy} {c : Core.Expr}
    (hw : wtS T Γ e = some τ) (hl : lowerS T Γ e = some c) (hΦ : Φ.Respects T.Δ) :
    SpecSemEquiv T Φ Ψ Γ e c :=
  (lowerS_sem_all T Φ Ψ hΦ).1 Γ e τ hw c hl

/-- 適格な let 列の独立 lowering は、末尾の対応から let 列の証明書を与える。 -/
theorem lowerStmtsS_bridge {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ Γ' : SCtx} {stmts : List Stmt} {binds : List (String × TyV × Core.Expr)}
    (hw : wtStmtsS T Γ stmts = some Γ') (hl : lowerStmtsS T Γ stmts = some binds)
    (hΦ : Φ.Respects T.Δ) {e : Expr} {c : Core.Expr} (tail : SpecSemEquiv T Φ Ψ Γ' e c) :
    SpecLetsBridge T Φ Ψ Γ stmts binds e c :=
  (lowerS_sem_all T Φ Ψ hΦ).2.1 Γ stmts Γ' hw binds hl e c tail

/-- 適格な腕列の独立 lowering は腕列の証明書を与える。 -/
theorem lowerArmsS_bridge {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {ts : NaruSem.Ty} {arms : List Arm} {cas : List Core.Arm} {τ : STy}
    (hw : wtArmsS T Γ ts arms = some τ) (hl : lowerArmsS T Γ ts arms = some cas)
    (hΦ : Φ.Respects T.Δ) : SpecArmsBridge T Φ Ψ Γ ts arms cas :=
  (lowerS_sem_all T Φ Ψ hΦ).2.2.1 Γ ts arms τ hw cas hl

/-- **全 spec 式の一般双方向同値**: 型付け文脈と一致する任意の環境で、同じ命題が Surface の意味であることと
Core の意味であることは同値。意味の存在は仮定も結論もしない(spec 解釈の不在による意味不在も両側で保つ)。 -/
theorem lowerS_sem_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {e : Expr} {τ : STy} {c : Core.Expr}
    (hw : wtS T Γ e = some τ) (hl : lowerS T Γ e = some c) (hΦ : Φ.Respects T.Δ)
    {ρ : SEnv} (hΓ : Γ = ρ.ctx) (P : Prop) :
    Sem T Φ Ψ ρ e P ↔ NaruSem.Call.Sem T.Δ Φ Ψ ρ c P :=
  (lowerS_equiv hw hl hΦ).iff hΓ P

/-- Surface の意味は Core の意味(順方向)。 -/
theorem lowerS_Sem {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {e : Expr} {τ : STy} {c : Core.Expr}
    (hw : wtS T Γ e = some τ) (hl : lowerS T Γ e = some c) (hΦ : Φ.Respects T.Δ)
    {ρ : SEnv} (hΓ : Γ = ρ.ctx) {P : Prop} (h : Sem T Φ Ψ ρ e P) :
    NaruSem.Call.Sem T.Δ Φ Ψ ρ c P :=
  (lowerS_sem_iff hw hl hΦ hΓ P).mp h

/-- Core の意味は Surface の意味(逆方向)。 -/
theorem Sem_lowerS {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {e : Expr} {τ : STy} {c : Core.Expr}
    (hw : wtS T Γ e = some τ) (hl : lowerS T Γ e = some c) (hΦ : Φ.Respects T.Δ)
    {ρ : SEnv} (hΓ : Γ = ρ.ctx) {P : Prop} (h : NaruSem.Call.Sem T.Δ Φ Ψ ρ c P) :
    Sem T Φ Ψ ρ e P :=
  (lowerS_sem_iff hw hl hΦ hΓ P).mpr h

/-- 意味の存在も両側で一致する(どちらにも意味が無い環境はどちらにも無い)。 -/
theorem lowerS_sem_exists_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {e : Expr} {τ : STy} {c : Core.Expr}
    (hw : wtS T Γ e = some τ) (hl : lowerS T Γ e = some c) (hΦ : Φ.Respects T.Δ)
    {ρ : SEnv} (hΓ : Γ = ρ.ctx) :
    (∃ P, Sem T Φ Ψ ρ e P) ↔ (∃ P, NaruSem.Call.Sem T.Δ Φ Ψ ρ c P) :=
  ⟨fun ⟨P, h⟩ => ⟨P, lowerS_Sem hw hl hΦ hΓ h⟩, fun ⟨P, h⟩ => ⟨P, Sem_lowerS hw hl hΦ hΓ h⟩⟩

/-- C44 / C55 の Core → 実生成 Lean の読み(`Call.denoteP`)と合成する: Surface の意味は、署名の鍵で
一致する読みの環境・包含する署名での読みと同値。読みの環境が宣言群の意味や実生成宣言と一致することは、
`FEnv.Agree` / `PEnv.Agree` の前提として受け取り、ここでは導かない。 -/
theorem lowerS_denote {T : Table} {Γ : SCtx} {e : Expr} {τ : STy} {c : Core.Expr}
    {Φ Φ' : NaruSem.Call.FEnv} {Ψ Ψ' : NaruSem.Call.PEnv} {Δ' : NaruSem.Call.SigEnv} {ρ : SEnv}
    (hw : wtS T Γ e = some τ) (hl : lowerS T Γ e = some c) (hΓ : Γ = ρ.ctx)
    (hΔ : NaruSem.Call.SigEnv.SubV T.Δ Δ') (hΦ' : Φ'.Respects Δ')
    (hA : NaruSem.Call.FEnv.Agree Φ Φ' T.Δ) (hPA : NaruSem.Call.PEnv.Agree Ψ Ψ' T.Δ)
    {P : Prop} (h : Sem T Φ Ψ ρ e P) : P ↔ NaruSem.Call.denoteP T.Δ Φ' Ψ' ρ c :=
  NaruSem.Call.Sem_denote hΔ hΦ' hA hPA (lowerS_wt hw hl) ρ hΓ
    (lowerS_Sem hw hl (hA.respects hΔ hΦ') hΓ h)

/-- 読み自体が Surface の意味になる(存在 + 同値 + 命題外延性)。spec 解釈が定義されていることは
`PEnv.Agree` から得る。 -/
theorem lowerS_denoteP {T : Table} {Γ : SCtx} {e : Expr} {τ : STy} {c : Core.Expr}
    {Φ Φ' : NaruSem.Call.FEnv} {Ψ Ψ' : NaruSem.Call.PEnv} {Δ' : NaruSem.Call.SigEnv} {ρ : SEnv}
    (hw : wtS T Γ e = some τ) (hf : τ.isForm = true) (hl : lowerS T Γ e = some c) (hΓ : Γ = ρ.ctx)
    (hΔ : NaruSem.Call.SigEnv.SubV T.Δ Δ') (hΦ' : Φ'.Respects Δ')
    (hA : NaruSem.Call.FEnv.Agree Φ Φ' T.Δ) (hPA : NaruSem.Call.PEnv.Agree Ψ Ψ' T.Δ) :
    Sem T Φ Ψ ρ e (NaruSem.Call.denoteP T.Δ Φ' Ψ' ρ c) := by
  obtain ⟨P, hP⟩ := Sem_exists hw hf Φ Ψ ρ hΓ (hA.respects hΔ hΦ') hPA.defined
  rw [propext (lowerS_denote hw hl hΓ hΔ hΦ' hA hPA hP)] at hP
  exact hP

end NaruSem.Surf.Call
