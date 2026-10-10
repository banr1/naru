import NaruSem.SurfaceTotality
import NaruSem.Denote

/-!
# Surface AST → Core の対応(IDEAL.md C49)

frontend(`compiler/Naru/Typecheck.lean`)が Surface AST を Core IR に elaborate する変換のうち、用語「Surface AST の保存対象」の runtime の式に対する
部分を、frontend から独立に Lean の関数 `Surf.lower : Ctx → Surf.Expr → Option Core.Expr` として定める(汎用翻訳方式。「コンパイラ意味論保存の保証方式」)。
`lower` は型に導かれる変換で、Core の注釈(二項演算の被演算子の型、`let` の型、`match` の scrutinee の型)を AST の型付け `Surf.wtR` から補い、
ブロックの `let` の列を `let_` の入れ子にする(`mkLets`: コンパイラの `Typecheck.mkLets` と同じ畳み込み)。frontend の実装(`infer` / `check` / `inferStmts` /
`checkPat` …)は参照しない。実際の frontend との一致は `lake exe naru_test semantics` が、実際に構文解析された AST の `lower` が実際に出力された Core に
等しいことを kernel に検査させて確かめる(`.lake/naru/test/semantics/SurfaceScope.lean` の `low_<f>`)。

一般定理 `lower_sound`(`lower_sound_all`: `Surf.wtR.mutual_induct` で式・`let` の列・腕の列・腕を同時に示す): 任意の適格な AST(`Surf.wtR Γ e = some t`)について
変換が定まり(`lower Γ e = some c`)、その Core は同じ文脈で適格(`NaruSem.wtR Γ c = some t`)で、任意の環境で AST の意味と Core の意味が一致する
(`∀ ρ, Surf.eval ρ e = NaruSem.eval ρ c`)。値の対応は等式(AST の意味論と Core の意味論は値 `Val` を共有する)。`lower_total` / `lower_wt` / `lower_eval` は系。
C40 / C41 の `denote_sound` と合成した `Surf.preserve_nat` / `Surf.preserve_bool`(AST の意味 = 生成 Lean の読み)と、接続検査の健全性
`Surf.check_sound_nat` / `Surf.check_sound_bool`(実生成宣言の接続検査 `conn_<f>` と `low_<f>` から AST の意味 = 実生成宣言の値)が、AST → Core → 生成 Lean を
つなぐ(C49 / C51)。spec の式(`.quant` を含む)の対応は C50(別ファイル)。
-/

namespace NaruSem
open Naru

/-- 対象の型 → Core の型表現。 -/
def Ty.toTyV : Ty → TyV
  | .nat => .nat
  | .bool => .bool

@[simp] theorem TyV.toTy?_toTyV (t : Ty) : TyV.toTy? t.toTyV = some t := by
  cases t <;> rfl

namespace Surf

/-! ## 変換 -/

/-- 対象のパターン → Core のパターン(位置情報を落とす)。 -/
def lowerPat : Pat → Core.Pat
  | .wild _ => .wild
  | .bind _ x => .bind x
  | .lit _ l => .lit l

/-- ブロックの束縛(名前・型・値)の列を `let_` の入れ子にする(コンパイラの `Typecheck.mkLets` と同じ畳み込み)。 -/
def mkLets (binds : List (String × TyV × Core.Expr)) (tail : Core.Expr) : Core.Expr :=
  binds.foldr (fun (n, t, v) body => .let_ n t v body) tail

@[simp] theorem mkLets_nil (c : Core.Expr) : mkLets [] c = c := rfl

@[simp] theorem mkLets_cons (x : String) (ty : TyV) (v : Core.Expr) (rest : List (String × TyV × Core.Expr)) (c : Core.Expr) :
    mkLets ((x, ty, v) :: rest) c = .let_ x ty v (mkLets rest c) := rfl

mutual

/-- runtime の Surface AST → Core。注釈は AST の型付け `wtR` から補う。対象外の構文は `none`。 -/
def lower (Γ : Ctx) : Expr → Option Core.Expr
  | .lit _ (.nat n) => some (.lit (.nat n) .nat)
  | .lit _ (.bool b) => some (.lit (.bool b) .bool)
  | .var _ [x] => some (.var x)
  | .binop _ op l r =>
    match wtR Γ l, lower Γ l, lower Γ r with
    | some tl, some cl, some cr => some (.binop op cl cr tl.toTyV)
    | _, _, _ => none
  | .unop _ op a =>
    if op = "!" then
      match lower Γ a with
      | some ca => some (.unop "!" ca)
      | none => none
    else none
  | .method _ r m [a] =>
    match NatMethod.ofString? m, lower Γ r, lower Γ a with
    | some _, some cr, some ca => some (.method "Nat" m cr [ca] .nat)
    | _, _, _ => none
  | .ite _ c t e =>
    match lower Γ c, lower Γ t, lower Γ e with
    | some cc, some ct, some ce => some (.ite cc ct ce)
    | _, _, _ => none
  | .matchE _ s arms =>
    match wtR Γ s with
    | some ts =>
      match lower Γ s, lowerArms Γ ts arms with
      | some cs, some cas => some (.match_ cs ts.toTyV cas)
      | _, _ => none
    | none => none
  | .block _ stmts (some e) =>
    match wtStmtsR Γ stmts, lowerStmts Γ stmts with
    | some Γ', some binds =>
      match lower Γ' e with
      | some c => some (mkLets binds c)
      | none => none
    | _, _ => none
  | _ => none

/-- ブロックの `let` の列 → 束縛(名前・型・値)の列。 -/
def lowerStmts (Γ : Ctx) : List Stmt → Option (List (String × TyV × Core.Expr))
  | [] => some []
  | .letS _ x _ v :: rest =>
    match wtR Γ v, lower Γ v with
    | some tv, some cv =>
      match lowerStmts (Γ.ext x tv) rest with
      | some binds => some ((x, tv.toTyV, cv) :: binds)
      | none => none
    | _, _ => none

def lowerArms (Γ : Ctx) (ts : NaruSem.Ty) : List Arm → Option (List Core.Arm)
  | [] => some []
  | arm :: rest =>
    match lowerArm Γ ts arm, lowerArms Γ ts rest with
    | some ca, some cas => some (ca :: cas)
    | _, _ => none

def lowerArm (Γ : Ctx) (ts : NaruSem.Ty) : Arm → Option Core.Arm
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none =>
        match lower (Γ.extPat bs) b with
        | some cb => some (.mk (lowerPat p) none cb)
        | none => none
      | some g =>
        match lower (Γ.extPat bs) g, lower (Γ.extPat bs) b with
        | some cg, some cb => some (.mk (lowerPat p) (some cg) cb)
        | _, _ => none

end

/-! ## 展開の補題 -/

theorem lowerStmts_cons (Γ : Ctx) (sp : Span) (x : String) (ty : Option Ty) (v : Expr) (rest : List Stmt) :
    lowerStmts Γ (.letS sp x ty v :: rest) =
      match wtR Γ v, lower Γ v with
      | some tv, some cv =>
        match lowerStmts (Γ.ext x tv) rest with
        | some binds => some ((x, tv.toTyV, cv) :: binds)
        | none => none
      | _, _ => none :=
  lowerStmts.eq_2 Γ sp x ty v rest

theorem lowerArms_cons (Γ : Ctx) (ts : NaruSem.Ty) (arm : Arm) (rest : List Arm) :
    lowerArms Γ ts (arm :: rest) =
      match lowerArm Γ ts arm, lowerArms Γ ts rest with
      | some ca, some cas => some (ca :: cas)
      | _, _ => none :=
  lowerArms.eq_2 Γ ts arm rest

theorem lowerArm_mk (Γ : Ctx) (ts : NaruSem.Ty) (p : Pat) (g : Option Expr) (b : Expr) :
    lowerArm Γ ts (.mk p g b) =
      match wtPat ts p with
      | none => none
      | some bs =>
        match g with
        | none =>
          match lower (Γ.extPat bs) b with
          | some cb => some (.mk (lowerPat p) none cb)
          | none => none
        | some g =>
          match lower (Γ.extPat bs) g, lower (Γ.extPat bs) b with
          | some cg, some cb => some (.mk (lowerPat p) (some cg) cb)
          | _, _ => none :=
  lowerArm.eq_1 Γ ts p g b

/-! ## パターン・演算・束縛の列の対応 -/

/-- パターンの型付けは変換で変わらない。 -/
theorem wtPat_lower (t : NaruSem.Ty) (p : Pat) : NaruSem.wtPat t (lowerPat p) = wtPat t p := by
  cases p with
  | wild => rfl
  | bind => rfl
  | lit _ l => cases l <;> rfl

/-- パターンの照合は変換で変わらない。 -/
theorem matchPat_lower (p : Pat) (v : Val) : NaruSem.matchPat (lowerPat p) v = matchPat p v := by
  cases p with
  | wild => rfl
  | bind => rfl
  | lit _ l => cases l <;> cases v <;> rfl

/-- 注釈の無い二項演算の型付け(被演算子の型だけから)は、被演算子の型を注釈にした Core の型付けと同じ結果。 -/
theorem binopResult_result {k : BinOp} {tl tr t : NaruSem.Ty} (h : binopResult k tl tr = some t) : k.result tl tr tl = some t := by
  cases k <;> cases tl <;> cases tr <;> simp_all [binopResult, BinOp.result]

/-- 束縛(名前・型・値)の列の型付け(Core の `let_` の入れ子と同じ規則)。 -/
def wtBinds (Γ : Ctx) : List (String × TyV × Core.Expr) → Option Ctx
  | [] => some Γ
  | (x, ty, v) :: rest =>
    match NaruSem.wtR Γ v, TyV.toTy? ty with
    | some tv, some ta => if tv = ta then wtBinds (Γ.ext x tv) rest else none
    | _, _ => none

/-- 束縛の列の評価(Core の `let_` の入れ子と同じ)。 -/
def evalBinds (ρ : Env) : List (String × TyV × Core.Expr) → Option Env
  | [] => some ρ
  | (x, _, v) :: rest =>
    match NaruSem.eval ρ v with
    | some w => evalBinds (ρ.ext x w) rest
    | none => none

theorem wtR_mkLets {Γ Γ' : Ctx} {binds : List (String × TyV × Core.Expr)} (hb : wtBinds Γ binds = some Γ')
    {c : Core.Expr} {t : NaruSem.Ty} (hc : NaruSem.wtR Γ' c = some t) : NaruSem.wtR Γ (mkLets binds c) = some t := by
  induction binds generalizing Γ with
  | nil =>
    simp only [wtBinds, Option.some.injEq] at hb
    subst hb
    simpa using hc
  | cons b rest ih =>
    obtain ⟨x, ty, v⟩ := b
    simp only [wtBinds] at hb
    cases hv : NaruSem.wtR Γ v with
    | none => simp [hv] at hb
    | some tv =>
      cases hty : TyV.toTy? ty with
      | none => simp [hv, hty] at hb
      | some ta =>
        simp only [hv, hty] at hb
        split at hb
        · rename_i heq
          subst heq
          simp only [mkLets_cons, NaruSem.wtR, hv, hty, ite_true]
          exact ih hb
        · cases hb

theorem eval_mkLets (ρ : Env) (binds : List (String × TyV × Core.Expr)) (c : Core.Expr) :
    NaruSem.eval ρ (mkLets binds c) =
      match evalBinds ρ binds with
      | some ρ' => NaruSem.eval ρ' c
      | none => none := by
  induction binds generalizing ρ with
  | nil => simp [evalBinds]
  | cons b rest ih =>
    obtain ⟨x, ty, v⟩ := b
    simp only [mkLets_cons, NaruSem.eval, evalBinds]
    cases NaruSem.eval ρ v <;> simp [ih]

/-! ## 一般定理 -/

/-- `wtR` / `wtStmtsR` / `wtArmsR` / `wtArmR` の関数帰納法で、式・`let` の列・腕の列・腕の 4 つを同時に示す: 適格な AST には変換が定まり、
その Core は同じ文脈で適格で、任意の環境で AST の意味と Core の意味が一致する。腕の列では網羅性の走査も変わらないことを同時に示す。 -/
theorem lower_sound_all :
    (∀ (Γ : Ctx) (e : Expr), ∀ t, wtR Γ e = some t →
        ∃ c, lower Γ e = some c ∧ NaruSem.wtR Γ c = some t ∧ ∀ ρ : Env, eval ρ e = NaruSem.eval ρ c) ∧
    (∀ (Γ : Ctx) (stmts : List Stmt), ∀ Γ', wtStmtsR Γ stmts = some Γ' →
        ∃ binds, lowerStmts Γ stmts = some binds ∧ wtBinds Γ binds = some Γ' ∧ ∀ ρ : Env, evalStmts ρ stmts = evalBinds ρ binds) ∧
    (∀ (Γ : Ctx) (ts : NaruSem.Ty) (arms : List Arm), ∀ t, wtArmsR Γ ts arms = some t →
        ∃ cas, lowerArms Γ ts arms = some cas ∧ NaruSem.wtArmsR Γ ts cas = some t ∧
          (∀ sawT sawF, exhaustiveFrom ts sawT sawF arms = NaruSem.exhaustiveFrom ts sawT sawF cas) ∧
          ∀ (ρ : Env) (v : Val), evalArms ρ v arms = NaruSem.evalArms ρ v cas) ∧
    (∀ (Γ : Ctx) (ts : NaruSem.Ty) (arm : Arm), ∀ t, wtArmR Γ ts arm = some t →
        ∃ ca, lowerArm Γ ts arm = some ca ∧ NaruSem.wtArmR Γ ts ca = some t ∧
          (∀ rest crest, (∀ sawT sawF, exhaustiveFrom ts sawT sawF rest = NaruSem.exhaustiveFrom ts sawT sawF crest) →
            ∀ sawT sawF, exhaustiveFrom ts sawT sawF (arm :: rest) = NaruSem.exhaustiveFrom ts sawT sawF (ca :: crest)) ∧
          ∀ (ρ : Env) (v : Val) rest crest, evalArms ρ v rest = NaruSem.evalArms ρ v crest →
            evalArms ρ v (arm :: rest) = NaruSem.evalArms ρ v (ca :: crest)) := by
  apply wtR.mutual_induct
  -- 1. Nat のリテラル
  · intro Γ _ n t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨_, rfl, rfl, fun ρ => by simp [eval, NaruSem.eval]⟩
  -- 2. Bool のリテラル
  · intro Γ _ b t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨_, rfl, rfl, fun ρ => by simp [eval, NaruSem.eval]⟩
  -- 3. 局所名
  · intro Γ _ x t ht
    simp only [wtR] at ht
    exact ⟨.var x, rfl, by simpa [NaruSem.wtR] using ht, fun ρ => by simp [eval, NaruSem.eval]⟩
  -- 4. 二項演算(適格)
  · intro Γ _ op l r k tl tr hr hl hk ihl ihr t ht
    simp only [wtR, hk, hl, hr] at ht
    obtain ⟨cl, hcl, hwl, hel⟩ := ihl tl hl
    obtain ⟨cr, hcr, hwr, her⟩ := ihr tr hr
    refine ⟨.binop op cl cr tl.toTyV, by simp [lower, hl, hcl, hcr], ?_, fun ρ => ?_⟩
    · simp only [NaruSem.wtR, hk, hwl, hwr, TyV.toTy?_toTyV]
      exact binopResult_result ht
    · simp only [eval, NaruSem.eval, hk, hel, her]
      rfl
  -- 5. 二項演算(不適格)
  · intro Γ _ op l r hno _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 6. `!`(適格)
  · intro Γ _ a ha iha t ht
    simp only [wtR, ha, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨ca, hca, hwa, hea⟩ := iha .bool ha
    refine ⟨.unop "!" ca, by simp [lower, hca], by simp [NaruSem.wtR, hwa], fun ρ => ?_⟩
    simp only [eval, NaruSem.eval, hea, ite_true]
    rfl
  -- 7. `!`(被演算子が Bool でない)
  · intro Γ _ a hno _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 8. 対象外の単項演算子
  · intro Γ _ op a hne t ht
    simp [wtR, hne] at ht
  -- 9. Nat の min / max(適格)
  · intro Γ _ r m a k ha hr hm ihr iha t ht
    simp only [wtR, hm, hr, ha, Option.some.injEq] at ht
    subst ht
    obtain ⟨cr, hcr, hwr, her⟩ := ihr .nat hr
    obtain ⟨ca, hca, hwa, hea⟩ := iha .nat ha
    refine ⟨.method "Nat" m cr [ca] .nat, by simp [lower, hm, hcr, hca], by simp [NaruSem.wtR, hm, hwr, hwa], fun ρ => ?_⟩
    simp only [eval, NaruSem.eval, hm, her, hea, ite_true]
    rfl
  -- 10. Nat のメソッド(不適格)
  · intro Γ _ r m a hno _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 11. if(適格)
  · intro Γ _ c t e te hte hc htt ihc iht ihe t' ht'
    simp only [wtR, hc, htt, hte, ite_true, Option.some.injEq] at ht'
    subst ht'
    obtain ⟨cc, hcc, hwc, hec⟩ := ihc .bool hc
    obtain ⟨ct, hct, hwt, het⟩ := iht te htt
    obtain ⟨ce, hce, hwe, hee⟩ := ihe te hte
    refine ⟨.ite cc ct ce, by simp [lower, hcc, hct, hce], by simp [NaruSem.wtR, hwc, hwt, hwe], fun ρ => ?_⟩
    simp only [eval, NaruSem.eval, hec, het, hee]
    rfl
  -- 12. if(分岐の型が違う)
  · intro Γ _ c t e tt te hte htt hc hne _ _ _ t' ht'
    simp [wtR, hc, htt, hte, hne] at ht'
  -- 13. if(不適格)
  · intro Γ _ c t e hno _ _ _ t' ht'
    simp only [wtR] at ht'
    first
      | (cases ht'; done)
      | (split at ht' <;> simp_all)
  -- 14. match(適格)
  · intro Γ _ s arms ta hs hex ihs iharms t ht
    simp only [wtR, hs, hex, ite_true] at ht
    obtain ⟨cs, hcs, hws, hes⟩ := ihs ta hs
    obtain ⟨cas, hcas, hwas, hexs, heas⟩ := iharms t ht
    refine ⟨.match_ cs ta.toTyV cas, by simp [lower, hs, hcs, hcas], ?_, fun ρ => ?_⟩
    · have hex' : NaruSem.exhaustive ta cas = true := by
        unfold NaruSem.exhaustive
        rw [← hexs]
        exact hex
      simp only [NaruSem.wtR, hws, TyV.toTy?_toTyV, hex', Bool.and_true, decide_true, ite_true]
      exact hwas
    · simp only [eval, NaruSem.eval, hes, heas]
      rfl
  -- 15. match(網羅しない)
  · intro Γ _ s arms ta hs hne _ t ht
    simp [wtR, hs, hne] at ht
  -- 16. match(scrutinee が不適格)
  · intro Γ _ s arms hs _ t ht
    simp [wtR, hs] at ht
  -- 17. ブロック(適格)
  · intro Γ _ stmts e Γ' hst ihst ihe t ht
    simp only [wtR, hst] at ht
    obtain ⟨binds, hlb, hwb, heb⟩ := ihst Γ' hst
    obtain ⟨c, hc, hw, he⟩ := ihe t ht
    refine ⟨mkLets binds c, by simp [lower, hst, hlb, hc], wtR_mkLets hwb hw, fun ρ => ?_⟩
    simp only [eval, eval_mkLets, heb]
    cases evalBinds ρ binds <;> simp [he]
  -- 18. ブロック(let の列が不適格)
  · intro Γ _ stmts e hst _ t ht
    simp [wtR, hst] at ht
  -- 19. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 t ht
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
  · intro Γ ts p g b hp t ht
    rw [wtArmR_mk, hp] at ht
    simp at ht
  -- 21. 腕(ガード無し)
  · intro Γ ts p b bts hp ihb t ht
    rw [wtArmR_mk, hp] at ht
    simp only at ht
    obtain ⟨cb, hcb, hwb, heb⟩ := ihb t ht
    refine ⟨.mk (lowerPat p) none cb, by rw [lowerArm_mk, hp]; simp [hcb], ?_, ?_, ?_⟩
    · rw [NaruSem.wtArmR.eq_1, wtPat_lower, hp]
      exact hwb
    · intro rest crest hrest sawT sawF
      cases p with
      | wild => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat]
      | bind => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat]
      | lit _ l =>
        cases l with
        | bool lb => cases lb <;> simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
        | nat n => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
        | str s => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
        | unit => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
    · intro ρ v rest crest hrest
      rw [evalArms_cons, NaruSem.evalArms_cons, matchPat_lower]
      cases matchPat p v with
      | none => exact hrest
      | some bs => simp only [heb]
  -- 22. 腕(ガードが Bool)
  · intro Γ ts p b bts hp g hg ihg ihb t ht
    rw [wtArmR_mk, hp] at ht
    simp only [hg] at ht
    obtain ⟨cg, hcg, hwg, heg⟩ := ihg .bool hg
    obtain ⟨cb, hcb, hwb, heb⟩ := ihb t ht
    refine ⟨.mk (lowerPat p) (some cg) cb, by rw [lowerArm_mk, hp]; simp [hcg, hcb], ?_, ?_, ?_⟩
    · rw [NaruSem.wtArmR.eq_1, wtPat_lower, hp]
      simp only [hwg]
      exact hwb
    · intro rest crest hrest sawT sawF
      simp [exhaustiveFrom, NaruSem.exhaustiveFrom, hrest]
    · intro ρ v rest crest hrest
      rw [evalArms_cons, NaruSem.evalArms_cons, matchPat_lower]
      cases matchPat p v with
      | none => exact hrest
      | some bs =>
        simp only [heg, heb]
        cases NaruSem.eval (ρ.extList bs) cg with
        | none => rfl
        | some w =>
          cases w with
          | nat => rfl
          | bool c => cases c <;> simp [hrest]
  -- 23. 腕(ガードが Bool でない)
  · intro Γ ts p b bts hp g hno _ t ht
    rw [wtArmR_mk, hp] at ht
    simp only at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 24. 腕の列(空)
  · intro Γ ts t ht
    simp [wtArmsR] at ht
  -- 25. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ t ht
    simp [wtArmsR, h] at ht
  -- 26. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih4 t ht
    simp only [wtArmsR, h1, Option.some.injEq] at ht
    subst ht
    obtain ⟨ca, hca, hwa, hexa, hea⟩ := ih4 t1 h1
    refine ⟨[ca], by rw [lowerArms_cons, hca]; rfl, ?_, ?_, ?_⟩
    · rw [NaruSem.wtArmsR.eq_def]
      simp [hwa]
    · intro sawT sawF
      exact hexa [] [] (fun _ _ => rfl) sawT sawF
    · intro ρ v
      exact hea ρ v [] [] rfl
  -- 27. 腕の列(先頭の腕と残りの型が同じ)
  · intro Γ ts arm head tail t2 h2 h1 ih4 ih3 t ht
    rw [wtArmsR.eq_def] at ht
    simp only [h1, h2, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨ca, hca, hwa, hexa, hea⟩ := ih4 t2 h1
    obtain ⟨cas, hcas, hwas, hexs, heas⟩ := ih3 t2 h2
    refine ⟨ca :: cas, by rw [lowerArms_cons, hca, hcas], ?_, ?_, ?_⟩
    · cases cas with
      | nil =>
        rw [NaruSem.wtArmsR.eq_def] at hwas
        simp at hwas
      | cons ca' cas' =>
        rw [NaruSem.wtArmsR.eq_def]
        simp [hwa, hwas]
    · intro sawT sawF
      exact hexa (head :: tail) cas hexs sawT sawF
    · intro ρ v
      exact hea ρ v (head :: tail) cas (heas ρ v)
  -- 28. 腕の列(先頭の腕と残りの型が違う)
  · intro Γ ts arm t1 head tail h1 t2 hne h2 _ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2, hne] at ht
  -- 29. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2] at ht
  -- 30. let の列(空)
  · intro Γ Γ' h
    simp only [wtStmtsR, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl, fun ρ => rfl⟩
  -- 31. let の列(適格)
  · intro Γ _ x ty v rest ta hv t hann ihv ihrest Γ' h
    simp only [wtStmtsR, hv, hann] at h
    have ht : t = ta := annot_eq hann
    subst ht
    obtain ⟨cv, hcv, hwv, hev⟩ := ihv t hv
    obtain ⟨binds, hlb, hwb, heb⟩ := ihrest Γ' h
    refine ⟨(x, t.toTyV, cv) :: binds, by rw [lowerStmts_cons]; simp [hv, hcv, hlb], ?_, fun ρ => ?_⟩
    · simp only [wtBinds, hwv, TyV.toTy?_toTyV, ite_true]
      exact hwb
    · rw [evalStmts_cons]
      simp only [evalBinds, hev]
      cases NaruSem.eval ρ cv <;> simp [heb]
  -- 32. let の列(注釈が合わない)
  · intro Γ _ x ty v rest ta hv hann _ Γ' h
    simp [wtStmtsR, hv, hann] at h
  -- 33. let の列(値が不適格)
  · intro Γ _ x ty v rest hv _ Γ' h
    simp [wtStmtsR, hv] at h

/-- **AST → Core の対応(C49)**: 文脈で適格な runtime の Surface AST には変換が定まり、その Core は同じ文脈で適格で、任意の環境で
AST の意味(`Surf.eval`)と Core の意味(`NaruSem.eval`)が一致する。 -/
theorem lower_sound {Γ : Ctx} {e : Expr} {t : NaruSem.Ty} (h : wtR Γ e = some t) :
    ∃ c, lower Γ e = some c ∧ NaruSem.wtR Γ c = some t ∧ ∀ ρ : Env, eval ρ e = NaruSem.eval ρ c :=
  lower_sound_all.1 Γ e t h

/-- 変換の全域性: 適格な AST の変換は定まる(一般定理が空虚でない)。 -/
theorem lower_total {Γ : Ctx} {e : Expr} {t : NaruSem.Ty} (h : wtR Γ e = some t) : ∃ c, lower Γ e = some c :=
  let ⟨c, hc, _, _⟩ := lower_sound h
  ⟨c, hc⟩

/-- 変換の適格性の保存: 適格な AST の変換結果(実際の Core と一致することを接続検査が確かめる `c`)は同じ文脈で適格。 -/
theorem lower_wt {Γ : Ctx} {e : Expr} {t : NaruSem.Ty} (h : wtR Γ e = some t) {c : Core.Expr} (hl : lower Γ e = some c) :
    NaruSem.wtR Γ c = some t := by
  obtain ⟨c', hc', hw, _⟩ := lower_sound h
  rw [hl] at hc'
  cases hc'
  exact hw

/-- 値の対応: 適格な AST とその変換結果について、任意の環境で AST の意味と Core の意味が一致する(等式)。 -/
theorem lower_eval {Γ : Ctx} {e : Expr} {t : NaruSem.Ty} (h : wtR Γ e = some t) {c : Core.Expr} (hl : lower Γ e = some c) (ρ : Env) :
    eval ρ e = NaruSem.eval ρ c := by
  obtain ⟨c', hc', _, he⟩ := lower_sound h
  rw [hl] at hc'
  cases hc'
  exact he ρ

/-! ## 生成 Lean への接続(C49 / C51: C40 / C41 の `denote_sound` と合成) -/

/-- **AST の意味 = 生成 Lean の読み(Nat)**: 適格な AST `e` とその変換結果 `c`、対応する環境で、AST の意味は Core の読み `denoteN ρ c`。 -/
theorem preserve_nat {Γ : Ctx} {e : Expr} (h : wtR Γ e = some .nat) {c : Core.Expr} (hl : lower Γ e = some c) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval ρ e = some (.nat (denoteN ρ c)) := by
  rw [lower_eval h hl ρ]
  exact NaruSem.preserve_nat (lower_wt h hl) ρ hρ

/-- 同じく Bool。 -/
theorem preserve_bool {Γ : Ctx} {e : Expr} (h : wtR Γ e = some .bool) {c : Core.Expr} (hl : lower Γ e = some c) (ρ : Env) (hρ : Γ = ρ.ty) :
    eval ρ e = some (.bool (denoteB ρ c)) := by
  rw [lower_eval h hl ρ]
  exact NaruSem.preserve_bool (lower_wt h hl) ρ hρ

/-- **接続検査の健全性(AST、Nat)**: 仮引数の値 `xs` の環境で適格な AST `e` について、変換結果 `c` が実際の Core(`low_<f>` が確かめる)で、
実生成宣言の値 `v` が `c` の読みと等しい(`conn_<f>` が確かめる)なら、AST の意味は `v`。 -/
theorem check_sound_nat (xs : List (String × Val)) {e : Expr}
    (h : wtR (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some .nat)
    {c : Core.Expr} (hl : lower (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some c)
    {v : Nat} (hv : v = denoteN (Env.ofList xs) c) : eval (Env.ofList xs) e = some (.nat v) := by
  subst hv
  exact preserve_nat h hl _ (Env.ty_ofList xs).symm

/-- 同じく Bool。 -/
theorem check_sound_bool (xs : List (String × Val)) {e : Expr}
    (h : wtR (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some .bool)
    {c : Core.Expr} (hl : lower (Ctx.ofList (xs.map fun p => (p.1, p.2.ty))) e = some c)
    {v : Bool} (hv : v = denoteB (Env.ofList xs) c) : eval (Env.ofList xs) e = some (.bool v) := by
  subst hv
  exact preserve_bool h hl _ (Env.ty_ofList xs).symm

end Surf
end NaruSem
