import NaruSem.Lower
import NaruSem.DenoteProp

/-!
# spec の Surface AST → Core の対応(IDEAL.md C50)

frontend(`compiler/Naru/Typecheck.lean`)が spec 宣言の本体(論理の位置の式)を Core IR に elaborate する変換のうち、用語「Surface AST の保存対象」の
spec の式に対する部分を、frontend から独立に Lean の関数 `Surf.lowerS : SCtx → Surf.Expr → Option Core.Expr` として定める(汎用翻訳方式)。
`lowerS` は AST の spec の型付け `Surf.wtS` に導かれる変換で、論理の位置(論理演算・命題の同値の `==` / `!=`・`!`・`if`・`match` の腕・量化の本体・
命題の `let` の値)は `lowerS` 自身で、値を要求する位置(算術・比較・Nat の等値の被演算子、`min` / `max`、scrutinee、値の `let` の値)は runtime の変換
`Surf.lower`(`Lower.lean`、C49)を値の文脈 `Γ.vals` で使う。Core の注釈は、論理演算と命題の同値の `==` / `!=` は `.bool`、値の `==` / `!=` は `.nat`、
比較は被演算子の型、命題の `let` は `.bool`(frontend と同じ)、値の `let` は値の型、量化の束縛は注釈の型、`match` は scrutinee の型。ブロックの `let` の列は
`mkLets` で `let_` の入れ子にする。frontend の実装は参照しない。実際の frontend との一致は `lake exe naru_test semantics` が、実際に構文解析された
spec 宣言の AST の `lowerS` が実際に出力された Core に等しいことを kernel に検査させて確かめる(`.lake/naru/test/semantics/SurfaceScope.lean` の `lows_<f>`)。

一般定理 `lowerS_sound`(`lowerS_sound_all`: `Surf.wtS.mutual_induct` で式・`let` の列・腕の列・腕を同時に示す): 任意の適格な spec の AST
(`Surf.wtS Γ e = some τ`)について変換が定まり(`lowerS Γ e = some c`)、その Core は同じ文脈で適格(`NaruSem.wtS Γ c = some τ`)で、対応する任意の環境
(`Γ = ρ.ctx`)で AST の意味は Core の意味(`Surf.Sem ρ e P → NaruSem.Sem ρ c P`)。意味の存在(`Surf.Sem_exists`)と Core の意味の一意性
(`NaruSem.Sem_unique`)から双方向の同値 `Sem_lowerS_iff`(`Surf.Sem ρ e P ↔ NaruSem.Sem ρ c P`。任意の命題 `P`)が従い、C42 / C43 の `Sem_denote` と
合成した `preserve_prop`(AST の意味 ↔ 生成 Lean の読み `denoteP`)と、接続検査の健全性 `check_sound_prop`(実生成 Statements 宣言の接続検査 `conn_<f>` と
`lows_<f>` から AST の意味 = 実生成宣言の命題)が、AST → Core → 生成 Lean をつなぐ(C50 / C51)。量化範囲(`Ty.carrier` の全要素)・前提・結論は Core と
AST の意味論が同じ規則で読み、命題を実行可能な Bool に戻す規則はどちらにも無い。

命題の区分 `proppyS`(命題でしか表せない式。Bool の `let` を命題に束ねるか値に束ねるかを決める)は AST と Core で一致する(`proppyS_lower` / `proppyS_lowerS`:
任意の文脈で `NaruSem.proppyS Γ₀ c = Surf.proppyS Γ₀ e`)。
-/

namespace NaruSem.Surf
open Naru

/-! ## 変換 -/

/-- 量化の束縛 → Core の束縛(名前, 型)。注釈が無い・Nat / Bool でなければ `none`。 -/
def lowerBinders : List Binder → Option (List (String × TyV))
  | [] => some []
  | b :: rest =>
    match b.ty with
    | some τ =>
      match τ.toTy? with
      | some t =>
        match lowerBinders rest with
        | some cbs => some ((b.name, t.toTyV) :: cbs)
        | none => none
      | none => none
    | none => none

mutual

/-- spec の Surface AST → Core。論理の位置は `wtS` に導かれ、値を要求する位置は runtime の変換 `lower`(値の文脈 `Γ.vals`)。対象外の構文は `none`。 -/
def lowerS (Γ : SCtx) : Expr → Option Core.Expr
  | .lit _ (.nat n) => some (.lit (.nat n) .nat)
  | .lit _ (.bool b) => some (.lit (.bool b) .bool)
  | .var _ [x] => some (.var x)
  | .ite _ c t e =>
    match lowerS Γ c, lowerS Γ t, lowerS Γ e with
    | some cc, some ct, some ce => some (.ite cc ct ce)
    | _, _, _ => none
  | .binop _ op l r =>
    match BinOp.ofString? op with
    | some (.logic _) =>
      match lowerS Γ l, lowerS Γ r with
      | some cl, some cr => some (.binop op cl cr .bool)
      | _, _ => none
    | some (.eq _) =>
      -- 両辺が Nat の値なら値の等値(注釈 `.nat`)、そうでなければ論理の位置(注釈 `.bool`: Bool の値の等値か命題の同値)
      if wtR Γ.vals l = some .nat ∧ wtR Γ.vals r = some .nat then
        match lower Γ.vals l, lower Γ.vals r with
        | some cl, some cr => some (.binop op cl cr .nat)
        | _, _ => none
      else
        match lowerS Γ l, lowerS Γ r with
        | some cl, some cr => some (.binop op cl cr .bool)
        | _, _ => none
    | some (.cmp _) =>
      match wtR Γ.vals l, lower Γ.vals l, lower Γ.vals r with
      | some tl, some cl, some cr => some (.binop op cl cr tl.toTyV)
      | _, _, _ => none
    | some (.arith _) =>
      match lower Γ.vals l, lower Γ.vals r with
      | some cl, some cr => some (.binop op cl cr .nat)
      | _, _ => none
    | none => none
  | .unop _ op a =>
    if op = "!" then
      match lowerS Γ a with
      | some ca => some (.unop "!" ca)
      | none => none
    else none
  | .method _ r m [a] =>
    match NatMethod.ofString? m, lower Γ.vals r, lower Γ.vals a with
    | some _, some cr, some ca => some (.method "Nat" m cr [ca] .nat)
    | _, _, _ => none
  | .matchE _ s arms =>
    match wtR Γ.vals s with
    | some ts =>
      match lower Γ.vals s, lowerArmsS Γ ts arms with
      | some cs, some cas => some (.match_ cs ts.toTyV cas)
      | _, _ => none
    | none => none
  | .block _ stmts (some e) =>
    match wtStmtsS Γ stmts, lowerStmtsS Γ stmts with
    | some Γ', some binds =>
      match lowerS Γ' e with
      | some c => some (mkLets binds c)
      | none => none
    | _, _ => none
  | .quant _ q bs b =>
    match SCtx.extBinders Γ bs, lowerBinders bs with
    | some Γ', some cbs =>
      match lowerS Γ' b with
      | some cb => some (.quant q cbs cb)
      | none => none
    | _, _ => none
  | _ => none

/-- ブロックの `let` の列(spec)→ 束縛(名前・型・値)の列: 値が命題(`proppyS`)なら `lowerS` で注釈 `.bool`、そうでなければ `lower` で値の型。 -/
def lowerStmtsS (Γ : SCtx) : List Stmt → Option (List (String × TyV × Core.Expr))
  | [] => some []
  | .letS _ x _ v :: rest =>
    if proppyS Γ v then
      match lowerS Γ v with
      | some cv =>
        match lowerStmtsS (Γ.ext x .prop) rest with
        | some binds => some ((x, .bool, cv) :: binds)
        | none => none
      | none => none
    else
      match wtR Γ.vals v, lower Γ.vals v with
      | some tv, some cv =>
        match lowerStmtsS (Γ.ext x (.val tv)) rest with
        | some binds => some ((x, tv.toTyV, cv) :: binds)
        | none => none
      | _, _ => none

def lowerArmsS (Γ : SCtx) (ts : NaruSem.Ty) : List Arm → Option (List Core.Arm)
  | [] => some []
  | arm :: rest =>
    match lowerArmS Γ ts arm, lowerArmsS Γ ts rest with
    | some ca, some cas => some (ca :: cas)
    | _, _ => none

def lowerArmS (Γ : SCtx) (ts : NaruSem.Ty) : Arm → Option Core.Arm
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none =>
        match lowerS (Γ.extVals bs) b with
        | some cb => some (.mk (lowerPat p) none cb)
        | none => none
      | some g =>
        match lowerS (Γ.extVals bs) g, lowerS (Γ.extVals bs) b with
        | some cg, some cb => some (.mk (lowerPat p) (some cg) cb)
        | _, _ => none

end

/-! ## 展開の補題 -/

theorem lowerStmtsS_cons (Γ : SCtx) (sp : Span) (x : String) (ty : Option Ty) (v : Expr) (rest : List Stmt) :
    lowerStmtsS Γ (.letS sp x ty v :: rest) =
      if proppyS Γ v then
        match lowerS Γ v with
        | some cv =>
          match lowerStmtsS (Γ.ext x .prop) rest with
          | some binds => some ((x, .bool, cv) :: binds)
          | none => none
        | none => none
      else
        match wtR Γ.vals v, lower Γ.vals v with
        | some tv, some cv =>
          match lowerStmtsS (Γ.ext x (.val tv)) rest with
          | some binds => some ((x, tv.toTyV, cv) :: binds)
          | none => none
        | _, _ => none :=
  lowerStmtsS.eq_2 Γ sp x ty v rest

theorem lowerArmsS_cons (Γ : SCtx) (ts : NaruSem.Ty) (arm : Arm) (rest : List Arm) :
    lowerArmsS Γ ts (arm :: rest) =
      match lowerArmS Γ ts arm, lowerArmsS Γ ts rest with
      | some ca, some cas => some (ca :: cas)
      | _, _ => none :=
  lowerArmsS.eq_2 Γ ts arm rest

theorem lowerArmS_mk (Γ : SCtx) (ts : NaruSem.Ty) (p : Pat) (g : Option Expr) (b : Expr) :
    lowerArmS Γ ts (.mk p g b) =
      match wtPat ts p with
      | none => none
      | some bs =>
        match g with
        | none =>
          match lowerS (Γ.extVals bs) b with
          | some cb => some (.mk (lowerPat p) none cb)
          | none => none
        | some g =>
          match lowerS (Γ.extVals bs) g, lowerS (Γ.extVals bs) b with
          | some cg, some cb => some (.mk (lowerPat p) (some cg) cb)
          | _, _ => none :=
  lowerArmS.eq_1 Γ ts p g b

/-- 腕の中の文脈(`proppyArms` のため): 変数パターンは値の型を知らず `.val .nat` で足す(Core の `SCtx.patCtx` と同じ)。 -/
def patCtxS (Γ : SCtx) : Pat → SCtx
  | .bind _ x => Γ.ext x (.val .nat)
  | _ => Γ

theorem patCtx_lower (Γ : SCtx) (p : Pat) : NaruSem.SCtx.patCtx Γ (lowerPat p) = patCtxS Γ p := by
  cases p <;> rfl

/-- `proppyArms` の腕 1 つ分の展開。 -/
theorem proppyArms_cons (Γ : SCtx) (p : Pat) (g : Option Expr) (b : Expr) (rest : List Arm) :
    proppyArms Γ (.mk p g b :: rest) =
      ((match g with | some g => proppyS (patCtxS Γ p) g | none => false) || proppyS (patCtxS Γ p) b || proppyArms Γ rest) := by
  cases p <;> cases g <;> rfl

theorem proppyStmts_nil (Γ : SCtx) : proppyStmts Γ [] = false := rfl

theorem proppyStmts_cons (Γ : SCtx) (sp : Span) (x : String) (ty : Option Ty) (v : Expr) (rest : List Stmt) :
    proppyStmts Γ (.letS sp x ty v :: rest) = (proppyS Γ v || proppyStmts (Γ.ext x (.val .nat)) rest) := rfl

theorem stmtsCtxP_nil (Γ : SCtx) : stmtsCtxP Γ [] = Γ := rfl

theorem stmtsCtxP_cons (Γ : SCtx) (sp : Span) (x : String) (ty : Option Ty) (v : Expr) (rest : List Stmt) :
    stmtsCtxP Γ (.letS sp x ty v :: rest) = stmtsCtxP (Γ.ext x (.val .nat)) rest := rfl

theorem proppyS_block_some (Γ : SCtx) (sp : Span) (stmts : List Stmt) (e : Expr) :
    proppyS Γ (.block sp stmts (some e)) = (proppyStmts Γ stmts || proppyS (stmtsCtxP Γ stmts) e) := rfl

/-! ## 命題の区分 `proppyS` は変換で変わらない(runtime の変換 `lower`) -/

/-- `lower` の関数帰納法で、式・`let` の列・腕の列・腕の 4 つを同時に示す: 変換結果の `proppyS` は、任意の文脈で元の AST の `proppyS` に等しい。 -/
theorem proppyS_lower_all :
    (∀ (Γ : Ctx) (e : Expr), ∀ c, lower Γ e = some c → ∀ Γ₀ : SCtx, NaruSem.proppyS Γ₀ c = proppyS Γ₀ e) ∧
    (∀ (Γ : Ctx) (stmts : List Stmt), ∀ binds, lowerStmts Γ stmts = some binds →
        ∀ (Γ₀ : SCtx) (c : Core.Expr) (e : Expr), (∀ Γ₁ : SCtx, NaruSem.proppyS Γ₁ c = proppyS Γ₁ e) →
        NaruSem.proppyS Γ₀ (mkLets binds c) = (proppyStmts Γ₀ stmts || proppyS (stmtsCtxP Γ₀ stmts) e)) ∧
    (∀ (Γ : Ctx) (ts : NaruSem.Ty) (arms : List Arm), ∀ cas, lowerArms Γ ts arms = some cas →
        ∀ Γ₀ : SCtx, NaruSem.proppyArms Γ₀ cas = proppyArms Γ₀ arms) ∧
    (∀ (Γ : Ctx) (ts : NaruSem.Ty) (arm : Arm), ∀ ca, lowerArm Γ ts arm = some ca →
        ∀ (Γ₀ : SCtx) (rest : List Arm) (crest : List Core.Arm), NaruSem.proppyArms Γ₀ crest = proppyArms Γ₀ rest →
        NaruSem.proppyArms Γ₀ (ca :: crest) = proppyArms Γ₀ (arm :: rest)) := by
  apply lower.mutual_induct
  -- 1. Nat のリテラル
  · intro Γ _ n c hc Γ₀
    simp only [lower, Option.some.injEq] at hc
    subst hc
    rfl
  -- 2. Bool のリテラル
  · intro Γ _ b c hc Γ₀
    simp only [lower, Option.some.injEq] at hc
    subst hc
    rfl
  -- 3. 局所名
  · intro Γ _ x c hc Γ₀
    simp only [lower, Option.some.injEq] at hc
    subst hc
    rfl
  -- 4. 二項演算(変換が定まる)
  · intro Γ _ op l r tl cl cr hcr hcl hl ihl ihr c hc Γ₀
    simp only [lower, hl, hcl, hcr, Option.some.injEq] at hc
    subst hc
    simp only [NaruSem.proppyS, proppyS, ihl cl hcl Γ₀, ihr cr hcr Γ₀]
  -- 5. 二項演算(定まらない)
  · intro Γ _ op l r hno _ _ c hc Γ₀
    simp only [lower] at hc
    first
      | (cases hc; done)
      | (split at hc <;> simp_all)
  -- 6. `!`(定まる)
  · intro Γ _ a ca hca iha c hc Γ₀
    simp only [lower, ite_true, hca, Option.some.injEq] at hc
    subst hc
    simp only [NaruSem.proppyS, proppyS, iha ca hca Γ₀]
  -- 7. `!`(被演算子が定まらない)
  · intro Γ _ a hca _ c hc Γ₀
    simp [lower, hca] at hc
  -- 8. 対象外の単項演算子
  · intro Γ _ op a hne c hc Γ₀
    simp [lower, hne] at hc
  -- 9. Nat の min / max(定まる)
  · intro Γ _ r m a k cr ca hca hcr hm ihr iha c hc Γ₀
    simp only [lower, hm, hcr, hca, Option.some.injEq] at hc
    subst hc
    simp only [NaruSem.proppyS, proppyS, ihr cr hcr Γ₀, iha ca hca Γ₀]
  -- 10. Nat のメソッド(定まらない)
  · intro Γ _ r m a hno _ _ c hc Γ₀
    simp only [lower] at hc
    first
      | (cases hc; done)
      | (split at hc <;> simp_all)
  -- 11. if(定まる)
  · intro Γ _ c t e cc ct ce hce hct hcc ihc iht ihe c' hc Γ₀
    simp only [lower, hcc, hct, hce, Option.some.injEq] at hc
    subst hc
    simp only [NaruSem.proppyS, proppyS, ihc cc hcc Γ₀, iht ct hct Γ₀, ihe ce hce Γ₀]
  -- 12. if(定まらない)
  · intro Γ _ c t e hno _ _ _ c' hc Γ₀
    simp only [lower] at hc
    first
      | (cases hc; done)
      | (split at hc <;> simp_all)
  -- 13. match(定まる)
  · intro Γ _ s arms ts hs cs cas hcas hcs ihs iharms c hc Γ₀
    simp only [lower, hs, hcs, hcas, Option.some.injEq] at hc
    subst hc
    simp only [NaruSem.proppyS, proppyS, ihs cs hcs Γ₀, iharms cas hcas Γ₀]
  -- 14. match(定まらない)
  · intro Γ _ s arms ts hs hno _ _ c hc Γ₀
    simp only [lower, hs] at hc
    first
      | (cases hc; done)
      | (split at hc <;> simp_all)
  -- 15. match(scrutinee の型が定まらない)
  · intro Γ _ s arms hs c hc Γ₀
    simp [lower, hs] at hc
  -- 16. ブロック(定まる)
  · intro Γ _ stmts e Γ' binds hlb hst ca hca ihst ihe c hc Γ₀
    simp only [lower, hst, hlb, hca, Option.some.injEq] at hc
    subst hc
    rw [ihst binds hlb Γ₀ ca e (ihe ca hca), proppyS_block_some]
  -- 17. ブロック(末尾式が定まらない)
  · intro Γ _ stmts e Γ' binds hlb hst hca _ _ c hc Γ₀
    simp [lower, hst, hlb, hca] at hc
  -- 18. ブロック(let の列が定まらない)
  · intro Γ _ stmts e hno _ c hc Γ₀
    simp only [lower] at hc
    first
      | (cases hc; done)
      | (split at hc <;> simp_all)
  -- 19. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 c hc Γ₀
    rw [lower.eq_def] at hc
    split at hc
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
      | (cases hc; done)
  -- 20. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp ca hca Γ₀ rest crest hrest
    rw [lowerArm_mk, hp] at hca
    simp at hca
  -- 21. 腕(ガード無し、定まる)
  · intro Γ ts p b bs hp cb hcb ihb ca hca Γ₀ rest crest hrest
    rw [lowerArm_mk, hp] at hca
    simp only [hcb, Option.some.injEq] at hca
    subst hca
    rw [NaruSem.proppyArms_cons, proppyArms_cons, patCtx_lower, hrest, ihb cb hcb]
  -- 22. 腕(ガード無し、本体が定まらない)
  · intro Γ ts p b bs hp hcb _ ca hca Γ₀ rest crest hrest
    rw [lowerArm_mk, hp] at hca
    simp [hcb] at hca
  -- 23. 腕(ガード付き、定まる)
  · intro Γ ts p b bs hp g cg cb hcb hcg ihg ihb ca hca Γ₀ rest crest hrest
    rw [lowerArm_mk, hp] at hca
    simp only [hcg, hcb, Option.some.injEq] at hca
    subst hca
    rw [NaruSem.proppyArms_cons, proppyArms_cons, patCtx_lower, hrest, ihb cb hcb]
    simp only [ihg cg hcg]
  -- 24. 腕(ガード付き、定まらない)
  · intro Γ ts p b bs hp g hno _ _ ca hca Γ₀ rest crest hrest
    rw [lowerArm_mk, hp] at hca
    simp only at hca
    first
      | (cases hca; done)
      | (split at hca <;> simp_all)
  -- 25. 腕の列(空)
  · intro Γ ts cas hcas Γ₀
    simp only [lowerArms, Option.some.injEq] at hcas
    subst hcas
    rfl
  -- 26. 腕の列(定まる)
  · intro Γ ts arm rest ca cas hcas hca iharm iharms cas' hcas' Γ₀
    rw [lowerArms_cons, hca, hcas] at hcas'
    simp only [Option.some.injEq] at hcas'
    subst hcas'
    exact iharm ca hca Γ₀ rest cas (iharms cas hcas Γ₀)
  -- 27. 腕の列(定まらない)
  · intro Γ ts arm rest hno _ _ cas hcas Γ₀
    rw [lowerArms_cons] at hcas
    first
      | (cases hcas; done)
      | (split at hcas <;> simp_all)
  -- 28. let の列(空)
  · intro Γ binds hb Γ₀ c e he
    simp only [lowerStmts, Option.some.injEq] at hb
    subst hb
    rw [mkLets_nil, proppyStmts_nil, stmtsCtxP_nil, Bool.false_or]
    exact he Γ₀
  -- 29. let の列(定まる)
  · intro Γ _ x ty v rest tv cv hcv hv binds hlb ihv ihrest binds' hb Γ₀ c e he
    simp only [lowerStmts_cons, hv, hcv, hlb, Option.some.injEq] at hb
    subst hb
    rw [mkLets_cons, proppyStmts_cons, stmtsCtxP_cons]
    simp only [NaruSem.proppyS, ihv cv hcv Γ₀, ihrest binds hlb (Γ₀.ext x (.val .nat)) c e he, Bool.or_assoc]
  -- 30. let の列(残りが定まらない)
  · intro Γ _ x ty v rest tv cv hcv hv hlb _ _ binds hb Γ₀ c e he
    simp [lowerStmts_cons, hv, hcv, hlb] at hb
  -- 31. let の列(値が定まらない)
  · intro Γ _ x ty v rest hno _ binds hb Γ₀ c e he
    rw [lowerStmts_cons] at hb
    first
      | (cases hb; done)
      | (split at hb <;> simp_all)

/-- runtime の変換 `lower` の結果の `proppyS` は、任意の文脈で元の AST の `proppyS` に等しい。 -/
theorem proppyS_lower {Γ : Ctx} {e : Expr} {c : Core.Expr} (hc : lower Γ e = some c) (Γ₀ : SCtx) :
    NaruSem.proppyS Γ₀ c = proppyS Γ₀ e :=
  proppyS_lower_all.1 Γ e c hc Γ₀

/-! ## 腕の対応の補題 -/

/-- 網羅性の走査は、腕のパターンとガードの有無が対応していれば変わらない。 -/
theorem exhaustiveFrom_lowerPat_cons (ts : NaruSem.Ty) (p : Pat) (g : Option Expr) (b : Expr) (cg : Option Core.Expr) (cb : Core.Expr)
    (hg : g.isSome = cg.isSome) (rest : List Arm) (crest : List Core.Arm)
    (hrest : ∀ sawT sawF, exhaustiveFrom ts sawT sawF rest = NaruSem.exhaustiveFrom ts sawT sawF crest) (sawT sawF : Bool) :
    exhaustiveFrom ts sawT sawF (.mk p g b :: rest) = NaruSem.exhaustiveFrom ts sawT sawF (.mk (lowerPat p) cg cb :: crest) := by
  cases g with
  | some g =>
    cases cg with
    | none => simp at hg
    | some cg => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, hrest]
  | none =>
    cases cg with
    | some cg => simp at hg
    | none =>
      cases p with
      | wild => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat]
      | bind => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat]
      | lit _ l =>
        cases l with
        | bool lb => cases lb <;> simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
        | nat n => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
        | str s => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]
        | unit => simp [exhaustiveFrom, NaruSem.exhaustiveFrom, lowerPat, hrest]

/-- 腕の `proppyArms` は、ガードと本体の `proppyS` が対応していれば変わらない。 -/
theorem proppyArms_lowerPat_cons (Γ₀ : SCtx) (p : Pat) (g : Option Expr) (b : Expr) (cg : Option Core.Expr) (cb : Core.Expr)
    (hg : g.isSome = cg.isSome) (hb : ∀ Γ₁ : SCtx, NaruSem.proppyS Γ₁ cb = proppyS Γ₁ b)
    (hgg : ∀ g' cg', g = some g' → cg = some cg' → ∀ Γ₁ : SCtx, NaruSem.proppyS Γ₁ cg' = proppyS Γ₁ g')
    (rest : List Arm) (crest : List Core.Arm) (hrest : NaruSem.proppyArms Γ₀ crest = proppyArms Γ₀ rest) :
    NaruSem.proppyArms Γ₀ (.mk (lowerPat p) cg cb :: crest) = proppyArms Γ₀ (.mk p g b :: rest) := by
  rw [NaruSem.proppyArms_cons, proppyArms_cons, patCtx_lower, hrest, hb]
  cases g with
  | none =>
    cases cg with
    | none => rfl
    | some _ => simp at hg
  | some g' =>
    cases cg with
    | none => simp at hg
    | some cg' => simp only [hgg g' cg' rfl rfl]

/-- 量化の束縛の列の対応: AST の束縛(注釈の型)が文脈に足せるなら Core の束縛も足せ、同じ文脈になる。 -/
theorem lowerBinders_sound : ∀ (bs : List Binder) {Γ Γ' : SCtx}, SCtx.extBinders Γ bs = some Γ' →
    ∃ cbs, lowerBinders bs = some cbs ∧ NaruSem.SCtx.extBinders Γ cbs = some Γ' ∧ cbs.length = bs.length := by
  intro bs
  induction bs with
  | nil =>
    intro Γ Γ' h
    simp only [SCtx.extBinders, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl, rfl⟩
  | cons bd rest ih =>
    obtain ⟨x, ty, bsp⟩ := bd
    intro Γ Γ' h
    simp only [SCtx.extBinders] at h
    cases ty with
    | none => simp at h
    | some ty =>
      simp only at h
      cases htv : ty.toTy? with
      | none => simp [htv] at h
      | some t =>
        simp only [htv] at h
        obtain ⟨crest, hcrest, hext, hlen⟩ := ih h
        refine ⟨(x, t.toTyV) :: crest, ?_, ?_, by simp [hlen]⟩
        · simp [lowerBinders, htv, hcrest]
        · simp [NaruSem.SCtx.extBinders, TyV.toTy?_toTyV, hext]

/-- 量化の意味の対応: 束縛を前から 1 つずつ剥がす `forallCons` / `existsCons` が、Core の同じ規則に写る(本体の対応を仮定)。 -/
theorem quant_sound {sp : Span} {q : Quant} {b : Expr} {cb : Core.Expr} :
    ∀ (bs : List Binder) {Γ Γ' : SCtx} {cbs : List (String × TyV)} {ρ : SEnv},
      lowerBinders bs = some cbs → SCtx.extBinders Γ bs = some Γ' → Γ = ρ.ctx →
      (∀ ρ' : SEnv, Γ' = ρ'.ctx → ∀ P : Prop, Sem ρ' b P → NaruSem.Sem ρ' cb P) →
      ∀ P : Prop, Sem ρ (.quant sp q bs b) P → NaruSem.Sem ρ (.quant q cbs cb) P := by
  intro bs
  induction bs with
  | nil =>
    intro Γ Γ' cbs ρ hcbs hb hΓ ih P hP
    simp only [lowerBinders, Option.some.injEq] at hcbs
    subst hcbs
    simp only [SCtx.extBinders, Option.some.injEq] at hb
    subst hb
    cases hP with
    | quantNil h => exact .quantNil (ih ρ hΓ P h)
  | cons bd rest ihr =>
    obtain ⟨x, ty, bsp⟩ := bd
    intro Γ Γ' cbs ρ hcbs hb hΓ ih P hP
    simp only [lowerBinders] at hcbs
    simp only [SCtx.extBinders] at hb
    cases ty with
    | none => simp at hb
    | some ty =>
      simp only at hb hcbs
      cases htv : ty.toTy? with
      | none => simp [htv] at hb
      | some t =>
        simp only [htv] at hb hcbs
        cases hrest : lowerBinders rest with
        | none => simp [hrest] at hcbs
        | some crest =>
          simp only [hrest, Option.some.injEq] at hcbs
          subst hcbs
          cases hP with
          | forallCons ht' h =>
            rw [htv] at ht'
            cases ht'
            exact .forallCons (TyV.toTy?_toTyV t)
              (fun a => ihr hrest hb (by rw [SEnv.ctx_ext, hΓ]; simp [SVal.ty]) ih _ (h a))
          | existsCons ht' h =>
            rw [htv] at ht'
            cases ht'
            exact .existsCons (TyV.toTy?_toTyV t)
              (fun a => ihr hrest hb (by rw [SEnv.ctx_ext, hΓ]; simp [SVal.ty]) ih _ (h a))

/-! ## 一般定理 -/

/-- `wtS` / `wtStmtsS` / `wtArmsS` / `wtArmS` の関数帰納法で、式・`let` の列・腕の列・腕の 4 つを同時に示す: 適格な spec の AST には変換が定まり、
その Core は同じ文脈で適格で、命題の区分 `proppyS` は任意の文脈で一致し、対応する任意の環境で AST の意味は Core の意味。
腕の列では網羅性の走査も変わらない。 -/
theorem lowerS_sound_all :
    (∀ (Γ : SCtx) (e : Expr), ∀ τ, wtS Γ e = some τ →
        ∃ c, lowerS Γ e = some c ∧ NaruSem.wtS Γ c = some τ ∧ (∀ Γ₀ : SCtx, NaruSem.proppyS Γ₀ c = proppyS Γ₀ e) ∧
          ∀ ρ : SEnv, Γ = ρ.ctx → ∀ P : Prop, Sem ρ e P → NaruSem.Sem ρ c P) ∧
    (∀ (Γ : SCtx) (stmts : List Stmt), ∀ Γ', wtStmtsS Γ stmts = some Γ' →
        ∃ binds, lowerStmtsS Γ stmts = some binds ∧
          (∀ (c : Core.Expr) (τ : STy), NaruSem.wtS Γ' c = some τ → NaruSem.wtS Γ (mkLets binds c) = some τ) ∧
          (∀ (Γ₀ : SCtx) (c : Core.Expr) (e : Expr), (∀ Γ₁ : SCtx, NaruSem.proppyS Γ₁ c = proppyS Γ₁ e) →
            NaruSem.proppyS Γ₀ (mkLets binds c) = (proppyStmts Γ₀ stmts || proppyS (stmtsCtxP Γ₀ stmts) e)) ∧
          ∀ ρ : SEnv, Γ = ρ.ctx → ∀ (sp : Span) (tail : Option Expr) (c : Core.Expr),
            (∀ ρ' : SEnv, Γ' = ρ'.ctx → ∀ P : Prop, Sem ρ' (.block sp [] tail) P → NaruSem.Sem ρ' c P) →
            ∀ P : Prop, Sem ρ (.block sp stmts tail) P → NaruSem.Sem ρ (mkLets binds c) P) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arms : List Arm), ∀ τ, wtArmsS Γ ts arms = some τ →
        ∃ cas, lowerArmsS Γ ts arms = some cas ∧ NaruSem.wtArmsS Γ ts cas = some τ ∧
          (∀ sawT sawF, exhaustiveFrom ts sawT sawF arms = NaruSem.exhaustiveFrom ts sawT sawF cas) ∧
          (∀ Γ₀ : SCtx, NaruSem.proppyArms Γ₀ cas = proppyArms Γ₀ arms) ∧
          ∀ ρ : SEnv, Γ = ρ.ctx → ∀ (sp : Span) (s : Expr) (cs : Core.Expr) (st : TyV) (v : Val),
            eval ρ.vals s = some v → NaruSem.eval ρ.vals cs = some v → v.ty = ts →
            ∀ P : Prop, Sem ρ (.matchE sp s arms) P → NaruSem.Sem ρ (.match_ cs st cas) P) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arm : Arm), ∀ p g b, arm = .mk p g b → ∀ τ, wtArmS Γ ts arm = some τ →
        ∃ cg cb, lowerArmS Γ ts arm = some (.mk (lowerPat p) cg cb) ∧ NaruSem.wtArmS Γ ts (.mk (lowerPat p) cg cb) = some τ ∧
          g.isSome = cg.isSome ∧
          (∀ Γ₀ : SCtx, NaruSem.proppyS Γ₀ cb = proppyS Γ₀ b) ∧
          (∀ g' cg', g = some g' → cg = some cg' → ∀ Γ₀ : SCtx, NaruSem.proppyS Γ₀ cg' = proppyS Γ₀ g') ∧
          ∀ ρ : SEnv, Γ = ρ.ctx → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
            (∀ P : Prop, Sem (ρ.extVals bs) b P → NaruSem.Sem (ρ.extVals bs) cb P) ∧
            (∀ g' cg', g = some g' → cg = some cg' → ∀ G : Prop, Sem (ρ.extVals bs) g' G → NaruSem.Sem (ρ.extVals bs) cg' G)) := by
  apply wtS.mutual_induct
  -- 1. Nat のリテラル(値)
  · intro Γ _ n τ hτ
    simp only [wtS, Option.some.injEq] at hτ
    subst hτ
    refine ⟨.lit (.nat n) .nat, rfl, rfl, fun _ => rfl, ?_⟩
    intro ρ _ P hP
    cases hP
  -- 2. Bool のリテラル
  · intro Γ _ b τ hτ
    simp only [wtS, Option.some.injEq] at hτ
    subst hτ
    refine ⟨.lit (.bool b) .bool, rfl, rfl, fun _ => rfl, ?_⟩
    intro ρ _ P hP
    cases hP
    exact .lit
  -- 3. 局所名
  · intro Γ _ x τ hτ
    simp only [wtS] at hτ
    refine ⟨.var x, rfl, by simpa [NaruSem.wtS] using hτ, fun _ => rfl, ?_⟩
    intro ρ _ P hP
    cases hP with
    | varVal h => exact .varVal h
    | varProp h => exact .varProp h
  -- 4. if(適格)
  · intro Γ _ c t e tc tt te hte htt hc j hj ihc iht ihe τ hτ
    simp only [wtS, hc, htt, hte, hj] at hτ
    obtain ⟨cc, hcc, hwc, hpc, hsc⟩ := ihc tc hc
    obtain ⟨ct, hct, hwt, hpt, hst⟩ := iht tt htt
    obtain ⟨ce, hce, hwe, hpe, hse⟩ := ihe te hte
    refine ⟨.ite cc ct ce, by simp [lowerS, hcc, hct, hce], ?_, ?_, ?_⟩
    · simp only [NaruSem.wtS, hwc, hwt, hwe, hj]
      exact hτ
    · intro Γ₀
      simp only [NaruSem.proppyS, proppyS, hpc, hpt, hpe]
    · intro ρ hΓ P hP
      cases hP with
      | ite hC hT hE => exact .ite (hsc ρ hΓ _ hC) (hst ρ hΓ _ hT) (hse ρ hΓ _ hE)
  -- 5. if(条件と then の結びが無い)
  · intro Γ _ c t e tc tt te hte htt hc hj _ _ _ τ hτ
    simp [wtS, hc, htt, hte, hj] at hτ
  -- 6. if(不適格)
  · intro Γ _ c t e hno _ _ _ τ hτ
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 7. 論理演算(適格)
  · intro Γ _ op l r k hk tl tr hr hl ihl ihr τ hτ
    simp only [wtS, hk, hl, hr] at hτ
    obtain ⟨cl, hcl, hwl, hpl, hsl⟩ := ihl tl hl
    obtain ⟨cr, hcr, hwr, hpr, hsr⟩ := ihr tr hr
    refine ⟨.binop op cl cr .bool, by simp [lowerS, hk, hcl, hcr], ?_, ?_, ?_⟩
    · simp only [NaruSem.wtS, hk, TyV.toTy?, hwl, hwr]
      exact hτ
    · intro Γ₀
      simp only [NaruSem.proppyS, proppyS, hpl, hpr]
    · intro ρ hΓ P hP
      cases hP with
      | logic hk' hl' hr' =>
        rw [hk] at hk'
        cases hk'
        exact .logic hk (hsl ρ hΓ _ hl') (hsr ρ hΓ _ hr')
      | eqNat hk' _ _ => rw [hk] at hk'; cases hk'
      | eqForm hk' _ _ => rw [hk] at hk'; cases hk'
      | cmpNat hk' _ _ => rw [hk] at hk'; cases hk'
      | cmpBool hk' _ _ => rw [hk] at hk'; cases hk'
  -- 8. 論理演算(被演算子が不適格)
  · intro Γ _ op l r k hk hno _ _ τ hτ
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 9. == / !=(両辺が Nat の値: 値の等値、注釈 `.nat`)
  · intro Γ _ op l r k hk hnn τ hτ
    simp only [wtS, hk, hnn, and_self, ite_true, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨cl, hcl⟩ := lower_total hnn.1
    obtain ⟨cr, hcr⟩ := lower_total hnn.2
    refine ⟨.binop op cl cr .nat, ?_, ?_, ?_, ?_⟩
    · simp [lowerS, hk, hnn, hcl, hcr]
    · simp [NaruSem.wtS, hk, TyV.toTy?, lower_wt hnn.1 hcl, lower_wt hnn.2 hcr]
    · intro Γ₀
      simp only [NaruSem.proppyS, proppyS, proppyS_lower hcl Γ₀, proppyS_lower hcr Γ₀]
    · intro ρ hΓ P hP
      cases hP with
      | logic hk' _ _ => rw [hk] at hk'; cases hk'
      | cmpNat hk' _ _ => rw [hk] at hk'; cases hk'
      | cmpBool hk' _ _ => rw [hk] at hk'; cases hk'
      | eqNat hk' hl hr =>
        rw [hk] at hk'
        cases hk'
        exact .eqNat hk (by rw [← lower_eval hnn.1 hcl]; exact hl) (by rw [← lower_eval hnn.2 hcr]; exact hr)
      | eqForm _ hl _ =>
        obtain ⟨a, ha, hat⟩ := evalS_total hnn.1 ρ hΓ
        cases a with
        | bool => simp [Val.ty] at hat
        | nat n => exact absurd ha (Sem_not_nat hl ρ.vals (Agree.vals ρ) n)
  -- 10. == / !=(論理の位置、適格: 注釈 `.bool`)
  · intro Γ _ op l r k hk hnn tl tr hr hl ihl ihr τ hτ
    simp only [wtS, hk, hnn, ite_false, hl, hr] at hτ
    obtain ⟨cl, hcl, hwl, hpl, hsl⟩ := ihl tl hl
    obtain ⟨cr, hcr, hwr, hpr, hsr⟩ := ihr tr hr
    refine ⟨.binop op cl cr .bool, ?_, ?_, ?_, ?_⟩
    · simp [lowerS, hk, hnn, hcl, hcr]
    · simp only [NaruSem.wtS, hk, TyV.toTy?, hwl, hwr]
      exact hτ
    · intro Γ₀
      simp only [NaruSem.proppyS, proppyS, hpl, hpr]
    · intro ρ hΓ P hP
      obtain ⟨hlf, _, _⟩ := STy.join_isForm hτ
      cases hP with
      | logic hk' _ _ => rw [hk] at hk'; cases hk'
      | cmpNat hk' _ _ => rw [hk] at hk'; cases hk'
      | cmpBool hk' _ _ => rw [hk] at hk'; cases hk'
      | eqForm hk' hl' hr' =>
        rw [hk] at hk'
        cases hk'
        exact .eqForm hk (hsl ρ hΓ _ hl') (hsr ρ hΓ _ hr')
      | eqNat _ hl' _ =>
        obtain ⟨Q, hQ⟩ := Sem_exists hl hlf ρ hΓ
        exact absurd hl' (Sem_not_nat hQ ρ.vals (Agree.vals ρ) _)
  -- 11. == / !=(論理の位置、被演算子が不適格)
  · intro Γ _ op l r k hk hnn hno _ _ τ hτ
    simp only [wtS, hk, hnn, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 12. 比較(適格: 注釈は被演算子の型)
  · intro Γ _ op l r k hk tr hr hl τ hτ
    simp [wtS, hk, hl, hr] at hτ
    subst hτ
    obtain ⟨cl, hcl⟩ := lower_total hl
    obtain ⟨cr, hcr⟩ := lower_total hr
    refine ⟨.binop op cl cr tr.toTyV, ?_, ?_, ?_, ?_⟩
    · simp [lowerS, hk, hl, hcl, hcr]
    · simp [NaruSem.wtS, hk, lower_wt hl hcl, lower_wt hr hcr]
    · intro Γ₀
      simp only [NaruSem.proppyS, proppyS, proppyS_lower hcl Γ₀, proppyS_lower hcr Γ₀]
    · intro ρ hΓ P hP
      obtain ⟨a, ha, hat⟩ := evalS_total hl ρ hΓ
      cases hP with
      | logic hk' _ _ => rw [hk] at hk'; cases hk'
      | eqNat hk' _ _ => rw [hk] at hk'; cases hk'
      | eqForm hk' _ _ => rw [hk] at hk'; cases hk'
      | cmpNat hk' hl' hr' =>
        rw [hk] at hk'
        cases hk'
        rw [hl'] at ha
        cases ha
        cases tr with
        | bool => simp [Val.ty] at hat
        | nat => exact .cmpNat hk (by rw [← lower_eval hl hcl]; exact hl') (by rw [← lower_eval hr hcr]; exact hr')
      | cmpBool hk' hl' hr' =>
        rw [hk] at hk'
        cases hk'
        rw [hl'] at ha
        cases ha
        cases tr with
        | nat => simp [Val.ty] at hat
        | bool => exact .cmpBool hk (by rw [← lower_eval hl hcl]; exact hl') (by rw [← lower_eval hr hcr]; exact hr')
  -- 13. 比較(被演算子の型が違う)
  · intro Γ _ op l r k hk tl tr hr hl hne τ hτ
    simp [wtS, hk, hl, hr, hne] at hτ
  -- 14. 比較(被演算子が不適格)
  · intro Γ _ op l r k hk hno τ hτ
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 15. 算術(値)
  · intro Γ _ op l r k hk hr hl τ hτ
    simp only [wtS, hk, hl, hr, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨cl, hcl⟩ := lower_total hl
    obtain ⟨cr, hcr⟩ := lower_total hr
    refine ⟨.binop op cl cr .nat, ?_, ?_, ?_, ?_⟩
    · simp [lowerS, hk, hcl, hcr]
    · simp [NaruSem.wtS, hk, TyV.toTy?, lower_wt hl hcl, lower_wt hr hcr]
    · intro Γ₀
      simp only [NaruSem.proppyS, proppyS, proppyS_lower hcl Γ₀, proppyS_lower hcr Γ₀]
    · intro ρ hΓ P hP
      cases hP with
      | logic hk' _ _ => rw [hk] at hk'; cases hk'
      | eqNat hk' _ _ => rw [hk] at hk'; cases hk'
      | eqForm hk' _ _ => rw [hk] at hk'; cases hk'
      | cmpNat hk' _ _ => rw [hk] at hk'; cases hk'
      | cmpBool hk' _ _ => rw [hk] at hk'; cases hk'
  -- 16. 算術(被演算子が不適格)
  · intro Γ _ op l r k hk hno τ hτ
    simp only [wtS, hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 17. 対象外の演算子
  · intro Γ _ op l r hk τ hτ
    simp [wtS, hk] at hτ
  -- 18. `!`(適格)
  · intro Γ _ a j hj hjf iha τ hτ
    simp [wtS, hj, hjf] at hτ
    subst hτ
    obtain ⟨ca, hca, hwa, hpa, hsa⟩ := iha j hj
    refine ⟨.unop "!" ca, by simp [lowerS, hca], by simp [NaruSem.wtS, hwa, hjf], ?_, ?_⟩
    · intro Γ₀
      simp only [NaruSem.proppyS, proppyS, hpa]
    · intro ρ hΓ P hP
      cases hP with
      | not h => exact .not (hsa ρ hΓ _ h)
  -- 19. `!`(被演算子が論理の位置の型でない)
  · intro Γ _ a j hj hjf _ τ hτ
    simp [wtS, hj, hjf] at hτ
  -- 20. `!`(被演算子が不適格)
  · intro Γ _ a hj _ τ hτ
    simp [wtS, hj] at hτ
  -- 21. 対象外の単項演算子
  · intro Γ _ op a hne τ hτ
    simp [wtS, hne] at hτ
  -- 22. Nat の min / max(値)
  · intro Γ _ r m a k ha hr hm τ hτ
    simp only [wtS, hm, hr, ha, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨cr, hcr⟩ := lower_total hr
    obtain ⟨ca, hca⟩ := lower_total ha
    refine ⟨.method "Nat" m cr [ca] .nat, ?_, ?_, ?_, ?_⟩
    · simp [lowerS, hm, hcr, hca]
    · simp [NaruSem.wtS, hm, lower_wt hr hcr, lower_wt ha hca]
    · intro Γ₀
      simp only [NaruSem.proppyS, proppyS, proppyS_lower hcr Γ₀, proppyS_lower hca Γ₀]
    · intro ρ hΓ P hP
      cases hP
  -- 23. Nat のメソッド(不適格)
  · intro Γ _ r m a hno τ hτ
    simp only [wtS] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 24. match(適格)
  · intro Γ _ s arms ta hs hex ih2 τ hτ
    simp only [wtS, hs, hex, ite_true] at hτ
    obtain ⟨cs, hcs⟩ := lower_total hs
    obtain ⟨cas, hcas, hwas, hexs, hpas, hsems⟩ := ih2 τ hτ
    refine ⟨.match_ cs ta.toTyV cas, ?_, ?_, ?_, ?_⟩
    · simp [lowerS, hs, hcs, hcas]
    · have hex' : NaruSem.exhaustive ta cas = true := by
        unfold NaruSem.exhaustive
        rw [← hexs]
        exact hex
      simp only [NaruSem.wtS, lower_wt hs hcs, TyV.toTy?_toTyV, hex', Bool.and_true, decide_true, ite_true]
      exact hwas
    · intro Γ₀
      simp only [NaruSem.proppyS, proppyS, proppyS_lower hcs Γ₀, hpas Γ₀]
    · intro ρ hΓ P hP
      obtain ⟨v, hv, hvt⟩ := evalS_total hs ρ hΓ
      exact hsems ρ hΓ _ s cs ta.toTyV v hv (by rw [← lower_eval hs hcs]; exact hv) hvt P hP
  -- 25. match(網羅しない)
  · intro Γ _ s arms ta hs hne τ hτ
    simp [wtS, hs, hne] at hτ
  -- 26. match(scrutinee が不適格)
  · intro Γ _ s arms hs τ hτ
    simp [wtS, hs] at hτ
  -- 27. ブロック(適格)
  · intro Γ sp stmts e Γ' hst ihst ihe τ hτ
    simp only [wtS, hst] at hτ
    obtain ⟨binds, hlb, hwb, hpb, hsb⟩ := ihst Γ' hst
    obtain ⟨c, hc, hw, hpc, hsc⟩ := ihe τ hτ
    refine ⟨mkLets binds c, by simp [lowerS, hst, hlb, hc], hwb c τ hw, ?_, ?_⟩
    · intro Γ₀
      rw [hpb Γ₀ c e hpc, proppyS_block_some]
    · intro ρ hΓ P hP
      refine hsb ρ hΓ sp (some e) c ?_ P hP
      intro ρ' hρ' Q hQ
      cases hQ with
      | blockTail h => exact hsc ρ' hρ' Q h
  -- 28. ブロック(let の列が不適格)
  · intro Γ _ stmts e hst _ τ hτ
    simp [wtS, hst] at hτ
  -- 29. 量化(束縛なし: 対象外)
  · intro Γ _ q b τ hτ
    simp [wtS] at hτ
  -- 30. 量化(適格)
  · intro Γ sp q bs b Γ' hb j hj hjf hne ih τ hτ
    obtain ⟨cbs, hcbs, hcb, hlen⟩ := lowerBinders_sound bs hb
    obtain ⟨cb, hcb', hwb, _, hsb⟩ := ih j hj
    have hτ' : τ = .prop := by
      cases bs with
      | nil => exact (hne rfl).elim
      | cons bd rest =>
        simp [wtS, hb, hj, hjf] at hτ
        exact hτ.symm
    subst hτ'
    refine ⟨.quant q cbs cb, ?_, ?_, fun _ => rfl, ?_⟩
    · simp [lowerS, hb, hcbs, hcb']
    · cases bs with
      | nil => exact (hne rfl).elim
      | cons bd rest =>
        cases cbs with
        | nil => simp at hlen
        | cons cbd crest => simp [NaruSem.wtS, hcb, hwb, hjf]
    · intro ρ hΓ P hP
      exact quant_sound bs hcbs hb hΓ (fun ρ' hρ' P hP => hsb ρ' hρ' P hP) P hP
  -- 31. 量化(本体が論理の位置の型でない)
  · intro Γ _ q bs b Γ' hb j hj hjf hne _ τ hτ
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj, hjf] at hτ
  -- 32. 量化(本体が不適格)
  · intro Γ _ q bs b Γ' hb hj hne _ τ hτ
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb, hj] at hτ
  -- 33. 量化(束縛の型が対象外)
  · intro Γ _ q bs b hb hne τ hτ
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest => simp [wtS, hb] at hτ
  -- 34. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 τ hτ
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
  · intro Γ ts p g b hp p' g' b' heq τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp at hτ
  -- 36. 腕(ガード無し、適格)
  · intro Γ ts p b bs' hp j hj hjf ihb p' g' b' heq τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only [hj, hjf, ite_true, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨cb, hcb, hwb, hpb, hsb⟩ := ihb j hj
    refine ⟨none, cb, ?_, ?_, rfl, hpb, ?_, ?_⟩
    · rw [lowerArmS_mk, hp]
      simp [hcb]
    · rw [NaruSem.wtArmS_mk, wtPat_lower, hp]
      simp [hwb, hjf]
    · intro g' cg' h
      cases h
    · intro ρ hΓ v hvt bs hm
      have hΓ' : Γ.extVals bs' = (ρ.extVals bs).ctx := by
        rw [SEnv.ctx_extVals, matchPat_types hp hvt hm, hΓ]
      refine ⟨fun P hP => hsb (ρ.extVals bs) hΓ' P hP, ?_⟩
      intro g' cg' h
      cases h
  -- 37. 腕(ガード無し、本体が論理の位置の型でない)
  · intro Γ ts p b bs' hp j hj hjf _ p' g' b' heq τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj, hjf] at hτ
  -- 38. 腕(ガード無し、本体が不適格)
  · intro Γ ts p b bs' hp hj _ p' g' b' heq τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj] at hτ
  -- 39. 腕(ガード付き、適格)
  · intro Γ ts p b bs' hp g tl tr hb hg ihg ihb p' g' b' heq τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only [hg, hb] at hτ
    obtain ⟨cg, hcg, hwg, hpg, hsg⟩ := ihg tl hg
    obtain ⟨cb, hcb, hwb, hpb, hsb⟩ := ihb tr hb
    refine ⟨some cg, cb, ?_, ?_, rfl, hpb, ?_, ?_⟩
    · rw [lowerArmS_mk, hp]
      simp [hcg, hcb]
    · rw [NaruSem.wtArmS_mk, wtPat_lower, hp]
      simp only [hwg, hwb]
      exact hτ
    · intro g'' cg'' h1 h2
      cases h1
      cases h2
      exact hpg
    · intro ρ hΓ v hvt bs hm
      have hΓ' : Γ.extVals bs' = (ρ.extVals bs).ctx := by
        rw [SEnv.ctx_extVals, matchPat_types hp hvt hm, hΓ]
      refine ⟨fun P hP => hsb (ρ.extVals bs) hΓ' P hP, ?_⟩
      intro g'' cg'' h1 h2 G hG
      cases h1
      cases h2
      exact hsg (ρ.extVals bs) hΓ' G hG
  -- 40. 腕(ガード付き、不適格)
  · intro Γ ts p b bs' hp g hno _ _ p' g' b' heq τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 41. 腕の列(空)
  · intro Γ ts τ hτ
    simp [wtArmsS] at hτ
  -- 42. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h] at hτ
  -- 43. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 τ hτ
    obtain ⟨p, g, b⟩ := arm
    rw [wtArmsS.eq_def] at hτ
    simp only [h1, Option.some.injEq] at hτ
    subst hτ
    obtain ⟨cg, cb, hca, hwa, hg, hpb, hpg, hsem⟩ := ih3 p g b rfl t1 h1
    refine ⟨[.mk (lowerPat p) cg cb], ?_, ?_, ?_, ?_, ?_⟩
    · rw [lowerArmsS_cons, hca]
      rfl
    · rw [NaruSem.wtArmsS.eq_def]
      simp [hwa]
    · intro sawT sawF
      exact exhaustiveFrom_lowerPat_cons ts p g b cg cb hg [] [] (fun _ _ => rfl) sawT sawF
    · intro Γ₀
      exact proppyArms_lowerPat_cons Γ₀ p g b cg cb hg hpb hpg [] [] rfl
    · intro ρ hΓ sp s cs st v hs hcs hvt P hP
      cases hP with
      | matchSkip _ _ hr => cases hr
      | matchHit hs' hm hb =>
        rw [hs] at hs'
        cases hs'
        cases cg with
        | some _ => simp at hg
        | none => exact .matchHit hcs (by rw [matchPat_lower]; exact hm) ((hsem ρ hΓ v hvt _ hm).1 _ hb)
      | matchGuard _ _ _ _ hr => cases hr
  -- 44. 腕の列(先頭の腕と残りがともに適格)
  · intro Γ ts arm t1 head tail h1 j hj ih3 ih2 τ hτ
    obtain ⟨p, g, b⟩ := arm
    rw [wtArmsS.eq_def] at hτ
    simp only [h1, hj] at hτ
    obtain ⟨cg, cb, hca, hwa, hg, hpb, hpg, hsem⟩ := ih3 p g b rfl t1 h1
    obtain ⟨cas, hcas, hwas, hexs, hpas, hsems⟩ := ih2 j hj
    refine ⟨.mk (lowerPat p) cg cb :: cas, ?_, ?_, ?_, ?_, ?_⟩
    · rw [lowerArmsS_cons, hca, hcas]
    · cases cas with
      | nil =>
        rw [NaruSem.wtArmsS.eq_def] at hwas
        simp at hwas
      | cons ca' cas' =>
        rw [NaruSem.wtArmsS.eq_def]
        simp only [hwa, hwas]
        exact hτ
    · intro sawT sawF
      exact exhaustiveFrom_lowerPat_cons ts p g b cg cb hg (head :: tail) cas hexs sawT sawF
    · intro Γ₀
      exact proppyArms_lowerPat_cons Γ₀ p g b cg cb hg hpb hpg (head :: tail) cas (hpas Γ₀)
    · intro ρ hΓ sp s cs st v hs hcs hvt P hP
      cases hP with
      | matchSkip hs' hm hr =>
        rw [hs] at hs'
        cases hs'
        exact .matchSkip hcs (by rw [matchPat_lower]; exact hm) (hsems ρ hΓ sp s cs st v hs hcs hvt _ hr)
      | matchHit hs' hm hb =>
        rw [hs] at hs'
        cases hs'
        cases cg with
        | some _ => simp at hg
        | none => exact .matchHit hcs (by rw [matchPat_lower]; exact hm) ((hsem ρ hΓ v hvt _ hm).1 _ hb)
      | matchGuard hs' hm hgG hb hr =>
        rw [hs] at hs'
        cases hs'
        cases cg with
        | none => simp at hg
        | some cg' =>
          exact .matchGuard hcs (by rw [matchPat_lower]; exact hm) ((hsem ρ hΓ v hvt _ hm).2 _ cg' rfl rfl _ hgG)
            ((hsem ρ hΓ v hvt _ hm).1 _ hb) (hsems ρ hΓ sp s cs st v hs hcs hvt _ hr)
  -- 45. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h1, h2] at hτ
  -- 46. let の列(空)
  · intro Γ Γ' h
    simp only [wtStmtsS, Option.some.injEq] at h
    subst h
    refine ⟨[], rfl, fun c τ hc => by simpa using hc, ?_, ?_⟩
    · intro Γ₀ c e he
      rw [mkLets_nil, proppyStmts_nil, stmtsCtxP_nil, Bool.false_or]
      exact he Γ₀
    · intro ρ hΓ sp tail c hk P hP
      exact hk ρ hΓ P hP
  -- 47. let の列(命題に束ねる、適格)
  · intro Γ _ x ty v rest hp hann hv ihv ihrest Γ' h
    simp only [wtStmtsS, hp, hann, hv, ite_true] at h
    obtain ⟨cv, hcv, hwv, hpv, hsv⟩ := ihv .prop hv
    obtain ⟨binds, hlb, hwb, hpb, hsb⟩ := ihrest Γ' h
    refine ⟨(x, .bool, cv) :: binds, ?_, ?_, ?_, ?_⟩
    · rw [lowerStmtsS_cons]
      simp [hp, hcv, hlb]
    · intro c τ hc
      simp only [mkLets_cons, NaruSem.wtS, TyV.toTy?, hpv Γ, hp, ite_true, hwv]
      exact hwb c τ hc
    · intro Γ₀ c e he
      rw [mkLets_cons, proppyStmts_cons, stmtsCtxP_cons]
      simp only [NaruSem.proppyS, hpv Γ₀, hpb (Γ₀.ext x (.val .nat)) c e he, Bool.or_assoc]
    · intro ρ hΓ sp tail c hk P hP
      cases hP with
      | blockLetVal hp' _ _ =>
        rw [← hΓ, hp] at hp'
        cases hp'
      | blockLetProp hp' hvP hb =>
        exact .letProp (by rw [hpv, ← hΓ]; exact hp) (hsv ρ hΓ _ hvP)
          (hsb (ρ.ext x (.prop _)) (by rw [SEnv.ctx_ext, hΓ]; rfl) sp tail c hk P hb)
  -- 48. let の列(命題だが不適格)
  · intro Γ _ x ty v rest hp hann hno _ Γ' h
    simp only [wtStmtsS, hp, hann, ite_true] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 49. let の列(命題だが注釈が Bool でない)
  · intro Γ _ x ty v rest hp hann Γ' h
    simp [wtStmtsS, hp, hann] at h
  -- 50. let の列(値に束ねる、適格)
  · intro Γ _ x ty v rest hp ta hv t hann ihrest Γ' h
    simp only [Bool.not_eq_true] at hp
    simp only [wtStmtsS, hp, Bool.false_eq_true, ite_false, hv, hann] at h
    have ht : t = ta := annot_eq hann
    subst ht
    obtain ⟨cv, hcv⟩ := lower_total hv
    have hwv := lower_wt hv hcv
    have hpv : ∀ Γ₀ : SCtx, NaruSem.proppyS Γ₀ cv = proppyS Γ₀ v := proppyS_lower hcv
    obtain ⟨binds, hlb, hwb, hpb, hsb⟩ := ihrest Γ' h
    refine ⟨(x, t.toTyV, cv) :: binds, ?_, ?_, ?_, ?_⟩
    · rw [lowerStmtsS_cons]
      simp [hp, hv, hcv, hlb]
    · intro c τ hc
      cases t with
      | nat =>
        simp only [mkLets_cons, NaruSem.wtS, Ty.toTyV, TyV.toTy?, hwv]
        exact hwb c τ hc
      | bool =>
        simp only [mkLets_cons, NaruSem.wtS, Ty.toTyV, TyV.toTy?, hpv Γ, hp, Bool.false_eq_true, ite_false, hwv]
        exact hwb c τ hc
    · intro Γ₀ c e he
      rw [mkLets_cons, proppyStmts_cons, stmtsCtxP_cons]
      simp only [NaruSem.proppyS, hpv Γ₀, hpb (Γ₀.ext x (.val .nat)) c e he, Bool.or_assoc]
    · intro ρ hΓ sp tail c hk P hP
      cases hP with
      | blockLetProp hp' _ _ =>
        rw [← hΓ, hp] at hp'
        cases hp'
      | @blockLetVal _ _ _ _ _ _ _ _ w _ _ hw hb =>
        obtain ⟨w', hw', hwt⟩ := evalS_total hv ρ hΓ
        rw [hw] at hw'
        cases hw'
        have hcw : NaruSem.eval ρ.vals cv = some w := by
          rw [← lower_eval hv hcv]
          exact hw
        have hb' := hsb (ρ.ext x (.val w)) (by rw [SEnv.ctx_ext, hΓ]; simp [SVal.ty, hwt]) sp tail c hk P hb
        cases t with
        | nat =>
          cases w with
          | bool => simp [Val.ty] at hwt
          | nat n => exact .letNat hcw hb'
        | bool =>
          cases w with
          | nat => simp [Val.ty] at hwt
          | bool w => exact .letBoolVal (by rw [hpv, ← hΓ]; exact hp) hcw hb'
  -- 51. let の列(値に束ねる、注釈が合わない)
  · intro Γ _ x ty v rest hp ta hv hann Γ' h
    simp only [Bool.not_eq_true] at hp
    simp [wtStmtsS, hp, hv, hann] at h
  -- 52. let の列(値が不適格)
  · intro Γ _ x ty v rest hp hv Γ' h
    simp only [Bool.not_eq_true] at hp
    simp [wtStmtsS, hp, hv] at h

/-- **spec の AST → Core の対応(C50)**: 文脈で適格な spec の Surface AST には変換が定まり、その Core は同じ文脈で適格で、対応する任意の環境で
AST の意味(`Surf.Sem`)は Core の意味(`NaruSem.Sem`)。 -/
theorem lowerS_sound {Γ : SCtx} {e : Expr} {τ : STy} (h : wtS Γ e = some τ) :
    ∃ c, lowerS Γ e = some c ∧ NaruSem.wtS Γ c = some τ ∧ ∀ ρ : SEnv, Γ = ρ.ctx → ∀ P : Prop, Sem ρ e P → NaruSem.Sem ρ c P :=
  let ⟨c, hc, hw, _, hs⟩ := lowerS_sound_all.1 Γ e τ h
  ⟨c, hc, hw, hs⟩

/-- 変換の全域性: 適格な spec の AST の変換は定まる(一般定理が空虚でない)。 -/
theorem lowerS_total {Γ : SCtx} {e : Expr} {τ : STy} (h : wtS Γ e = some τ) : ∃ c, lowerS Γ e = some c :=
  let ⟨c, hc, _, _⟩ := lowerS_sound h
  ⟨c, hc⟩

/-- 変換の適格性の保存: 適格な spec の AST の変換結果(実際の Core と一致することを接続検査が確かめる `c`)は同じ文脈で適格。 -/
theorem lowerS_wt {Γ : SCtx} {e : Expr} {τ : STy} (h : wtS Γ e = some τ) {c : Core.Expr} (hl : lowerS Γ e = some c) :
    NaruSem.wtS Γ c = some τ := by
  obtain ⟨c', hc', hw, _⟩ := lowerS_sound h
  rw [hl] at hc'
  cases hc'
  exact hw

/-- 命題の区分は変換で変わらない: 任意の文脈で `NaruSem.proppyS Γ₀ c = Surf.proppyS Γ₀ e`。 -/
theorem proppyS_lowerS {Γ : SCtx} {e : Expr} {τ : STy} (h : wtS Γ e = some τ) {c : Core.Expr} (hl : lowerS Γ e = some c) (Γ₀ : SCtx) :
    NaruSem.proppyS Γ₀ c = proppyS Γ₀ e := by
  obtain ⟨c', hc', _, hp, _⟩ := lowerS_sound_all.1 Γ e τ h
  rw [hl] at hc'
  cases hc'
  exact hp Γ₀

/-- 意味の対応(AST → Core): 適格な AST とその変換結果について、対応する環境で AST の意味は Core の意味。 -/
theorem lowerS_Sem {Γ : SCtx} {e : Expr} {τ : STy} (h : wtS Γ e = some τ) {c : Core.Expr} (hl : lowerS Γ e = some c)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) {P : Prop} (hP : Sem ρ e P) : NaruSem.Sem ρ c P := by
  obtain ⟨c', hc', _, hs⟩ := lowerS_sound h
  rw [hl] at hc'
  cases hc'
  exact hs ρ hρ P hP

/-- **双方向の同値(C50)**: 論理の位置で適格な AST とその変換結果について、対応する環境で、任意の命題 `P` が AST の意味であることと
Core の意味であることは同値(意味の存在 `Surf.Sem_exists` と Core の意味の一意性 `NaruSem.Sem_unique` から)。 -/
theorem Sem_lowerS_iff {Γ : SCtx} {e : Expr} {τ : STy} (h : wtS Γ e = some τ) (hf : τ.isForm = true) {c : Core.Expr}
    (hl : lowerS Γ e = some c) (ρ : SEnv) (hρ : Γ = ρ.ctx) (P : Prop) : Sem ρ e P ↔ NaruSem.Sem ρ c P := by
  refine ⟨lowerS_Sem h hl ρ hρ, fun hc => ?_⟩
  obtain ⟨Q, hQ⟩ := Sem_exists h hf ρ hρ
  have hQP : Q = P := NaruSem.Sem_unique (lowerS_Sem h hl ρ hρ hQ) hc
  subst hQP
  exact hQ

/-! ## 生成 Lean への接続(C50 / C51: C42 / C43 の `Sem_denote` と合成) -/

/-- **AST の意味 ↔ 生成 Lean の読み(命題)**: 適格な AST `e` とその変換結果 `c`、対応する環境で、AST の意味 `P` は Core の読み `denoteP ρ c` と同値。 -/
theorem preserve_prop {Γ : SCtx} {e : Expr} {τ : STy} (h : wtS Γ e = some τ) {c : Core.Expr} (hl : lowerS Γ e = some c)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) {P : Prop} (hP : Sem ρ e P) : P ↔ denoteP ρ c :=
  NaruSem.Sem_denote (lowerS_wt h hl) ρ hρ (lowerS_Sem h hl ρ hρ hP)

/-- **接続検査の健全性(AST、命題)**: 仮引数の値 `xs` の環境で適格な AST `e` について、変換結果 `c` が実際の Core(`lows_<f>` が確かめる)で、
実生成宣言の命題 `Q` が `c` の読みと等しい(`conn_<f>` が確かめる)なら、`Q` は AST の意味そのもの。 -/
theorem check_sound_prop (xs : List (String × Val)) {e : Expr} {τ : STy}
    (h : wtS (SCtx.ofList (xs.map fun p => (p.1, STy.val p.2.ty))) e = some τ) (hf : τ.isForm = true)
    {c : Core.Expr} (hl : lowerS (SCtx.ofList (xs.map fun p => (p.1, STy.val p.2.ty))) e = some c)
    {Q : Prop} (hq : Q = denoteP (SEnv.ofList (xs.map fun p => (p.1, SVal.val p.2))) c) :
    Sem (SEnv.ofList (xs.map fun p => (p.1, SVal.val p.2))) e Q := by
  have hρ : SCtx.ofList (xs.map fun p => (p.1, STy.val p.2.ty)) = (SEnv.ofList (xs.map fun p => (p.1, SVal.val p.2))).ctx := by
    rw [SEnv.ctx_ofList, List.map_map]
    rfl
  exact (Sem_lowerS_iff h hf hl _ hρ Q).2 (NaruSem.check_sound_prop xs (lowerS_wt h hl) hf hq)

end NaruSem.Surf
