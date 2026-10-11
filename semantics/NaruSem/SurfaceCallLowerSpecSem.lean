import NaruSem.SurfaceCallLowerSpecSound
import NaruSem.SurfaceCallTotality

/-!
# spec ブロックの let 列の局所意味合成

値の子式には既存の runtime 評価保存を使う。命題の子式と末尾の
双方向対応は明示的な前提であり、全 spec 式の帰納保存や宣言群の保存ではない。
存在する意味の証人を双方向に運び、意味の無い子式に True / False を補わない。
意味の存在そのものはこの局所対応の主張ではない。
-/
namespace NaruSem.Surf.Call
open Naru

/-- 同じ文脈で、意味の証人を双方向に運ぶ局所対応。命題は同値でよい。 -/
def SpecSemEquiv (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (Γ : SCtx) (e : Expr) (c : Core.Expr) : Prop :=
  ∀ ρ : SEnv, Γ = ρ.ctx → ∀ P : Prop,
    (Sem T Φ Ψ ρ e P → ∃ Q, NaruSem.Call.Sem T.Δ Φ Ψ ρ c Q ∧ (P ↔ Q)) ∧
    (NaruSem.Call.Sem T.Δ Φ Ψ ρ c P → ∃ Q, Sem T Φ Ψ ρ e Q ∧ (P ↔ Q))

/-- `propext` によって同値な命題を同じ命題として扱い、後続の環境も一致する。 -/
theorem SpecSemEquiv.iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {e : Expr} {c : Core.Expr} (h : SpecSemEquiv T Φ Ψ Γ e c)
    {ρ : SEnv} (hΓ : Γ = ρ.ctx) (P : Prop) :
    Sem T Φ Ψ ρ e P ↔ NaruSem.Call.Sem T.Δ Φ Ψ ρ c P := by
  constructor
  · intro hs
    obtain ⟨Q, hc, he⟩ := (h ρ hΓ P).1 hs
    exact (propext he).symm ▸ hc
  · intro hc
    obtain ⟨Q, hs, he⟩ := (h ρ hΓ P).2 hc
    exact (propext he).symm ▸ hs

/-- let 列を合成する証明書。値の子式の spec 意味対応は要求しない。
命題の子式と末尾の対応だけを局所的な前提にする。同名の再束縛も許す。 -/
inductive SpecLetsBridge (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) :
    SCtx → List Stmt → List (String × TyV × Core.Expr) → Expr → Core.Expr → Prop where
  | nil {Γ e c} (tail : SpecSemEquiv T Φ Ψ Γ e c) :
      SpecLetsBridge T Φ Ψ Γ [] [] e c
  | prop {Γ x sp ty v cv rest binds e c}
      (hp : proppyS T Γ v = true) (hw : wtS T Γ v = some .prop)
      (hl : lowerS T Γ v = some cv) (child : SpecSemEquiv T Φ Ψ Γ v cv)
      (restBridge : SpecLetsBridge T Φ Ψ (Γ.ext x .prop) rest binds e c) :
      SpecLetsBridge T Φ Ψ Γ (.letS sp x ty v :: rest) ((x, .bool, cv) :: binds) e c
  | value {Γ x sp ty v cv t rest binds e c}
      (hp : proppyS T Γ v = false) (hw : wtR T Γ v = some t)
      (hl : lower T Γ v = some cv)
      (restBridge : SpecLetsBridge T Φ Ψ (Γ.ext x (.val t)) rest binds e c) :
      SpecLetsBridge T Φ Ψ Γ (.letS sp x ty v :: rest) ((x, t.toTyV, cv) :: binds) e c

/-- 証明書の束縛列は独立 lowerStmtsS の出力そのもの。 -/
theorem SpecLetsBridge.lower {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {stmts : List Stmt} {binds : List (String × TyV × Core.Expr)}
    {e : Expr} {c : Core.Expr} (h : SpecLetsBridge T Φ Ψ Γ stmts binds e c) :
    lowerStmtsS T Γ stmts = some binds := by
  induction h with
  | nil => rfl
  | prop hp _ hl _ _ ih => simp [lowerStmtsS, hp, hl, ih]
  | value hp hw hl _ ih => simp [lowerStmtsS, hp, hw, hl, ih]

private theorem block_nat_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {ρ : SEnv} {sp lsp : Span} {x : String} {ty : Option NaruSem.Surf.Ty} {v : Expr}
    {rest : List Stmt} {e : Expr} {cv cb : Core.Expr} {n : Nat} {Q : Prop}
    (hp : proppyS T ρ.ctx v = false)
    (hv : eval T Φ ρ v = some (.nat n))
    (hc : NaruSem.Call.eval Φ ρ.vals cv = some (.nat n))
    (hb : Sem T Φ Ψ (ρ.ext x (.val (.nat n))) (.block sp rest (some e)) Q ↔
      NaruSem.Call.Sem T.Δ Φ Ψ (ρ.ext x (.val (.nat n))) cb Q) :
    Sem T Φ Ψ ρ (.block sp (.letS lsp x ty v :: rest) (some e)) Q ↔
      NaruSem.Call.Sem T.Δ Φ Ψ ρ (.let_ x .nat cv cb) Q := by
  constructor
  · intro h
    cases h with
    | blockLetVal _ hv' hb' =>
      have he := hv'.symm.trans hv
      cases he
      exact .letNat hc (hb.mp hb')
    | blockLetProp hp' _ _ => simp [hp] at hp'
  · intro h
    cases h with
    | letNat hc' hb' =>
      have he := hc'.symm.trans hc
      cases he
      exact .blockLetVal hp hv (hb.mpr hb')

private theorem block_bool_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {ρ : SEnv} {sp lsp : Span} {x : String} {ty : Option NaruSem.Surf.Ty} {v : Expr}
    {rest : List Stmt} {e : Expr} {cv cb : Core.Expr} {b : Bool} {Q : Prop}
    (hp : proppyS T ρ.ctx v = false) (hcp : NaruSem.Call.proppyS T.Δ ρ.ctx cv = false)
    (hv : eval T Φ ρ v = some (.bool b))
    (hc : NaruSem.Call.eval Φ ρ.vals cv = some (.bool b))
    (hb : Sem T Φ Ψ (ρ.ext x (.val (.bool b))) (.block sp rest (some e)) Q ↔
      NaruSem.Call.Sem T.Δ Φ Ψ (ρ.ext x (.val (.bool b))) cb Q) :
    Sem T Φ Ψ ρ (.block sp (.letS lsp x ty v :: rest) (some e)) Q ↔
      NaruSem.Call.Sem T.Δ Φ Ψ ρ (.let_ x .bool cv cb) Q := by
  constructor
  · intro h
    cases h with
    | blockLetVal _ hv' hb' =>
      have he := hv'.symm.trans hv
      cases he
      exact .letBoolVal hcp hc (hb.mp hb')
    | blockLetProp hp' _ _ => simp [hp] at hp'
  · intro h
    cases h with
    | letBoolVal _ hc' hb' =>
      have he := hc'.symm.trans hc
      cases he
      exact .blockLetVal hp hv (hb.mpr hb')
    | letProp hp' _ _ => simp [hcp] at hp'

private theorem block_prop_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {ρ : SEnv} {sp lsp : Span} {x : String} {ty : Option NaruSem.Surf.Ty} {v : Expr}
    {rest : List Stmt} {e : Expr} {cv cb : Core.Expr} {Q : Prop}
    (hp : proppyS T ρ.ctx v = true) (hcp : NaruSem.Call.proppyS T.Δ ρ.ctx cv = true)
    (hv : ∀ P, Sem T Φ Ψ ρ v P ↔ NaruSem.Call.Sem T.Δ Φ Ψ ρ cv P)
    (hb : ∀ P, Sem T Φ Ψ (ρ.ext x (.prop P)) (.block sp rest (some e)) Q ↔
      NaruSem.Call.Sem T.Δ Φ Ψ (ρ.ext x (.prop P)) cb Q) :
    Sem T Φ Ψ ρ (.block sp (.letS lsp x ty v :: rest) (some e)) Q ↔
      NaruSem.Call.Sem T.Δ Φ Ψ ρ (.let_ x .bool cv cb) Q := by
  constructor
  · intro h
    cases h with
    | blockLetVal hp' _ _ => simp [hp] at hp'
    | blockLetProp _ hv' hb' => exact .letProp hcp ((hv _).mp hv') ((hb _).mp hb')
  · intro h
    cases h with
    | letBoolVal hp' _ _ => simp [hcp] at hp'
    | letProp _ hv' hb' => exact .blockLetProp hp ((hv _).mpr hv') ((hb _).mpr hb')

/-- 任意の let 列を合成する双方向意味保存。関数は署名を守る任意の解釈、
spec は任意の解釈。Nat / Bool 値と Prop を分け、同名 shadowing を制限しない。 -/
theorem SpecLetsBridge.sem_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {stmts : List Stmt} {binds : List (String × TyV × Core.Expr)}
    {e : Expr} {c : Core.Expr} (h : SpecLetsBridge T Φ Ψ Γ stmts binds e c)
    (hΦ : Φ.Respects T.Δ) {ρ : SEnv} (hΓ : Γ = ρ.ctx) (sp : Span) (Q : Prop) :
    Sem T Φ Ψ ρ (.block sp stmts (some e)) Q ↔
      NaruSem.Call.Sem T.Δ Φ Ψ ρ (Surf.mkLets binds c) Q := by
  induction h generalizing ρ with
  | nil tail =>
    constructor
    · intro hs
      cases hs with
      | blockTail hs => exact (tail.iff hΓ Q).mp hs
    · intro hc
      exact .blockTail ((tail.iff hΓ Q).mpr hc)
  | @prop Γ x lsp ty v cv rest binds e c hp hw hl child restBridge ih =>
    have hpρ : proppyS T ρ.ctx v = true := hΓ ▸ hp
    have hcp : NaruSem.Call.proppyS T.Δ ρ.ctx cv = true := by
      rw [← hΓ, proppyS_lowerS hw hl, hp]
    apply block_prop_iff hpρ hcp (fun P => child.iff hΓ P)
    intro P
    apply ih
    simpa only [SEnv.ctx_ext, SVal.ty] using congrArg (fun Γ => Γ.ext x .prop) hΓ
  | @value Γ x lsp ty v cv t rest binds e c hp hw hl restBridge ih =>
    have hpρ : proppyS T ρ.ctx v = false := hΓ ▸ hp
    have he := lower_eval hw hl hΓ hΦ
    obtain ⟨w, hv, ht⟩ := eval_total hw Φ ρ hΓ hΦ
    have hc : NaruSem.Call.eval Φ ρ.vals cv = some w := he ▸ hv
    have hΓ' : Γ.ext x (.val t) = (ρ.ext x (.val w)).ctx := by
      rw [SEnv.ctx_ext, SVal.ty, ht, ← hΓ]
    cases w with
    | nat n =>
      simp only [Val.ty] at ht
      subst t
      exact block_nat_iff hpρ hv hc (ih hΓ')
    | bool b =>
      simp only [Val.ty] at ht
      subst t
      have hcp : NaruSem.Call.proppyS T.Δ ρ.ctx cv = false := by
        rw [← hΓ]
        exact NaruSem.Call.proppyS_false_of_wtR (lower_wt hw hl) (fun _ h => h)
      exact block_bool_iff hpρ hcp hv hc (ih hΓ')

/-- 公開入口: 適格性と独立 let lowering 成功を照合した上で局所証明を合成する。
命題の子式・末尾の対応を証明書から一般帰納で自動生成する主張ではない。 -/
theorem lowerStmtsS_sem_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ Γ' : SCtx} {stmts : List Stmt} {binds expected : List (String × TyV × Core.Expr)}
    {e : Expr} {c : Core.Expr}
    (_hw : wtStmtsS T Γ stmts = some Γ') (hl : lowerStmtsS T Γ stmts = some binds)
    (h : SpecLetsBridge T Φ Ψ Γ stmts expected e c)
    (hΦ : Φ.Respects T.Δ) {ρ : SEnv} (hΓ : Γ = ρ.ctx) (sp : Span) (Q : Prop) :
    Sem T Φ Ψ ρ (.block sp stmts (some e)) Q ↔
      NaruSem.Call.Sem T.Δ Φ Ψ ρ (Surf.mkLets binds c) Q := by
  have he := hl.symm.trans h.lower
  cases he
  exact h.sem_iff hΦ hΓ sp Q

/-- 適格な block の独立 `lowerS` が出した実 Core への局所合成。
末尾の lowering 成功も明示し、任意の似た Core を代用しない。 -/
theorem lowerS_block_sem_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ Γ' : SCtx} {stmts : List Stmt} {binds : List (String × TyV × Core.Expr)}
    {e : Expr} {c d : Core.Expr} {τ : STy} {sp : Span}
    (hw : wtStmtsS T Γ stmts = some Γ') (_ht : wtS T Γ' e = some τ)
    (hc : lowerS T Γ' e = some c)
    (hl : lowerS T Γ (.block sp stmts (some e)) = some d)
    (h : SpecLetsBridge T Φ Ψ Γ stmts binds e c)
    (hΦ : Φ.Respects T.Δ) {ρ : SEnv} (hΓ : Γ = ρ.ctx) (Q : Prop) :
    Sem T Φ Ψ ρ (.block sp stmts (some e)) Q ↔ NaruSem.Call.Sem T.Δ Φ Ψ ρ d Q := by
  have hd : d = Surf.mkLets binds c := by
    simpa only [lowerS, hw, h.lower, hc, Option.some.injEq] using hl.symm
  rw [hd]
  exact h.sem_iff hΦ hΓ sp Q

end NaruSem.Surf.Call
