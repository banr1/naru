import NaruSem.SurfaceCallLowerSpecSound
import NaruSem.SurfaceCallTotality

/-!
# spec の let 列・ガード付き match・量化の局所意味合成

値の子式には既存の runtime 評価保存を使う。命題の子式と末尾の
双方向対応、match のガード・本体と量化の本体の対応は明示的な前提であり、
全 spec 式の帰納保存や宣言群の保存ではない。
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

/-! ## ガード付き match の腕列の局所意味合成 -/

/-- 各腕の本体とガードの意味対応を明示する証明書。腕の順序とパターン、
束縛の型、独立 lowering の出力を保持する。子式の対応は一般帰納の結論ではない。 -/
inductive SpecArmsBridge (T : Table) (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv)
    (Γ : SCtx) (ts : NaruSem.Ty) : List Arm → List Core.Arm → Prop where
  | nil : SpecArmsBridge T Φ Ψ Γ ts [] []
  | hit {p b cb bts rest cas}
      (pat : wtPat ts p = some bts)
      (bodyLower : lowerS T (Γ.extVals bts) b = some cb)
      (body : SpecSemEquiv T Φ Ψ (Γ.extVals bts) b cb)
      (tail : SpecArmsBridge T Φ Ψ Γ ts rest cas) :
      SpecArmsBridge T Φ Ψ Γ ts (.mk p none b :: rest)
        (.mk (Surf.lowerPat p) none cb :: cas)
  | guard {p g b cg cb bts rest cas}
      (pat : wtPat ts p = some bts)
      (guardLower : lowerS T (Γ.extVals bts) g = some cg)
      (bodyLower : lowerS T (Γ.extVals bts) b = some cb)
      (guardSem : SpecSemEquiv T Φ Ψ (Γ.extVals bts) g cg)
      (body : SpecSemEquiv T Φ Ψ (Γ.extVals bts) b cb)
      (tail : SpecArmsBridge T Φ Ψ Γ ts rest cas) :
      SpecArmsBridge T Φ Ψ Γ ts (.mk p (some g) b :: rest)
        (.mk (Surf.lowerPat p) (some cg) cb :: cas)

/-- 証明書の腕列は独立 lowerArmsS が出した腕列と同じ。 -/
theorem SpecArmsBridge.lower {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {ts : NaruSem.Ty} {arms : List Arm} {cas : List Core.Arm}
    (h : SpecArmsBridge T Φ Ψ Γ ts arms cas) : lowerArmsS T Γ ts arms = some cas := by
  induction h with
  | nil => rfl
  | hit hp hl _ _ ih => simp [lowerArmsS, lowerArmS, hp, hl, ih]
  | guard hp hg hl _ _ _ ih => simp [lowerArmsS, lowerArmS, hp, hg, hl, ih]

/-- 同じ scrutinee 値と子式の双方向対応から任意の腕列の意味を合成する。
パターンの束縛はガード・本体だけへ渡し、後続腕には元の環境を使う。
網羅性や意味の存在を主張せず、空の腕列では両側に意味の証人が無い。 -/
theorem SpecArmsBridge.sem_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {ts : NaruSem.Ty} {arms : List Arm} {cas : List Core.Arm}
    (h : SpecArmsBridge T Φ Ψ Γ ts arms cas)
    {ρ : SEnv} (hΓ : Γ = ρ.ctx) {s : Expr} {cs : Core.Expr} {v : Val}
    (hs : eval T Φ ρ s = some v) (hcs : NaruSem.Call.eval Φ ρ.vals cs = some v)
    (hv : v.ty = ts) (sp : Span) (P : Prop) :
    Sem T Φ Ψ ρ (.matchE sp s arms) P ↔
      NaruSem.Call.Sem T.Δ Φ Ψ ρ (.match_ cs ts.toTyV cas) P := by
  induction h generalizing P with
  | nil => constructor <;> intro h <;> cases h
  | @hit p b cb bts rest cas hp hl body tail ih =>
    have hctx : ∀ bs, matchPat p v = some bs → Γ.extVals bts = (ρ.extVals bs).ctx := by
      intro bs hm
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, ← hΓ]
    constructor
    · intro h
      cases h with
      | matchSkip hs' hm hr =>
        have he := hs'.symm.trans hs
        cases he
        exact .matchSkip hcs (by rw [Surf.matchPat_lower]; exact hm) (ih _ |>.mp hr)
      | matchHit hs' hm hb =>
        have he := hs'.symm.trans hs
        cases he
        exact .matchHit hcs (by rw [Surf.matchPat_lower]; exact hm)
          ((body.iff (hctx _ hm) _).mp hb)
    · intro h
      cases h with
      | matchSkip hcs' hm hr =>
        have he := hcs'.symm.trans hcs
        cases he
        rw [Surf.matchPat_lower] at hm
        exact .matchSkip hs hm (ih _ |>.mpr hr)
      | matchHit hcs' hm hb =>
        have he := hcs'.symm.trans hcs
        cases he
        rw [Surf.matchPat_lower] at hm
        exact .matchHit hs hm ((body.iff (hctx _ hm) _).mpr hb)
  | @guard p g b cg cb bts rest cas hp hg hl guardSem body tail ih =>
    have hctx : ∀ bs, matchPat p v = some bs → Γ.extVals bts = (ρ.extVals bs).ctx := by
      intro bs hm
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, ← hΓ]
    constructor
    · intro h
      cases h with
      | matchSkip hs' hm hr =>
        have he := hs'.symm.trans hs
        cases he
        exact .matchSkip hcs (by rw [Surf.matchPat_lower]; exact hm) (ih _ |>.mp hr)
      | matchGuard hs' hm hguard hb hr =>
        have he := hs'.symm.trans hs
        cases he
        exact .matchGuard hcs (by rw [Surf.matchPat_lower]; exact hm)
          ((guardSem.iff (hctx _ hm) _).mp hguard)
          ((body.iff (hctx _ hm) _).mp hb) (ih _ |>.mp hr)
    · intro h
      cases h with
      | matchSkip hcs' hm hr =>
        have he := hcs'.symm.trans hcs
        cases he
        rw [Surf.matchPat_lower] at hm
        exact .matchSkip hs hm (ih _ |>.mpr hr)
      | matchGuard hcs' hm hguard hb hr =>
        have he := hcs'.symm.trans hcs
        cases he
        rw [Surf.matchPat_lower] at hm
        exact .matchGuard hs hm ((guardSem.iff (hctx _ hm) _).mpr hguard)
          ((body.iff (hctx _ hm) _).mpr hb) (ih _ |>.mpr hr)

/-- runtime 保存を scrutinee に適用し、実際の lowerS の match へ局所合成する。
本体とガードの意味対応は証明書の前提として残る。 -/
theorem lowerS_match_sem_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ : SCtx} {ts : NaruSem.Ty} {s : Expr} {arms : List Arm}
    {cs d : Core.Expr} {cas : List Core.Arm} {sp : Span}
    (hw : wtR T Γ s = some ts) (hc : lower T Γ s = some cs)
    (hl : lowerS T Γ (.matchE sp s arms) = some d)
    (h : SpecArmsBridge T Φ Ψ Γ ts arms cas)
    (hΦ : Φ.Respects T.Δ) {ρ : SEnv} (hΓ : Γ = ρ.ctx) (P : Prop) :
    Sem T Φ Ψ ρ (.matchE sp s arms) P ↔ NaruSem.Call.Sem T.Δ Φ Ψ ρ d P := by
  have hd : d = .match_ cs ts.toTyV cas := by
    simpa only [lowerS, hw, hc, h.lower, Option.some.injEq] using hl.symm
  rw [hd]
  obtain ⟨v, hs, hv⟩ := eval_total hw Φ ρ hΓ hΦ
  have hcs : NaruSem.Call.eval Φ ρ.vals cs = some v := (lower_eval hw hc hΓ hΦ) ▸ hs
  exact h.sem_iff hΓ hs hcs hv sp P

/-! ## Nat / Bool の量化の局所意味合成 -/

/-- 任意長の束縛列を、同じ Nat / Bool の全量化範囲で双方向に運ぶ。
本体の対応は拡張後の任意環境で要求する。名前の重複・外側の命題の隠蔽を許す。
意味の存在や本体の対応をこの定理だけから導くものではない。 -/
theorem lowerBinders_sem_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {b : Expr} {cb : Core.Expr} (bs : List Binder) :
    ∀ {Γ Γ' : SCtx} {cbs : List (String × TyV)} {ρ : SEnv},
      Surf.lowerBinders bs = some cbs → SCtx.extBinders Γ bs = some Γ' → Γ = ρ.ctx →
      SpecSemEquiv T Φ Ψ Γ' b cb → ∀ (sp : Span) (q : Quant) (P : Prop),
      Sem T Φ Ψ ρ (.quant sp q bs b) P ↔
        NaruSem.Call.Sem T.Δ Φ Ψ ρ (.quant q cbs cb) P := by
  induction bs with
  | nil =>
    intro Γ Γ' cbs ρ hcbs hb hΓ child sp q P
    simp only [Surf.lowerBinders, Option.some.injEq] at hcbs
    subst cbs
    simp only [SCtx.extBinders, Option.some.injEq] at hb
    subst Γ'
    constructor
    · intro h
      cases h with
      | quantNil h => exact .quantNil ((child.iff hΓ _).mp h)
    · intro h
      cases h with
      | quantNil h => exact .quantNil ((child.iff hΓ _).mpr h)
  | cons bd rest ih =>
    obtain ⟨x, ty, bsp⟩ := bd
    intro Γ Γ' cbs ρ hcbs hb hΓ child sp q P
    simp only [Surf.lowerBinders] at hcbs
    simp only [SCtx.extBinders] at hb
    cases ty with
    | none => simp at hb
    | some ty =>
      simp only at hb hcbs
      cases ht : ty.toTy? with
      | none => simp [ht] at hb
      | some t =>
        simp only [ht] at hb hcbs
        cases hr : Surf.lowerBinders rest with
        | none => simp [hr] at hcbs
        | some crest =>
          simp only [hr, Option.some.injEq] at hcbs
          subst cbs
          have hctx (a : t.carrier) :
              Γ.ext x (.val t) = (ρ.ext x (.val (Val.of t a))).ctx := by
            rw [SEnv.ctx_ext, ← hΓ]
            simp [SVal.ty]
          constructor
          · intro h
            cases h with
            | forallCons ht' h =>
              rw [ht] at ht'
              cases ht'
              exact .forallCons (TyV.toTy?_toTyV t)
                (fun a => (ih hr hb (hctx a) child sp .forall_ _).mp (h a))
            | existsCons ht' h =>
              rw [ht] at ht'
              cases ht'
              exact .existsCons (TyV.toTy?_toTyV t)
                (fun a => (ih hr hb (hctx a) child sp .exists_ _).mp (h a))
          · intro h
            cases h with
            | forallCons ht' h =>
              rw [TyV.toTy?_toTyV] at ht'
              cases ht'
              exact .forallCons ht
                (fun a => (ih hr hb (hctx a) child sp .forall_ _).mpr (h a))
            | existsCons ht' h =>
              rw [TyV.toTy?_toTyV] at ht'
              cases ht'
              exact .existsCons ht
                (fun a => (ih hr hb (hctx a) child sp .exists_ _).mpr (h a))

/-- 本体の双方向対応を任意の束縛列の対応へ合成する。 -/
theorem lowerS_quant_equiv {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ Γ' : SCtx} {bs : List Binder} {cbs : List (String × TyV)}
    {b : Expr} {cb : Core.Expr} {sp : Span} {q : Quant}
    (hb : SCtx.extBinders Γ bs = some Γ') (hcbs : Surf.lowerBinders bs = some cbs)
    (child : SpecSemEquiv T Φ Ψ Γ' b cb) :
    SpecSemEquiv T Φ Ψ Γ (.quant sp q bs b) (.quant q cbs cb) := by
  intro ρ hΓ P
  have h := lowerBinders_sem_iff bs hcbs hb hΓ child sp q P
  exact ⟨fun hs => ⟨P, h.mp hs, Iff.rfl⟩, fun hc => ⟨P, h.mpr hc, Iff.rfl⟩⟩

/-- 適格性・本体の lowering・実量化出力との一致を照合する公開入口。
本体の対応は前提であり、全 spec 式の一般帰納保存ではない。 -/
theorem lowerS_quant_sem_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {Γ Γ' : SCtx} {bs : List Binder} {cbs : List (String × TyV)}
    {b : Expr} {cb d : Core.Expr} {sp : Span} {q : Quant} {τ : STy}
    (hb : SCtx.extBinders Γ bs = some Γ') (hcbs : Surf.lowerBinders bs = some cbs)
    (_hw : wtS T Γ' b = some τ) (hc : lowerS T Γ' b = some cb)
    (hl : lowerS T Γ (.quant sp q bs b) = some d)
    (child : SpecSemEquiv T Φ Ψ Γ' b cb) {ρ : SEnv} (hΓ : Γ = ρ.ctx) (P : Prop) :
    Sem T Φ Ψ ρ (.quant sp q bs b) P ↔ NaruSem.Call.Sem T.Δ Φ Ψ ρ d P := by
  have hd : d = .quant q cbs cb := by
    simpa only [lowerS, hb, hcbs, hc, Option.some.injEq] using hl.symm
  rw [hd]
  exact lowerBinders_sem_iff bs hcbs hb hΓ child sp q P

end NaruSem.Surf.Call
