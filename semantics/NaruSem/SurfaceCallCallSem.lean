import NaruSem.SurfaceCallLowerSpecSem

/-!
# 呼出し葉の双方向意味保存

通常呼出し(位置・名前付き・ゼロ引数・修飾名)とUFCSのwhole wtSと
独立lowerS出力から、同じ署名と任意の関数/input・spec解釈で意味証人を両方向に運ぶ。
実引数の評価対応はruntimeの一般保存から導き、子SpecSemEquivを仮定しない。
spec解釈の存在は要求せず、欠落による意味不在も保つ。呼出し先の意味自体の対応と
全spec式の相互帰納、Surface/Core宣言群・実生成Leanへの合成は別の証明義務である。
-/
namespace NaruSem.Surf.Call
open Naru

private theorem call_leaf_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {ρ : SEnv} {sp sf : Span} {path : List String} {args : List Arg} {k : String}
    {s : DeclSig} {vals : List (Option String × Val)} {vs : List Val} {cs : List Core.Expr}
    (hg : headBound ρ path = false) (hr : T.resolve path = some k) (hs : T.sig k = some s)
    (ha : evalArgs T Φ ρ args = some vals) (hv : arrange s.params vals = some vs)
    (hc : NaruSem.Call.evalArgs Φ ρ.vals cs = some vs) (P : Prop) :
    Sem T Φ Ψ ρ (.call sp (.var sf path) args) P ↔
      NaruSem.Call.Sem T.Δ Φ Ψ ρ (.call k cs) P := by
  cases s with
  | fn ps t | input ps t =>
    constructor
    · intro h
      cases h with
      | callVal hg' hr' hd hf ha' hv' hb =>
        have hk := hr.symm.trans hr'; cases hk
        simp only [hs, Option.bind_some, DeclSig.value?, Option.some.injEq, Prod.mk.injEq] at hd
        rcases hd with ⟨rfl, rfl⟩
        have he := ha.symm.trans ha'; cases he
        have he := hv.symm.trans hv'; cases he
        exact .callVal (by simp [NaruSem.Call.isValueKey, NaruSem.Call.valueSig?, Table.Δ, hs,
          DeclSig.toSig, NaruSem.Call.Sig.value?]) hf hc hb
      | callSpec hg' hr' hd =>
        have hk := hr.symm.trans hr'; cases hk
        simp [hs] at hd
    · intro h
      cases h with
      | callVal hk hf hc' hb =>
        have he := hc.symm.trans hc'; cases he
        exact .callVal (ps := ps) (t := t) hg hr (by simp [hs, DeclSig.value?]) hf ha (by simpa only [DeclSig.params] using hv) hb
      | callSpec hk =>
        simp [NaruSem.Call.isSpecKey, NaruSem.Call.specSig?, Table.Δ, hs,
          DeclSig.toSig, NaruSem.Call.Sig.spec?] at hk
  | spec ps =>
    constructor
    · intro h
      cases h with
      | callVal hg' hr' hd =>
        have hk := hr.symm.trans hr'; cases hk
        simp [hs, DeclSig.value?] at hd
      | callSpec hg' hr' hd hF ha' hv' =>
        have hk := hr.symm.trans hr'; cases hk
        simp only [hs, Option.some.injEq, DeclSig.spec.injEq] at hd
        subst hd
        have he := ha.symm.trans ha'; cases he
        have he := hv.symm.trans hv'; cases he
        exact .callSpec (by simp [NaruSem.Call.isSpecKey, specSig?_Δ hs]) hF hc
    · intro h
      cases h with
      | callVal hk =>
        simp [NaruSem.Call.isValueKey, NaruSem.Call.valueSig?, Table.Δ, hs,
          DeclSig.toSig, NaruSem.Call.Sig.value?] at hk
      | callSpec hk hF hc' =>
        have he := hc.symm.trans hc'; cases he
        exact .callSpec hg hr hs hF ha hv

private theorem ufcs_leaf_iff {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    {ρ : SEnv} {sp : Span} {r : Expr} {m : String} {args : List Arg} {k : String}
    {s : DeclSig} {vals : List (Option String × Val)} {vs : List Val} {cs : List Core.Expr} {rv : Val}
    (hg : ufcs T ρ m = true) (hr : T.resolve [m] = some k) (hs : T.sig k = some s)
    (her : eval T Φ ρ r = some rv) (ha : evalArgs T Φ ρ args = some vals) (hv : arrange s.params ((none, rv) :: vals) = some vs)
    (hc : NaruSem.Call.evalArgs Φ ρ.vals cs = some vs) (P : Prop) :
    Sem T Φ Ψ ρ (.method sp r m args) P ↔
      NaruSem.Call.Sem T.Δ Φ Ψ ρ (.call k cs) P := by
  cases s with
  | fn ps t | input ps t =>
    constructor
    · intro h
      cases h with
      | ufcsVal hg' hr' hd hf her' ha' hv' hb =>
        have hk := hr.symm.trans hr'; cases hk
        simp only [hs, Option.bind_some, DeclSig.value?, Option.some.injEq, Prod.mk.injEq] at hd
        rcases hd with ⟨rfl, rfl⟩
        have he := her.symm.trans her'; cases he
        have he := ha.symm.trans ha'; cases he
        have he := hv.symm.trans hv'; cases he
        exact .callVal (by simp [NaruSem.Call.isValueKey, NaruSem.Call.valueSig?, Table.Δ, hs,
          DeclSig.toSig, NaruSem.Call.Sig.value?]) hf hc hb
      | ufcsSpec hg' hr' hd =>
        have hk := hr.symm.trans hr'; cases hk
        simp [hs] at hd
    · intro h
      cases h with
      | callVal hk hf hc' hb =>
        have he := hc.symm.trans hc'; cases he
        exact .ufcsVal (ps := ps) (t := t) hg hr (by simp [hs, DeclSig.value?]) hf her ha (by simpa only [DeclSig.params] using hv) hb
      | callSpec hk =>
        simp [NaruSem.Call.isSpecKey, NaruSem.Call.specSig?, Table.Δ, hs,
          DeclSig.toSig, NaruSem.Call.Sig.spec?] at hk
  | spec ps =>
    constructor
    · intro h
      cases h with
      | ufcsVal hg' hr' hd =>
        have hk := hr.symm.trans hr'; cases hk
        simp [hs, DeclSig.value?] at hd
      | ufcsSpec hg' hr' hd hF her' ha' hv' =>
        have hk := hr.symm.trans hr'; cases hk
        simp only [hs, Option.some.injEq, DeclSig.spec.injEq] at hd
        subst hd
        have he := her.symm.trans her'; cases he
        have he := ha.symm.trans ha'; cases he
        have he := hv.symm.trans hv'; cases he
        exact .callSpec (by simp [NaruSem.Call.isSpecKey, specSig?_Δ hs]) hF hc
    · intro h
      cases h with
      | callVal hk =>
        simp [NaruSem.Call.isValueKey, NaruSem.Call.valueSig?, Table.Δ, hs,
          DeclSig.toSig, NaruSem.Call.Sig.value?] at hk
      | callSpec hk hF hc' =>
        have he := hc.symm.trans hc'; cases he
        exact .ufcsSpec hg hr hs hF her ha hv

/-- 適格な引数から同じ仮引数順の値を導く。子式の対応はruntime一般定理を使う。 -/
theorem lowerArgs_arrange_eval {T : Table} {Γ : SCtx} {args : List Arg}
    {tys : List (Option String × NaruSem.Ty)} {cargs : List (Option String × Core.Expr)}
    {ps : List (String × NaruSem.Ty)} {cs : List Core.Expr}
    {Φ : NaruSem.Call.FEnv} {ρ : SEnv}
    (hw : wtArgs T Γ args = some tys) (hl : lowerArgs T Γ args = some cargs)
    (ht : arrange ps tys = some (ps.map (·.2))) (hc : arrange ps cargs = some cs)
    (hΓ : Γ = ρ.ctx) (hΦ : Φ.Respects T.Δ) :
    ∃ vals vs, evalArgs T Φ ρ args = some vals ∧ arrange ps vals = some vs ∧
      NaruSem.Call.evalArgs Φ ρ.vals cs = some vs ∧ vs.map Val.ty = ps.map (·.2) := by
  obtain ⟨vals, ha, he⟩ := lowerArgs_eval hw hl hΓ hΦ
  obtain ⟨vals', ha', hvt⟩ := evalArgs_total hw Φ ρ hΓ hΦ
  have heq := ha'.symm.trans ha
  cases heq
  obtain ⟨vs, hv, hvst⟩ := arrange_vals hvt ht
  exact ⟨vals, vs, ha, hv, arrange_eval he hc hv, hvst⟩

private theorem callTyS_params {T : Table} {path : List String}
    {tys : List (Option String × NaruSem.Ty)} {τ : STy}
    (hw : callTyS T path tys = some τ) :
    ∃ k s, T.resolve path = some k ∧ T.sig k = some s ∧
      arrange s.params tys = some (s.params.map (·.2)) := by
  unfold callTyS at hw
  cases hr : T.resolve path with
  | none => simp [hr] at hw
  | some k =>
    simp only [hr] at hw
    cases hs : T.sig k with
    | none => simp [hs] at hw
    | some s =>
      cases s <;> simp only [hs] at hw
      all_goals
        split at hw
        · rename_i ht
          exact ⟨k, _, rfl, hs, ht⟩
        · cases hw

/-- 通常呼出しの双方向対応。whole wtSと実lowerS出力から全引数・署名を導く。
任意のspec解釈(不在を含む)を許し、callee保存をここでは仮定しない。 -/
theorem lowerS_call_sem_iff {T : Table} {Γ : SCtx} {sp sf : Span}
    {path : List String} {args : List Arg} {τ : STy} {d : Core.Expr}
    {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv} {ρ : SEnv}
    (hw : wtS T Γ (.call sp (.var sf path) args) = some τ)
    (hl : lowerS T Γ (.call sp (.var sf path) args) = some d)
    (hΦ : Φ.Respects T.Δ) (hΓ : Γ = ρ.ctx) (P : Prop) :
    Sem T Φ Ψ ρ (.call sp (.var sf path) args) P ↔ NaruSem.Call.Sem T.Δ Φ Ψ ρ d P := by
  rw [wtS.eq_def] at hw
  cases hb : headBound Γ path with
  | true => simp [hb] at hw
  | false =>
    simp only [hb, Bool.false_eq_true, ite_false] at hw
    cases hargs : wtArgs T Γ args with
    | none => simp [hargs] at hw
    | some tys =>
      simp only [hargs] at hw
      obtain ⟨k, s, hr, hs, ht⟩ := callTyS_params hw
      rw [lowerS.eq_def] at hl
      simp only [hb, Bool.false_eq_true, ite_false] at hl
      cases hlargs : lowerArgs T Γ args with
      | none => simp [hlargs] at hl
      | some cargs =>
        simp only [hlargs, Option.bind_some, lowerCallS, hr, hs] at hl
        cases hc : arrange s.params cargs with
        | none => simp [hc] at hl
        | some cs =>
          simp only [hc, Option.map_some, Option.some.injEq] at hl
          subst d
          obtain ⟨vals, vs, ha, hv, he, _⟩ := lowerArgs_arrange_eval hargs hlargs ht hc hΓ hΦ
          have hρ : headBound ρ path = false := by rw [← headBound_ctx, ← hΓ]; exact hb
          exact call_leaf_iff hρ hr hs ha hv he P

/-- UFCSの受け手を先頭へ運び、whole wtSと実lowerS出力から双方向対応を導く。
Nat.min/maxの組込み分岐は対象にせず、同じinput/spec解釈をそのまま渡す。 -/
theorem lowerS_ufcs_sem_iff {T : Table} {Γ : SCtx} {sp : Span}
    {r : Expr} {m : String} {args : List Arg} {τ : STy} {d : Core.Expr}
    {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv} {ρ : SEnv}
    (hu : ufcs T Γ m = true) (hw : wtS T Γ (.method sp r m args) = some τ)
    (hl : lowerS T Γ (.method sp r m args) = some d)
    (hΦ : Φ.Respects T.Δ) (hΓ : Γ = ρ.ctx) (P : Prop) :
    Sem T Φ Ψ ρ (.method sp r m args) P ↔ NaruSem.Call.Sem T.Δ Φ Ψ ρ d P := by
  rw [wtS.eq_def] at hw
  simp only [hu, ite_true] at hw
  cases hwr : wtR T Γ r with
  | none => simp [hwr] at hw
  | some tr =>
    cases hargs : wtArgs T Γ args with
    | none => simp [hwr, hargs] at hw
    | some tys =>
      simp only [hwr, hargs] at hw
      obtain ⟨k, s, hr, hs, ht⟩ := callTyS_params hw
      rw [lowerS.eq_def] at hl
      simp only [hu, ite_true] at hl
      cases hlr : lower T Γ r with
      | none => simp [hlr] at hl
      | some cr =>
        cases hlargs : lowerArgs T Γ args with
        | none => simp [hlr, hlargs] at hl
        | some cargs =>
          simp only [hlr, hlargs, lowerCallS, hr, hs] at hl
          cases hc : arrange s.params ((none, cr) :: cargs) with
          | none => simp [hc] at hl
          | some cs =>
            simp only [hc, Option.map_some, Option.some.injEq] at hl
            subst d
            have hw' : wtArgs T Γ (.pos r :: args) = some ((none, tr) :: tys) := by
              simp [wtArgs, hwr, hargs]
            have hl' : lowerArgs T Γ (.pos r :: args) = some ((none, cr) :: cargs) := by
              simp [lowerArgs, hlr, hlargs]
            obtain ⟨vals, vs, ha, hv, he, _⟩ := lowerArgs_arrange_eval hw' hl' ht hc hΓ hΦ
            rw [evalArgs.eq_def] at ha
            cases her : eval T Φ ρ r with
            | none => simp [her] at ha
            | some rv =>
              cases hae : evalArgs T Φ ρ args with
              | none => simp [her, hae] at ha
              | some avs =>
                simp only [her, hae, Option.some.injEq] at ha
                subst vals
                have hρ : ufcs T ρ m = true := by rw [← ufcs_ctx, ← hΓ]; exact hu
                exact ufcs_leaf_iff hρ hr hs her hae hv he P

/-- 通常呼出しを全spec帰納法の子式対応に使える形へ写す。 -/
theorem lowerS_call_equiv {T : Table} {Γ : SCtx} {sp sf : Span}
    {path : List String} {args : List Arg} {τ : STy} {d : Core.Expr}
    {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    (hw : wtS T Γ (.call sp (.var sf path) args) = some τ)
    (hl : lowerS T Γ (.call sp (.var sf path) args) = some d)
    (hΦ : Φ.Respects T.Δ) : SpecSemEquiv T Φ Ψ Γ (.call sp (.var sf path) args) d :=
  SpecSemEquiv.of_iff (fun _ hΓ P => lowerS_call_sem_iff hw hl hΦ hΓ P)

/-- UFCSを全spec帰納法の子式対応に使える形へ写す。 -/
theorem lowerS_ufcs_equiv {T : Table} {Γ : SCtx} {sp : Span}
    {r : Expr} {m : String} {args : List Arg} {τ : STy} {d : Core.Expr}
    {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv}
    (hu : ufcs T Γ m = true) (hw : wtS T Γ (.method sp r m args) = some τ)
    (hl : lowerS T Γ (.method sp r m args) = some d)
    (hΦ : Φ.Respects T.Δ) : SpecSemEquiv T Φ Ψ Γ (.method sp r m args) d :=
  SpecSemEquiv.of_iff (fun _ hΓ P => lowerS_ufcs_sem_iff hu hw hl hΦ hΓ P)

end NaruSem.Surf.Call
