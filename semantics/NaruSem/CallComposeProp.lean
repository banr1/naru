import NaruSem.CallDenoteProp

/-!
# 宣言群の命題同値の合成

各 spec の接続証拠は、その宣言より前の署名で本体を読む。実生成定数の環境は
全宣言を含んでよいが、型付けと値/命題の分類には依存 prefix を使う。
`SpecEvidence` は署名を宣言順に更新するため、別の prefix の証拠を流用できない。
`interp_prop_agree` は fn の証拠と同じ input 解釈、各 spec の証拠から、独立した
宣言群の意味と実生成命題環境の双方向の同値を合成する。Surface の保存は別の義務。
-/

namespace NaruSem.Call
open Naru

/-- spec 一つの接続: 型に合う任意の実引数で実生成命題と prefix 署名での本体の読みが同値。 -/
def SpecConn (Δ : SigEnv) (Φ' : FEnv) (Ψ' : PEnv) (k : String)
    (ps : List (String × Ty)) (body : Core.Expr) : Prop :=
  ∃ F', Ψ' k = some F' ∧
    ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) →
      (F' vs ↔ denoteP Δ Φ' Ψ' (Env.toSEnv (Env.ofList ((ps.map (·.1)).zip vs))) body)

/-- prefix を更新しながら全 spec の証拠を要求する。fn の証拠は既存の `Evidence` に保持する。 -/
def SpecEvidence (Φ' : FEnv) (Ψ' : PEnv) : SigEnv → Prog → Prop
  | _, [] => True
  | Δ, d :: rest =>
    (match d with | .spec k ps body => SpecConn Δ Φ' Ψ' k ps body | _ => True) ∧
      SpecEvidence Φ' Ψ' (Δ.ext d.key d.sig) rest

/-- 各宣言の step で値の一致を既存の fn 合成から、命題同値を spec 接続から導く。 -/
theorem interpFrom_prop_inputs_agree (Δ' : SigEnv) (Φ' : FEnv) (Ψ' : PEnv) (hΦ' : Φ'.Respects Δ') :
    ∀ (P : Prog) (m : Interp) {Δ : SigEnv}, wtProg m.Δ P = some Δ →
      m.Φ.Respects m.Δ → m.Φ.RespectsInputs P → m.Ψ.Defined m.Δ →
      SigEnv.SubV Δ Δ' → InputsAgree m.Φ Φ' P → Evidence Δ' Φ' P → SpecEvidence Φ' Ψ' m.Δ P →
      FEnv.Agree m.Φ Φ' m.Δ → PEnv.Agree m.Ψ Ψ' m.Δ → PEnv.Agree (interpFrom m P).Ψ Ψ' Δ
  | [], m, Δ, h, _, _, _, _, _, _, _, _, hp => by
    simp only [wtProg, Option.some.injEq] at h
    subst h
    simpa [interpFrom] using hp
  | d :: rest, m, Δ, h, hΦ, hI, hΨ, hsub, hin, hev, hspec, hag, hp => by
    obtain ⟨hfresh, hwt, hrest⟩ := wtProg_cons h
    obtain ⟨hΦs, hIs, hΨs⟩ := Interp.step_inv m d rest hfresh hwt hrest hΦ hI hΨ
    have hsubm : SigEnv.SubV m.Δ Δ' := fun k ps t hk => hsub k ps t (SubV_of_wtProg (d :: rest) h k ps t hk)
    have hsubs : SigEnv.SubV (m.step d).Δ Δ' := by
      rw [Interp.step_Δ]
      exact fun k ps t hk => hsub k ps t (SubV_of_wtProg rest hrest k ps t hk)
    have hone : wtProg m.Δ [d] = some (m.step d).Δ := by
      rw [Interp.step_Δ]
      simp [wtProg, hfresh, hwt]
    have hags : FEnv.Agree (m.step d).Φ Φ' (m.step d).Δ := by
      have := interpFrom_inputs_agree Δ' Φ' hΦ' [d] m hone hΦ
        (fun k ps t hk => hI k ps t (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hk)))) hΨ hsubs
        (fun k ps t hk => hin k ps t (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hk))))
        (fun d' hd => hev d' (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hd)))) hag
      simpa [interpFrom] using this
    have hps : PEnv.Agree (m.step d).Ψ Ψ' (m.step d).Δ := by
      intro y ps hy
      rw [Interp.step_Δ] at hy
      by_cases hk : y = d.key
      · subst hk
        rw [specSig?, SigEnv.ext_self] at hy
        cases d with
        | fn k ps' t body => simp [Decl.sig, Sig.spec?] at hy
        | input k ps' t => simp [Decl.sig, Sig.spec?] at hy
        | spec k ps' body =>
          simp only [Decl.sig, Sig.spec?, Option.bind_some, Option.some.injEq] at hy
          subst ps
          have hc : SpecConn m.Δ Φ' Ψ' k ps' body := hspec.1
          obtain ⟨F', hF', hconn⟩ := hc
          refine ⟨(fun vs => ∃ ρ, bindParams ps' vs = some ρ ∧ ∃ Q, Sem m.Δ m.Φ m.Ψ (Env.toSEnv ρ) body Q ∧ Q), F', ?_, hF', ?_⟩
          · simp [Interp.step, PEnv.ext, Decl.key]
          · intro vs hvs
            obtain ⟨hb, hty⟩ := bindParams_ty hvs
            simp only [wtDecl] at hwt
            split at hwt
            · rename_i τ hτ
              have hctx : paramSCtx ps' = (Env.toSEnv (Env.ofList ((ps'.map (·.1)).zip vs))).ctx := by
                rw [Env.toSEnv_ctx, hty, paramSCtx_eq]
              constructor
              · rintro ⟨ρ, hρ, Q, hQ, hq⟩
                rw [hb] at hρ
                cases hρ
                exact (hconn vs hvs).mpr ((Sem_denote hsubm hΦ' hag hp hτ _ hctx hQ).mp hq)
              · intro hq
                exact ⟨_, hb, _, Sem_denoteP hsubm hΦ' hag hp hτ hwt _ hctx, (hconn vs hvs).mp hq⟩
            · cases hwt
      · rw [specSig?, SigEnv.ext_ne _ _ _ hk] at hy
        obtain ⟨F, F', hF, hF', hiff⟩ := hp y ps hy
        exact ⟨F, F', by rw [Interp.step_Ψ_ne _ _ hk]; exact hF, hF', hiff⟩
    have hin' : InputsAgree (m.step d).Φ Φ' rest := by
      intro k ps t hk vs hvs
      have hne : k ≠ d.key := by
        intro he
        have hf := wtProg_fresh rest hrest _ hk
        change (m.Δ.ext d.key d.sig) k = none at hf
        rw [he, SigEnv.ext_self] at hf
        cases hf
      rw [Interp.step_Φ_ne _ _ hne]
      exact hin k ps t (List.mem_cons_of_mem _ hk) vs hvs
    have hevs : Evidence Δ' Φ' rest := fun d' hd => hev d' (List.mem_cons_of_mem _ hd)
    have hspecs : SpecEvidence Φ' Ψ' (m.step d).Δ rest := by
      rw [Interp.step_Δ]
      exact hspec.2
    simp only [interpFrom]
    exact interpFrom_prop_inputs_agree Δ' Φ' Ψ' hΦ' rest (m.step d)
      (by rw [Interp.step_Δ]; exact hrest) hΦs hIs hΨs hsub hin' hevs hspecs hags hps

/-- 適格な宣言群と型内で一致する任意 input 解釈で、全 fn/spec 接続証拠から spec の双方向同値を合成する。 -/
theorem interp_prop_inputs_agree {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ)
    {I : FEnv} (hI : I.RespectsInputs P) {Δ' : SigEnv} {Φ' : FEnv} {Ψ' : PEnv}
    (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hin : InputsAgree I Φ' P)
    (hev : Evidence Δ' Φ' P) (hsp : SpecEvidence Φ' Ψ' SigEnv.empty P) :
    PEnv.Agree (interp I P).Ψ Ψ' Δ :=
  interpFrom_prop_inputs_agree Δ' Φ' Ψ' hΦ' P (Interp.init I) hP (Interp.init_respects I) hI
    (Interp.init_defined I) hΔ hin hev hsp
    (fun k ps t h => by simp [Interp.init, valueSig?, SigEnv.empty] at h)
    (fun k ps h => by simp [Interp.init, specSig?, SigEnv.empty] at h)

/-- 従来の関数全体の input 等式を使う命題合成 API。 -/
theorem interpFrom_prop_agree (Δ' : SigEnv) (Φ' : FEnv) (Ψ' : PEnv) (hΦ' : Φ'.Respects Δ')
    (P : Prog) (m : Interp) {Δ : SigEnv} (hP : wtProg m.Δ P = some Δ)
    (hΦ : m.Φ.Respects m.Δ) (hI : m.Φ.RespectsInputs P) (hΨ : m.Ψ.Defined m.Δ)
    (hΔ : SigEnv.SubV Δ Δ') (hin : SameInputs m.Φ Φ' P) (hev : Evidence Δ' Φ' P)
    (hsp : SpecEvidence Φ' Ψ' m.Δ P) (hag : FEnv.Agree m.Φ Φ' m.Δ)
    (hp : PEnv.Agree m.Ψ Ψ' m.Δ) : PEnv.Agree (interpFrom m P).Ψ Ψ' Δ :=
  interpFrom_prop_inputs_agree Δ' Φ' Ψ' hΦ' P m hP hΦ hI hΨ hΔ hin.agree hev hsp hag hp

theorem interp_prop_agree {P : Prog} {Δ : SigEnv} (hP : wtProg SigEnv.empty P = some Δ)
    {I : FEnv} (hI : I.RespectsInputs P) {Δ' : SigEnv} {Φ' : FEnv} {Ψ' : PEnv}
    (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hin : SameInputs I Φ' P)
    (hev : Evidence Δ' Φ' P) (hsp : SpecEvidence Φ' Ψ' SigEnv.empty P) :
    PEnv.Agree (interp I P).Ψ Ψ' Δ :=
  interp_prop_inputs_agree hP hI hΔ hΦ' hin.agree hev hsp

/-! ## カリー化された実生成 spec の接続 -/

def PFn : List Ty → Type
  | [] => Prop
  | t :: ps => t.carrier → PFn ps

def wrapP : (ps : List Ty) → PFn ps → List Val → Prop
  | [], g, [] => g
  | .nat :: ps, g, .nat n :: vs => wrapP ps (g n) vs
  | .bool :: ps, g, .bool b :: vs => wrapP ps (g b) vs
  | _, _, _ => False

theorem wrapP_nil (g : PFn []) : wrapP [] g [] = g := by rfl
theorem wrapP_nat (ps : List Ty) (g : PFn (.nat :: ps)) (n : Nat) (vs : List Val) :
    wrapP (.nat :: ps) g (.nat n :: vs) = wrapP ps (g n) vs := by rfl
theorem wrapP_bool (ps : List Ty) (g : PFn (.bool :: ps)) (b : Bool) (vs : List Val) :
    wrapP (.bool :: ps) g (.bool b :: vs) = wrapP ps (g b) vs := by rfl

def CurriedP (Δ : SigEnv) (Φ : FEnv) (Ψ : PEnv) (body : Core.Expr) :
    (ps : List (String × Ty)) → PFn (ps.map (·.2)) → List (String × Val) → Prop
  | [], g, acc => g ↔ denoteP Δ Φ Ψ (Env.toSEnv (Env.ofList acc)) body
  | (x, .nat) :: ps, g, acc => ∀ n : Nat, CurriedP Δ Φ Ψ body ps (g n) (acc ++ [(x, .nat n)])
  | (x, .bool) :: ps, g, acc => ∀ b : Bool, CurriedP Δ Φ Ψ body ps (g b) (acc ++ [(x, .bool b)])

theorem curried_wrapP (Δ : SigEnv) (Φ : FEnv) (Ψ : PEnv) (body : Core.Expr) :
    ∀ (ps : List (String × Ty)) (g : PFn (ps.map (·.2))) (acc : List (String × Val)),
      CurriedP Δ Φ Ψ body ps g acc → ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) →
        (wrapP (ps.map (·.2)) g vs ↔ denoteP Δ Φ Ψ (Env.toSEnv (Env.ofList (acc ++ (ps.map (·.1)).zip vs))) body)
  | [], g, acc, h, vs, hvs => by
    cases vs with
    | nil =>
      change g ↔ denoteP Δ Φ Ψ (Env.toSEnv (Env.ofList (acc ++ []))) body
      rw [List.append_nil]
      exact h
    | cons v vs => simp at hvs
  | (x, .nat) :: ps, g, acc, h, vs, hvs => by
    cases vs with
    | nil => simp at hvs
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at hvs
      obtain ⟨hv, hvs⟩ := hvs
      cases v with
      | bool => simp [Val.ty] at hv
      | nat n =>
        have hh := curried_wrapP Δ Φ Ψ body ps (g n) (acc ++ [(x, .nat n)]) (h n) vs hvs
        rw [List.append_assoc, List.singleton_append] at hh
        change wrapP (.nat :: ps.map (fun p : String × Ty => p.2)) g (.nat n :: vs) ↔ _
        rw [wrapP_nat]
        exact hh
  | (x, .bool) :: ps, g, acc, h, vs, hvs => by
    cases vs with
    | nil => simp at hvs
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at hvs
      obtain ⟨hv, hvs⟩ := hvs
      cases v with
      | nat => simp [Val.ty] at hv
      | bool b =>
        have hh := curried_wrapP Δ Φ Ψ body ps (g b) (acc ++ [(x, .bool b)]) (h b) vs hvs
        rw [List.append_assoc, List.singleton_append] at hh
        change wrapP (.bool :: ps.map (fun p : String × Ty => p.2)) g (.bool b :: vs) ↔ _
        rw [wrapP_bool]
        exact hh

/-- kernel 検査済みの任意仮引数での同値と実生成定数の lookup から spec 接続証拠を作る。 -/
theorem specConn_of_curried (Δ : SigEnv) (Φ : FEnv) (Ψ : PEnv) (k : String)
    (ps : List (String × Ty)) (body : Core.Expr) (g : PFn (ps.map (·.2)))
    (h : CurriedP Δ Φ Ψ body ps g []) (hΨ : Ψ k = some (wrapP (ps.map (·.2)) g)) :
    SpecConn Δ Φ Ψ k ps body := by
  refine ⟨_, hΨ, ?_⟩
  intro vs hvs
  simpa using curried_wrapP Δ Φ Ψ body ps g [] h vs hvs

end NaruSem.Call
