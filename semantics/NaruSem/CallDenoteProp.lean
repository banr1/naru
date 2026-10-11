import NaruSem.CallDenote
import NaruSem.DenoteProp

/-!
# 呼出しを含む命題の読みと独立意味論の一般同値

型付け署名 `Δ` に従って呼出し先の値/命題を区別し、読みの環境 `Φ'`/`Ψ'` の Lean の値/命題を使う。
Bool の等値と if は常に命題の形で読む。値だけの場合には通常の Bool 等値/if と同値だが、定義的等式ではない。
既定値は不適格な構文の読みを全域にするだけで、独立意味論 `Sem` の定義には使わない。
一般保証は適格な式について任意の対応環境・型に合う任意の実引数で成立する。
-/

namespace NaruSem.Call
open Naru

/-- 2 つの命題環境が署名の鍵で一致する(型に合う実引数で両方向の同値)。 -/
def PEnv.Agree (Ψ Ψ' : PEnv) (Δ : SigEnv) : Prop :=
  ∀ k ps, specSig? Δ k = some ps →
    ∃ F F', Ψ k = some F ∧ Ψ' k = some F' ∧ ∀ vs : List Val, vs.map Val.ty = ps → (F vs ↔ F' vs)

/-- spec 署名の包含。 -/
def SigEnv.SubP (Δ Δ' : SigEnv) : Prop :=
  ∀ k ps, specSig? Δ k = some ps → specSig? Δ' k = some ps

theorem SigEnv.SubP.refl (Δ : SigEnv) : SigEnv.SubP Δ Δ := fun _ _ h => h

theorem PEnv.Defined.mono {Δ Δ' : SigEnv} {Ψ : PEnv} (hΔ : SigEnv.SubP Δ Δ') (h : Ψ.Defined Δ') : Ψ.Defined Δ :=
  fun k ps hk => h k ps (hΔ k ps hk)

theorem PEnv.Agree.refl {Δ : SigEnv} {Ψ : PEnv} (h : Ψ.Defined Δ) : PEnv.Agree Ψ Ψ Δ := by
  intro k ps hk
  obtain ⟨F, hF⟩ := h k ps hk
  exact ⟨F, F, hF, hF, fun _ _ => Iff.rfl⟩

theorem PEnv.Agree.defined {Δ : SigEnv} {Ψ Ψ' : PEnv} (h : PEnv.Agree Ψ Ψ' Δ) : Ψ.Defined Δ := by
  intro k ps hk
  obtain ⟨F, _, hF, _, _⟩ := h k ps hk
  exact ⟨F, hF⟩

mutual


def denoteP (Δ : SigEnv) (Φ : FEnv) (Ψ : PEnv) (ρ : SEnv) : Core.Expr → Prop
  | .lit (.bool true) _ => True
  | .lit (.bool false) _ => False
  | .var x =>
    match ρ x with
    | some (.val (.bool b)) => b = true
    | some (.prop P) => P
    | _ => False
  | .call k args =>
    match specSig? Δ k with
    | some ps => match Ψ k with
      | some F => F (denoteArgs Δ Φ ρ.vals args ps)
      | none => False
    | none => denoteB Δ Φ ρ.vals (.call k args) = true
  | .let_ x ty v b =>
    match ty with
    | .nat => denoteP Δ Φ Ψ (ρ.ext x (.val (.nat (denoteN Δ Φ ρ.vals v)))) b
    | .bool =>
      match proppyS Δ ρ.ctx v with
      | true => denoteP Δ Φ Ψ (ρ.ext x (.prop (denoteP Δ Φ Ψ ρ v))) b
      | false => denoteP Δ Φ Ψ (ρ.ext x (.val (.bool (denoteB Δ Φ ρ.vals v)))) b
    | _ => False
  | .ite c t e => (denoteP Δ Φ Ψ ρ c → denoteP Δ Φ Ψ ρ t) ∧ (¬ denoteP Δ Φ Ψ ρ c → denoteP Δ Φ Ψ ρ e)
  | .binop op l r ty =>
    match BinOp.ofString? op, TyV.toTy? ty with
    | some (.logic k), some .bool => k.prop (denoteP Δ Φ Ψ ρ l) (denoteP Δ Φ Ψ ρ r)
    | some (.eq k), some .nat => k.propNat (denoteN Δ Φ ρ.vals l) (denoteN Δ Φ ρ.vals r)
    | some (.eq k), some .bool =>
      k.propIff (denoteP Δ Φ Ψ ρ l) (denoteP Δ Φ Ψ ρ r)
    | some (.cmp k), some .nat => k.propNat (denoteN Δ Φ ρ.vals l) (denoteN Δ Φ ρ.vals r)
    | some (.cmp k), some .bool => k.leanBoolProp (denoteB Δ Φ ρ.vals l) (denoteB Δ Φ ρ.vals r)
    | _, _ => False
  | .unop op a => if op = "!" then ¬ denoteP Δ Φ Ψ ρ a else False
  | .match_ s st arms =>
    match st with
    | .nat => denoteArmsP Δ Φ Ψ ρ (.nat (denoteN Δ Φ ρ.vals s)) arms
    | .bool => denoteArmsP Δ Φ Ψ ρ (.bool (denoteB Δ Φ ρ.vals s)) arms
    | _ => False
  | .quant q bs b => denoteQuant q ρ bs (fun ρ' => denoteP Δ Φ Ψ ρ' b)
  | _ => False


def denoteArmsP (Δ : SigEnv) (Φ : FEnv) (Ψ : PEnv) (ρ : SEnv) (v : Val) : List Core.Arm → Prop
  | [] => False
  | .mk p none b :: rest =>
    match matchPat p v with
    | some bs => denoteP Δ Φ Ψ (ρ.extVals bs) b
    | none => denoteArmsP Δ Φ Ψ ρ v rest
  | .mk p (some g) b :: rest =>
    (match matchPat p v with
     | some bs => denoteP Δ Φ Ψ (ρ.extVals bs) g → denoteP Δ Φ Ψ (ρ.extVals bs) b
     | none => True) ∧
    (¬ (match matchPat p v with
        | some bs => denoteP Δ Φ Ψ (ρ.extVals bs) g
        | none => False) →
      denoteArmsP Δ Φ Ψ ρ v rest)

end

def wtSNoExh (Δ : SigEnv) (Γ : SCtx) : Core.Expr → Option STy
  | .match_ s st arms =>
    match wtR Δ Γ.vals s, TyV.toTy? st with
    | some ts, some ta => if ts = ta then wtArmsS Δ Γ ts arms else none
    | _, _ => none
  | .quant _ bs b =>
    match Γ.extBinders bs with
    | some Γ' =>
      match wtS Δ Γ' b with
      | some t => if t.isForm then some .prop else none
      | none => none
    | none => none
  | e => wtS Δ Γ e

theorem wtS_noExh {Δ : SigEnv} {Γ : SCtx} {e : Core.Expr} {τ : STy} (h : wtS Δ Γ e = some τ) : wtSNoExh Δ Γ e = some τ := by
  cases e with
  | match_ s st arms =>
    simp only [wtS] at h
    simp only [wtSNoExh]
    cases hs : wtR Δ Γ.vals s with
    | none => simp [hs] at h
    | some ts =>
      cases hta : TyV.toTy? st with
      | none => simp [hs, hta] at h
      | some ta =>
        simp only [hs, hta] at h ⊢
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨hts, _⟩ := hc
          subst hts
          simp [h]
        · cases h
  | quant q bs b =>
    simp only [wtS] at h
    simp only [wtSNoExh]
    cases bs with
    | nil => cases h
    | cons xt rest => exact h
  | _ => exact h


theorem wtArmsS_head {Δ : SigEnv} {Γ : SCtx} {ts : Ty} {arm : Core.Arm} {rest : List Core.Arm} {τ : STy}
    (h : wtArmsS Δ Γ ts (arm :: rest) = some τ) : ∃ t1, wtArmS Δ Γ ts arm = some t1 := by
  rw [wtArmsS.eq_def] at h
  cases h1 : wtArmS Δ Γ ts arm with
  | none => simp [h1] at h
  | some t1 => exact ⟨t1, rfl⟩


theorem wtArmsS_tail {Δ : SigEnv} {Γ : SCtx} {ts : Ty} {arm a2 : Core.Arm} {rest : List Core.Arm} {τ : STy}
    (h : wtArmsS Δ Γ ts (arm :: a2 :: rest) = some τ) : ∃ t2, wtArmsS Δ Γ ts (a2 :: rest) = some t2 := by
  rw [wtArmsS.eq_def] at h
  cases h1 : wtArmS Δ Γ ts arm with
  | none => simp [h1] at h
  | some t1 =>
    simp only [h1] at h
    cases h2 : wtArmsS Δ Γ ts (a2 :: rest) with
    | none => simp [h2] at h
    | some t2 => exact ⟨t2, rfl⟩

theorem Sem_denote_all {Δ : SigEnv} {Φ Φ' : FEnv} {Ψ Ψ' : PEnv}
    (hΦ' : Φ'.Respects Δ) (hA : FEnv.Agree Φ Φ' Δ) (hPA : PEnv.Agree Ψ Ψ' Δ)
    {ρ : SEnv} {e : Core.Expr} {P : Prop} (h : Sem Δ Φ Ψ ρ e P) :
    ∀ τ, wtSNoExh Δ ρ.ctx e = some τ → (P ↔ denoteP Δ Φ' Ψ' ρ e) := by
  induction h with
  | @lit ρ b =>
    intro τ _
    cases b <;> simp [denoteP]
  | @varVal ρ x b h =>
    intro τ _
    simp [denoteP, h]
  | @varProp ρ x P h =>
    intro τ _
    simp [denoteP, h]
  | @callVal ρ k args f vs b hk hf ha hv =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.call k args) = some τ := hw
    cases hsig : Δ k with
    | none => simp [wtS, hsig] at hw
    | some sig =>
      cases sig with
      | spec ps => simp [isValueKey, valueSig?, hsig, Sig.value?] at hk
      | fn ps t | input ps t =>
        have hargs : wtArgs Δ ρ.ctx.vals args ps = true := by
          simp only [wtS, hsig] at hw
          split at hw
          · assumption
          · cases hw
        obtain ⟨hea, hty⟩ := (denote_sound_all Δ Δ Φ Φ' (SigEnv.SubV.refl Δ) hΦ' hA).2.2.2
          ρ.ctx.vals args ps ρ.vals (SEnv.ctx_vals ρ) hargs
        rw [ha] at hea
        cases hea
        have hval : valueSig? Δ k = some (ps, t) := by simp [valueSig?, hsig, Sig.value?]
        obtain ⟨f₀, f', hf₀, hf', hag⟩ := hA k ps t hval
        rw [hf] at hf₀
        cases hf₀
        have hv' : f' (denoteArgs Δ Φ' ρ.vals args ps) = some (.bool b) := by
          rw [← hag _ hty]
          exact hv
        simp [denoteP, specSig?, hsig, Sig.spec?, denoteB, hval, hf', hv']
  | @callSpec ρ k args F vs hk hF ha =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.call k args) = some τ := hw
    cases hsig : Δ k with
    | none => simp [wtS, hsig] at hw
    | some sig =>
      cases sig with
      | fn ps t | input ps t => simp [isSpecKey, specSig?, hsig, Sig.spec?] at hk
      | spec ps =>
        have hargs : wtArgs Δ ρ.ctx.vals args ps = true := by
          simp only [wtS, hsig] at hw
          split at hw
          · assumption
          · cases hw
        obtain ⟨hea, hty⟩ := (denote_sound_all Δ Δ Φ Φ' (SigEnv.SubV.refl Δ) hΦ' hA).2.2.2
          ρ.ctx.vals args ps ρ.vals (SEnv.ctx_vals ρ) hargs
        rw [ha] at hea
        cases hea
        have hspec : specSig? Δ k = some ps := specSig?_spec hsig
        obtain ⟨F₀, F', hF₀, hF', hag⟩ := hPA k ps hspec
        rw [hF] at hF₀
        cases hF₀
        simp only [denoteP, hspec, hF']
        exact hag _ hty
  | @logic ρ op k l r P Q hk hl hr ihl ihr =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.binop op l r .bool) = some τ := hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtS Δ ρ.ctx l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtS Δ ρ.ctx r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        have el := ihl tl (wtS_noExh hwl)
        have er := ihr tr (wtS_noExh hwr)
        simp only [denoteP, hk, TyV.toTy?]
        cases k <;> simp [LogicOp.prop, el, er]
  | @eqNat ρ op k l r a b hk hl hr =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.binop op l r .nat) = some τ := hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtR Δ ρ.ctx.vals l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtR Δ ρ.ctx.vals r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        cases tl <;> cases tr <;> simp [hwl, hwr] at hw
        have pl := preserve_nat (SigEnv.SubV.refl Δ) hΦ' hA hwl ρ.vals (SEnv.ctx_vals ρ)
        have pr := preserve_nat (SigEnv.SubV.refl Δ) hΦ' hA hwr ρ.vals (SEnv.ctx_vals ρ)
        rw [hl] at pl
        rw [hr] at pr
        cases pl
        cases pr
        simp [denoteP, hk, TyV.toTy?]
  | @eqForm ρ op k l r P Q hk hl hr ihl ihr =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.binop op l r .bool) = some τ := hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtS Δ ρ.ctx l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtS Δ ρ.ctx r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        have el := ihl tl (wtS_noExh hwl)
        have er := ihr tr (wtS_noExh hwr)
        simp only [denoteP, hk, TyV.toTy?]
        rw [propext el, propext er]
  | @cmpNat ρ op k l r a b hk hl hr =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.binop op l r .nat) = some τ := hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtR Δ ρ.ctx.vals l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtR Δ ρ.ctx.vals r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        cases tl <;> cases tr <;> simp [hwl, hwr] at hw
        have pl := preserve_nat (SigEnv.SubV.refl Δ) hΦ' hA hwl ρ.vals (SEnv.ctx_vals ρ)
        have pr := preserve_nat (SigEnv.SubV.refl Δ) hΦ' hA hwr ρ.vals (SEnv.ctx_vals ρ)
        rw [hl] at pl
        rw [hr] at pr
        cases pl
        cases pr
        simp [denoteP, hk, TyV.toTy?]
  | @cmpBool ρ op k l r a b hk hl hr =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.binop op l r .bool) = some τ := hw
    simp only [wtS, hk, TyV.toTy?] at hw
    cases hwl : wtR Δ ρ.ctx.vals l with
    | none => simp [hwl] at hw
    | some tl =>
      cases hwr : wtR Δ ρ.ctx.vals r with
      | none => simp [hwl, hwr] at hw
      | some tr =>
        cases tl <;> cases tr <;> simp [hwl, hwr] at hw
        have pl := preserve_bool (SigEnv.SubV.refl Δ) hΦ' hA hwl ρ.vals (SEnv.ctx_vals ρ)
        have pr := preserve_bool (SigEnv.SubV.refl Δ) hΦ' hA hwr ρ.vals (SEnv.ctx_vals ρ)
        rw [hl] at pl
        rw [hr] at pr
        cases pl
        cases pr
        simp only [denoteP, hk, TyV.toTy?]
        exact (CmpOp.leanBoolProp_iff k _ _).symm
  | @not ρ a P h ih =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.unop "!" a) = some τ := hw
    simp only [wtS, ite_true] at hw
    cases hwa : wtS Δ ρ.ctx a with
    | none => simp [hwa] at hw
    | some ta =>
      have ea := ih ta (wtS_noExh hwa)
      simp only [denoteP, ite_true]
      rw [propext ea]
  | @ite ρ c t e C P Q hc ht he ihc iht ihe =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.ite c t e) = some τ := hw
    simp only [wtS] at hw
    cases hwc : wtS Δ ρ.ctx c with
    | none => simp [hwc] at hw
    | some tc =>
      cases hwt : wtS Δ ρ.ctx t with
      | none => simp [hwc, hwt] at hw
      | some tt =>
        cases hwe : wtS Δ ρ.ctx e with
        | none => simp [hwc, hwt, hwe] at hw
        | some te =>
          have ec := ihc tc (wtS_noExh hwc)
          have et := iht tt (wtS_noExh hwt)
          have ee := ihe te (wtS_noExh hwe)
          simp only [denoteP]
          rw [propext ec, propext et, propext ee]
  | @letNat ρ x v b n Q hv hb ihb =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.let_ x .nat v b) = some τ := hw
    simp only [wtS, TyV.toTy?] at hw
    cases hwv : wtR Δ ρ.ctx.vals v with
    | none => simp [hwv] at hw
    | some tv =>
      cases tv with
      | bool => simp [hwv] at hw
      | nat =>
        simp only [hwv] at hw
        have pv := preserve_nat (SigEnv.SubV.refl Δ) hΦ' hA hwv ρ.vals (SEnv.ctx_vals ρ)
        rw [hv] at pv
        cases pv
        have hΓ' : (ρ.ext x (.val (.nat (denoteN Δ Φ' ρ.vals v)))).ctx = ρ.ctx.ext x (.val .nat) := by
          rw [SEnv.ctx_ext]
          rfl
        have := ihb τ (by rw [hΓ']; exact wtS_noExh hw)
        simpa [denoteP] using this
  | @letBoolVal ρ x v b w Q hp hv hb ihb =>
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.let_ x .bool v b) = some τ := hw
    simp only [wtS, TyV.toTy?, hp, Bool.false_eq_true, ite_false] at hw
    cases hwv : wtR Δ ρ.ctx.vals v with
    | none => simp [hwv] at hw
    | some tv =>
      cases tv with
      | nat => simp [hwv] at hw
      | bool =>
        simp only [hwv] at hw
        have pv := preserve_bool (SigEnv.SubV.refl Δ) hΦ' hA hwv ρ.vals (SEnv.ctx_vals ρ)
        rw [hv] at pv
        cases pv
        have hΓ' : (ρ.ext x (.val (.bool (denoteB Δ Φ' ρ.vals v)))).ctx = ρ.ctx.ext x (.val .bool) := by
          rw [SEnv.ctx_ext]
          rfl
        have := ihb τ (by rw [hΓ']; exact wtS_noExh hw)
        simpa [denoteP, hp] using this
  | @letProp ρ x v b P Q hp hv hb ihv ihb =>
    -- 命題の `let`: 値の意味 `P` と読み `denoteP Δ Φ' Ψ' ρ v` は同値 → 命題外延性で環境を揃える
    intro τ hw
    replace hw : wtS Δ ρ.ctx (.let_ x .bool v b) = some τ := hw
    simp only [wtS, TyV.toTy?, hp, ite_true] at hw
    cases hwv : wtS Δ ρ.ctx v with
    | none => simp [hwv] at hw
    | some tv =>
      cases tv with
      | val t => simp [hwv] at hw
      | prop =>
        simp only [hwv] at hw
        have ev := ihv .prop (wtS_noExh hwv)
        have hΓ' : (ρ.ext x (.prop P)).ctx = ρ.ctx.ext x .prop := by
          rw [SEnv.ctx_ext]
          rfl
        have eb := ihb τ (by rw [hΓ']; exact wtS_noExh hw)
        simp only [denoteP, hp]
        rw [propext ev] at eb
        exact eb
  | @matchSkip ρ s st p g b rest v P hs hp hr ihr =>
    -- 先頭の腕が一致しない: 残りの腕(外側の環境)。残りは単独では網羅的でなくてよい(`wtSNoExh`)
    intro τ hw
    simp only [wtSNoExh] at hw
    cases hws : wtR Δ ρ.ctx.vals s with
    | none => simp [hws] at hw
    | some ts =>
      cases hst : TyV.toTy? st with
      | none => simp [hws, hst] at hw
      | some ta =>
        simp only [hws, hst] at hw
        split at hw
        · rename_i hts
          subst hts
          cases rest with
          | nil => cases hr
          | cons a2 rest2 =>
            obtain ⟨t2, hw2⟩ := wtArmsS_tail hw
            have er := ihr t2 (by simp [wtSNoExh, hws, hst, hw2])
            have pv := denote_sound (SigEnv.SubV.refl Δ) hΦ' hA hws ρ.vals (SEnv.ctx_vals ρ)
            rw [hs] at pv
            cases pv
            rw [er]
            cases ts <;> cases st <;> simp [TyV.toTy?] at hst
            all_goals
              simp only [denoteP]
              simp only [denoteV] at hp
              cases g <;> first
                | (rw [denoteArmsP.eq_2]; simp [hp])
                | (rw [denoteArmsP.eq_3]; simp [hp])
        · cases hw
  | @matchHit ρ s st p b rest v bs P hs hp hb ihb =>
    -- ガード無しの腕が一致: 束縛を足した環境で本体
    intro τ hw
    simp only [wtSNoExh] at hw
    cases hws : wtR Δ ρ.ctx.vals s with
    | none => simp [hws] at hw
    | some ts =>
      cases hst : TyV.toTy? st with
      | none => simp [hws, hst] at hw
      | some ta =>
        simp only [hws, hst] at hw
        split at hw
        · rename_i hts
          subst hts
          obtain ⟨t1, hw1⟩ := wtArmsS_head hw
          rw [wtArmS_mk] at hw1
          cases hpat : wtPat ts p with
          | none => simp [hpat] at hw1
          | some bts =>
            simp only [hpat] at hw1
            cases hwb : wtS Δ (ρ.ctx.extVals bts) b with
            | none => simp [hwb] at hw1
            | some tb =>
              have pv := denote_sound (SigEnv.SubV.refl Δ) hΦ' hA hws ρ.vals (SEnv.ctx_vals ρ)
              rw [hs] at pv
              cases pv
              have hv : (denoteV Δ Φ' ρ.vals ts s).ty = ts := denoteV_ty Δ Φ' ρ.vals ts s
              have hΓ' : (ρ.extVals bs).ctx = ρ.ctx.extVals bts := by
                rw [SEnv.ctx_extVals, matchPat_types hpat hv hp]
              have eb := ihb tb (by rw [hΓ']; exact wtS_noExh hwb)
              rw [eb]
              cases ts <;> cases st <;> simp [TyV.toTy?] at hst
              all_goals
                simp only [denoteP]
                simp only [denoteV] at hp
                rw [denoteArmsP.eq_2]
                simp [hp]
        · cases hw
  | @matchGuard ρ s st p g b rest v bs G P R hs hp hg hb hr ihg ihb ihr =>
    -- ガード付きの腕が一致: `(G → B) ∧ (¬ G → R)`。ガードと本体は束縛を足した環境、残りの腕は外側の環境
    intro τ hw
    simp only [wtSNoExh] at hw
    cases hws : wtR Δ ρ.ctx.vals s with
    | none => simp [hws] at hw
    | some ts =>
      cases hst : TyV.toTy? st with
      | none => simp [hws, hst] at hw
      | some ta =>
        simp only [hws, hst] at hw
        split at hw
        · rename_i hts
          subst hts
          obtain ⟨t1, hw1⟩ := wtArmsS_head hw
          rw [wtArmS_mk] at hw1
          cases hpat : wtPat ts p with
          | none => simp [hpat] at hw1
          | some bts =>
            simp only [hpat] at hw1
            cases hwg : wtS Δ (ρ.ctx.extVals bts) g with
            | none => simp [hwg] at hw1
            | some tg =>
              cases hwb : wtS Δ (ρ.ctx.extVals bts) b with
              | none => simp [hwg, hwb] at hw1
              | some tb =>
                cases rest with
                | nil => cases hr
                | cons a2 rest2 =>
                  obtain ⟨t2, hw2⟩ := wtArmsS_tail hw
                  have er := ihr t2 (by simp [wtSNoExh, hws, hst, hw2])
                  have pv := denote_sound (SigEnv.SubV.refl Δ) hΦ' hA hws ρ.vals (SEnv.ctx_vals ρ)
                  rw [hs] at pv
                  cases pv
                  have hv : (denoteV Δ Φ' ρ.vals ts s).ty = ts := denoteV_ty Δ Φ' ρ.vals ts s
                  have hΓ' : (ρ.extVals bs).ctx = ρ.ctx.extVals bts := by
                    rw [SEnv.ctx_extVals, matchPat_types hpat hv hp]
                  have eg := ihg tg (by rw [hΓ']; exact wtS_noExh hwg)
                  have eb := ihb tb (by rw [hΓ']; exact wtS_noExh hwb)
                  rw [propext eg, propext eb, propext er]
                  cases ts <;> cases st <;> simp [TyV.toTy?] at hst
                  all_goals
                    simp only [denoteP]
                    simp only [denoteV] at hp
                    rw [denoteArmsP.eq_3]
                    simp [hp]
        · cases hw
  | @quantNil ρ q b P h ih =>
    intro τ hw
    simp only [wtSNoExh, SCtx.extBinders] at hw
    cases hwb : wtS Δ ρ.ctx b with
    | none => simp [hwb] at hw
    | some t =>
      have := ih t (wtS_noExh hwb)
      simpa [denoteP, denoteQuant] using this
  | @forallCons ρ x tv t bs b F ht h ih =>
    -- `T` の全要素 `a` について、束縛を足した環境での同値を `∀` で束ねる
    intro τ hw
    simp only [wtSNoExh, SCtx.extBinders, ht] at hw
    have hw' : ∀ a : t.carrier, wtSNoExh Δ (ρ.ext x (.val (Val.of t a))).ctx (.quant .forall_ bs b) = some τ := by
      intro a
      rw [SEnv.ctx_ext]
      simp only [SVal.ty, Val.ty_of]
      simp only [wtSNoExh]
      exact hw
    simp only [denoteP, denoteQuant, ht]
    exact forall_congr' fun a => (ih a τ (hw' a)).trans (by simp only [denoteP])
  | @existsCons ρ x tv t bs b F ht h ih =>
    intro τ hw
    simp only [wtSNoExh, SCtx.extBinders, ht] at hw
    have hw' : ∀ a : t.carrier, wtSNoExh Δ (ρ.ext x (.val (Val.of t a))).ctx (.quant .exists_ bs b) = some τ := by
      intro a
      rw [SEnv.ctx_ext]
      simp only [SVal.ty, Val.ty_of]
      simp only [wtSNoExh]
      exact hw
    simp only [denoteP, denoteQuant, ht]
    exact exists_congr fun a => (ih a τ (hw' a)).trans (by simp only [denoteP])

/-- 適格式の独立意味論は、署名の鍵で値/命題が対応する読みと両方向に同値。
大きい署名 `Δ'` を守る読みの関数環境は包含で型付け署名 `Δ` も守る。
読みは `Δ` の分類で構成するため、無関係な追加鍵の意味に仮定を置かない。 -/
theorem Sem_denote {Δ Δ' : SigEnv} {Φ Φ' : FEnv} {Ψ Ψ' : PEnv}
    (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ')
    (hA : FEnv.Agree Φ Φ' Δ) (hPA : PEnv.Agree Ψ Ψ' Δ)
    {Γ : SCtx} {e : Core.Expr} {τ : STy} (hw : wtS Δ Γ e = some τ)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) {P : Prop} (h : Sem Δ Φ Ψ ρ e P) :
    P ↔ denoteP Δ Φ' Ψ' ρ e :=
  Sem_denote_all (FEnv.Respects.mono hΔ hΦ') hA hPA h τ (wtS_noExh (hρ ▸ hw))

/-- 読み自体が独立意味論の命題となる(存在 + 同値 + 命題外延性)。 -/
theorem Sem_denoteP {Δ Δ' : SigEnv} {Φ Φ' : FEnv} {Ψ Ψ' : PEnv}
    (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ')
    (hA : FEnv.Agree Φ Φ' Δ) (hPA : PEnv.Agree Ψ Ψ' Δ)
    {Γ : SCtx} {e : Core.Expr} {τ : STy} (hw : wtS Δ Γ e = some τ) (hf : τ.isForm = true)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) : Sem Δ Φ Ψ ρ e (denoteP Δ Φ' Ψ' ρ e) := by
  obtain ⟨P, hP⟩ := Sem_exists hw hf Φ Ψ ρ hρ (FEnv.Agree.respects hΔ hΦ' hA) (PEnv.Agree.defined hPA)
  rw [propext (Sem_denote hΔ hΦ' hA hPA hw ρ hρ hP)] at hP
  exact hP

/-- 同じ環境での一般同値。 -/
theorem Sem_denote_self {Δ : SigEnv} {Φ : FEnv} {Ψ : PEnv}
    (hΦ : Φ.Respects Δ) (hΨ : Ψ.Defined Δ)
    {Γ : SCtx} {e : Core.Expr} {τ : STy} (hw : wtS Δ Γ e = some τ)
    (ρ : SEnv) (hρ : Γ = ρ.ctx) {P : Prop} (h : Sem Δ Φ Ψ ρ e P) :
    P ↔ denoteP Δ Φ Ψ ρ e :=
  Sem_denote (SigEnv.SubV.refl Δ) hΦ (FEnv.Agree.refl hΦ) (PEnv.Agree.refl hΨ) hw ρ hρ h

/-- 実生成命題 `Q` と読みの同値を接続検査したとき、`Q` は独立意味論の意味そのもの。
Bool の if/等値は命題形と定義的に異なりうるため、接続は等式より一般の同値を受け取る。 -/
theorem check_sound_prop {Δ Δ' : SigEnv} {Φ Φ' : FEnv} {Ψ Ψ' : PEnv}
    (hΔ : SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ')
    (hA : FEnv.Agree Φ Φ' Δ) (hPA : PEnv.Agree Ψ Ψ' Δ)
    (xs : List (String × Val)) {e : Core.Expr} {τ : STy}
    (hw : wtS Δ (SCtx.ofList (xs.map fun p => (p.1, STy.val p.2.ty))) e = some τ) (hf : τ.isForm = true)
    {Q : Prop} (hq : Q ↔ denoteP Δ Φ' Ψ' (SEnv.ofList (xs.map fun p => (p.1, SVal.val p.2))) e) :
    Sem Δ Φ Ψ (SEnv.ofList (xs.map fun p => (p.1, SVal.val p.2))) e Q := by
  rw [propext hq]
  apply Sem_denoteP hΔ hΦ' hA hPA hw hf
  rw [SEnv.ctx_ofList, List.map_map]
  rfl

end NaruSem.Call
