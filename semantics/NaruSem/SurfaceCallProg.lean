import NaruSem.SurfaceCallLowerSpecSemAll
import NaruSem.SurfaceCallLowerSound
import NaruSem.CallComposeProp

/-!
# Surface / Core の宣言群の意味の対応と、Surface から実生成 Statements への合成(IDEAL.md C55 / C57、用語「関数・input の保存対象」)

Surface AST の宣言群 `Surf.Call.Prog` と Core の宣言群 `Call.Prog` が **宣言ごとに対応**している
(`DeclLower`: 鍵・署名(仮引数の名前と型・戻り型)が同じで、fn / spec 宣言の本体はその宣言より前の宣言の表
での独立 lowering `Surf.Call.lower` / `lowerS` の実出力、input は本体なし。`ProgLower` はその列)とき、
同じ input の解釈 `I` の下の宣言群の意味 `Surf.Call.interp I P` と `Call.interp I C` は、callee 環境
`Φ`(fn の意味と input の解釈)が署名の鍵で一致し(`FEnv.Agree`)、spec 宣言の環境 `Ψ` が型の合う任意の
実引数で双方向に同値(`PEnv.Agree`)である(`interp_lower_agree`)。証明は宣言群の帰納法: fn の段は
runtime の一般評価保存 `lower_eval_agree`、spec 宣言の段は spec の一般双方向同値 `lowerS_sem_iff` を
読み `Call.denoteP` を経由して(`lowerS_denote` / `lowerS_denoteP` と `Call.Sem_denote_self` / `Sem_denoteP`)
それまでの対応に合成する。input の段は同じ解釈 `I` をそのまま運ぶ。翻訳の正しさや呼出し先の正しさは仮定しない。

`spec_sem_denote` は、既存の Core → 実生成 Lean の対応(`Call.interp_agree` / `interp_prop_agree` の結論
`FEnv.Agree (Call.interp I C).Φ Φ' Δ` / `PEnv.Agree (Call.interp I C).Ψ Ψ' Δ`)とこの対応を推移で結び、
Surface の宣言群の意味の下での spec 本体の意味が、実生成環境での読み `Call.denoteP` と同値であること
(読み自体が意味であること、任意の意味が読みと同値であること)を与える。検査プログラムはこれに各 spec の
実生成 Statements 宣言と読みの接続(`read_*`)を合わせ、Surface AST → 実生成 Statements 宣言の同値証拠を書く。

`Δ_take_eq` は、対応する宣言群の prefix の表の署名が Core 側の prefix の署名(`SigEnv.ext` の畳み込み)と
等しいことを与える(検査プログラムの `Δprefix_*` との結び)。`Δ_take_sub` は prefix の表の署名が
宣言群全体の表の署名に含まれることを与える。
-/

namespace NaruSem.Call
open Naru

/-- fn / input の署名の包含の推移。 -/
theorem SigEnv.SubV.trans {Δ₁ Δ₂ Δ₃ : SigEnv} (h₁ : SigEnv.SubV Δ₁ Δ₂) (h₂ : SigEnv.SubV Δ₂ Δ₃) : SigEnv.SubV Δ₁ Δ₃ :=
  fun k ps t hk => h₂ k ps t (h₁ k ps t hk)

/-- spec 宣言の署名の包含の推移。 -/
theorem SigEnv.SubP.trans {Δ₁ Δ₂ Δ₃ : SigEnv} (h₁ : SigEnv.SubP Δ₁ Δ₂) (h₂ : SigEnv.SubP Δ₂ Δ₃) : SigEnv.SubP Δ₁ Δ₃ :=
  fun k ps hk => h₂ k ps (h₁ k ps hk)

/-- 関数環境の署名の鍵での一致の推移。 -/
theorem FEnv.Agree.trans {Φ₁ Φ₂ Φ₃ : FEnv} {Δ : SigEnv} (h₁ : FEnv.Agree Φ₁ Φ₂ Δ) (h₂ : FEnv.Agree Φ₂ Φ₃ Δ) :
    FEnv.Agree Φ₁ Φ₃ Δ := by
  intro k ps t hk
  obtain ⟨f₁, f₂, hf₁, hf₂, h12⟩ := h₁ k ps t hk
  obtain ⟨f₂', f₃, hf₂', hf₃, h23⟩ := h₂ k ps t hk
  rw [hf₂] at hf₂'
  cases hf₂'
  exact ⟨f₁, f₃, hf₁, hf₃, fun vs hvs => (h12 vs hvs).trans (h23 vs hvs)⟩

/-- 小さい署名でも一致する。 -/
theorem FEnv.Agree.mono {Φ Φ' : FEnv} {Δ Δ' : SigEnv} (hΔ : SigEnv.SubV Δ Δ') (h : FEnv.Agree Φ Φ' Δ') : FEnv.Agree Φ Φ' Δ :=
  fun k ps t hk => h k ps t (hΔ k ps t hk)

/-- 命題環境の署名の鍵での一致の推移。 -/
theorem PEnv.Agree.trans {Ψ₁ Ψ₂ Ψ₃ : PEnv} {Δ : SigEnv} (h₁ : PEnv.Agree Ψ₁ Ψ₂ Δ) (h₂ : PEnv.Agree Ψ₂ Ψ₃ Δ) :
    PEnv.Agree Ψ₁ Ψ₃ Δ := by
  intro k ps hk
  obtain ⟨F₁, F₂, hF₁, hF₂, h12⟩ := h₁ k ps hk
  obtain ⟨F₂', F₃, hF₂', hF₃, h23⟩ := h₂ k ps hk
  rw [hF₂] at hF₂'
  cases hF₂'
  exact ⟨F₁, F₃, hF₁, hF₃, fun vs hvs => (h12 vs hvs).trans (h23 vs hvs)⟩

/-- 小さい署名でも一致する。 -/
theorem PEnv.Agree.mono {Ψ Ψ' : PEnv} {Δ Δ' : SigEnv} (hΔ : SigEnv.SubP Δ Δ') (h : PEnv.Agree Ψ Ψ' Δ') : PEnv.Agree Ψ Ψ' Δ :=
  fun k ps hk => h k ps (hΔ k ps hk)

/-- spec 宣言の意味(Core): 実引数を束ねた環境での本体の意味。 -/
theorem Interp.step_Ψ_spec (m : Interp) (k : String) (ps : List (String × Ty)) (body : Core.Expr) :
    (m.step (.spec k ps body)).Ψ k =
      some fun vs => ∃ ρ, bindParams ps vs = some ρ ∧ ∃ P, Sem m.Δ m.Φ m.Ψ (Env.toSEnv ρ) body P ∧ P := by
  simp [Interp.step, PEnv.ext]

/-- 適格な宣言群の署名は、宣言の署名を順に足した畳み込み。 -/
theorem wtProg_foldl : ∀ (P : Prog) (Δ₀ Δ : SigEnv), wtProg Δ₀ P = some Δ → Δ = P.foldl (fun Δ d => Δ.ext d.key d.sig) Δ₀
  | [], _, _, h => by
    simp only [wtProg, Option.some.injEq] at h
    subst h
    rfl
  | d :: rest, Δ₀, Δ, h => by
    obtain ⟨_, _, hrest⟩ := wtProg_cons h
    simp only [List.foldl_cons]
    exact wtProg_foldl rest _ Δ hrest

end NaruSem.Call

namespace NaruSem

/-- 値だけを束ねた環境の値の部分は、値の環境。 -/
theorem SEnv.vals_ofList (xs : List (String × Val)) :
    (SEnv.ofList (xs.map fun (x, v) => (x, SVal.val v))).vals = Env.ofList xs := by
  show (SEnv.empty.extVals xs).vals = Env.empty.extList xs
  rw [SEnv.vals_extVals]
  rfl

end NaruSem

namespace NaruSem.Surf.Call
open Naru

/-! ## 宣言の対応 -/

/-- Surface の宣言と Core の宣言の対応(表 `T` = その宣言より前の宣言の表): 鍵と署名(仮引数の名前と型・戻り型)が同じで、
fn の本体は `lower`、spec 宣言の本体は `lowerS` の(表と仮引数の文脈での)独立 lowering の実出力、input は本体なし。 -/
def DeclLower (T : Table) (sd : Decl) : NaruSem.Call.Decl → Prop
  | .fn k ps t body => sd.key = k ∧ sd.sig? = some (.fn ps t) ∧ ∃ b, sd.body = some b ∧ lower T (NaruSem.Call.paramSCtx ps) b = some body
  | .spec k ps body => sd.key = k ∧ sd.sig? = some (.spec ps) ∧ ∃ b, sd.body = some b ∧ lowerS T (NaruSem.Call.paramSCtx ps) b = some body
  | .input k ps t => sd.key = k ∧ sd.sig? = some (.input ps t) ∧ sd.body = none

theorem DeclLower.key {T : Table} {sd : Decl} {cd : NaruSem.Call.Decl} (h : DeclLower T sd cd) : sd.key = cd.key := by
  cases cd <;> exact h.1

theorem DeclLower.sig {T : Table} {sd : Decl} {cd : NaruSem.Call.Decl} (h : DeclLower T sd cd) :
    (sd.sig?).map DeclSig.toSig = some cd.sig := by
  cases cd with
  | fn k ps t body => rw [h.2.1]; rfl
  | spec k ps body => rw [h.2.1]; rfl
  | input k ps t => rw [h.2.1]; rfl

theorem DeclLower.sig_isSome {T : Table} {sd : Decl} {cd : NaruSem.Call.Decl} (h : DeclLower T sd cd) : (sd.sig?).isSome = true := by
  cases cd <;> simp [h.2.1]

/-- 宣言群の対応(`seen` = それより前の Surface の宣言。各宣言の表は `tableOf all seen`)。 -/
inductive ProgLowerFrom (all : Prog) : Prog → Prog → NaruSem.Call.Prog → Prop
  | nil (seen : Prog) : ProgLowerFrom all seen [] []
  | cons {seen : Prog} {sd : Decl} {srest : Prog} {cd : NaruSem.Call.Decl} {crest : NaruSem.Call.Prog}
      (h : DeclLower (tableOf all seen) sd cd) (rest : ProgLowerFrom all (seen ++ [sd]) srest crest) :
      ProgLowerFrom all seen (sd :: srest) (cd :: crest)

/-- 宣言群全体の対応(各宣言の本体はその宣言より前の宣言の表で lowering する)。 -/
abbrev ProgLower (P : Prog) (C : NaruSem.Call.Prog) : Prop := ProgLowerFrom P [] P C

/-- 対応する宣言群は同じ長さ。 -/
theorem ProgLowerFrom.length {all seen srest : Prog} {crest : NaruSem.Call.Prog} (hl : ProgLowerFrom all seen srest crest) :
    srest.length = crest.length := by
  induction hl with
  | nil _ => rfl
  | cons _ _ ih => simp [ih]

/-! ## 表の署名と Core の署名の対応 -/

theorem tableOf_nil_Δ (all : Prog) : (tableOf all []).Δ = NaruSem.Call.SigEnv.empty := by
  funext k
  simp [Table.Δ, tableOf, sigsOf, NaruSem.Call.SigEnv.empty]

/-- 対応する宣言を 1 つ足した表の署名は、Core の署名で伸ばしたもの。 -/
theorem Δ_step_of_lower {all seen : Prog} {sd : Decl} {cd : NaruSem.Call.Decl} (hall : AllSig seen)
    (hfresh : sigsOf seen sd.key = none) (hdl : DeclLower (tableOf all seen) sd cd) :
    (tableOf all (seen ++ [sd])).Δ = (tableOf all seen).Δ.ext cd.key cd.sig := by
  funext k
  by_cases hk : k = cd.key
  · subst hk
    rw [NaruSem.Call.SigEnv.ext_self, ← hdl.key, Δ_append_self hall hfresh, hdl.sig]
  · rw [NaruSem.Call.SigEnv.ext_ne _ _ _ hk, Δ_append_ne all seen sd (fun he => hk (he.trans hdl.key))]

/-- 対応する宣言群の prefix の表の署名は、Core の prefix の署名の畳み込み。 -/
theorem Δ_take_of_lower (all : Prog) {seen srest : Prog} {crest : NaruSem.Call.Prog}
    (hl : ProgLowerFrom all seen srest crest) :
    ∀ (Δ₀ : NaruSem.Call.SigEnv), AllSig seen → wtProgFrom all seen srest = true → (tableOf all seen).Δ = Δ₀ →
      ∀ i, (tableOf all (seen ++ srest.take i)).Δ = (crest.take i).foldl (fun Δ d => Δ.ext d.key d.sig) Δ₀ := by
  induction hl with
  | nil seen =>
    intro Δ₀ _ _ hΔ i
    simp [hΔ]
  | @cons seen sd srest cd crest hdl _ ih =>
    intro Δ₀ hall h hΔ i
    obtain ⟨hfresh, _, _, hrest⟩ := wtProgFrom_cons h
    cases i with
    | zero => simp [hΔ]
    | succ i =>
      have := ih (Δ₀.ext cd.key cd.sig) (hall.append hdl.sig_isSome) hrest
        (by rw [Δ_step_of_lower hall hfresh hdl, hΔ]) i
      simpa [List.take_succ_cons, List.append_assoc] using this

/-- **宣言群の prefix の署名の一致**: 対応する宣言群について、Surface の prefix の表の署名は Core の prefix の署名
(検査プログラムの `prefix_call` の形)に等しい。 -/
theorem Δ_take_eq {P : Prog} {C : NaruSem.Call.Prog} (hP : wtProg P = true) (hl : ProgLower P C) (i : Nat) :
    (tableOf P (P.take i)).Δ = (C.take i).foldl (fun Δ d => Δ.ext d.key d.sig) NaruSem.Call.SigEnv.empty := by
  have := Δ_take_of_lower P hl NaruSem.Call.SigEnv.empty AllSig.nil hP (tableOf_nil_Δ P) i
  simpa using this

/-- 対応する適格な宣言群について、Surface の宣言群全体の表の署名は Core の宣言群の署名。 -/
theorem Δ_full_eq {P : Prog} {C : NaruSem.Call.Prog} {Δ : NaruSem.Call.SigEnv}
    (hP : wtProg P = true) (hC : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty C = some Δ) (hl : ProgLower P C) :
    (tableOf P P).Δ = Δ := by
  have h1 := Δ_take_eq hP hl P.length
  rw [List.take_length, hl.length, List.take_length] at h1
  rw [h1]
  exact (NaruSem.Call.wtProg_foldl C _ Δ hC).symm

/-- 表の署名は、後ろに宣言を足しても保たれる。 -/
theorem sigsOf_append_of_some {l₁ : Prog} (l₂ : Prog) {k : String} {s : DeclSig} (h : sigsOf l₁ k = some s) :
    sigsOf (l₁ ++ l₂) k = some s := by
  simp only [sigsOf, List.find?_append] at h ⊢
  cases hf : l₁.find? (fun e => e.key == k) with
  | none => simp [hf] at h
  | some e =>
    rw [hf] at h
    simp only [Option.some_or]
    exact h

/-- prefix の表の署名は、宣言群全体の表の署名に含まれる(fn / input と spec 宣言の両方)。 -/
theorem Δ_take_sub (all : Prog) (i : Nat) :
    NaruSem.Call.SigEnv.SubV (tableOf all (all.take i)).Δ (tableOf all all).Δ ∧
      NaruSem.Call.SigEnv.SubP (tableOf all (all.take i)).Δ (tableOf all all).Δ := by
  have key : ∀ k s, (tableOf all (all.take i)).Δ k = some s → (tableOf all all).Δ k = some s := by
    intro k s hk
    simp only [Table.Δ, tableOf] at hk ⊢
    cases hs : sigsOf (all.take i) k with
    | none => simp [hs] at hk
    | some ds =>
      rw [hs] at hk
      have := sigsOf_append_of_some (all.drop i) hs
      rw [List.take_append_drop] at this
      rw [this]
      exact hk
  constructor
  · intro k ps t hk
    simp only [NaruSem.Call.valueSig?] at hk ⊢
    cases hΔ : (tableOf all (all.take i)).Δ k with
    | none => simp [hΔ] at hk
    | some s =>
      rw [hΔ] at hk
      rw [key k s hΔ]
      exact hk
  · intro k ps hk
    simp only [NaruSem.Call.specSig?] at hk ⊢
    cases hΔ : (tableOf all (all.take i)).Δ k with
    | none => simp [hΔ] at hk
    | some s =>
      rw [hΔ] at hk
      rw [key k s hΔ]
      exact hk

/-- 対応する適格な宣言群について、prefix の表の署名は Core の宣言群の署名に含まれる。 -/
theorem Δ_take_subV {P : Prog} {C : NaruSem.Call.Prog} {Δ : NaruSem.Call.SigEnv}
    (hP : wtProg P = true) (hC : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty C = some Δ) (hl : ProgLower P C) (i : Nat) :
    NaruSem.Call.SigEnv.SubV (tableOf P (P.take i)).Δ Δ ∧ NaruSem.Call.SigEnv.SubP (tableOf P (P.take i)).Δ Δ := by
  have := Δ_take_sub P i
  rw [Δ_full_eq hP hC hl] at this
  exact this

/-! ## input の解釈の対応 -/

/-- Core の宣言群の input の署名を守る解釈は、対応する Surface の宣言群の input の署名も守る。 -/
theorem respectsInputs_of_lower {all : Prog} {seen srest : Prog} {crest : NaruSem.Call.Prog}
    (hl : ProgLowerFrom all seen srest crest) : ∀ {I : NaruSem.Call.FEnv}, I.RespectsInputs crest → RespectsInputs I srest := by
  induction hl with
  | nil _ =>
    intro I _ d hd
    simp at hd
  | @cons seen sd srest cd crest hdl _ ih =>
    intro I hI d hd ps t hs
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · cases cd with
      | fn k ps' t' body => rw [hdl.2.1] at hs; cases hs
      | spec k ps' body => rw [hdl.2.1] at hs; cases hs
      | input k ps' t' =>
        rw [hdl.2.1] at hs
        cases hs
        rw [hdl.1]
        exact hI k _ _ (List.mem_cons_self ..)
    · exact ih (fun k ps t hk => hI k ps t (List.mem_cons_of_mem _ hk)) d hd ps t hs

/-! ## 宣言群の意味の対応 -/

/-- **宣言群の意味の対応(宣言群の帰納法)**: 対応する Surface / Core の宣言群と、それまでの意味が署名の鍵で一致する
(`FEnv.Agree` / `PEnv.Agree`)環境について、残りの宣言群を足した意味も一致する。fn の段は runtime の一般評価保存
(`lower_eval_agree`)、spec 宣言の段は spec の一般双方向同値を読みを経由して合成し(`lowerS_denote` /
`lowerS_denoteP`、`Call.Sem_denote_self` / `Sem_denoteP`)、input の段は同じ解釈(残りの input の鍵で両者が同じ)を運ぶ。 -/
theorem interpFrom_lower_agree (all : Prog) {seen srest : Prog} {crest : NaruSem.Call.Prog}
    (hl : ProgLowerFrom all seen srest crest) :
    ∀ (mS : Interp) (mC : NaruSem.Call.Interp) {Δ : NaruSem.Call.SigEnv},
      AllSig seen → wtProgFrom all seen srest = true → (tableOf all seen).Δ = mC.Δ →
      NaruSem.Call.wtProg mC.Δ crest = some Δ →
      RespectsInputs mS.Φ srest → mC.Φ.Respects mC.Δ → mC.Φ.RespectsInputs crest → mC.Ψ.Defined mC.Δ →
      NaruSem.Call.FEnv.Agree mS.Φ mC.Φ mC.Δ → NaruSem.Call.PEnv.Agree mS.Ψ mC.Ψ mC.Δ →
      (∀ k ps t, NaruSem.Call.Decl.input k ps t ∈ crest → mS.Φ k = mC.Φ k) →
      NaruSem.Call.FEnv.Agree (interpFrom all seen mS srest).Φ (NaruSem.Call.interpFrom mC crest).Φ Δ ∧
        NaruSem.Call.PEnv.Agree (interpFrom all seen mS srest).Ψ (NaruSem.Call.interpFrom mC crest).Ψ Δ ∧
        (tableOf all (seen ++ srest)).Δ = Δ := by
  induction hl with
  | nil seen =>
    intro mS mC Δ _ _ hΔ hC _ _ _ _ hag hp _
    simp only [NaruSem.Call.wtProg, Option.some.injEq] at hC
    subst hC
    simp only [interpFrom, NaruSem.Call.interpFrom]
    exact ⟨hag, hp, by simpa using hΔ⟩
  | @cons seen sd srest cd crest hdl _ ih =>
    intro mS mC Δ hall h hΔ hC hIS hΦC hIC hΨC hag hp hin
    obtain ⟨hfresh, _, hwt, hrest⟩ := wtProgFrom_cons h
    obtain ⟨hcfresh, hcwt, hcrest⟩ := NaruSem.Call.wtProg_cons hC
    have hkey : sd.key = cd.key := hdl.key
    -- Surface の段の不変条件(署名を守る関数環境・定義された spec 環境は Core 側との一致から)
    have hΦS : mS.Φ.Respects (tableOf all seen).Δ := by
      rw [hΔ]; exact hag.respects (NaruSem.Call.SigEnv.SubV.refl _) hΦC
    have hΨS : mS.Ψ.Defined (tableOf all seen).Δ := by
      rw [hΔ]; exact hp.defined
    obtain ⟨hall', _, hIS', _⟩ := Interp.step_inv all seen mS sd srest hall hfresh hwt hrest hΦS hIS hΨS
    obtain ⟨hΦC', hIC', hΨC'⟩ := NaruSem.Call.Interp.step_inv mC cd crest hcfresh hcwt hcrest hΦC hIC hΨC
    -- 表の署名は同じ鍵で伸びる
    have hΔ' : (tableOf all (seen ++ [sd])).Δ = (mC.step cd).Δ := by
      rw [Δ_step_of_lower hall hfresh hdl, hΔ, NaruSem.Call.Interp.step_Δ]
    -- 残りの input の鍵は足した宣言の鍵でない
    have hrestFresh : ∀ k ps t, NaruSem.Call.Decl.input k ps t ∈ crest → k ≠ cd.key := by
      intro k ps t hk he
      have := NaruSem.Call.wtProg_fresh crest hcrest _ hk
      change (mC.Δ.ext cd.key cd.sig) k = none at this
      rw [he, NaruSem.Call.SigEnv.ext_self] at this
      cases this
    -- それまでの対応を表の署名で言い換える
    have hΦC'' : mC.Φ.Respects (tableOf all seen).Δ := by rw [hΔ]; exact hΦC
    have hΨC'' : mC.Ψ.Defined (tableOf all seen).Δ := by rw [hΔ]; exact hΨC
    have hag'' : NaruSem.Call.FEnv.Agree mS.Φ mC.Φ (tableOf all seen).Δ := by rw [hΔ]; exact hag
    have hp'' : NaruSem.Call.PEnv.Agree mS.Ψ mC.Ψ (tableOf all seen).Δ := by rw [hΔ]; exact hp
    have hsub : NaruSem.Call.SigEnv.SubV (tableOf all seen).Δ mC.Δ := by
      rw [hΔ]; exact NaruSem.Call.SigEnv.SubV.refl _
    -- 関数環境の一致
    have hag' : NaruSem.Call.FEnv.Agree (Interp.step all seen mS sd).Φ (mC.step cd).Φ (mC.step cd).Δ := by
      intro y ps t hy
      rw [NaruSem.Call.Interp.step_Δ] at hy
      by_cases hk : y = cd.key
      · subst hk
        rw [NaruSem.Call.valueSig?, NaruSem.Call.SigEnv.ext_self] at hy
        cases cd with
        | fn k ps' t' body =>
          simp only [NaruSem.Call.Decl.sig, NaruSem.Call.Sig.value?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hy
          obtain ⟨rfl, rfl⟩ := hy
          obtain ⟨hk', hs, b, hb, hl⟩ := hdl
          refine ⟨fun vs => match NaruSem.Call.bindParams ps' vs with
                | some ρ => eval (tableOf all seen) mS.Φ (NaruSem.Call.Env.toSEnv ρ) b
                | none => none,
              fun vs => match NaruSem.Call.bindParams ps' vs with
                | some ρ => NaruSem.Call.eval mC.Φ ρ body
                | none => none, ?_, ?_, ?_⟩
          · have := Interp.step_Φ_fn all seen mS sd hs hb
            rw [hk'] at this
            exact this
          · exact NaruSem.Call.Interp.step_Φ_fn mC k ps' t' body
          · intro vs hvs
            obtain ⟨hbind, hty⟩ := NaruSem.Call.bindParams_ty hvs
            simp only [hbind]
            simp only [wtDecl, hs, hb, decide_eq_true_eq] at hwt
            have hctx : NaruSem.Call.paramSCtx ps' = (NaruSem.Call.Env.toSEnv (Env.ofList ((ps'.map (·.1)).zip vs))).ctx := by
              rw [NaruSem.Call.Env.toSEnv_ctx, hty, NaruSem.Call.paramSCtx_eq]
            rw [lower_eval_agree hwt hl hctx hΦC'' hag'', NaruSem.Call.Env.toSEnv_vals]
        | spec k ps' body => simp [NaruSem.Call.Decl.sig, NaruSem.Call.Sig.value?] at hy
        | input k ps' t' =>
          simp only [NaruSem.Call.Decl.sig, NaruSem.Call.Sig.value?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hy
          obtain ⟨rfl, rfl⟩ := hy
          obtain ⟨hk', hs, hb⟩ := hdl
          have hsame : mS.Φ k = mC.Φ k := hin k ps' t' (List.mem_cons_self ..)
          obtain ⟨f', hf', _⟩ := hIC k ps' t' (List.mem_cons_self ..)
          refine ⟨f', f', ?_, hf', fun _ _ => rfl⟩
          rw [Interp.step_input all seen mS sd hs hb]
          show mS.Φ k = some f'
          rw [hsame]
          exact hf'
      · rw [NaruSem.Call.valueSig?, NaruSem.Call.SigEnv.ext_ne _ _ _ hk] at hy
        obtain ⟨f, f', hf, hf', hfe⟩ := hag y ps t hy
        exact ⟨f, f', by rw [Interp.step_Φ_ne all seen mS sd (fun he => hk (he.trans hkey))]; exact hf,
          by rw [NaruSem.Call.Interp.step_Φ_ne _ _ hk]; exact hf', hfe⟩
    -- spec 宣言の環境の一致
    have hp' : NaruSem.Call.PEnv.Agree (Interp.step all seen mS sd).Ψ (mC.step cd).Ψ (mC.step cd).Δ := by
      intro y ps hy
      rw [NaruSem.Call.Interp.step_Δ] at hy
      by_cases hk : y = cd.key
      · subst hk
        rw [NaruSem.Call.specSig?, NaruSem.Call.SigEnv.ext_self] at hy
        cases cd with
        | fn k ps' t' body => simp [NaruSem.Call.Decl.sig, NaruSem.Call.Sig.spec?] at hy
        | input k ps' t' => simp [NaruSem.Call.Decl.sig, NaruSem.Call.Sig.spec?] at hy
        | spec k ps' body =>
          simp only [NaruSem.Call.Decl.sig, NaruSem.Call.Sig.spec?, Option.bind_some, Option.some.injEq] at hy
          subst hy
          obtain ⟨hk', hs, b, hb, hl⟩ := hdl
          refine ⟨fun vs => ∃ ρ, NaruSem.Call.bindParams ps' vs = some ρ ∧
                ∃ P, Sem (tableOf all seen) mS.Φ mS.Ψ (NaruSem.Call.Env.toSEnv ρ) b P ∧ P,
              fun vs => ∃ ρ, NaruSem.Call.bindParams ps' vs = some ρ ∧
                ∃ P, NaruSem.Call.Sem mC.Δ mC.Φ mC.Ψ (NaruSem.Call.Env.toSEnv ρ) body P ∧ P, ?_, ?_, ?_⟩
          · have := Interp.step_Ψ_spec all seen mS sd hs hb
            rw [hk'] at this
            exact this
          · exact NaruSem.Call.Interp.step_Ψ_spec mC k ps' body
          · intro vs hvs
            obtain ⟨hbind, hty⟩ := NaruSem.Call.bindParams_ty hvs
            simp only [wtDecl, hs, hb] at hwt
            split at hwt
            · rename_i τ hτ
              have hctx : NaruSem.Call.paramSCtx ps' = (NaruSem.Call.Env.toSEnv (Env.ofList ((ps'.map (·.1)).zip vs))).ctx := by
                rw [NaruSem.Call.Env.toSEnv_ctx, hty, NaruSem.Call.paramSCtx_eq]
              have hwC : NaruSem.Call.wtS mC.Δ (NaruSem.Call.paramSCtx ps') body = some τ := by
                rw [← hΔ]; exact lowerS_wt hτ hl
              constructor
              · rintro ⟨ρ, hρ, P, hP, hpP⟩
                rw [hbind] at hρ
                cases hρ
                have hiff := lowerS_denote hτ hl hctx hsub hΦC hag'' hp'' hP
                rw [hΔ] at hiff
                exact ⟨_, hbind, _, NaruSem.Call.Sem_denoteP (NaruSem.Call.SigEnv.SubV.refl _) hΦC
                  (NaruSem.Call.FEnv.Agree.refl hΦC) (NaruSem.Call.PEnv.Agree.refl hΨC) hwC hwt _ hctx, hiff.mp hpP⟩
              · rintro ⟨ρ, hρ, Q, hQ, hq⟩
                rw [hbind] at hρ
                cases hρ
                have hiffQ := NaruSem.Call.Sem_denote_self hΦC hΨC hwC _ hctx hQ
                have hS := lowerS_denoteP hτ hwt hl hctx hsub hΦC hag'' hp''
                rw [hΔ] at hS
                exact ⟨_, hbind, _, hS, hiffQ.mp hq⟩
            · cases hwt
      · rw [NaruSem.Call.specSig?, NaruSem.Call.SigEnv.ext_ne _ _ _ hk] at hy
        obtain ⟨F, F', hF, hF', hFe⟩ := hp y ps hy
        exact ⟨F, F', by rw [Interp.step_Ψ_ne all seen mS sd (fun he => hk (he.trans hkey))]; exact hF,
          by rw [NaruSem.Call.Interp.step_Ψ_ne _ _ hk]; exact hF', hFe⟩
    -- 残りの input の鍵では両者とも同じ解釈のまま
    have hin' : ∀ k ps t, NaruSem.Call.Decl.input k ps t ∈ crest → (Interp.step all seen mS sd).Φ k = (mC.step cd).Φ k := by
      intro k ps t hk
      rw [Interp.step_Φ_ne all seen mS sd (fun he => hrestFresh k ps t hk (he.trans hkey)),
        NaruSem.Call.Interp.step_Φ_ne _ _ (hrestFresh k ps t hk)]
      exact hin k ps t (List.mem_cons_of_mem _ hk)
    have := ih (Interp.step all seen mS sd) (mC.step cd) hall' hrest hΔ'
      (by rw [NaruSem.Call.Interp.step_Δ]; exact hcrest) hIS' hΦC' hIC' hΨC' hag' hp' hin'
    simp only [interpFrom, NaruSem.Call.interpFrom]
    refine ⟨this.1, this.2.1, ?_⟩
    simpa [List.append_assoc] using this.2.2

/-- **宣言群の意味の対応(C55 / C57)**: 適格な Surface の宣言群 `P` と適格な Core の宣言群 `C` が宣言ごとに対応し
(`ProgLower P C`: 鍵・署名が同じで、各本体がその宣言より前の宣言の表での独立 lowering の実出力)、`I` が input の署名を
守る任意の解釈なら、同じ `I` の下の宣言群の意味は署名の鍵で一致する: fn / input の意味(`FEnv.Agree`)は型の合う任意の
実引数で同じ値、spec 宣言の意味(`PEnv.Agree`)は型の合う任意の実引数で双方向に同値。宣言群全体の表の署名は Core の署名。 -/
theorem interp_lower_agree {P : Prog} {C : NaruSem.Call.Prog} {Δ : NaruSem.Call.SigEnv}
    (hP : wtProg P = true) (hC : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty C = some Δ) (hl : ProgLower P C)
    {I : NaruSem.Call.FEnv} (hI : I.RespectsInputs C) :
    NaruSem.Call.FEnv.Agree (interp I P).Φ (NaruSem.Call.interp I C).Φ Δ ∧
      NaruSem.Call.PEnv.Agree (interp I P).Ψ (NaruSem.Call.interp I C).Ψ Δ ∧ (tableOf P P).Δ = Δ := by
  have := interpFrom_lower_agree P hl { Φ := I, Ψ := NaruSem.Call.PEnv.empty } (NaruSem.Call.Interp.init I) AllSig.nil hP
    (tableOf_nil_Δ P) hC (respectsInputs_of_lower hl hI) (NaruSem.Call.Interp.init_respects I) hI
    (NaruSem.Call.Interp.init_defined I)
    (fun k ps t h => by simp [NaruSem.Call.Interp.init, NaruSem.Call.valueSig?, NaruSem.Call.SigEnv.empty] at h)
    (fun k ps h => by simp [NaruSem.Call.Interp.init, NaruSem.Call.specSig?, NaruSem.Call.SigEnv.empty] at h)
    (fun _ _ _ _ => rfl)
  simpa [interp, NaruSem.Call.interp] using this

/-! ## Surface の宣言群の意味から実生成環境での読みへ -/

/-- **Surface の宣言群の意味の下での spec 本体と実生成環境での読み(C55 / C57)**: 対応する宣言群と、Core の宣言群の意味と
実生成環境の対応(`Call.interp_agree` / `interp_prop_agree` の結論)から、prefix の表 `tableOf P (P.take i)` で論理の位置で
適格な Surface の式と独立 lowering の実出力 `c` について、Surface の宣言群の意味 `interp I P` の下での式の意味は
実生成環境 `Φ'` / `Ψ'` での読み `Call.denoteP` と同値: 読み自体が意味であり、任意の意味は読みと同値。 -/
theorem spec_sem_denote {P : Prog} {C : NaruSem.Call.Prog} {Δ : NaruSem.Call.SigEnv}
    (hP : wtProg P = true) (hC : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty C = some Δ) (hl : ProgLower P C)
    {I : NaruSem.Call.FEnv} (hI : I.RespectsInputs C)
    {Δ' : NaruSem.Call.SigEnv} {Φ' : NaruSem.Call.FEnv} {Ψ' : NaruSem.Call.PEnv}
    (hΔ : NaruSem.Call.SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ')
    (hA : NaruSem.Call.FEnv.Agree (NaruSem.Call.interp I C).Φ Φ' Δ)
    (hPA : NaruSem.Call.PEnv.Agree (NaruSem.Call.interp I C).Ψ Ψ' Δ)
    (i : Nat) {Γ : SCtx} {e : Expr} {τ : STy} {c : Core.Expr}
    (hw : wtS (tableOf P (P.take i)) Γ e = some τ) (hf : τ.isForm = true)
    (hlow : lowerS (tableOf P (P.take i)) Γ e = some c) {ρ : SEnv} (hΓ : Γ = ρ.ctx) :
    Sem (tableOf P (P.take i)) (interp I P).Φ (interp I P).Ψ ρ e
        (NaruSem.Call.denoteP (tableOf P (P.take i)).Δ Φ' Ψ' ρ c) ∧
      ∀ Q, Sem (tableOf P (P.take i)) (interp I P).Φ (interp I P).Ψ ρ e Q →
        (Q ↔ NaruSem.Call.denoteP (tableOf P (P.take i)).Δ Φ' Ψ' ρ c) := by
  obtain ⟨hAS, hPS, hTΔ⟩ := interp_lower_agree hP hC hl hI
  obtain ⟨hTV, hTP⟩ := Δ_take_sub P i
  rw [hTΔ] at hTV hTP
  have hA' := (hAS.trans hA).mono hTV
  have hPA' := (hPS.trans hPA).mono hTP
  have hΔ' := hTV.trans hΔ
  exact ⟨lowerS_denoteP hw hf hlow hΓ hΔ' hΦ' hA' hPA',
    fun Q hQ => lowerS_denote hw hlow hΓ hΔ' hΦ' hA' hPA' hQ⟩

end NaruSem.Surf.Call
