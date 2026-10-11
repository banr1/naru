import NaruSem.CallDenote

/-!
# 任意の署名を守る input 解釈から Lean の値・全域関数への対応

`RespectsInputs` は型の合う引数での全域性だけを要求する。`wrap` の逆方向も
その範囲だけで一致させる。不適切な引数の挙動を隠したり、`SameInputs` の
関数そのものの等式をこの対応から導いたりはしない。
標準の選択公理で数学的な解釈を表現する証明であり、新しい実行経路ではない。
-/

namespace NaruSem.Call

/-- 署名を守る任意の解釈を、型の合う全引数で同じ値を返す Lean の
カリー化された全域関数に写す。ゼロ引数なら Lean の値。 -/
theorem exists_fn (ps : List Ty) (t : Ty) (f : List Val → Option Val)
    (h : ∀ vs, vs.map Val.ty = ps → ∃ v, f vs = some v ∧ v.ty = t) :
    ∃ g : Fn ps t, ∀ vs, vs.map Val.ty = ps → wrap ps t g vs = f vs := by
  classical
  induction ps generalizing f with
  | nil =>
    obtain ⟨v, hv, ht⟩ := h [] rfl
    cases t <;> cases v <;> simp only [Val.ty] at ht
    · rename_i n
      refine ⟨n, ?_⟩
      intro vs hvs
      cases vs with
      | nil => exact (wrap_nil _ _).trans hv.symm
      | cons => simp at hvs
    · cases ht
    · cases ht
    · rename_i b
      refine ⟨b, ?_⟩
      intro vs hvs
      cases vs with
      | nil => exact (wrap_nil _ _).trans hv.symm
      | cons => simp at hvs
  | cons p ps ih =>
    have tail (a : p.carrier) :
        ∃ g : Fn ps t, ∀ vs, vs.map Val.ty = ps → wrap ps t g vs = f (Val.of p a :: vs) :=
      ih (fun vs => f (Val.of p a :: vs)) (fun vs hvs => h _ (by simp [hvs]))
    let g (a : p.carrier) := Classical.choose (tail a)
    have hg (a : p.carrier) := Classical.choose_spec (tail a)
    cases p
    · refine ⟨g, ?_⟩
      intro vs hvs
      cases vs with
      | nil => simp at hvs
      | cons v vs =>
        cases v with
        | bool b => simp [Val.ty] at hvs
        | nat n =>
          simp only [List.map_cons, Val.ty, List.cons.injEq, true_and] at hvs
          exact (wrap_nat ps t g n vs).trans (hg n vs hvs)
    · refine ⟨g, ?_⟩
      intro vs hvs
      cases vs with
      | nil => simp at hvs
      | cons v vs =>
        cases v with
        | nat n => simp [Val.ty] at hvs
        | bool b =>
          simp only [List.map_cons, Val.ty, List.cons.injEq, true_and] at hvs
          exact (wrap_bool ps t g b vs).trans (hg b vs hvs)

/-- 宣言の鍵と署名を保った、任意の input 解釈の一つの Lean 表現。 -/
theorem input_representable {P : Prog} {I : FEnv} (hI : I.RespectsInputs P)
    {k : String} {ps : List (String × Ty)} {t : Ty} (hd : Decl.input k ps t ∈ P) :
    ∃ g : Fn (ps.map (·.2)) t, ∃ f, I k = some f ∧
      ∀ vs, vs.map Val.ty = ps.map (·.2) → wrap (ps.map (·.2)) t g vs = f vs := by
  obtain ⟨f, hf, htotal⟩ := hI k ps t hd
  obtain ⟨g, hg⟩ := exists_fn (ps.map (·.2)) t f htotal
  exact ⟨g, f, hf, hg⟩

/-- 同型の input も宣言の鍵と署名で識別した Lean 表現の族。 -/
abbrev InputValues (P : Prog) := ∀ k ps t, Decl.input k ps t ∈ P → Fn (ps.map (·.2)) t

/-- 同じ任意の解釈の全 input を同時に表現する。必要な前提は input の署名遵守。 -/
theorem inputs_representable {P : Prog} {I : FEnv} (hI : I.RespectsInputs P) :
    ∃ gs : InputValues P, ∀ k ps t (hd : Decl.input k ps t ∈ P),
      ∃ f, I k = some f ∧ ∀ vs, vs.map Val.ty = ps.map (·.2) →
        wrap (ps.map (·.2)) t (gs k ps t hd) vs = f vs := by
  classical
  exact ⟨fun k ps t hd => Classical.choose (input_representable hI hd),
    fun k ps t hd => Classical.choose_spec (input_representable hI hd)⟩

/-- 型外の引数で値を返す解釈も、型内での全域性の前提を満たす。 -/
theorem illtyped_total : ∀ vs : List Val, vs.map Val.ty = [.nat] →
    ∃ v, (some (Val.nat 7) : Option Val) = some v ∧ v.ty = .nat := by
  intro _ _
  exact ⟨.nat 7, rfl, rfl⟩

/-- 型外の挙動まで `wrap` と等しいという強すぎる主張は成立しない。 -/
theorem illtyped_not_equal (g : Fn [.nat] .nat) :
    wrap [.nat] .nat g [.bool true] ≠ some (.nat 7) := by
  simp [wrap]

end NaruSem.Call
