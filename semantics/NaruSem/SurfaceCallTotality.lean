import NaruSem.SurfaceCall
import NaruSem.SurfaceTotality
import NaruSem.CallTotality

/-!
# 関数・input の保存対象の Surface AST には意味が定まる(IDEAL.md C54)

`SurfaceCall.lean` の呼出し(位置 / 名前付き引数・修飾名・UFCS)と input を含む Surface AST の意味論について、適格な式と対応する環境には
意味が定まることを証明する。前提は C48(`SurfaceTotality.lean`)と同じ「文脈と環境の対応」に、C54 の Core 側(`CallTotality.lean`)と同じ
「呼出し先の環境が宣言表の署名を守る」を加えたもの:

- `Γ = ρ.ctx` — 局所の束縛文脈は環境の文脈(この層では runtime の式も `SCtx` / `SEnv` の上で読む)。
- `Φ.Respects T.Δ` — runtime の呼出し先の環境(fn の意味と input の解釈)は宣言表 `T` の fn / input の署名を守る(型の合う実引数に型の合う結果を返す)。
- `Ψ.Defined T.Δ` — spec 宣言の環境は宣言表の spec 宣言の鍵に定義されている。

結果:

- runtime: `eval_total`(適格な式は値を持ち、値の型は型付けの型)、`evalArgs_total`(実引数の列。名前付きの印はそのまま)、`Eval_unique`。
  名前付き引数の並べ替え `arrange` は名前だけを見るので値の列と型の列で可換(`arrange_map`): 型の列が仮引数の順に並べ替えられるなら、
  実引数の値の列も同じ順に並べ替えられて型が合う(`arrange_vals`)。
- spec: `Sem_exists`(論理の位置で適格な式には意味がある)、`Sem_unique`(意味は一意: fn / input の呼出しの規則と spec 宣言の呼出しの規則は
  宣言表の署名で排他、注釈の無い `==` の `eqNat` / `eqForm` は `Sem_not_nat` で排他)。`Sem_not_nat` の帰納法には評価の単調性 `eval_mono`
  (値の束縛と束縛の有無(局所名が大域名を隠すこと)を保つ環境の拡張は、定まっていた値を変えない)を使う。
- 宣言群: `interp_respects` / `interp_defined`(適格な宣言群 `wtProg P = true` と input の署名を守る任意の解釈 `I` について、宣言群の意味
  `interp I P` は宣言群全体の表の署名を守る)、`fn_total`(各 fn は型の合う任意の実引数に型の合う値を返す)、`spec_defined`(各 spec 宣言には
  意味がある)、`spec_meaning`(spec 宣言の意味は、それより前の宣言の表と意味の下での本体の意味そのもの)。

翻訳の正しさ(frontend の変換・backend の出力)は現れない。`CallTotality.lean` の宣言群の帰納法(`Interp.step_inv`)と同じ構成で、
宣言表は `tableOf all seen`(解決は宣言群全体、署名はそれより前の宣言)なので、表の署名が宣言を 1 つ足すごとにその宣言の鍵だけで
伸びること(`Δ_append_self` / `Δ_append_ne`)を宣言群の適格性(鍵の重複なし・各宣言の署名が対象)から導く。
-/

namespace NaruSem.Surf.Call
open Naru

/-! ## 展開の補題(入れ子の帰納型の上の構造的再帰の等式は、`simp` に定義として渡さずこれらで書き換える) -/

theorem wtArgs_pos (T : Table) (Γ : SCtx) (e : Expr) (rest : List Arg) :
    wtArgs T Γ (.pos e :: rest) =
      match wtR T Γ e, wtArgs T Γ rest with
      | some t, some tys => some ((none, t) :: tys)
      | _, _ => none :=
  wtArgs.eq_2 T Γ e rest

theorem wtArgs_named (T : Table) (Γ : SCtx) (n : String) (e : Expr) (rest : List Arg) :
    wtArgs T Γ (.named n e :: rest) =
      match wtR T Γ e, wtArgs T Γ rest with
      | some t, some tys => some ((some n, t) :: tys)
      | _, _ => none :=
  wtArgs.eq_3 T Γ n e rest

theorem evalArgs_pos (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (e : Expr) (rest : List Arg) :
    evalArgs T Φ ρ (.pos e :: rest) =
      match eval T Φ ρ e, evalArgs T Φ ρ rest with
      | some v, some vals => some ((none, v) :: vals)
      | _, _ => none :=
  evalArgs.eq_2 T Φ ρ e rest

theorem evalArgs_named (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (n : String) (e : Expr) (rest : List Arg) :
    evalArgs T Φ ρ (.named n e :: rest) =
      match eval T Φ ρ e, evalArgs T Φ ρ rest with
      | some v, some vals => some ((some n, v) :: vals)
      | _, _ => none :=
  evalArgs.eq_3 T Φ ρ n e rest

theorem evalArms_cons (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (v : Val) (p : Pat) (g : Option Expr) (b : Expr) (rest : List Arm) :
    evalArms T Φ ρ v (.mk p g b :: rest) =
      match matchPat p v with
      | none => evalArms T Φ ρ v rest
      | some bs =>
        match g with
        | none => eval T Φ (ρ.extVals bs) b
        | some g =>
          match eval T Φ (ρ.extVals bs) g with
          | some (.bool true) => eval T Φ (ρ.extVals bs) b
          | some (.bool false) => evalArms T Φ ρ v rest
          | _ => none :=
  evalArms.eq_2 T Φ ρ v p g b rest

theorem evalStmts_cons (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (sp : Span) (x : String) (ty : Option Ty) (v : Expr) (rest : List Stmt) :
    evalStmts T Φ ρ (.letS sp x ty v :: rest) =
      match eval T Φ ρ v with
      | some w => evalStmts T Φ (ρ.ext x (.val w)) rest
      | none => none :=
  evalStmts.eq_2 T Φ ρ sp x ty v rest

theorem wtArmR_mk (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) (p : Pat) (g : Option Expr) (b : Expr) :
    wtArmR T Γ ts (.mk p g b) =
      match wtPat ts p with
      | none => none
      | some bs =>
        match g with
        | none => wtR T (Γ.extVals bs) b
        | some g =>
          match wtR T (Γ.extVals bs) g with
          | some .bool => wtR T (Γ.extVals bs) b
          | _ => none :=
  wtArmR.eq_1 T Γ ts p g b

theorem wtArmS_mk (T : Table) (Γ : SCtx) (ts : NaruSem.Ty) (p : Pat) (g : Option Expr) (b : Expr) :
    wtArmS T Γ ts (.mk p g b) =
      match wtPat ts p with
      | none => none
      | some bs =>
        match g with
        | none =>
          match wtS T (Γ.extVals bs) b with
          | some t => if t.isForm then some t else none
          | none => none
        | some g =>
          match wtS T (Γ.extVals bs) g, wtS T (Γ.extVals bs) b with
          | some tg, some tb => tg.join tb
          | _, _ => none :=
  wtArmS.eq_1 T Γ ts p g b

/-- ブロックの `let` 1 つ分の評価の形(末尾式があってもなくても成り立つ)。 -/
theorem eval_block_cons (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (sp lsp : Span) (x : String) (ty : Option Ty) (v : Expr)
    (rest : List Stmt) (tail : Option Expr) :
    eval T Φ ρ (.block sp (.letS lsp x ty v :: rest) tail) =
      match eval T Φ ρ v with
      | some w => eval T Φ (ρ.ext x (.val w)) (.block sp rest tail)
      | none => none := by
  cases tail with
  | none =>
    simp only [eval]
    split <;> rfl
  | some e =>
    simp only [eval, evalStmts_cons]
    cases eval T Φ ρ v <;> simp

theorem eval_block_nil (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (sp : Span) (e : Expr) :
    eval T Φ ρ (.block sp [] (some e)) = eval T Φ ρ e := by
  simp [eval, evalStmts]

theorem eval_match (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (sp : Span) (s : Expr) (arms : List Arm) (v : Val)
    (hs : eval T Φ ρ s = some v) : eval T Φ ρ (.matchE sp s arms) = evalArms T Φ ρ v arms := by
  simp [eval, hs]

/-! ## 網羅性の補題(`Surface.lean` と同じ規則の、呼出しを含む腕の列の版) -/

theorem exhaustiveFrom_guard (t : NaruSem.Ty) (sawT sawF : Bool) (p : Pat) (g b : Expr) (rest : List Arm) :
    exhaustiveFrom t sawT sawF (.mk p (some g) b :: rest) = exhaustiveFrom t sawT sawF rest := by
  simp [exhaustiveFrom]

theorem exhaustiveFrom_true (t : NaruSem.Ty) (sawT sawF : Bool) (sp : Span) (b : Expr) (rest : List Arm) :
    exhaustiveFrom t sawT sawF (.mk (.lit sp (.bool true)) none b :: rest) =
      ((decide (t = .bool) && sawF) || exhaustiveFrom t true sawF rest) := by
  simp [exhaustiveFrom]

theorem exhaustiveFrom_false (t : NaruSem.Ty) (sawT sawF : Bool) (sp : Span) (b : Expr) (rest : List Arm) :
    exhaustiveFrom t sawT sawF (.mk (.lit sp (.bool false)) none b :: rest) =
      ((decide (t = .bool) && sawT) || exhaustiveFrom t sawT true rest) := by
  simp [exhaustiveFrom]

theorem exhaustiveFrom_nat (t : NaruSem.Ty) (sawT sawF : Bool) (sp : Span) (n : Nat) (b : Expr) (rest : List Arm) :
    exhaustiveFrom t sawT sawF (.mk (.lit sp (.nat n)) none b :: rest) = exhaustiveFrom t sawT sawF rest := by
  simp [exhaustiveFrom]

/-! ## 局所名による隠蔽は文脈と環境で一致する -/

/-- 呼出し先の経路の頭が束ねられているかは、環境でもその文脈でも同じ(束縛の有無だけを見る)。 -/
theorem headBound_ctx (ρ : SEnv) (path : List String) : headBound ρ.ctx path = headBound ρ path := by
  match path with
  | [x] => simp [headBound, SEnv.ctx]
  | [] => rfl
  | _ :: _ :: _ => rfl

theorem ufcs_ctx (T : Table) (ρ : SEnv) (m : String) : ufcs T ρ.ctx m = ufcs T ρ m := by
  simp [ufcs, SEnv.ctx]

/-! ## 宣言表の署名と Core 側の署名の文脈 -/

/-- 表の fn / input の署名は、Core 側の署名の文脈 `T.Δ` の fn / input の署名(仮引数の名前を落としたもの)。 -/
theorem valueSig?_Δ {T : Table} {k : String} {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
    (h : (T.sig k).bind DeclSig.value? = some (ps, t)) : NaruSem.Call.valueSig? T.Δ k = some (ps.map (·.2), t) := by
  unfold NaruSem.Call.valueSig? Table.Δ
  cases hs : T.sig k with
  | none => simp [hs] at h
  | some s =>
    rw [hs] at h
    cases s with
    | fn ps' t' =>
      simp only [Option.bind_some, DeclSig.value?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | input ps' t' =>
      simp only [Option.bind_some, DeclSig.value?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | spec _ => simp [DeclSig.value?] at h

/-- 表の spec 宣言の署名は、Core 側の署名の文脈の spec 宣言の署名。 -/
theorem specSig?_Δ {T : Table} {k : String} {ps : List (String × NaruSem.Ty)} (h : T.sig k = some (.spec ps)) :
    NaruSem.Call.specSig? T.Δ k = some (ps.map (·.2)) := by
  simp [NaruSem.Call.specSig?, Table.Δ, h, DeclSig.toSig, NaruSem.Call.Sig.spec?]

/-! ## 実引数の並べ替えは payload の写像と可換(名前だけを見る) -/

/-- 名前付き実引数の payload の写像(名前はそのまま)。 -/
def mapArg {α β : Type} (f : α → β) (p : Option String × α) : Option String × β := (p.1, f p.2)

theorem assign_map {α β : Type} (f : α → β) (ps : List (String × NaruSem.Ty)) :
    ∀ (args : List (Option String × α)) (i : Nat) (sawNamed : Bool) (slots : List (Option α)),
      assign ps (args.map (mapArg f)) i sawNamed (slots.map (Option.map f)) =
        (assign ps args i sawNamed slots).map (List.map (Option.map f))
  | [], _, _, _ => by simp [assign]
  | (none, v) :: rest, i, sawNamed, slots => by
    simp only [List.map_cons, mapArg, assign, List.length_map]
    by_cases hsn : sawNamed = true
    · simp [hsn]
    · simp only [hsn, Bool.false_eq_true, ite_false]
      by_cases hi : i < slots.length
      · simp only [hi, ite_true]
        rw [show (some (f v) : Option β) = Option.map f (some v) from rfl, ← List.map_set]
        exact assign_map f ps rest (i + 1) false (slots.set i (some v))
      · simp [hi]
  | (some n, v) :: rest, i, sawNamed, slots => by
    simp only [List.map_cons, mapArg, assign]
    cases ps.findIdx? (fun p => p.1 == n) with
    | none => rfl
    | some j =>
      simp only [List.getElem?_map]
      cases slots[j]? with
      | none => rfl
      | some o =>
        cases o with
        | none =>
          simp only [Option.map_some, Option.map_none]
          rw [show (some (f v) : Option β) = Option.map f (some v) from rfl, ← List.map_set]
          exact assign_map f ps rest i true (slots.set j (some v))
        | some w => rfl

theorem allSome_map {α β : Type} (f : α → β) : ∀ xs : List (Option α), allSome (xs.map (Option.map f)) = (allSome xs).map (List.map f)
  | [] => rfl
  | some v :: rest => by
    simp only [List.map_cons, Option.map_some, allSome, allSome_map f rest]
    cases allSome rest <;> rfl
  | none :: rest => rfl

/-- **並べ替えは payload の写像と可換**: 名前付き実引数の列の payload を写してから仮引数の順に並べても、並べてから写しても同じ。 -/
theorem arrange_map {α β : Type} (f : α → β) (ps : List (String × NaruSem.Ty)) (args : List (Option String × α)) :
    arrange ps (args.map (mapArg f)) = (arrange ps args).map (List.map f) := by
  unfold arrange
  have hinit : (ps.map fun _ => (none : Option β)) = (ps.map fun _ => (none : Option α)).map (Option.map f) := by
    simp [List.map_map, Function.comp_def]
  rw [hinit, assign_map]
  cases assign ps args 0 false (ps.map fun _ => none) with
  | none => rfl
  | some slots => simp [allSome_map]

/-- 実引数の値の列の型の列が仮引数の順に並べ替えられて仮引数の型に一致するなら、値の列も同じ順に並べ替えられ、その型は仮引数の型。 -/
theorem arrange_vals {ps : List (String × NaruSem.Ty)} {vals : List (Option String × Val)} {tys : List (Option String × NaruSem.Ty)}
    (hvt : vals.map (mapArg Val.ty) = tys) (harr : arrange ps tys = some (ps.map (·.2))) :
    ∃ vs, arrange ps vals = some vs ∧ vs.map Val.ty = ps.map (·.2) := by
  subst hvt
  rw [arrange_map] at harr
  cases h : arrange ps vals with
  | none => rw [h] at harr; cases harr
  | some vs =>
    rw [h, Option.map_some] at harr
    exact ⟨vs, rfl, Option.some.inj harr⟩

/-! ## runtime の全域性 -/

/-- `wtR` / `wtStmtsR` / `wtArmsR` / `wtArmR` / `wtArgs` の関数帰納法で、式・`let` の列・腕の列・腕・実引数の列の 5 つを同時に示す。
腕の列の不変条件は `SurfaceTotality.lean` と同じ。実引数の列は、型の列(構文解析の順、名前付きは名前つき)に対して同じ名前の印の値の列を持つ。
呼出しは、実引数の値の列を仮引数の順に並べ替えて(`arrange_vals`)、署名を守る関数環境の関数に渡す。 -/
theorem wtR_total_all (T : Table) :
    (∀ (Γ : SCtx) (e : Expr), ∀ (Φ : NaruSem.Call.FEnv) (ρ : SEnv), Γ = ρ.ctx → Φ.Respects T.Δ → ∀ t, wtR T Γ e = some t →
        ∃ v, eval T Φ ρ e = some v ∧ v.ty = t) ∧
    (∀ (Γ : SCtx) (stmts : List Stmt), ∀ (Φ : NaruSem.Call.FEnv) (ρ : SEnv), Γ = ρ.ctx → Φ.Respects T.Δ → ∀ Γ',
        wtStmtsR T Γ stmts = some Γ' → ∃ ρ', evalStmts T Φ ρ stmts = some ρ' ∧ Γ' = ρ'.ctx) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arms : List Arm), ∀ (Φ : NaruSem.Call.FEnv) (ρ : SEnv), Γ = ρ.ctx → Φ.Respects T.Δ → ∀ t,
        wtArmsR T Γ ts arms = some t → ∀ v : Val, v.ty = ts → ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        ∃ w, evalArms T Φ ρ v arms = some w ∧ w.ty = t) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arm : Arm), ∀ p g b, arm = .mk p g b → ∀ (Φ : NaruSem.Call.FEnv) (ρ : SEnv), Γ = ρ.ctx →
        Φ.Respects T.Δ → ∀ t, wtArmR T Γ ts arm = some t → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        (∃ w, eval T Φ (ρ.extVals bs) b = some w ∧ w.ty = t) ∧
        (∀ g', g = some g' → ∃ c : Bool, eval T Φ (ρ.extVals bs) g' = some (.bool c))) ∧
    (∀ (Γ : SCtx) (args : List Arg), ∀ (Φ : NaruSem.Call.FEnv) (ρ : SEnv), Γ = ρ.ctx → Φ.Respects T.Δ → ∀ tys,
        wtArgs T Γ args = some tys → ∃ vals, evalArgs T Φ ρ args = some vals ∧ vals.map (mapArg Val.ty) = tys) := by
  apply wtR.mutual_induct T
  -- 1. Nat のリテラル
  · intro Γ _ n Φ ρ _ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨.nat n, by simp [eval], rfl⟩
  -- 2. Bool のリテラル
  · intro Γ _ b Φ ρ _ _ t ht
    simp only [wtR, Option.some.injEq] at ht
    subst ht
    exact ⟨.bool b, by simp [eval], rfl⟩
  -- 3. 局所名(値に束ねられている)
  · intro Γ _ x t hx Φ ρ hΓ _ t' ht
    simp only [wtR, hx, Option.some.injEq] at ht
    subst ht
    subst hΓ
    simp only [SEnv.ctx] at hx
    cases h : ρ x with
    | none => simp [h] at hx
    | some s =>
      simp only [h, Option.map_some, Option.some.injEq] at hx
      cases s with
      | prop _ => simp [SVal.ty] at hx
      | val v =>
        simp only [SVal.ty, STy.val.injEq] at hx
        exact ⟨v, by simp [eval, h], hx⟩
  -- 4. 局所名(値に束ねられていない: スコープ外か命題)
  · intro Γ _ x hno Φ ρ _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht
         · rename_i t' hx
           exact (hno t' hx).elim
         · cases ht)
  -- 5. 呼出し(頭が局所名: 対象外)
  · intro Γ _ _ path args hb Φ ρ _ _ t ht
    simp [wtR, hb] at ht
  -- 6. 呼出し(実引数が適格): 値の列を仮引数の順に並べ替えて、署名を守る関数環境の関数に渡す
  · intro Γ _ _ path args hnb tys hargs ih5 Φ ρ hΓ hΦ t ht
    simp only [Bool.not_eq_true] at hnb
    simp only [wtR, hnb, Bool.false_eq_true, ite_false, hargs] at ht
    obtain ⟨vals, hvals, hvt⟩ := ih5 Φ ρ hΓ hΦ tys hargs
    have hnb' : headBound ρ path = false := by rw [← headBound_ctx, ← hΓ]; exact hnb
    simp only [callTy] at ht
    cases hres : T.resolve path with
    | none => simp [hres] at ht
    | some k =>
      simp only [hres] at ht
      cases hd : (T.sig k).bind DeclSig.value? with
      | none => simp [hd] at ht
      | some pt =>
        obtain ⟨ps, t₀⟩ := pt
        simp only [hd] at ht
        split at ht
        · rename_i harr
          cases ht
          obtain ⟨vs, hvs, hvst⟩ := arrange_vals hvt harr
          obtain ⟨f, hf, hfv⟩ := hΦ k _ _ (valueSig?_Δ hd)
          obtain ⟨v, hv, hvty⟩ := hfv vs hvst
          refine ⟨v, ?_, hvty⟩
          simp [eval, hnb', hvals, callVal, hres, hd, hf, hvs, hv]
        · cases ht
  -- 7. 呼出し(実引数が不適格)
  · intro Γ _ _ path args hnb hargs _ Φ ρ _ _ t ht
    simp only [Bool.not_eq_true] at hnb
    simp [wtR, hnb, hargs] at ht
  -- 8. 二項演算(適格)
  · intro Γ _ op l r k tl tr hr hl hk ihl ihr Φ ρ hΓ hΦ t ht
    simp only [wtR, hk, hl, hr] at ht
    obtain ⟨a, ha, hat⟩ := ihl Φ ρ hΓ hΦ tl hl
    obtain ⟨b, hb, hbt⟩ := ihr Φ ρ hΓ hΦ tr hr
    simp only [eval, hk, ha, hb]
    subst hat hbt
    cases k <;> cases a <;> cases b <;> simp_all [binopResult, BinOp.apply, Val.ty]
  -- 9. 二項演算(不適格)
  · intro Γ _ op l r hno _ _ Φ ρ _ _ t ht
    simp only [wtR] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 10. `!`(適格)
  · intro Γ _ a ha iha Φ ρ hΓ hΦ t ht
    simp only [wtR, ha, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨va, hva, hvat⟩ := iha Φ ρ hΓ hΦ .bool ha
    cases va with
    | nat => simp [Val.ty] at hvat
    | bool ba => exact ⟨.bool (!ba), by simp [eval, hva], rfl⟩
  -- 11. `!`(被演算子が Bool でない)
  · intro Γ _ a hno _ Φ ρ _ _ t ht
    simp only [wtR, ite_true] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 12. 対象外の単項演算子
  · intro Γ _ op a hne Φ ρ _ _ t ht
    simp [wtR, hne] at ht
  -- 13. UFCS の呼出し(適格): 受け手を先頭の位置引数にして呼出し
  · intro Γ _ r m args hu tr tys hargs hr ihr ih5 Φ ρ hΓ hΦ t ht
    rw [wtR.eq_def] at ht
    simp only [hu, ite_true, hr, hargs] at ht
    obtain ⟨v, hv, hvt⟩ := ihr Φ ρ hΓ hΦ tr hr
    obtain ⟨vals, hvals, hvts⟩ := ih5 Φ ρ hΓ hΦ tys hargs
    have hu' : ufcs T ρ m = true := by rw [← ufcs_ctx, ← hΓ]; exact hu
    have hvt' : ((none, v) :: vals).map (mapArg Val.ty) = (none, tr) :: tys := by simp [mapArg, hvt, hvts]
    simp only [callTy] at ht
    cases hres : T.resolve [m] with
    | none => simp [hres] at ht
    | some k =>
      simp only [hres] at ht
      cases hd : (T.sig k).bind DeclSig.value? with
      | none => simp [hd] at ht
      | some pt =>
        obtain ⟨ps, t₀⟩ := pt
        simp only [hd] at ht
        split at ht
        · rename_i harr
          cases ht
          obtain ⟨vs, hvs, hvst⟩ := arrange_vals hvt' harr
          obtain ⟨f, hf, hfv⟩ := hΦ k _ _ (valueSig?_Δ hd)
          obtain ⟨w, hw, hwty⟩ := hfv vs hvst
          refine ⟨w, ?_, hwty⟩
          rw [eval.eq_def]
          simp only [hu', ite_true, hv, hvals, callVal, hres, hd, hf, hvs, hw]
        · cases ht
  -- 14. UFCS の呼出し(受け手か実引数が不適格)
  · intro Γ _ r m args hu hno _ _ Φ ρ _ _ t ht
    rw [wtR.eq_def] at ht
    simp only [hu, ite_true] at ht
    cases hwr : wtR T Γ r with
    | none => simp at ht
    | some tr =>
      cases hwa : wtArgs T Γ args with
      | none => simp at ht
      | some tys => exact (hno tr tys hwr hwa).elim
  -- 15. Nat の min / max(適格)
  · intro Γ _ r m hnu a k ha hr hm ihr iha Φ ρ hΓ hΦ t ht
    simp only [Bool.not_eq_true] at hnu
    simp only [wtR, hnu, Bool.false_eq_true, ite_false, hm, hr, ha, Option.some.injEq] at ht
    subst ht
    have hnu' : ufcs T ρ m = false := by rw [← ufcs_ctx, ← hΓ]; exact hnu
    obtain ⟨x, hx, hxt⟩ := ihr Φ ρ hΓ hΦ .nat hr
    obtain ⟨y, hy, hyt⟩ := iha Φ ρ hΓ hΦ .nat ha
    cases x with
    | bool => simp [Val.ty] at hxt
    | nat x =>
      cases y with
      | bool => simp [Val.ty] at hyt
      | nat y => exact ⟨.nat (k.eval x y), by simp [eval, hnu', hm, hx, hy], rfl⟩
  -- 16. Nat のメソッド(不適格)
  · intro Γ _ r m hnu a hno _ _ Φ ρ _ _ t ht
    simp only [Bool.not_eq_true] at hnu
    rw [wtR.eq_def] at ht
    simp only [hnu, Bool.false_eq_true, ite_false] at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 17. メソッド(位置引数 1 つでない: 対象外)
  · intro Γ _ r m args hnu hne Φ ρ _ _ t ht
    simp only [Bool.not_eq_true] at hnu
    simp only [wtR, hnu, Bool.false_eq_true, ite_false] at ht
    cases args with
    | nil => simp at ht
    | cons a rest =>
      cases a with
      | named n e => simp at ht
      | pos e =>
        cases rest with
        | nil => exact (hne e rfl).elim
        | cons b rest' => simp at ht
  -- 18. if(適格)
  · intro Γ _ c t e te hte hc htt ihc iht ihe Φ ρ hΓ hΦ t' ht'
    simp only [wtR, hc, htt, hte, ite_true, Option.some.injEq] at ht'
    subst ht'
    obtain ⟨vc, hvc, hvct⟩ := ihc Φ ρ hΓ hΦ .bool hc
    cases vc with
    | nat => simp [Val.ty] at hvct
    | bool bc =>
      cases bc with
      | true =>
        obtain ⟨w, hw, hwt⟩ := iht Φ ρ hΓ hΦ te htt
        exact ⟨w, by simp [eval, hvc, hw], hwt⟩
      | false =>
        obtain ⟨w, hw, hwt⟩ := ihe Φ ρ hΓ hΦ te hte
        exact ⟨w, by simp [eval, hvc, hw], hwt⟩
  -- 19. if(分岐の型が違う)
  · intro Γ _ c t e tt te hte htt hc hne _ _ _ Φ ρ _ _ t' ht'
    simp [wtR, hc, htt, hte, hne] at ht'
  -- 20. if(不適格)
  · intro Γ _ c t e hno _ _ _ Φ ρ _ _ t' ht'
    simp only [wtR] at ht'
    first
      | (cases ht'; done)
      | (split at ht' <;> simp_all)
  -- 21. match(適格)
  · intro Γ _ s arms ta hs hex ihs iharms Φ ρ hΓ hΦ t ht
    simp only [wtR, hs, hex, ite_true] at ht
    obtain ⟨v, hv, hvt⟩ := ihs Φ ρ hΓ hΦ ta hs
    obtain ⟨w, hw, hwt⟩ := iharms Φ ρ hΓ hΦ t ht v hvt false false hex (fun _ => rfl) (fun _ => rfl)
    exact ⟨w, by simp [eval, hv, hw], hwt⟩
  -- 22. match(網羅しない)
  · intro Γ _ s arms ta hs hne _ Φ ρ _ _ t ht
    simp [wtR, hs, hne] at ht
  -- 23. match(scrutinee が不適格)
  · intro Γ _ s arms hs _ Φ ρ _ _ t ht
    simp [wtR, hs] at ht
  -- 24. ブロック(適格)
  · intro Γ _ stmts e Γ' hst ihst ihe Φ ρ hΓ hΦ t ht
    simp only [wtR, hst] at ht
    obtain ⟨ρ', hρ', hΓ'⟩ := ihst Φ ρ hΓ hΦ Γ' hst
    obtain ⟨w, hw, hwt⟩ := ihe Φ ρ' hΓ' hΦ t ht
    exact ⟨w, by simp [eval, hρ', hw], hwt⟩
  -- 25. ブロック(let の列が不適格)
  · intro Γ _ stmts e hst _ Φ ρ _ _ t ht
    simp [wtR, hst] at ht
  -- 26. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 Φ ρ _ _ t ht
    rw [wtR.eq_def] at ht
    split at ht
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ _ rfl).elim
      | exact (h7 _ _ _ _ rfl).elim
      | exact (h8 _ _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | exact (h10 _ _ _ rfl).elim
      | (cases ht; done)
  -- 27. 腕(パターンが型に合わない)
  · intro Γ ts p g b hp p' g' b' heq Φ ρ _ _ t ht
    cases heq
    rw [wtArmR_mk, hp] at ht
    simp at ht
  -- 28. 腕(ガード無し)
  · intro Γ ts p b bts hp ihb p' g' b' heq Φ ρ hΓ hΦ t ht v hv bs hm
    cases heq
    rw [wtArmR_mk, hp] at ht
    simp only at ht
    have hΓ' : Γ.extVals bts = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb Φ (ρ.extVals bs) hΓ' hΦ t ht, ?_⟩
    intro g' hg
    cases hg
  -- 29. 腕(ガードが Bool)
  · intro Γ ts p b bts hp g hg ihg ihb p' g' b' heq Φ ρ hΓ hΦ t ht v hv bs hm
    cases heq
    rw [wtArmR_mk, hp] at ht
    simp only [hg] at ht
    have hΓ' : Γ.extVals bts = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb Φ (ρ.extVals bs) hΓ' hΦ t ht, ?_⟩
    intro g'' hg''
    cases hg''
    obtain ⟨c, hc, hct⟩ := ihg Φ (ρ.extVals bs) hΓ' hΦ .bool hg
    cases c with
    | nat => simp [Val.ty] at hct
    | bool cb => exact ⟨cb, hc⟩
  -- 30. 腕(ガードが Bool でない)
  · intro Γ ts p b bts hp g hno _ p' g' b' heq Φ ρ _ _ t ht
    cases heq
    rw [wtArmR_mk, hp] at ht
    simp only at ht
    first
      | (cases ht; done)
      | (split at ht <;> simp_all)
  -- 31. 実引数の列(空)
  · intro Γ Φ ρ _ _ tys h
    rw [wtArgs.eq_1, Option.some.injEq] at h
    subst h
    exact ⟨[], evalArgs.eq_1 T Φ ρ, rfl⟩
  -- 32. 実引数の列(位置引数、適格)
  · intro Γ e rest tr tys hrest he ihe ihrest Φ ρ hΓ hΦ tys' h
    rw [wtArgs_pos] at h
    simp only [he, hrest, Option.some.injEq] at h
    subst h
    obtain ⟨v, hv, hvt⟩ := ihe Φ ρ hΓ hΦ tr he
    obtain ⟨vals, hvals, hvts⟩ := ihrest Φ ρ hΓ hΦ tys hrest
    exact ⟨(none, v) :: vals, by rw [evalArgs_pos]; simp [hv, hvals], by simp [mapArg, hvt, hvts]⟩
  -- 33. 実引数の列(位置引数、不適格)
  · intro Γ e rest hno _ _ Φ ρ _ _ tys h
    rw [wtArgs_pos] at h
    cases hwe : wtR T Γ e with
    | none => simp [hwe] at h
    | some tr =>
      cases hwr : wtArgs T Γ rest with
      | none => simp [hwe, hwr] at h
      | some tys' => exact (hno tr tys' hwe hwr).elim
  -- 34. 実引数の列(名前付き引数、適格)
  · intro Γ n e rest tr tys hrest he ihe ihrest Φ ρ hΓ hΦ tys' h
    rw [wtArgs_named] at h
    simp only [he, hrest, Option.some.injEq] at h
    subst h
    obtain ⟨v, hv, hvt⟩ := ihe Φ ρ hΓ hΦ tr he
    obtain ⟨vals, hvals, hvts⟩ := ihrest Φ ρ hΓ hΦ tys hrest
    exact ⟨(some n, v) :: vals, by rw [evalArgs_named]; simp [hv, hvals], by simp [mapArg, hvt, hvts]⟩
  -- 35. 実引数の列(名前付き引数、不適格)
  · intro Γ n e rest hno _ _ Φ ρ _ _ tys h
    rw [wtArgs_named] at h
    cases hwe : wtR T Γ e with
    | none => simp [hwe] at h
    | some tr =>
      cases hwr : wtArgs T Γ rest with
      | none => simp [hwe, hwr] at h
      | some tys' => exact (hno tr tys' hwe hwr).elim
  -- 36. 腕の列(空)
  · intro Γ ts Φ ρ _ _ t ht
    simp [wtArmsR] at ht
  -- 37. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ Φ ρ _ _ t ht
    simp [wtArmsR, h] at ht
  -- 38. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 Φ ρ hΓ hΦ t ht v hv sawT sawF hex hT hF
    simp only [wtArmsR, h1, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
    cases g with
    | some g => simp [exhaustiveFrom] at hex
    | none =>
      cases p with
      | wild sp =>
        obtain ⟨w, hw, hwt⟩ := (ih3 (.wild sp) none b rfl Φ ρ hΓ hΦ t1 h1 v hv [] rfl).1
        exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
      | bind sp x =>
        obtain ⟨w, hw, hwt⟩ := (ih3 (.bind sp x) none b rfl Φ ρ hΓ hΦ t1 h1 v hv [(x, v)] rfl).1
        exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
      | lit sp l =>
        cases l with
        | bool lb =>
          cases lb with
          | true =>
            rw [exhaustiveFrom_true] at hex
            simp only [exhaustiveFrom, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at hex
            obtain ⟨hts, hsf⟩ := hex
            subst hts
            cases v with
            | nat => simp [Val.ty] at hv
            | bool c =>
              cases c with
              | false => exact absurd (hF rfl) (by simp [hsf])
              | true =>
                obtain ⟨w, hw, hwt⟩ := (ih3 (.lit sp (.bool true)) none b rfl Φ ρ hΓ hΦ t1 h1 (.bool true) hv [] rfl).1
                exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
          | false =>
            rw [exhaustiveFrom_false] at hex
            simp only [exhaustiveFrom, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at hex
            obtain ⟨hts, hst⟩ := hex
            subst hts
            cases v with
            | nat => simp [Val.ty] at hv
            | bool c =>
              cases c with
              | true => exact absurd (hT rfl) (by simp [hst])
              | false =>
                obtain ⟨w, hw, hwt⟩ := (ih3 (.lit sp (.bool false)) none b rfl Φ ρ hΓ hΦ t1 h1 (.bool false) hv [] rfl).1
                exact ⟨w, by simp [evalArms_cons, matchPat, hw], hwt⟩
        | nat n => rw [exhaustiveFrom_nat] at hex; simp [exhaustiveFrom] at hex
        | str s => simp [exhaustiveFrom] at hex
        | unit => simp [exhaustiveFrom] at hex
  -- 39. 腕の列(先頭の腕と残りの型が同じ)
  · intro Γ ts arm head tail t2 h2 h1 ih3 ih2 Φ ρ hΓ hΦ t ht v hv sawT sawF hex hT hF
    rw [wtArmsR.eq_def] at ht
    simp only [h1, h2, ite_true, Option.some.injEq] at ht
    subst ht
    obtain ⟨p, g, b⟩ := arm
    cases hm : matchPat p v with
    | some bs =>
      obtain ⟨⟨w, hw, hwt⟩, hguard⟩ := ih3 p g b rfl Φ ρ hΓ hΦ t2 h1 v hv bs hm
      cases g with
      | none => exact ⟨w, by simp [evalArms_cons, hm, hw], hwt⟩
      | some g =>
        obtain ⟨c, hc⟩ := hguard g rfl
        cases c with
        | true => exact ⟨w, by simp [evalArms_cons, hm, hc, hw], hwt⟩
        | false =>
          rw [exhaustiveFrom_guard] at hex
          obtain ⟨w', hw', hwt'⟩ := ih2 Φ ρ hΓ hΦ t2 h2 v hv sawT sawF hex hT hF
          exact ⟨w', by simp [evalArms_cons, hm, hc, hw'], hwt'⟩
    | none =>
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          ∃ w, evalArms T Φ ρ v (Arm.mk p g b :: head :: tail) = some w ∧ w.ty = t2 := by
        intro sawT' sawF' hex' hT' hF'
        obtain ⟨w', hw', hwt'⟩ := ih2 Φ ρ hΓ hΦ t2 h2 v hv sawT' sawF' hex' hT' hF'
        exact ⟨w', by simp [evalArms_cons, hm, hw'], hwt'⟩
      cases g with
      | some g =>
        rw [exhaustiveFrom_guard] at hex
        exact step sawT sawF hex hT hF
      | none =>
        cases p with
        | wild => simp [matchPat] at hm
        | bind => simp [matchPat] at hm
        | lit sp l =>
          cases l with
          | bool lb =>
            cases lb with
            | true =>
              rw [exhaustiveFrom_true] at hex
              simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hex
              have hne : v ≠ .bool true := by
                intro h
                subst h
                simp [matchPat] at hm
              rcases hex with ⟨hts, hsf⟩ | hrest
              · subst hts
                cases v with
                | nat => simp [Val.ty] at hv
                | bool c =>
                  cases c with
                  | true => exact absurd rfl hne
                  | false => exact absurd (hF rfl) (by simp [hsf])
              · exact step true sawF hrest (fun h => absurd h hne) hF
            | false =>
              rw [exhaustiveFrom_false] at hex
              simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hex
              have hne : v ≠ .bool false := by
                intro h
                subst h
                simp [matchPat] at hm
              rcases hex with ⟨hts, hst⟩ | hrest
              · subst hts
                cases v with
                | nat => simp [Val.ty] at hv
                | bool c =>
                  cases c with
                  | false => exact absurd rfl hne
                  | true => exact absurd (hT rfl) (by simp [hst])
              · exact step sawT true hrest hT (fun h => absurd h hne)
          | nat n =>
            rw [exhaustiveFrom_nat] at hex
            exact step sawT sawF hex hT hF
          | str s => exact step sawT sawF (by simpa [exhaustiveFrom] using hex) hT hF
          | unit => exact step sawT sawF (by simpa [exhaustiveFrom] using hex) hT hF
  -- 40. 腕の列(先頭の腕と残りの型が違う)
  · intro Γ ts arm t1 head tail h1 t2 hne h2 _ _ Φ ρ _ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2, hne] at ht
  -- 41. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ Φ ρ _ _ t ht
    rw [wtArmsR.eq_def] at ht
    simp [h1, h2] at ht
  -- 42. let の列(空)
  · intro Γ Φ ρ hΓ _ Γ' h
    simp only [wtStmtsR, Option.some.injEq] at h
    subst h
    exact ⟨ρ, rfl, hΓ⟩
  -- 43. let の列(適格)
  · intro Γ _ x ty v rest ta hv t hann ihv ihrest Φ ρ hΓ hΦ Γ' h
    simp only [wtStmtsR, hv, hann] at h
    obtain ⟨w, hw, hwt⟩ := ihv Φ ρ hΓ hΦ ta hv
    have ht : t = ta := annot_eq hann
    subst ht
    obtain ⟨ρ', hρ', hΓ'⟩ := ihrest Φ (ρ.ext x (.val w)) (by rw [SEnv.ctx_ext, hΓ]; simp [SVal.ty, hwt]) hΦ Γ' h
    exact ⟨ρ', by simp [evalStmts_cons, hw, hρ'], hΓ'⟩
  -- 44. let の列(注釈が合わない)
  · intro Γ _ x ty v rest ta hv hann _ Φ ρ _ _ Γ' h
    simp [wtStmtsR, hv, hann] at h
  -- 45. let の列(値が不適格)
  · intro Γ _ x ty v rest hv _ Φ ρ _ _ Γ' h
    simp [wtStmtsR, hv] at h

/-- **runtime の全域性**: 宣言表 `T` と文脈 `Γ` で適格な、呼出しを含む Surface AST の式は、対応する環境(`Γ = ρ.ctx`)と署名を守る関数環境
(`Φ.Respects T.Δ`)で必ず値を持ち、その型は型付けの型。 -/
theorem eval_total {T : Table} {Γ : SCtx} {e : Expr} {t : NaruSem.Ty} (h : wtR T Γ e = some t) (Φ : NaruSem.Call.FEnv) (ρ : SEnv)
    (hρ : Γ = ρ.ctx) (hΦ : Φ.Respects T.Δ) : ∃ v, eval T Φ ρ e = some v ∧ v.ty = t :=
  (wtR_total_all T).1 Γ e Φ ρ hρ hΦ t h

/-- 実引数の列(構文解析の順、名前付きは名前つき)の全域性: 型の列に対して同じ名前の印の値の列を持つ。 -/
theorem evalArgs_total {T : Table} {Γ : SCtx} {args : List Arg} {tys : List (Option String × NaruSem.Ty)} (h : wtArgs T Γ args = some tys)
    (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (hρ : Γ = ρ.ctx) (hΦ : Φ.Respects T.Δ) :
    ∃ vals, evalArgs T Φ ρ args = some vals ∧ vals.map (mapArg Val.ty) = tys :=
  (wtR_total_all T).2.2.2.2 Γ args Φ ρ hρ hΦ tys h

/-- **runtime の一意性**: 評価関係(`Eval T Φ ρ e v := eval T Φ ρ e = some v`)の結果は一意。 -/
theorem Eval_unique {T : Table} {Φ : NaruSem.Call.FEnv} {ρ : SEnv} {e : Expr} {v w : Val} (hv : Eval T Φ ρ e v) (hw : Eval T Φ ρ e w) : v = w := by
  unfold Eval at hv hw
  rw [hv] at hw
  exact Option.some.inj hw

/-! ## 評価の単調性 -/

/-- 環境の拡張: 束縛の有無(局所名が大域名を隠すこと)は同じで、`ρ₁` の値の束縛はすべて `ρ₂` にもある(命題の束縛は値の束縛に変わってよい)。 -/
def SEnv.Sub (ρ₁ ρ₂ : SEnv) : Prop :=
  (∀ x, (ρ₂ x).isSome = (ρ₁ x).isSome) ∧ (∀ x v, ρ₁ x = some (.val v) → ρ₂ x = some (.val v))

theorem SEnv.Sub.refl (ρ : SEnv) : SEnv.Sub ρ ρ := ⟨fun _ => rfl, fun _ _ h => h⟩

theorem SEnv.Sub.ext {ρ₁ ρ₂ : SEnv} (h : SEnv.Sub ρ₁ ρ₂) (x : String) (s : SVal) : SEnv.Sub (ρ₁.ext x s) (ρ₂.ext x s) := by
  refine ⟨?_, ?_⟩
  · intro y
    simp only [NaruSem.SEnv.ext]
    by_cases hyx : y = x
    · simp [hyx]
    · simp only [hyx, ite_false]
      exact h.1 y
  · intro y v hy
    simp only [NaruSem.SEnv.ext] at hy ⊢
    by_cases hyx : y = x
    · simp only [hyx, ite_true] at hy ⊢
      exact hy
    · simp only [hyx, ite_false] at hy ⊢
      exact h.2 y v hy

theorem SEnv.Sub.extVals {ρ₁ ρ₂ : SEnv} (h : SEnv.Sub ρ₁ ρ₂) (bs : List (String × Val)) : SEnv.Sub (ρ₁.extVals bs) (ρ₂.extVals bs) := by
  induction bs generalizing ρ₁ ρ₂ with
  | nil => exact h
  | cons xv rest ih =>
    obtain ⟨x, v⟩ := xv
    exact ih (h.ext x (.val v))

/-- 束縛の有無が同じなら、経路の頭の隠蔽も同じ。 -/
theorem headBound_sub {ρ₁ ρ₂ : SEnv} (h : SEnv.Sub ρ₁ ρ₂) (path : List String) : headBound ρ₂ path = headBound ρ₁ path := by
  match path with
  | [x] => simp only [headBound]; exact h.1 x
  | [] => rfl
  | _ :: _ :: _ => rfl

theorem ufcs_sub {ρ₁ ρ₂ : SEnv} (h : SEnv.Sub ρ₁ ρ₂) (T : Table) (m : String) : ufcs T ρ₂ m = ufcs T ρ₁ m := by
  have hs := h.1 m
  simp only [ufcs]
  cases h1 : ρ₁ m <;> cases h2 : ρ₂ m <;> simp_all

/-- **評価の単調性**: 値の束縛と束縛の有無を保つ環境の拡張は、定まっていた値を変えない(命題に束ねた名前に値を足しても、既に値のある式の評価は同じ)。
呼出しの評価は環境の値の束縛(実引数)と束縛の有無(隠蔽)だけに依る。 -/
theorem eval_mono_all (T : Table) (Φ : NaruSem.Call.FEnv) :
    (∀ (ρ : SEnv) (e : Expr), ∀ ρ₂, SEnv.Sub ρ ρ₂ → ∀ v, eval T Φ ρ e = some v → eval T Φ ρ₂ e = some v) ∧
    (∀ (ρ : SEnv) (stmts : List Stmt), ∀ ρ₂, SEnv.Sub ρ ρ₂ → ∀ ρ', evalStmts T Φ ρ stmts = some ρ' →
        ∃ ρ₂', evalStmts T Φ ρ₂ stmts = some ρ₂' ∧ SEnv.Sub ρ' ρ₂') ∧
    (∀ (ρ : SEnv) (v : Val) (arms : List Arm), ∀ ρ₂, SEnv.Sub ρ ρ₂ → ∀ w, evalArms T Φ ρ v arms = some w → evalArms T Φ ρ₂ v arms = some w) ∧
    (∀ (ρ : SEnv) (args : List Arg), ∀ ρ₂, SEnv.Sub ρ ρ₂ → ∀ vals, evalArgs T Φ ρ args = some vals → evalArgs T Φ ρ₂ args = some vals) := by
  apply eval.mutual_induct T Φ
  -- 1. Nat のリテラル
  · intro ρ _ n ρ₂ _ v h
    simpa [eval] using h
  -- 2. Bool のリテラル
  · intro ρ _ b ρ₂ _ v h
    simpa [eval] using h
  -- 3. 局所名(値に束ねられている)
  · intro ρ _ x w hx ρ₂ hsub v h
    rw [eval.eq_def] at h ⊢
    simp only [hx, hsub.2 x w hx] at h ⊢
    exact h
  -- 4. 局所名(値に束ねられていない)
  · intro ρ _ x hno ρ₂ _ v h
    rw [eval.eq_def] at h
    simp only at h
    first
      | (cases h; done)
      | (split at h
         · rename_i w hx
           exact (hno w hx).elim
         · cases h)
  -- 5. 呼出し(頭が局所名)
  · intro ρ _ _ path args hb ρ₂ _ v h
    rw [eval.eq_def] at h
    simp [hb] at h
  -- 6. 呼出し(実引数に値)
  · intro ρ _ _ path args hnb vals hvals ih4 ρ₂ hsub v h
    simp only [Bool.not_eq_true] at hnb
    have hnb₂ : headBound ρ₂ path = false := by rw [headBound_sub hsub]; exact hnb
    rw [eval.eq_def] at h ⊢
    simp only [hnb, hnb₂, Bool.false_eq_true, ite_false, hvals, ih4 ρ₂ hsub vals hvals] at h ⊢
    exact h
  -- 7. 呼出し(実引数に値が無い)
  · intro ρ _ _ path args hnb hvals _ ρ₂ _ v h
    simp only [Bool.not_eq_true] at hnb
    rw [eval.eq_def] at h
    simp [hnb, hvals] at h
  -- 8. 二項演算(両辺に値)
  · intro ρ _ op l r k a b hr hl hk ihl ihr ρ₂ hsub v h
    simp only [eval, hk, hl, hr] at h
    simp [eval, hk, ihl ρ₂ hsub a hl, ihr ρ₂ hsub b hr, h]
  -- 9. 二項演算(値が無い)
  · intro ρ _ op l r hno _ _ ρ₂ _ v h
    simp only [eval] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 10. `!`(Bool の値)
  · intro ρ _ a x ha iha ρ₂ hsub v h
    simp only [eval, ha, ite_true] at h
    simp [eval, iha ρ₂ hsub _ ha, h]
  -- 11. `!`(値が Bool でない)
  · intro ρ _ a hno _ ρ₂ _ v h
    simp only [eval, ite_true] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 12. 対象外の単項演算子
  · intro ρ _ op a hne ρ₂ _ v h
    simp [eval, hne] at h
  -- 13. UFCS(受け手と実引数に値)
  · intro ρ _ r m args hu w vals hvals hr ihr ih4 ρ₂ hsub v h
    have hu₂ : ufcs T ρ₂ m = true := by rw [ufcs_sub hsub]; exact hu
    rw [eval.eq_def] at h ⊢
    simp only [hu, hu₂, ite_true, hr, hvals, ihr ρ₂ hsub w hr, ih4 ρ₂ hsub vals hvals] at h ⊢
    exact h
  -- 14. UFCS(受け手か実引数に値が無い)
  · intro ρ _ r m args hu hno _ _ ρ₂ _ v h
    rw [eval.eq_def] at h
    simp only [hu, ite_true] at h
    cases hwr : eval T Φ ρ r with
    | none => simp at h
    | some w =>
      cases hwa : evalArgs T Φ ρ args with
      | none => simp at h
      | some vals => exact (hno w vals hwr hwa).elim
  -- 15. min / max(値あり)
  · intro ρ _ r m hnu a k x y ha hr hm ihr iha ρ₂ hsub v h
    simp only [Bool.not_eq_true] at hnu
    have hnu₂ : ufcs T ρ₂ m = false := by rw [ufcs_sub hsub]; exact hnu
    rw [eval.eq_def] at h ⊢
    simp only [hnu, hnu₂, Bool.false_eq_true, ite_false, hm, hr, ha, ihr ρ₂ hsub _ hr, iha ρ₂ hsub _ ha] at h ⊢
    exact h
  -- 16. min / max(値なし)
  · intro ρ _ r m hnu a hno _ _ ρ₂ _ v h
    simp only [Bool.not_eq_true] at hnu
    rw [eval.eq_def] at h
    simp only [hnu, Bool.false_eq_true, ite_false] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 17. メソッド(位置引数 1 つでない)
  · intro ρ _ r m args hnu hne ρ₂ _ v h
    simp only [Bool.not_eq_true] at hnu
    rw [eval.eq_def] at h
    simp only [hnu, Bool.false_eq_true, ite_false] at h
    cases args with
    | nil => simp at h
    | cons a rest =>
      cases a with
      | named n e => simp at h
      | pos e =>
        cases rest with
        | nil => exact (hne e rfl).elim
        | cons b rest' => simp at h
  -- 18. if(真)
  · intro ρ _ c t e hc ihc iht ρ₂ hsub v h
    simp only [eval, hc] at h
    simp [eval, ihc ρ₂ hsub _ hc, iht ρ₂ hsub v h]
  -- 19. if(偽)
  · intro ρ _ c t e hc ihc ihe ρ₂ hsub v h
    simp only [eval, hc] at h
    simp [eval, ihc ρ₂ hsub _ hc, ihe ρ₂ hsub v h]
  -- 20. if(条件に Bool の値が無い)
  · intro ρ _ c t e hnt hnf _ ρ₂ _ v h
    simp only [eval] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 21. match(scrutinee に値)
  · intro ρ _ s arms w hs ihs iharms ρ₂ hsub v h
    simp only [eval, hs] at h
    simp [eval, ihs ρ₂ hsub w hs, iharms ρ₂ hsub v h]
  -- 22. match(scrutinee に値が無い)
  · intro ρ _ s arms hs _ ρ₂ _ v h
    simp [eval, hs] at h
  -- 23. ブロック(let の列に値)
  · intro ρ _ stmts e ρ' hst ihst ihe ρ₂ hsub v h
    simp only [eval, hst] at h
    obtain ⟨ρ₂', hρ₂', hsub'⟩ := ihst ρ₂ hsub ρ' hst
    simp [eval, hρ₂', ihe ρ₂' hsub' v h]
  -- 24. ブロック(let の列に値が無い)
  · intro ρ _ stmts e hst _ ρ₂ _ v h
    simp [eval, hst] at h
  -- 25. 対象外の構文
  · intro e ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ρ₂ _ v h
    rw [eval.eq_def] at h
    split at h
    all_goals first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ rfl).elim
      | exact (h3 _ _ rfl).elim
      | exact (h4 _ _ _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ _ rfl).elim
      | exact (h7 _ _ _ _ rfl).elim
      | exact (h8 _ _ _ _ rfl).elim
      | exact (h9 _ _ _ rfl).elim
      | exact (h10 _ _ _ rfl).elim
      | (cases h; done)
  -- 26. 実引数の列(空)
  · intro ρ ρ₂ _ vals h
    rw [evalArgs.eq_1] at h ⊢
    exact h
  -- 27. 実引数の列(位置引数、値あり)
  · intro ρ e rest w vals hrest he ihe ihrest ρ₂ hsub vals' h
    rw [evalArgs_pos] at h ⊢
    simp only [he, hrest] at h
    simp [ihe ρ₂ hsub w he, ihrest ρ₂ hsub vals hrest, h]
  -- 28. 実引数の列(位置引数、値なし)
  · intro ρ e rest hno _ _ ρ₂ _ vals h
    rw [evalArgs_pos] at h
    cases hwe : eval T Φ ρ e with
    | none => simp at h
    | some w =>
      cases hwr : evalArgs T Φ ρ rest with
      | none => simp at h
      | some vals' => exact (hno w vals' hwe hwr).elim
  -- 29. 実引数の列(名前付き引数、値あり)
  · intro ρ n e rest w vals hrest he ihe ihrest ρ₂ hsub vals' h
    rw [evalArgs_named] at h ⊢
    simp only [he, hrest] at h
    simp [ihe ρ₂ hsub w he, ihrest ρ₂ hsub vals hrest, h]
  -- 30. 実引数の列(名前付き引数、値なし)
  · intro ρ n e rest hno _ _ ρ₂ _ vals h
    rw [evalArgs_named] at h
    cases hwe : eval T Φ ρ e with
    | none => simp at h
    | some w =>
      cases hwr : evalArgs T Φ ρ rest with
      | none => simp at h
      | some vals' => exact (hno w vals' hwe hwr).elim
  -- 31. 腕の列(空)
  · intro ρ v ρ₂ _ w h
    simp [evalArms] at h
  -- 32. 腕の列(一致しない)
  · intro ρ v p g b rest hm ih ρ₂ hsub w h
    rw [evalArms_cons, hm] at h ⊢
    exact ih ρ₂ hsub w h
  -- 33. 腕の列(一致、ガード無し)
  · intro ρ v p b rest bs hm ih ρ₂ hsub w h
    rw [evalArms_cons, hm] at h ⊢
    exact ih (ρ₂.extVals bs) (hsub.extVals bs) w h
  -- 34. 腕の列(一致、ガード真)
  · intro ρ v p b rest bs hm g hg ihg ihb ρ₂ hsub w h
    rw [evalArms_cons, hm] at h ⊢
    simp only [hg] at h
    simp only [ihg (ρ₂.extVals bs) (hsub.extVals bs) _ hg]
    exact ihb (ρ₂.extVals bs) (hsub.extVals bs) w h
  -- 35. 腕の列(一致、ガード偽)
  · intro ρ v p b rest bs hm g hg ihg ihrest ρ₂ hsub w h
    rw [evalArms_cons, hm] at h ⊢
    simp only [hg] at h
    simp only [ihg (ρ₂.extVals bs) (hsub.extVals bs) _ hg]
    exact ihrest ρ₂ hsub w h
  -- 36. 腕の列(一致、ガードに Bool の値が無い)
  · intro ρ v p b rest bs hm g hnt hnf _ ρ₂ _ w h
    rw [evalArms_cons, hm] at h
    simp only at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 37. let の列(空)
  · intro ρ ρ₂ hsub ρ' h
    simp only [evalStmts, Option.some.injEq] at h
    subst h
    exact ⟨ρ₂, rfl, hsub⟩
  -- 38. let の列(値あり)
  · intro ρ _ x ty v rest w hv ihv ihrest ρ₂ hsub ρ' h
    rw [evalStmts_cons, hv] at h
    obtain ⟨ρ₂', hρ₂', hsub'⟩ := ihrest (ρ₂.ext x (.val w)) (hsub.ext x (.val w)) ρ' h
    exact ⟨ρ₂', by rw [evalStmts_cons, ihv ρ₂ hsub w hv]; exact hρ₂', hsub'⟩
  -- 39. let の列(値なし)
  · intro ρ _ x ty v rest hv _ ρ₂ _ ρ' h
    rw [evalStmts_cons, hv] at h
    cases h

theorem eval_mono {T : Table} {Φ : NaruSem.Call.FEnv} {ρ ρ₂ : SEnv} (hsub : SEnv.Sub ρ ρ₂) {e : Expr} {v : Val} (h : eval T Φ ρ e = some v) :
    eval T Φ ρ₂ e = some v :=
  (eval_mono_all T Φ).1 ρ e ρ₂ hsub v h

theorem evalArgs_mono {T : Table} {Φ : NaruSem.Call.FEnv} {ρ ρ₂ : SEnv} (hsub : SEnv.Sub ρ ρ₂) {args : List Arg}
    {vals : List (Option String × Val)} (h : evalArgs T Φ ρ args = some vals) : evalArgs T Φ ρ₂ args = some vals :=
  (eval_mono_all T Φ).2.2.2 ρ args ρ₂ hsub vals h

/-! ## 論理の位置の式は Nat の値に評価されない -/

/-- 評価の環境 `ρe` と spec の環境 `ρ` の対応: `ρ` の値の束縛と束縛の有無は `ρe` にもあり(`SEnv.Sub`)、`ρ` が命題に束ねた名前は `ρe` で
Nat の値を持たない。 -/
def Agree (ρe ρ : SEnv) : Prop :=
  SEnv.Sub ρ ρe ∧ (∀ x (P : Prop) n, ρ x = some (.prop P) → ρe x ≠ some (.val (.nat n)))

theorem Agree.refl (ρ : SEnv) : Agree ρ ρ := by
  refine ⟨SEnv.Sub.refl ρ, ?_⟩
  intro x P n hx h
  rw [hx] at h
  cases h

theorem Agree.sub {ρe ρ : SEnv} (h : Agree ρe ρ) : SEnv.Sub ρ ρe := h.1

theorem Agree.ext_val {ρe ρ : SEnv} (h : Agree ρe ρ) (x : String) (w : Val) : Agree (ρe.ext x (.val w)) (ρ.ext x (.val w)) := by
  refine ⟨h.1.ext x (.val w), ?_⟩
  intro y P n hy
  simp only [NaruSem.SEnv.ext] at hy ⊢
  by_cases hyx : y = x
  · simp [hyx] at hy
  · simp only [hyx, ite_false] at hy ⊢
    exact h.2 y P n hy

theorem Agree.ext_prop {ρe ρ : SEnv} (h : Agree ρe ρ) (x : String) (w : Val) (hw : ∀ n, w ≠ .nat n) (P : Prop) :
    Agree (ρe.ext x (.val w)) (ρ.ext x (.prop P)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro y
    simp only [NaruSem.SEnv.ext]
    by_cases hyx : y = x
    · simp [hyx]
    · simp only [hyx, ite_false]
      exact h.1.1 y
  · intro y u hy
    simp only [NaruSem.SEnv.ext] at hy ⊢
    by_cases hyx : y = x
    · simp [hyx] at hy
    · simp only [hyx, ite_false] at hy ⊢
      exact h.1.2 y u hy
  · intro y Q n hy
    simp only [NaruSem.SEnv.ext] at hy ⊢
    by_cases hyx : y = x
    · simp only [hyx, ite_true]
      intro heq
      exact hw n (SVal.val.inj (Option.some.inj heq))
    · simp only [hyx, ite_false] at hy ⊢
      exact h.2 y Q n hy

theorem Agree.extVals {ρe ρ : SEnv} (h : Agree ρe ρ) (bs : List (String × Val)) : Agree (ρe.extVals bs) (ρ.extVals bs) := by
  induction bs generalizing ρe ρ with
  | nil => exact h
  | cons xv rest ih =>
    obtain ⟨x, v⟩ := xv
    exact ih (h.ext_val x v)

/-- 論理・等値・比較の二項演算の評価は Nat の値にならない。 -/
theorem eval_binop_not_nat (T : Table) (Φ : NaruSem.Call.FEnv) (ρe : SEnv) (sp : Span) (op : String) (l r : Expr) (k : BinOp)
    (hk : BinOp.ofString? op = some k) (hna : ∀ j, k ≠ .arith j) (n : Nat) : eval T Φ ρe (.binop sp op l r) ≠ some (.nat n) := by
  simp only [eval, hk]
  cases eval T Φ ρe l with
  | none => simp
  | some a =>
    cases eval T Φ ρe r with
    | none => simp
    | some b =>
      simp only
      exact BinOp.apply_not_nat k hna a b n

/-- **論理の位置の式は Nat の値に評価されない**: `Sem` の導出のある式は、対応する評価の環境で Nat の値を持たない(`==` / `!=` の 2 つの規則の排他性)。
fn / input の呼出しの意味は Bool の結果(`callVal` / `ufcsVal`)、spec 宣言の呼出しは値を持たない(署名が fn / input でないので `callVal` は `none`)。 -/
theorem Sem_not_nat {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv} {ρ : SEnv} {e : Expr} {P : Prop} (h : Sem T Φ Ψ ρ e P) :
    ∀ ρe, Agree ρe ρ → ∀ n, eval T Φ ρe e ≠ some (.nat n) := by
  induction h with
  | lit => intro ρe _ n; simp [eval]
  | @varVal _ _ x b hx =>
    intro ρe ha n
    have hb : ρe x = some (.val (.bool b)) := ha.1.2 x _ hx
    rw [eval.eq_def]
    simp [hb]
  | @varProp _ _ x _ hx =>
    intro ρe ha n
    rw [eval.eq_def]
    simp only
    cases hy : ρe x with
    | none => simp
    | some s =>
      cases s with
      | prop _ => simp
      | val v =>
        cases v with
        | nat m => exact absurd hy (ha.2 x _ m hx)
        | bool _ => simp
  | callVal hs hr hd hf ha harr hv =>
    intro ρe hag n
    rw [eval.eq_def]
    simp only [headBound_sub hag.sub, hs, Bool.false_eq_true, ite_false, evalArgs_mono hag.sub ha, callVal, hr, hd, hf, harr, hv]
      <;> simp
  | callSpec hs hr hd hF ha harr =>
    intro ρe hag n
    rw [eval.eq_def]
    simp only [headBound_sub hag.sub, hs, Bool.false_eq_true, ite_false]
    cases evalArgs T Φ ρe _ with
    | none => simp
    | some vals' => simp [callVal, hr, hd, DeclSig.value?]
  | ufcsVal hu hr hd hf hrv ha harr hv =>
    intro ρe hag n
    rw [eval.eq_def]
    simp only [ufcs_sub hag.sub, hu, ite_true, eval_mono hag.sub hrv, evalArgs_mono hag.sub ha, callVal, hr, hd, hf, harr, hv]
      <;> simp
  | ufcsSpec hu hr hd hF hrv ha harr =>
    intro ρe hag n
    rw [eval.eq_def]
    simp only [ufcs_sub hag.sub, hu, ite_true, eval_mono hag.sub hrv, evalArgs_mono hag.sub ha]
    simp [callVal, hr, hd, DeclSig.value?]
  | logic hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat T Φ ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | eqNat hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat T Φ ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | eqForm hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat T Φ ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | cmpNat hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat T Φ ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | cmpBool hk _ _ =>
    intro ρe _ n
    exact eval_binop_not_nat T Φ ρe _ _ _ _ _ hk (fun _ h => by cases h) n
  | not _ =>
    intro ρe _ n
    simp only [eval, ite_true]
    split <;> simp
  | ite _ _ _ _ iht ihe =>
    intro ρe ha n
    simp only [eval]
    split
    · exact iht ρe ha n
    · exact ihe ρe ha n
    · simp
  | blockTail _ ih =>
    intro ρe ha n
    rw [eval_block_nil]
    exact ih ρe ha n
  | blockLetVal hp hv _ ih =>
    intro ρe ha n
    rw [eval_block_cons, eval_mono ha.sub hv]
    exact ih (ρe.ext _ (.val _)) (ha.ext_val _ _) n
  | blockLetProp hp _ _ ihv ih =>
    intro ρe ha n
    rw [eval_block_cons]
    cases hw : eval T Φ ρe _ with
    | none => simp
    | some w =>
      simp only
      exact ih (ρe.ext _ (.val w)) (ha.ext_prop _ w (fun m heq => ihv ρe ha m (heq ▸ hw)) _) n
  | matchSkip hs hp _ ih =>
    intro ρe ha n
    have hrest := ih ρe ha n
    rw [eval_match _ _ _ _ _ _ _ (eval_mono ha.sub hs)] at hrest ⊢
    rw [evalArms_cons, hp]
    exact hrest
  | matchHit hs hp _ ih =>
    intro ρe ha n
    rw [eval_match _ _ _ _ _ _ _ (eval_mono ha.sub hs), evalArms_cons, hp]
    exact ih (ρe.extVals _) (ha.extVals _) n
  | matchGuard hs hp _ _ _ ihg ihb ihr =>
    intro ρe ha n
    have hrest := ihr ρe ha n
    rw [eval_match _ _ _ _ _ _ _ (eval_mono ha.sub hs)] at hrest ⊢
    rw [evalArms_cons, hp]
    simp only
    cases hg : eval T Φ (ρe.extVals _) _ with
    | none => simp
    | some c =>
      cases c with
      | nat m => exact absurd hg (ihg (ρe.extVals _) (ha.extVals _) m)
      | bool cb =>
        cases cb with
        | true => exact ihb (ρe.extVals _) (ha.extVals _) n
        | false => exact hrest
  | quantNil _ => intro ρe _ n; simp [eval]
  | forallCons _ _ => intro ρe _ n; simp [eval]
  | existsCons _ _ => intro ρe _ n; simp [eval]

/-! ## spec の意味の存在 -/

/-- `wtS` / `wtStmtsS` / `wtArmsS` / `wtArmS` の関数帰納法。値の位置(算術・比較・Nat の等値・`min` / `max`・scrutinee・値の `let`・実引数)は
runtime の全域性 `eval_total` / `evalArgs_total` で値を得る。fn / input の呼出しは署名を守る関数環境から Bool の結果を得て命題に写し、
spec 宣言の呼出しは定義された spec 宣言の環境から意味を得る。 -/
theorem Sem_exists_all (T : Table) :
    (∀ (Γ : SCtx) (e : Expr), ∀ (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (ρ : SEnv), Γ = ρ.ctx → Φ.Respects T.Δ → Ψ.Defined T.Δ →
        ∀ τ, wtS T Γ e = some τ → τ.isForm = true → ∃ P, Sem T Φ Ψ ρ e P) ∧
    (∀ (Γ : SCtx) (stmts : List Stmt), ∀ (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (ρ : SEnv), Γ = ρ.ctx → Φ.Respects T.Δ →
        Ψ.Defined T.Δ → ∀ Γ', wtStmtsS T Γ stmts = some Γ' →
        ∀ (sp : Span) (tail : Option Expr), (∀ ρ' : SEnv, Γ' = ρ'.ctx → ∃ P, Sem T Φ Ψ ρ' (.block sp [] tail) P) →
        ∃ P, Sem T Φ Ψ ρ (.block sp stmts tail) P) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arms : List Arm), ∀ (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (ρ : SEnv), Γ = ρ.ctx →
        Φ.Respects T.Δ → Ψ.Defined T.Δ → ∀ τ, wtArmsS T Γ ts arms = some τ →
        ∀ (sp : Span) (s : Expr) (v : Val), eval T Φ ρ s = some v → v.ty = ts →
        ∀ sawT sawF : Bool, exhaustiveFrom ts sawT sawF arms = true →
        (v = .bool true → sawT = false) → (v = .bool false → sawF = false) →
        ∃ P, Sem T Φ Ψ ρ (.matchE sp s arms) P) ∧
    (∀ (Γ : SCtx) (ts : NaruSem.Ty) (arm : Arm), ∀ p g b, arm = .mk p g b → ∀ (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (ρ : SEnv),
        Γ = ρ.ctx → Φ.Respects T.Δ → Ψ.Defined T.Δ → ∀ τ, wtArmS T Γ ts arm = some τ → ∀ v : Val, v.ty = ts → ∀ bs, matchPat p v = some bs →
        (∃ P, Sem T Φ Ψ (ρ.extVals bs) b P) ∧
        (∀ g', g = some g' → ∃ G, Sem T Φ Ψ (ρ.extVals bs) g' G)) := by
  apply wtS.mutual_induct T
  -- 1. Nat のリテラル(値: 論理の位置ではない)
  · intro Γ _ n Φ Ψ ρ _ _ _ τ hτ hf
    rw [wtS.eq_def] at hτ
    simp only [Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 2. Bool のリテラル
  · intro Γ _ b Φ Ψ ρ _ _ _ τ _ _
    exact ⟨b = true, .lit⟩
  -- 3. 局所名
  · intro Γ _ x Φ Ψ ρ hΓ _ _ τ hτ hf
    subst hΓ
    rw [wtS.eq_def] at hτ
    simp only [SEnv.ctx] at hτ
    cases h : ρ x with
    | none => simp [h] at hτ
    | some s =>
      simp only [h, Option.map_some, Option.some.injEq] at hτ
      subst hτ
      cases s with
      | prop P => exact ⟨P, .varProp h⟩
      | val v =>
        cases v with
        | nat n => simp [SVal.ty, Val.ty, STy.isForm] at hf
        | bool b => exact ⟨b = true, .varVal h⟩
  -- 4. 呼出し(頭が局所名: 対象外)
  · intro Γ _ _ path args hb Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hb] at hτ
  -- 5. 呼出し(実引数が適格): fn / input は Bool の結果を命題に、spec 宣言はその意味に実引数を渡す
  · intro Γ _ _ path args hnb tys hargs Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    simp only [Bool.not_eq_true] at hnb
    rw [wtS.eq_def] at hτ
    simp only [hnb, Bool.false_eq_true, ite_false, hargs] at hτ
    obtain ⟨vals, hvals, hvt⟩ := evalArgs_total hargs Φ ρ hΓ hΦ
    have hnb' : headBound ρ path = false := by rw [← headBound_ctx, ← hΓ]; exact hnb
    simp only [callTyS] at hτ
    cases hres : T.resolve path with
    | none => simp [hres] at hτ
    | some k =>
      simp only [hres] at hτ
      cases hsig : T.sig k with
      | none => simp [hsig] at hτ
      | some s =>
        simp only [hsig] at hτ
        cases s with
        | fn ps t | input ps t =>
          simp only at hτ
          split at hτ
          · rename_i harr
            simp only [Option.some.injEq] at hτ
            subst hτ
            cases t with
            | nat => simp [STy.isForm] at hf
            | bool =>
              obtain ⟨vs, hvs, hvst⟩ := arrange_vals hvt harr
              have hd : (T.sig k).bind DeclSig.value? = some (ps, .bool) := by rw [hsig]; rfl
              obtain ⟨f, hf', hfv⟩ := hΦ k _ _ (valueSig?_Δ hd)
              obtain ⟨v, hv, hvty⟩ := hfv vs hvst
              cases v with
              | nat => simp [Val.ty] at hvty
              | bool b => exact ⟨b = true, .callVal hnb' hres hd hf' hvals hvs hv⟩
          · cases hτ
        | spec ps =>
          simp only at hτ
          split at hτ
          · rename_i harr
            obtain ⟨vs, hvs, hvst⟩ := arrange_vals hvt harr
            obtain ⟨F, hF⟩ := hΨ k _ (specSig?_Δ hsig)
            exact ⟨F vs, .callSpec hnb' hres hsig hF hvals hvs⟩
          · cases hτ
  -- 6. 呼出し(実引数が不適格)
  · intro Γ _ _ path args hnb hargs Φ Ψ ρ _ _ _ τ hτ _
    simp only [Bool.not_eq_true] at hnb
    rw [wtS.eq_def] at hτ
    simp [hnb, hargs] at hτ
  -- 7. if(適格)
  · intro Γ _ c t e tc tt te hte htt hc j hj ihc iht ihe Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    obtain ⟨hcf, htf, hjf⟩ := STy.join_isForm hj
    rw [wtS.eq_def] at hτ
    simp only [hc, htt, hte, hj] at hτ
    obtain ⟨_, hef, _⟩ := STy.join_isForm hτ
    obtain ⟨C, hC⟩ := ihc Φ Ψ ρ hΓ hΦ hΨ tc hc hcf
    obtain ⟨P, hP⟩ := iht Φ Ψ ρ hΓ hΦ hΨ tt htt htf
    obtain ⟨Q, hQ⟩ := ihe Φ Ψ ρ hΓ hΦ hΨ te hte hef
    exact ⟨(C → P) ∧ (¬ C → Q), .ite hC hP hQ⟩
  -- 8. if(条件と then の結びが無い)
  · intro Γ _ c t e tc tt te hte htt hc hj _ _ _ Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hc, htt, hte, hj] at hτ
  -- 9. if(不適格)
  · intro Γ _ c t e hno _ _ _ Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp only at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 10. 論理演算(適格)
  · intro Γ _ op l r k hk tl tr hr hl ihl ihr Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    rw [wtS.eq_def] at hτ
    simp only [hk, hl, hr] at hτ
    obtain ⟨hlf, hrf, _⟩ := STy.join_isForm hτ
    obtain ⟨P, hP⟩ := ihl Φ Ψ ρ hΓ hΦ hΨ tl hl hlf
    obtain ⟨Q, hQ⟩ := ihr Φ Ψ ρ hΓ hΦ hΨ tr hr hrf
    exact ⟨k.prop P Q, .logic hk hP hQ⟩
  -- 11. 論理演算(被演算子が不適格)
  · intro Γ _ op l r k hk hno _ _ Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp only [hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 12. == / !=(両辺が Nat の値)
  · intro Γ _ op l r k hk hnn Φ Ψ ρ hΓ hΦ _ τ _ _
    obtain ⟨a, ha, hat⟩ := eval_total hnn.1 Φ ρ hΓ hΦ
    obtain ⟨b, hb, hbt⟩ := eval_total hnn.2 Φ ρ hΓ hΦ
    cases a with
    | bool => simp [Val.ty] at hat
    | nat a =>
      cases b with
      | bool => simp [Val.ty] at hbt
      | nat b => exact ⟨k.propNat a b, .eqNat hk ha hb⟩
  -- 13. == / !=(論理の位置、適格)
  · intro Γ _ op l r k hk hnn tl tr hr hl ihl ihr Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    rw [wtS.eq_def] at hτ
    simp only [hk, hnn, ite_false, hl, hr] at hτ
    obtain ⟨hlf, hrf, _⟩ := STy.join_isForm hτ
    obtain ⟨P, hP⟩ := ihl Φ Ψ ρ hΓ hΦ hΨ tl hl hlf
    obtain ⟨Q, hQ⟩ := ihr Φ Ψ ρ hΓ hΦ hΨ tr hr hrf
    exact ⟨k.propIff P Q, .eqForm hk hP hQ⟩
  -- 14. == / !=(論理の位置、被演算子が不適格)
  · intro Γ _ op l r k hk hnn hno _ _ Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp only [hk, hnn, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 15. 比較(適格)
  · intro Γ _ op l r k hk tr hr hl Φ Ψ ρ hΓ hΦ _ τ _ _
    obtain ⟨a, ha, hat⟩ := eval_total hl Φ ρ hΓ hΦ
    obtain ⟨b, hb, hbt⟩ := eval_total hr Φ ρ hΓ hΦ
    cases tr with
    | bool =>
      cases a with
      | nat a => simp [Val.ty] at hat
      | bool a =>
        cases b with
        | nat b => simp [Val.ty] at hbt
        | bool b => exact ⟨k.evalBool a b = true, .cmpBool hk ha hb⟩
    | nat =>
      cases a with
      | bool a => simp [Val.ty] at hat
      | nat a =>
        cases b with
        | bool b => simp [Val.ty] at hbt
        | nat b => exact ⟨k.propNat a b, .cmpNat hk ha hb⟩
  -- 16. 比較(被演算子の型が違う)
  · intro Γ _ op l r k hk tl tr hr hl hne Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hk, hl, hr, hne] at hτ
  -- 17. 比較(被演算子が不適格)
  · intro Γ _ op l r k hk hno Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp only [hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 18. 算術(値: 論理の位置ではない)
  · intro Γ _ op l r k hk hr hl Φ Ψ ρ _ _ _ τ hτ hf
    rw [wtS.eq_def] at hτ
    simp only [hk, hl, hr, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 19. 算術(被演算子が不適格)
  · intro Γ _ op l r k hk hno Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp only [hk] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 20. 対象外の演算子
  · intro Γ _ op l r hk Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hk] at hτ
  -- 21. `!`(適格)
  · intro Γ _ a j hj hjf iha Φ Ψ ρ hΓ hΦ hΨ τ _ _
    obtain ⟨P, hP⟩ := iha Φ Ψ ρ hΓ hΦ hΨ j hj hjf
    exact ⟨¬ P, .not hP⟩
  -- 22. `!`(被演算子が論理の位置の型でない)
  · intro Γ _ a j hj hjf _ Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hj, hjf] at hτ
  -- 23. `!`(被演算子が不適格)
  · intro Γ _ a hj _ Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hj] at hτ
  -- 24. 対象外の単項演算子
  · intro Γ _ op a hne Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hne] at hτ
  -- 25. UFCS の呼出し(適格)
  · intro Γ _ r m args hu tr tys hargs hr Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    rw [wtS.eq_def] at hτ
    simp only [hu, ite_true, hr, hargs] at hτ
    obtain ⟨v, hv, hvt⟩ := eval_total hr Φ ρ hΓ hΦ
    obtain ⟨vals, hvals, hvts⟩ := evalArgs_total hargs Φ ρ hΓ hΦ
    have hu' : ufcs T ρ m = true := by rw [← ufcs_ctx, ← hΓ]; exact hu
    have hvt' : ((none, v) :: vals).map (mapArg Val.ty) = (none, tr) :: tys := by simp [mapArg, hvt, hvts]
    simp only [callTyS] at hτ
    cases hres : T.resolve [m] with
    | none => simp [hres] at hτ
    | some k =>
      simp only [hres] at hτ
      cases hsig : T.sig k with
      | none => simp [hsig] at hτ
      | some s =>
        simp only [hsig] at hτ
        cases s with
        | fn ps t | input ps t =>
          simp only at hτ
          split at hτ
          · rename_i harr
            simp only [Option.some.injEq] at hτ
            subst hτ
            cases t with
            | nat => simp [STy.isForm] at hf
            | bool =>
              obtain ⟨vs, hvs, hvst⟩ := arrange_vals hvt' harr
              have hd : (T.sig k).bind DeclSig.value? = some (ps, .bool) := by rw [hsig]; rfl
              obtain ⟨f, hf', hfv⟩ := hΦ k _ _ (valueSig?_Δ hd)
              obtain ⟨w, hw, hwty⟩ := hfv vs hvst
              cases w with
              | nat => simp [Val.ty] at hwty
              | bool b => exact ⟨b = true, .ufcsVal hu' hres hd hf' hv hvals hvs hw⟩
          · cases hτ
        | spec ps =>
          simp only at hτ
          split at hτ
          · rename_i harr
            obtain ⟨vs, hvs, hvst⟩ := arrange_vals hvt' harr
            obtain ⟨F, hF⟩ := hΨ k _ (specSig?_Δ hsig)
            exact ⟨F vs, .ufcsSpec hu' hres hsig hF hv hvals hvs⟩
          · cases hτ
  -- 26. UFCS の呼出し(受け手か実引数が不適格)
  · intro Γ _ r m args hu hno Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp only [hu, ite_true] at hτ
    cases hwr : wtR T Γ r with
    | none => simp at hτ
    | some tr =>
      cases hwa : wtArgs T Γ args with
      | none => simp at hτ
      | some tys => exact (hno tr tys hwr hwa).elim
  -- 27. Nat の min / max(値)
  · intro Γ _ r m hnu a k ha hr hm Φ Ψ ρ _ _ _ τ hτ hf
    simp only [Bool.not_eq_true] at hnu
    rw [wtS.eq_def] at hτ
    simp only [hnu, Bool.false_eq_true, ite_false, hm, hr, ha, Option.some.injEq] at hτ
    subst hτ
    simp [STy.isForm] at hf
  -- 28. Nat のメソッド(不適格)
  · intro Γ _ r m hnu a hno Φ Ψ ρ _ _ _ τ hτ _
    simp only [Bool.not_eq_true] at hnu
    rw [wtS.eq_def] at hτ
    simp only [hnu, Bool.false_eq_true, ite_false] at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 29. メソッド(位置引数 1 つでない: 対象外)
  · intro Γ _ r m args hnu hne Φ Ψ ρ _ _ _ τ hτ _
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
  -- 30. match(適格)
  · intro Γ _ s arms ta hs hex ih2 Φ Ψ ρ hΓ hΦ hΨ τ hτ _
    rw [wtS.eq_def] at hτ
    simp only [hs, hex, ite_true] at hτ
    obtain ⟨v, hv, hvt⟩ := eval_total hs Φ ρ hΓ hΦ
    exact ih2 Φ Ψ ρ hΓ hΦ hΨ τ hτ _ s v hv hvt false false hex (fun _ => rfl) (fun _ => rfl)
  -- 31. match(網羅しない)
  · intro Γ _ s arms ta hs hne Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hs, hne] at hτ
  -- 32. match(scrutinee が不適格)
  · intro Γ _ s arms hs Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hs] at hτ
  -- 33. ブロック(適格)
  · intro Γ sp stmts e Γ' hst ihst ihe Φ Ψ ρ hΓ hΦ hΨ τ hτ hf
    rw [wtS.eq_def] at hτ
    simp only [hst] at hτ
    refine ihst Φ Ψ ρ hΓ hΦ hΨ Γ' hst sp (some e) ?_
    intro ρ' hρ'
    obtain ⟨P, hP⟩ := ihe Φ Ψ ρ' hρ' hΦ hΨ τ hτ hf
    exact ⟨P, .blockTail hP⟩
  -- 34. ブロック(let の列が不適格)
  · intro Γ _ stmts e hst _ Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp [hst] at hτ
  -- 35. 量化(束縛なし: 対象外)
  · intro Γ _ q b Φ Ψ ρ _ _ _ τ hτ _
    rw [wtS.eq_def] at hτ
    simp at hτ
  -- 36. 量化(適格)
  · intro Γ sp q bs b Γ' hb j hj hjf _ ih Φ Ψ ρ hΓ hΦ hΨ τ _ _
    have aux : ∀ (bs' : List Binder) (Γ₀ : SCtx) (ρ₀ : SEnv), Γ₀ = ρ₀.ctx → SCtx.extBinders Γ₀ bs' = some Γ' →
        ∃ P, Sem T Φ Ψ ρ₀ (.quant sp q bs' b) P := by
      intro bs'
      induction bs' with
      | nil =>
        intro Γ₀ ρ₀ h0 hb0
        simp only [SCtx.extBinders, Option.some.injEq] at hb0
        subst hb0
        obtain ⟨P, hP⟩ := ih Φ Ψ ρ₀ h0 hΦ hΨ j hj hjf
        exact ⟨P, .quantNil hP⟩
      | cons bd rest ihr =>
        obtain ⟨x, ty, bsp⟩ := bd
        intro Γ₀ ρ₀ h0 hb0
        simp only [SCtx.extBinders] at hb0
        cases ty with
        | none => simp at hb0
        | some ty =>
          simp only at hb0
          cases htv : ty.toTy? with
          | none => simp [htv] at hb0
          | some t =>
            simp only [htv] at hb0
            have hall : ∀ a : t.carrier, ∃ P, Sem T Φ Ψ (ρ₀.ext x (.val (Val.of t a))) (.quant sp q rest b) P := fun a =>
              ihr (Γ₀.ext x (.val t)) (ρ₀.ext x (.val (Val.of t a))) (by rw [SEnv.ctx_ext, h0]; simp [SVal.ty]) hb0
            have hF : ∀ a, Sem T Φ Ψ (ρ₀.ext x (.val (Val.of t a))) (.quant sp q rest b) (Classical.choose (hall a)) :=
              fun a => Classical.choose_spec (hall a)
            cases q with
            | forall_ => exact ⟨∀ a, Classical.choose (hall a), .forallCons htv hF⟩
            | exists_ => exact ⟨∃ a, Classical.choose (hall a), .existsCons htv hF⟩
    exact aux bs Γ ρ hΓ hb
  -- 37. 量化(本体が論理の位置の型でない)
  · intro Γ _ q bs b Γ' hb j hj hjf hne _ Φ Ψ ρ _ _ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest =>
      rw [wtS.eq_def] at hτ
      simp [hb, hj, hjf] at hτ
  -- 38. 量化(本体が不適格)
  · intro Γ _ q bs b Γ' hb hj hne _ Φ Ψ ρ _ _ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest =>
      rw [wtS.eq_def] at hτ
      simp [hb, hj] at hτ
  -- 39. 量化(束縛の型が対象外)
  · intro Γ _ q bs b hb hne Φ Ψ ρ _ _ _ τ hτ _
    cases bs with
    | nil => exact (hne rfl).elim
    | cons xt rest =>
      rw [wtS.eq_def] at hτ
      simp [hb] at hτ
  -- 40. 対象外の構文
  · intro e Γ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 Φ Ψ ρ _ _ _ τ hτ _
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
  · intro Γ ts p g b hp p' g' b' heq Φ Ψ ρ _ _ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp at hτ
  -- 42. 腕(ガード無し、適格)
  · intro Γ ts p b bs' hp j hj hjf ihb p' g' b' heq Φ Ψ ρ hΓ hΦ hΨ τ hτ v hv bs hm
    cases heq
    have hΓ' : Γ.extVals bs' = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb Φ Ψ (ρ.extVals bs) hΓ' hΦ hΨ j hj hjf, ?_⟩
    intro g' hg
    cases hg
  -- 43. 腕(ガード無し、本体が論理の位置の型でない)
  · intro Γ ts p b bs' hp j hj hjf _ p' g' b' heq Φ Ψ ρ _ _ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj, hjf] at hτ
  -- 44. 腕(ガード無し、本体が不適格)
  · intro Γ ts p b bs' hp hj _ p' g' b' heq Φ Ψ ρ _ _ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp [hj] at hτ
  -- 45. 腕(ガード付き、適格)
  · intro Γ ts p b bs' hp g tl tr hb hg ihg ihb p' g' b' heq Φ Ψ ρ hΓ hΦ hΨ τ hτ v hv bs hm
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only [hg, hb] at hτ
    obtain ⟨hgf, hbf, _⟩ := STy.join_isForm hτ
    have hΓ' : Γ.extVals bs' = (ρ.extVals bs).ctx := by
      rw [SEnv.ctx_extVals, matchPat_types hp hv hm, hΓ]
    refine ⟨ihb Φ Ψ (ρ.extVals bs) hΓ' hΦ hΨ tr hb hbf, ?_⟩
    intro g'' hg''
    cases hg''
    exact ihg Φ Ψ (ρ.extVals bs) hΓ' hΦ hΨ tl hg hgf
  -- 46. 腕(ガード付き、不適格)
  · intro Γ ts p b bs' hp g hno _ _ p' g' b' heq Φ Ψ ρ _ _ _ τ hτ
    cases heq
    rw [wtArmS_mk, hp] at hτ
    simp only at hτ
    first
      | (cases hτ; done)
      | (split at hτ <;> simp_all)
  -- 47. 腕の列(空)
  · intro Γ ts Φ Ψ ρ _ _ _ τ hτ
    simp [wtArmsS] at hτ
  -- 48. 腕の列(先頭の腕が不適格)
  · intro Γ ts arm rest h _ Φ Ψ ρ _ _ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h] at hτ
  -- 49. 腕の列(最後の 1 つ)
  · intro Γ ts arm t1 h1 ih3 Φ Ψ ρ hΓ hΦ hΨ τ hτ sp s v hs hv sawT sawF hex hT hF
    obtain ⟨p, g, b⟩ := arm
    cases g with
    | some g => simp [exhaustiveFrom] at hex
    | none =>
      cases p with
      | wild psp =>
        obtain ⟨P, hP⟩ := (ih3 (.wild psp) none b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 v hv [] rfl).1
        exact ⟨P, .matchHit hs rfl hP⟩
      | bind psp x =>
        obtain ⟨P, hP⟩ := (ih3 (.bind psp x) none b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 v hv [(x, v)] rfl).1
        exact ⟨P, .matchHit hs rfl hP⟩
      | lit psp l =>
        cases l with
        | bool lb =>
          cases lb with
          | true =>
            rw [exhaustiveFrom_true] at hex
            simp only [exhaustiveFrom, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at hex
            obtain ⟨hts, hsf⟩ := hex
            subst hts
            cases v with
            | nat => simp [Val.ty] at hv
            | bool c =>
              cases c with
              | false => exact absurd (hF rfl) (by simp [hsf])
              | true =>
                obtain ⟨P, hP⟩ := (ih3 (.lit psp (.bool true)) none b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 (.bool true) hv [] rfl).1
                exact ⟨P, .matchHit hs rfl hP⟩
          | false =>
            rw [exhaustiveFrom_false] at hex
            simp only [exhaustiveFrom, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at hex
            obtain ⟨hts, hst⟩ := hex
            subst hts
            cases v with
            | nat => simp [Val.ty] at hv
            | bool c =>
              cases c with
              | true => exact absurd (hT rfl) (by simp [hst])
              | false =>
                obtain ⟨P, hP⟩ := (ih3 (.lit psp (.bool false)) none b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 (.bool false) hv [] rfl).1
                exact ⟨P, .matchHit hs rfl hP⟩
        | nat n => rw [exhaustiveFrom_nat] at hex; simp [exhaustiveFrom] at hex
        | str s => simp [exhaustiveFrom] at hex
        | unit => simp [exhaustiveFrom] at hex
  -- 50. 腕の列(先頭の腕と残りがともに適格)
  · intro Γ ts arm t1 head tail h1 j hj ih3 ih2 Φ Ψ ρ hΓ hΦ hΨ τ hτ sp s v hs hv sawT sawF hex hT hF
    obtain ⟨p, g, b⟩ := arm
    cases hm : matchPat p v with
    | some bs =>
      obtain ⟨⟨P, hP⟩, hguard⟩ := ih3 p g b rfl Φ Ψ ρ hΓ hΦ hΨ t1 h1 v hv bs hm
      cases g with
      | none => exact ⟨P, .matchHit hs hm hP⟩
      | some g =>
        obtain ⟨G, hG⟩ := hguard g rfl
        rw [exhaustiveFrom_guard] at hex
        obtain ⟨R, hR⟩ := ih2 Φ Ψ ρ hΓ hΦ hΨ j hj sp s v hs hv sawT sawF hex hT hF
        exact ⟨(G → P) ∧ (¬ G → R), .matchGuard hs hm hG hP hR⟩
    | none =>
      have step : ∀ sawT' sawF', exhaustiveFrom ts sawT' sawF' (head :: tail) = true →
          (v = .bool true → sawT' = false) → (v = .bool false → sawF' = false) →
          ∃ P, Sem T Φ Ψ ρ (.matchE sp s (Arm.mk p g b :: head :: tail)) P := by
        intro sawT' sawF' hex' hT' hF'
        obtain ⟨R, hR⟩ := ih2 Φ Ψ ρ hΓ hΦ hΨ j hj sp s v hs hv sawT' sawF' hex' hT' hF'
        exact ⟨R, .matchSkip hs hm hR⟩
      cases g with
      | some g =>
        rw [exhaustiveFrom_guard] at hex
        exact step sawT sawF hex hT hF
      | none =>
        cases p with
        | wild => simp [matchPat] at hm
        | bind => simp [matchPat] at hm
        | lit psp l =>
          cases l with
          | bool lb =>
            cases lb with
            | true =>
              rw [exhaustiveFrom_true] at hex
              simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hex
              have hne : v ≠ .bool true := by
                intro h
                subst h
                simp [matchPat] at hm
              rcases hex with ⟨hts, hsf⟩ | hrest
              · subst hts
                cases v with
                | nat => simp [Val.ty] at hv
                | bool c =>
                  cases c with
                  | true => exact absurd rfl hne
                  | false => exact absurd (hF rfl) (by simp [hsf])
              · exact step true sawF hrest (fun h => absurd h hne) hF
            | false =>
              rw [exhaustiveFrom_false] at hex
              simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hex
              have hne : v ≠ .bool false := by
                intro h
                subst h
                simp [matchPat] at hm
              rcases hex with ⟨hts, hst⟩ | hrest
              · subst hts
                cases v with
                | nat => simp [Val.ty] at hv
                | bool c =>
                  cases c with
                  | false => exact absurd rfl hne
                  | true => exact absurd (hT rfl) (by simp [hst])
              · exact step sawT true hrest hT (fun h => absurd h hne)
          | nat n =>
            rw [exhaustiveFrom_nat] at hex
            exact step sawT sawF hex hT hF
          | str s => exact step sawT sawF (by simpa [exhaustiveFrom] using hex) hT hF
          | unit => exact step sawT sawF (by simpa [exhaustiveFrom] using hex) hT hF
  -- 51. 腕の列(残りが不適格)
  · intro Γ ts arm t1 head tail h1 h2 _ _ Φ Ψ ρ _ _ _ τ hτ
    rw [wtArmsS.eq_def] at hτ
    simp [h1, h2] at hτ
  -- 52. let の列(空)
  · intro Γ Φ Ψ ρ hΓ _ _ Γ' h sp tail hk
    simp only [wtStmtsS, Option.some.injEq] at h
    subst h
    exact hk ρ hΓ
  -- 53. let の列(命題に束ねる、適格)
  · intro Γ _ x ty v rest hp hann hv ihv ihrest Φ Ψ ρ hΓ hΦ hΨ Γ' h sp tail hk
    rw [wtStmtsS.eq_2] at h
    simp only [hp, hann, hv, ite_true] at h
    obtain ⟨P, hP⟩ := ihv Φ Ψ ρ hΓ hΦ hΨ .prop hv rfl
    obtain ⟨Q, hQ⟩ := ihrest Φ Ψ (ρ.ext x (.prop P)) (by rw [SEnv.ctx_ext, hΓ]; rfl) hΦ hΨ Γ' h sp tail hk
    exact ⟨Q, .blockLetProp (by rw [← hΓ]; exact hp) hP hQ⟩
  -- 54. let の列(命題だが不適格)
  · intro Γ _ x ty v rest hp hann hno _ Φ Ψ ρ _ _ _ Γ' h sp tail _
    rw [wtStmtsS.eq_2] at h
    simp only [hp, hann, ite_true] at h
    first
      | (cases h; done)
      | (split at h <;> simp_all)
  -- 55. let の列(命題だが注釈が Bool でない)
  · intro Γ _ x ty v rest hp hann Φ Ψ ρ _ _ _ Γ' h sp tail _
    rw [wtStmtsS.eq_2] at h
    simp [hp, hann] at h
  -- 56. let の列(値に束ねる、適格)
  · intro Γ _ x ty v rest hp ta hv t hann ihrest Φ Ψ ρ hΓ hΦ hΨ Γ' h sp tail hk
    simp only [Bool.not_eq_true] at hp
    rw [wtStmtsS.eq_2] at h
    simp only [hp, Bool.false_eq_true, ite_false, hv, hann] at h
    obtain ⟨w, hw, hwt⟩ := eval_total hv Φ ρ hΓ hΦ
    have ht : t = ta := annot_eq hann
    subst ht
    obtain ⟨Q, hQ⟩ := ihrest Φ Ψ (ρ.ext x (.val w)) (by rw [SEnv.ctx_ext, hΓ]; simp [SVal.ty, hwt]) hΦ hΨ Γ' h sp tail hk
    exact ⟨Q, .blockLetVal (by rw [← hΓ]; exact hp) hw hQ⟩
  -- 57. let の列(値に束ねる、注釈が合わない)
  · intro Γ _ x ty v rest hp ta hv hann Φ Ψ ρ _ _ _ Γ' h sp tail _
    simp only [Bool.not_eq_true] at hp
    rw [wtStmtsS.eq_2] at h
    simp [hp, hv, hann] at h
  -- 58. let の列(値が不適格)
  · intro Γ _ x ty v rest hp hv Φ Ψ ρ _ _ _ Γ' h sp tail _
    simp only [Bool.not_eq_true] at hp
    rw [wtStmtsS.eq_2] at h
    simp [hp, hv] at h

/-- **spec の意味の存在**: 宣言表と文脈で論理の位置で適格な、呼出しを含む Surface AST の式は、対応する環境・署名を守る関数環境・定義された
spec 宣言の環境で意味(命題)を持つ。 -/
theorem Sem_exists {T : Table} {Γ : SCtx} {e : Expr} {τ : STy} (h : wtS T Γ e = some τ) (hf : τ.isForm = true)
    (Φ : NaruSem.Call.FEnv) (Ψ : NaruSem.Call.PEnv) (ρ : SEnv) (hρ : Γ = ρ.ctx) (hΦ : Φ.Respects T.Δ) (hΨ : Ψ.Defined T.Δ) :
    ∃ P, Sem T Φ Ψ ρ e P :=
  (Sem_exists_all T).1 Γ e Φ Ψ ρ hρ hΦ hΨ τ h hf

/-! ## spec の意味の一意性 -/

/-- **spec の意味の一意性**: 同じ環境・式の意味は等しい。fn / input の呼出しの規則(`callVal` / `ufcsVal`)と spec 宣言の呼出しの規則
(`callSpec` / `ufcsSpec`)は宣言表の署名(fn / input か spec 宣言か)で排他、`==` / `!=` の 2 つの規則は `Sem_not_nat` で排他。 -/
theorem Sem_unique {T : Table} {Φ : NaruSem.Call.FEnv} {Ψ : NaruSem.Call.PEnv} {ρ : SEnv} {e : Expr} {P : Prop} (h : Sem T Φ Ψ ρ e P) :
    ∀ {Q : Prop}, Sem T Φ Ψ ρ e Q → P = Q := by
  induction h with
  | lit =>
    intro Q hQ
    cases hQ
    rfl
  | varVal h =>
    intro Q hQ
    cases hQ with
    | varVal h' => rw [h] at h'; cases h'; rfl
    | varProp h' => rw [h] at h'; cases h'
  | varProp h =>
    intro Q hQ
    cases hQ with
    | varVal h' => rw [h] at h'; cases h'
    | varProp h' => rw [h] at h'; cases h'; rfl
  | callVal hs hr hd hf ha harr hv =>
    intro Q hQ
    cases hQ with
    | callVal hs' hr' hd' hf' ha' harr' hv' =>
      rw [hr] at hr'; cases hr'; rw [hd] at hd'; cases hd'; rw [hf] at hf'; cases hf'; rw [ha] at ha'; cases ha'
      rw [harr] at harr'; cases harr'; rw [hv] at hv'; cases hv'; rfl
    | callSpec hs' hr' hd' => rw [hr] at hr'; cases hr'; rw [hd'] at hd; simp [DeclSig.value?] at hd
  | callSpec hs hr hd hF ha harr =>
    intro Q hQ
    cases hQ with
    | callVal hs' hr' hd' => rw [hr] at hr'; cases hr'; rw [hd] at hd'; simp [DeclSig.value?] at hd'
    | callSpec hs' hr' hd' hF' ha' harr' =>
      rw [hr] at hr'; cases hr'; rw [hd] at hd'; cases hd'; rw [hF] at hF'; cases hF'; rw [ha] at ha'; cases ha'
      rw [harr] at harr'; cases harr'; rfl
  | ufcsVal hu hr hd hf hrv ha harr hv =>
    intro Q hQ
    cases hQ with
    | ufcsVal hu' hr' hd' hf' hrv' ha' harr' hv' =>
      rw [hr] at hr'; cases hr'; rw [hd] at hd'; cases hd'; rw [hf] at hf'; cases hf'; rw [hrv] at hrv'; cases hrv'
      rw [ha] at ha'; cases ha'; rw [harr] at harr'; cases harr'; rw [hv] at hv'; cases hv'; rfl
    | ufcsSpec hu' hr' hd' => rw [hr] at hr'; cases hr'; rw [hd'] at hd; simp [DeclSig.value?] at hd
  | ufcsSpec hu hr hd hF hrv ha harr =>
    intro Q hQ
    cases hQ with
    | ufcsVal hu' hr' hd' => rw [hr] at hr'; cases hr'; rw [hd] at hd'; simp [DeclSig.value?] at hd'
    | ufcsSpec hu' hr' hd' hF' hrv' ha' harr' =>
      rw [hr] at hr'; cases hr'; rw [hd] at hd'; cases hd'; rw [hF] at hF'; cases hF'; rw [hrv] at hrv'; cases hrv'
      rw [ha] at ha'; cases ha'; rw [harr] at harr'; cases harr'; rfl
  | logic hk hl hr ihl ihr =>
    intro Q hQ
    cases hQ with
    | logic hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [ihl hl', ihr hr']
    | eqNat hk' => rw [hk] at hk'; cases hk'
    | eqForm hk' => rw [hk] at hk'; cases hk'
    | cmpNat hk' => rw [hk] at hk'; cases hk'
    | cmpBool hk' => rw [hk] at hk'; cases hk'
  | eqNat hk hl hr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqNat hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [hl] at hl'; cases hl'; rw [hr] at hr'; cases hr'; rfl
    | eqForm hk' hl' hr' => exact absurd hl (Sem_not_nat hl' _ (Agree.refl _) _)
    | cmpNat hk' => rw [hk] at hk'; cases hk'
    | cmpBool hk' => rw [hk] at hk'; cases hk'
  | eqForm hk hl hr ihl ihr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqNat hk' hl' hr' => exact absurd hl' (Sem_not_nat hl _ (Agree.refl _) _)
    | eqForm hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [ihl hl', ihr hr']
    | cmpNat hk' => rw [hk] at hk'; cases hk'
    | cmpBool hk' => rw [hk] at hk'; cases hk'
  | cmpNat hk hl hr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqNat hk' => rw [hk] at hk'; cases hk'
    | eqForm hk' => rw [hk] at hk'; cases hk'
    | cmpNat hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [hl] at hl'; cases hl'; rw [hr] at hr'; cases hr'; rfl
    | cmpBool hk' hl' hr' => rw [hl] at hl'; cases hl'
  | cmpBool hk hl hr =>
    intro Q hQ
    cases hQ with
    | logic hk' => rw [hk] at hk'; cases hk'
    | eqNat hk' => rw [hk] at hk'; cases hk'
    | eqForm hk' => rw [hk] at hk'; cases hk'
    | cmpNat hk' hl' hr' => rw [hl] at hl'; cases hl'
    | cmpBool hk' hl' hr' => rw [hk] at hk'; cases hk'; rw [hl] at hl'; cases hl'; rw [hr] at hr'; cases hr'; rfl
  | not h ih =>
    intro Q hQ
    cases hQ with
    | not h' => rw [ih h']
  | ite hc ht he ihc iht ihe =>
    intro Q hQ
    cases hQ with
    | ite hc' ht' he' => rw [ihc hc', iht ht', ihe he']
  | blockTail h ih =>
    intro Q hQ
    cases hQ with
    | blockTail h' => exact ih h'
  | blockLetVal hp hv hb ihb =>
    intro Q hQ
    cases hQ with
    | blockLetVal hp' hv' hb' => rw [hv] at hv'; cases hv'; exact ihb hb'
    | blockLetProp hp' => rw [hp] at hp'; cases hp'
  | blockLetProp hp hv hb ihv ihb =>
    intro Q hQ
    cases hQ with
    | blockLetVal hp' => rw [hp] at hp'; cases hp'
    | blockLetProp hp' hv' hb' =>
      have := ihv hv'
      subst this
      exact ihb hb'
  | matchSkip hs hp hr ihr =>
    intro Q hQ
    cases hQ with
    | matchSkip hs' hp' hr' => rw [hs] at hs'; cases hs'; exact ihr hr'
    | matchHit hs' hp' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
    | matchGuard hs' hp' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
  | matchHit hs hp hb ihb =>
    intro Q hQ
    cases hQ with
    | matchSkip hs' hp' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
    | matchHit hs' hp' hb' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'; exact ihb hb'
  | matchGuard hs hp hg hb hr ihg ihb ihr =>
    intro Q hQ
    cases hQ with
    | matchSkip hs' hp' => rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
    | matchGuard hs' hp' hg' hb' hr' =>
      rw [hs] at hs'; cases hs'; rw [hp] at hp'; cases hp'
      rw [ihg hg', ihb hb', ihr hr']
  | quantNil h ih =>
    intro Q hQ
    cases hQ with
    | quantNil h' => exact ih h'
  | forallCons ht h ih =>
    intro Q hQ
    cases hQ with
    | forallCons ht' h' =>
      rw [ht] at ht'
      cases ht'
      have hF : _ = _ := funext fun a => ih a (h' a)
      rw [hF]
  | existsCons ht h ih =>
    intro Q hQ
    cases hQ with
    | existsCons ht' h' =>
      rw [ht] at ht'
      cases ht'
      have hF : _ = _ := funext fun a => ih a (h' a)
      rw [hF]

/-! ## 宣言群 -/

/-- 宣言群の適格性の 1 段: 先頭の宣言の鍵と単純名は未使用、本体はそれまでの表で適格、残りは先頭を足した表で適格。 -/
theorem wtProgFrom_cons {all seen : Prog} {d : Decl} {rest : Prog} (h : wtProgFrom all seen (d :: rest) = true) :
    sigsOf seen d.key = none ∧ seen.all (fun e => e.name != d.name) = true ∧ wtDecl (tableOf all seen) d = true ∧
      wtProgFrom all (seen ++ [d]) rest = true := by
  simp only [wtProgFrom, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- 適格な宣言の署名は対象(`sig?` が定まる)。 -/
theorem wtDecl_sig {T : Table} {d : Decl} (h : wtDecl T d = true) : (d.sig?).isSome = true := by
  cases hs : d.sig? with
  | none => cases hb : d.body <;> simp [wtDecl, hs, hb] at h
  | some _ => rfl

/-- 宣言群の全宣言の署名が対象。 -/
def AllSig (P : Prog) : Prop := ∀ d ∈ P, (d.sig?).isSome = true

theorem AllSig.nil : AllSig [] := fun _ h => by simp at h

theorem AllSig.append {seen : Prog} (h : AllSig seen) {d : Decl} (hd : (d.sig?).isSome = true) : AllSig (seen ++ [d]) := by
  intro e he
  simp only [List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · exact h e he
  · exact hd

/-- 全宣言の署名が対象の宣言群で署名が無い鍵は、どの宣言の鍵でもない。 -/
theorem find?_eq_none_of_sigsOf_none {seen : Prog} (hall : AllSig seen) {k : String} (h : sigsOf seen k = none) :
    seen.find? (fun e => e.key == k) = none := by
  cases hf : seen.find? (fun e => e.key == k) with
  | none => rfl
  | some e =>
    have hsome := hall e (List.mem_of_find?_eq_some hf)
    simp only [sigsOf, hf, Option.bind_some] at h
    rw [h] at hsome
    cases hsome

/-- 宣言を 1 つ足した表の、その宣言の鍵の署名(鍵が未使用なら)。 -/
theorem sigsOf_append_self {seen : Prog} (hall : AllSig seen) {d : Decl} (hfresh : sigsOf seen d.key = none) :
    sigsOf (seen ++ [d]) d.key = d.sig? := by
  simp only [sigsOf, List.find?_append, find?_eq_none_of_sigsOf_none hall hfresh, Option.none_or]
  rw [List.find?_cons_of_pos (by simp)]
  rfl

/-- 宣言を 1 つ足しても他の鍵の署名は変わらない。 -/
theorem sigsOf_append_ne (seen : Prog) (d : Decl) {k : String} (hk : k ≠ d.key) : sigsOf (seen ++ [d]) k = sigsOf seen k := by
  simp only [sigsOf, List.find?_append]
  cases seen.find? (fun e => e.key == k) with
  | some e => rfl
  | none =>
    simp only [Option.none_or]
    rw [List.find?_cons_of_neg (by intro h; exact hk (beq_iff_eq.mp h).symm)]
    rfl

theorem sigsOf_none_of_append {seen : Prog} {d : Decl} {k : String} (h : sigsOf (seen ++ [d]) k = none) : sigsOf seen k = none := by
  unfold sigsOf at h ⊢
  rw [List.find?_append] at h
  cases hf : seen.find? (fun e => e.key == k) with
  | some e =>
    rw [hf, Option.some_or] at h
    exact h
  | none => rfl

/-- 表の署名の文脈は、宣言を 1 つ足すとその宣言の鍵だけで伸びる。 -/
theorem Δ_append_self {all seen : Prog} (hall : AllSig seen) {d : Decl} (hfresh : sigsOf seen d.key = none) :
    (tableOf all (seen ++ [d])).Δ d.key = (d.sig?).map DeclSig.toSig := by
  simp only [Table.Δ, tableOf, sigsOf_append_self hall hfresh]

theorem Δ_append_ne (all seen : Prog) (d : Decl) {k : String} (hk : k ≠ d.key) :
    (tableOf all (seen ++ [d])).Δ k = (tableOf all seen).Δ k := by
  simp only [Table.Δ, tableOf, sigsOf_append_ne seen d hk]

/-- 適格な宣言群の残りの各宣言の鍵は、それまでの表に無い(重複しない)。 -/
theorem wtProgFrom_fresh (all : Prog) : ∀ (seen rest : Prog), wtProgFrom all seen rest = true → ∀ e ∈ rest, sigsOf seen e.key = none
  | _, [], _, _, he => by simp at he
  | seen, d :: rest, h, e, he => by
    obtain ⟨hfresh, _, _, hrest⟩ := wtProgFrom_cons h
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hfresh
    · exact sigsOf_none_of_append (wtProgFrom_fresh all (seen ++ [d]) rest hrest e he)

/-- 適格な宣言群の各宣言の署名は、宣言群全体の表にある。 -/
theorem wtProgFrom_sig (all : Prog) : ∀ (seen rest : Prog), AllSig seen → wtProgFrom all seen rest = true →
    ∀ e ∈ rest, sigsOf (seen ++ rest) e.key = e.sig?
  | _, [], _, _, _, he => by simp at he
  | seen, d :: rest, hall, h, e, he => by
    obtain ⟨hfresh, _, hwt, hrest⟩ := wtProgFrom_cons h
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp only [sigsOf, List.find?_append, find?_eq_none_of_sigsOf_none hall hfresh, Option.none_or]
      rw [List.find?_cons_of_pos (by simp)]
      rfl
    · have := wtProgFrom_sig all (seen ++ [d]) rest (hall.append (wtDecl_sig hwt)) hrest e he
      simpa [List.append_assoc] using this

theorem Interp.step_Φ_ne (all seen : Prog) (m : Interp) (d : Decl) {k : String} (h : k ≠ d.key) :
    (Interp.step all seen m d).Φ k = m.Φ k := by
  simp only [Interp.step]
  split <;> simp [NaruSem.Call.FEnv.ext, h]

theorem Interp.step_Ψ_ne (all seen : Prog) (m : Interp) (d : Decl) {k : String} (h : k ≠ d.key) :
    (Interp.step all seen m d).Ψ k = m.Ψ k := by
  simp only [Interp.step]
  split <;> simp [NaruSem.Call.PEnv.ext, h]

/-- fn の意味: 実引数を仮引数に束ねて、それまでの表と環境で本体を評価する関数。 -/
theorem Interp.step_Φ_fn (all seen : Prog) (m : Interp) (d : Decl) {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty} {b : Expr}
    (hs : d.sig? = some (.fn ps t)) (hb : d.body = some b) :
    (Interp.step all seen m d).Φ d.key = some fun vs =>
      match NaruSem.Call.bindParams ps vs with
      | some ρ => eval (tableOf all seen) m.Φ (NaruSem.Call.Env.toSEnv ρ) b
      | none => none := by
  simp only [Interp.step, hs, hb, NaruSem.Call.FEnv.ext, ite_true]
  rfl

/-- spec 宣言の意味: 実引数を束ねた環境での本体の意味。 -/
theorem Interp.step_Ψ_spec (all seen : Prog) (m : Interp) (d : Decl) {ps : List (String × NaruSem.Ty)} {b : Expr}
    (hs : d.sig? = some (.spec ps)) (hb : d.body = some b) :
    (Interp.step all seen m d).Ψ d.key = some fun vs =>
      ∃ ρ, NaruSem.Call.bindParams ps vs = some ρ ∧ ∃ P, Sem (tableOf all seen) m.Φ m.Ψ (NaruSem.Call.Env.toSEnv ρ) b P ∧ P := by
  simp [Interp.step, hs, hb, NaruSem.Call.PEnv.ext]

/-- input は意味を足さない(解釈は最初の環境にある)。 -/
theorem Interp.step_input (all seen : Prog) (m : Interp) (d : Decl) {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty}
    (hs : d.sig? = some (.input ps t)) (hb : d.body = none) : Interp.step all seen m d = m := by
  simp [Interp.step, hs, hb]

/-- 宣言 1 つの意味を足す段の不変条件: 全宣言の署名が対象であること、署名を守る関数環境、残りの input の解釈、定義された spec 宣言の環境は
保たれる(表の署名は足した宣言の鍵だけで伸びる)。 -/
theorem Interp.step_inv (all seen : Prog) (m : Interp) (d : Decl) (rest : Prog) (hall : AllSig seen)
    (hfresh : sigsOf seen d.key = none) (hwt : wtDecl (tableOf all seen) d = true) (hrest : wtProgFrom all (seen ++ [d]) rest = true)
    (hΦ : m.Φ.Respects (tableOf all seen).Δ) (hI : RespectsInputs m.Φ (d :: rest)) (hΨ : m.Ψ.Defined (tableOf all seen).Δ) :
    AllSig (seen ++ [d]) ∧ (Interp.step all seen m d).Φ.Respects (tableOf all (seen ++ [d])).Δ ∧
      RespectsInputs (Interp.step all seen m d).Φ rest ∧ (Interp.step all seen m d).Ψ.Defined (tableOf all (seen ++ [d])).Δ := by
  have hdsig := wtDecl_sig hwt
  have hall' : AllSig (seen ++ [d]) := hall.append hdsig
  have hrestFresh : ∀ e ∈ rest, e.key ≠ d.key := by
    intro e he heq
    have := wtProgFrom_fresh all (seen ++ [d]) rest hrest e he
    rw [heq, sigsOf_append_self hall hfresh] at this
    rw [this] at hdsig
    cases hdsig
  refine ⟨hall', ?_, ?_, ?_⟩
  · -- 関数環境が署名を守る
    intro y ps t hy
    by_cases hk : y = d.key
    · subst hk
      rw [NaruSem.Call.valueSig?, Δ_append_self hall hfresh] at hy
      cases hs : d.sig? with
      | none => simp [hs] at hy
      | some s =>
        rw [hs] at hy
        cases s with
        | fn ps' t' =>
          simp only [Option.map_some, DeclSig.toSig, Option.bind_some, NaruSem.Call.Sig.value?, Option.some.injEq, Prod.mk.injEq] at hy
          obtain ⟨rfl, rfl⟩ := hy
          cases hb : d.body with
          | none => simp [wtDecl, hs, hb] at hwt
          | some b =>
            simp only [wtDecl, hs, hb, decide_eq_true_eq] at hwt
            refine ⟨_, Interp.step_Φ_fn all seen m d hs hb, ?_⟩
            intro vs hvs
            obtain ⟨hbind, hty⟩ := NaruSem.Call.bindParams_ty hvs
            simp only [hbind]
            have hctx : NaruSem.Call.paramSCtx ps' = (NaruSem.Call.Env.toSEnv (Env.ofList ((ps'.map (·.1)).zip vs))).ctx := by
              rw [NaruSem.Call.Env.toSEnv_ctx, hty, NaruSem.Call.paramSCtx_eq]
            exact eval_total hwt m.Φ _ hctx hΦ
        | input ps' t' =>
          simp only [Option.map_some, DeclSig.toSig, Option.bind_some, NaruSem.Call.Sig.value?, Option.some.injEq, Prod.mk.injEq] at hy
          obtain ⟨rfl, rfl⟩ := hy
          cases hb : d.body with
          | some b => simp [wtDecl, hs, hb] at hwt
          | none =>
            obtain ⟨f, hf, hfv⟩ := hI d (List.mem_cons_self ..) ps' t' hs
            exact ⟨f, by rw [Interp.step_input all seen m d hs hb]; exact hf, hfv⟩
        | spec _ => simp [DeclSig.toSig, NaruSem.Call.Sig.value?] at hy
    · rw [NaruSem.Call.valueSig?, Δ_append_ne all seen d hk] at hy
      obtain ⟨f, hf, hfv⟩ := hΦ y ps t hy
      exact ⟨f, by rw [Interp.step_Φ_ne all seen m d hk]; exact hf, hfv⟩
  · -- 残りの input の解釈は保たれる(鍵は重複しない)
    intro e he ps t hs
    obtain ⟨f, hf, hfv⟩ := hI e (List.mem_cons_of_mem _ he) ps t hs
    exact ⟨f, by rw [Interp.step_Φ_ne all seen m d (hrestFresh e he)]; exact hf, hfv⟩
  · -- spec 宣言の環境は定義されている
    intro y ps hy
    by_cases hk : y = d.key
    · subst hk
      rw [NaruSem.Call.specSig?, Δ_append_self hall hfresh] at hy
      cases hs : d.sig? with
      | none => simp [hs] at hy
      | some s =>
        rw [hs] at hy
        cases s with
        | fn _ _ => simp [DeclSig.toSig, NaruSem.Call.Sig.spec?] at hy
        | input _ _ => simp [DeclSig.toSig, NaruSem.Call.Sig.spec?] at hy
        | spec ps' =>
          cases hb : d.body with
          | none => simp [wtDecl, hs, hb] at hwt
          | some b => exact ⟨_, Interp.step_Ψ_spec all seen m d hs hb⟩
    · rw [NaruSem.Call.specSig?, Δ_append_ne all seen d hk] at hy
      obtain ⟨F, hF⟩ := hΨ y ps hy
      exact ⟨F, by rw [Interp.step_Ψ_ne all seen m d hk]; exact hF⟩

/-- 適格な宣言群の意味は、その署名を守り(fn の意味は型の合う実引数に型の合う値を返す)、spec 宣言の意味は定義されている。 -/
theorem interpFrom_inv (all : Prog) : ∀ (seen rest : Prog) (m : Interp), AllSig seen → wtProgFrom all seen rest = true →
    m.Φ.Respects (tableOf all seen).Δ → RespectsInputs m.Φ rest → m.Ψ.Defined (tableOf all seen).Δ →
    (interpFrom all seen m rest).Φ.Respects (tableOf all (seen ++ rest)).Δ ∧
      (interpFrom all seen m rest).Ψ.Defined (tableOf all (seen ++ rest)).Δ
  | seen, [], m, _, _, hΦ, _, hΨ => by simpa [interpFrom] using And.intro hΦ hΨ
  | seen, d :: rest, m, hall, h, hΦ, hI, hΨ => by
    obtain ⟨hfresh, _, hwt, hrest⟩ := wtProgFrom_cons h
    obtain ⟨hall', hΦ', hI', hΨ'⟩ := Interp.step_inv all seen m d rest hall hfresh hwt hrest hΦ hI hΨ
    have := interpFrom_inv all (seen ++ [d]) rest (Interp.step all seen m d) hall' hrest hΦ' hI' hΨ'
    simpa [interpFrom, List.append_assoc] using this

/-- 既に署名のある鍵の意味は、以後の宣言で変わらない(鍵は重複しない)。 -/
theorem interpFrom_stable (all : Prog) : ∀ (seen rest : Prog) (m : Interp), AllSig seen → wtProgFrom all seen rest = true →
    ∀ k s, sigsOf seen k = some s → (interpFrom all seen m rest).Φ k = m.Φ k ∧ (interpFrom all seen m rest).Ψ k = m.Ψ k
  | _, [], _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | seen, d :: rest, m, hall, h, k, s, hk => by
    obtain ⟨hfresh, _, hwt, hrest⟩ := wtProgFrom_cons h
    have hne : k ≠ d.key := by
      intro he
      rw [he, hfresh] at hk
      cases hk
    have hk' : sigsOf (seen ++ [d]) k = some s := by rw [sigsOf_append_ne seen d hne]; exact hk
    obtain ⟨h1, h2⟩ := interpFrom_stable all (seen ++ [d]) rest (Interp.step all seen m d) (hall.append (wtDecl_sig hwt)) hrest k s hk'
    simp only [interpFrom]
    exact ⟨by rw [h1, Interp.step_Φ_ne all seen m d hne], by rw [h2, Interp.step_Ψ_ne all seen m d hne]⟩

theorem init_respects (all : Prog) (I : NaruSem.Call.FEnv) : I.Respects (tableOf all []).Δ := by
  intro k ps t h
  simp [NaruSem.Call.valueSig?, Table.Δ, tableOf, sigsOf] at h

theorem init_defined (all : Prog) : NaruSem.Call.PEnv.empty.Defined (tableOf all []).Δ := by
  intro k ps h
  simp [NaruSem.Call.specSig?, Table.Δ, tableOf, sigsOf] at h

/-- **宣言群の意味は署名を守る**: 適格な宣言群(`wtProg P = true`)と input の署名を守る任意の解釈 `I` について、宣言群の意味 `interp I P` の
関数環境は宣言群全体の表 `tableOf P P` の署名を守る(各 fn / input の鍵の関数は型の合う実引数に型の合う値を返す)。 -/
theorem interp_respects {P : Prog} (hP : wtProg P = true) {I : NaruSem.Call.FEnv} (hI : RespectsInputs I P) :
    (interp I P).Φ.Respects (tableOf P P).Δ := by
  have := (interpFrom_inv P [] P { Φ := I, Ψ := NaruSem.Call.PEnv.empty } AllSig.nil hP (init_respects P I) hI (init_defined P)).1
  simpa [interp] using this

/-- **spec 宣言の意味は定義されている**。 -/
theorem interp_defined {P : Prog} (hP : wtProg P = true) {I : NaruSem.Call.FEnv} (hI : RespectsInputs I P) :
    (interp I P).Ψ.Defined (tableOf P P).Δ := by
  have := (interpFrom_inv P [] P { Φ := I, Ψ := NaruSem.Call.PEnv.empty } AllSig.nil hP (init_respects P I) hI (init_defined P)).2
  simpa [interp] using this

/-- 適格な宣言群の各宣言の署名は、宣言群全体の表にある。 -/
theorem wtProg_sig {P : Prog} (hP : wtProg P = true) {d : Decl} (hd : d ∈ P) : sigsOf P d.key = d.sig? := by
  have := wtProgFrom_sig P [] P AllSig.nil hP d hd
  simpa using this

/-- **fn / input の全域性**: 適格な宣言群の各 fn(と input)は、型の合う任意の実引数に対して値を持ち、その型は戻り型。 -/
theorem fn_total {P : Prog} (hP : wtProg P = true) {I : NaruSem.Call.FEnv} (hI : RespectsInputs I P) {d : Decl} (hd : d ∈ P)
    {ps : List (String × NaruSem.Ty)} {t : NaruSem.Ty} (hs : (d.sig?).bind DeclSig.value? = some (ps, t)) :
    ∃ f, (interp I P).Φ d.key = some f ∧ ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) → ∃ v, f vs = some v ∧ v.ty = t := by
  refine interp_respects hP hI d.key _ t (valueSig?_Δ ?_)
  show (sigsOf P d.key).bind DeclSig.value? = _
  rw [wtProg_sig hP hd, hs]

/-- **spec 宣言の意味の存在**: 適格な宣言群の各 spec 宣言には意味(実引数の値の列 → 命題)がある。 -/
theorem spec_defined {P : Prog} (hP : wtProg P = true) {I : NaruSem.Call.FEnv} (hI : RespectsInputs I P) {d : Decl} (hd : d ∈ P)
    {ps : List (String × NaruSem.Ty)} (hs : d.sig? = some (.spec ps)) : ∃ F, (interp I P).Ψ d.key = some F := by
  refine interp_defined hP hI d.key (ps.map (·.2)) (specSig?_Δ (ps := ps) ?_)
  show sigsOf P d.key = _
  rw [wtProg_sig hP hd, hs]

/-- **spec 宣言の意味は本体の意味**: 適格な宣言群の spec 宣言の意味 `F` は、型の合う任意の実引数 `vs` について、実引数を束ねた環境での本体の
(それより前の宣言の表 `T'` と意味 `m'` の下の)意味 `Q` と同値(`F vs ↔ Q`)。本体の意味は存在して一意(`Sem_exists` / `Sem_unique`)なので、
`Interp.step` の `∃ P, Sem … P ∧ P` は既定値や `False` で埋めたものではなく本体の意味そのもの。 -/
theorem interpFrom_spec_meaning (all : Prog) : ∀ (seen rest : Prog) (m : Interp), AllSig seen → wtProgFrom all seen rest = true →
    m.Φ.Respects (tableOf all seen).Δ → RespectsInputs m.Φ rest → m.Ψ.Defined (tableOf all seen).Δ →
    ∀ {d : Decl}, d ∈ rest → ∀ {ps : List (String × NaruSem.Ty)} {b : Expr}, d.sig? = some (.spec ps) → d.body = some b →
    ∃ F, (interpFrom all seen m rest).Ψ d.key = some F ∧ ∃ (T' : Table) (m' : Interp), m'.Φ.Respects T'.Δ ∧ m'.Ψ.Defined T'.Δ ∧
      (∃ τ, wtS T' (NaruSem.Call.paramSCtx ps) b = some τ ∧ τ.isForm = true) ∧
      ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) →
        ∃ ρ Q, NaruSem.Call.bindParams ps vs = some ρ ∧ Sem T' m'.Φ m'.Ψ (NaruSem.Call.Env.toSEnv ρ) b Q ∧ (F vs ↔ Q)
  | _, [], _, _, _, _, _, _, _, hd, _, _, _, _ => by simp at hd
  | seen, d :: rest, m, hall, h, hΦ, hI, hΨ, e, he, ps, b, hs, hb => by
    obtain ⟨hfresh, _, hwt, hrest⟩ := wtProgFrom_cons h
    obtain ⟨hall', hΦ', hI', hΨ'⟩ := Interp.step_inv all seen m d rest hall hfresh hwt hrest hΦ hI hΨ
    simp only [List.mem_cons] at he
    simp only [interpFrom]
    rcases he with rfl | he
    · -- この宣言: 意味は `step` が足したもので、以後変わらない
      have hstable := interpFrom_stable all (seen ++ [e]) rest (Interp.step all seen m e) hall' hrest e.key _
        (by rw [sigsOf_append_self hall hfresh, hs])
      refine ⟨fun vs => ∃ ρ, NaruSem.Call.bindParams ps vs = some ρ ∧
          ∃ P, Sem (tableOf all seen) m.Φ m.Ψ (NaruSem.Call.Env.toSEnv ρ) b P ∧ P,
        ?_, tableOf all seen, m, hΦ, hΨ, ?_, ?_⟩
      · rw [hstable.2]
        exact Interp.step_Ψ_spec all seen m e hs hb
      · simp only [wtDecl, hs, hb] at hwt
        split at hwt
        · rename_i τ hτ
          exact ⟨τ, hτ, hwt⟩
        · cases hwt
      · intro vs hvs
        obtain ⟨hbind, hty⟩ := NaruSem.Call.bindParams_ty hvs
        simp only [wtDecl, hs, hb] at hwt
        split at hwt
        · rename_i τ hτ
          have hctx : NaruSem.Call.paramSCtx ps = (NaruSem.Call.Env.toSEnv (Env.ofList ((ps.map (·.1)).zip vs))).ctx := by
            rw [NaruSem.Call.Env.toSEnv_ctx, hty, NaruSem.Call.paramSCtx_eq]
          obtain ⟨Q, hQ⟩ := Sem_exists hτ hwt m.Φ m.Ψ _ hctx hΦ hΨ
          refine ⟨_, Q, hbind, hQ, ?_⟩
          constructor
          · rintro ⟨ρ', hρ', P', hP', hp⟩
            rw [hbind] at hρ'
            cases hρ'
            rw [← Sem_unique hP' hQ]
            exact hp
          · intro hq
            exact ⟨_, hbind, Q, hQ, hq⟩
        · cases hwt
    · exact interpFrom_spec_meaning all (seen ++ [d]) rest (Interp.step all seen m d) hall' hrest hΦ' hI' hΨ' he hs hb

theorem spec_meaning {P : Prog} (hP : wtProg P = true) {I : NaruSem.Call.FEnv} (hI : RespectsInputs I P) {d : Decl} (hd : d ∈ P)
    {ps : List (String × NaruSem.Ty)} {b : Expr} (hs : d.sig? = some (.spec ps)) (hb : d.body = some b) :
    ∃ F, (interp I P).Ψ d.key = some F ∧ ∃ (T' : Table) (m' : Interp), m'.Φ.Respects T'.Δ ∧ m'.Ψ.Defined T'.Δ ∧
      (∃ τ, wtS T' (NaruSem.Call.paramSCtx ps) b = some τ ∧ τ.isForm = true) ∧
      ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) →
        ∃ ρ Q, NaruSem.Call.bindParams ps vs = some ρ ∧ Sem T' m'.Φ m'.Ψ (NaruSem.Call.Env.toSEnv ρ) b Q ∧ (F vs ↔ Q) :=
  interpFrom_spec_meaning P [] P { Φ := I, Ψ := NaruSem.Call.PEnv.empty } AllSig.nil hP (init_respects P I) hI (init_defined P) hd hs hb

end NaruSem.Surf.Call
