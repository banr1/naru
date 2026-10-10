import NaruSem.SemTotality
import NaruSem.Denote
import NaruSem.DenoteProp

/-!
# 対象範囲と行き詰まりの検体(IDEAL.md C39 / C40 / C41 / C42)

一般定理が空虚でないこと、不適格な Core が保証対象にならないこと、評価不能を成功値に置き換えないことを、具体的な Core で kernel に
検査させる(`decide`: `wtR` / `wtS` / `eval` は構造的再帰の関数なので kernel が計算できる)。名前付きの定理にして
`NaruSem.lean` の公理監査に載せる(欠落すれば監査が失敗する)。実際の compiler 経路から得た検体は `lake exe naru_test semantics`
(`tests/accept/sem_core.naru`)が引用して検査する。
-/

namespace NaruSem
open Naru

/-! ## 適格な検体(手書き): 対象範囲は空でない -/

/-- `let y = x + 1; y * 2`(x : Nat)は適格で Nat。 -/
theorem ex_wtR_let : wtR (Ctx.ofList [("x", .nat)])
    (.let_ "y" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat) (.binop "*" (.var "y") (.lit (.nat 2) .nat) .nat)) = some .nat := by
  decide

/-- 同じ式を x = 4 で評価すると 10。 -/
theorem ex_eval_let : eval (Env.ofList [("x", .nat 4)])
    (.let_ "y" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat) (.binop "*" (.var "y") (.lit (.nat 2) .nat) .nat)) = some (.nat 10) := by
  decide

/-- ガード付き match(同名の束縛、ガード不成立からの継続): `match 7 { x if x == 0 => false, _ => x == 0 }` は仮引数 x = 0 を見る。 -/
theorem ex_eval_match_guard : eval (Env.ofList [("x", .nat 0)])
    (.match_ (.lit (.nat 7) .nat) .nat
      [.mk (.bind "x") (some (.binop "==" (.var "x") (.lit (.nat 0) .nat) .nat)) (.lit (.bool false) .bool),
       .mk .wild none (.binop "==" (.var "x") (.lit (.nat 0) .nat) .nat)]) = some (.bool true) := by
  decide

/-- spec: `forall n: Nat { n + x >= x }` は命題。 -/
theorem ex_wtS_forall : wtS (SCtx.ofList [("x", .val .nat)])
    (.quant .forall_ [("n", .nat)] (.binop ">=" (.binop "+" (.var "n") (.var "x") .nat) (.var "x") .nat)) = some .prop := by
  decide

/-- spec: 命題に束ねた名前と Bool の値の論理結合は命題。 -/
theorem ex_wtS_prop_and : wtS (SCtx.ofList [("p", .prop), ("b", .val .bool)]) (.binop "&&" (.var "p") (.var "b") .bool) = some .prop := by
  decide

/-! ## 境界の挙動(言語の意味として明示: `docs/language.md`「式」) -/

theorem ex_nat_sub_truncates : eval Env.empty (.binop "-" (.lit (.nat 3) .nat) (.lit (.nat 5) .nat) .nat) = some (.nat 0) := by
  decide

theorem ex_nat_div_zero : eval Env.empty (.binop "/" (.lit (.nat 7) .nat) (.lit (.nat 0) .nat) .nat) = some (.nat 0) := by
  decide

theorem ex_nat_mod_zero : eval Env.empty (.binop "%" (.lit (.nat 7) .nat) (.lit (.nat 0) .nat) .nat) = some (.nat 7) := by
  decide

theorem ex_bool_order : eval Env.empty (.binop "<" (.lit (.bool false) .bool) (.lit (.bool true) .bool) .bool) = some (.bool true) := by
  decide

theorem ex_implies : eval Env.empty (.binop "implies" (.lit (.bool true) .bool) (.lit (.bool false) .bool) .bool) = some (.bool false) := by
  decide

/-! ## Lean での読み(C40): 基礎段階の範囲と境界の挙動(`NaruSem/Denote.lean`) -/

/-- 基礎段階の範囲は空でない: `let y = x + 1; y * 2` は基礎の式。 -/
theorem ex_basic_let : basic
    (.let_ "y" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat) (.binop "*" (.var "y") (.lit (.nat 2) .nat) .nat)) = true := by
  decide

/-- `match` は基礎段階(C40)の範囲外(C41 の段階。一般定理 `denote_sound` は周回 42 から両方を扱う)。 -/
theorem neg_basic_match : basic (.match_ (.lit (.nat 3) .nat) .nat [.mk .wild none (.lit (.nat 1) .nat)]) = false := by decide

/-- 読みは境界の挙動を保つ(生成 Lean と同じ `Nat` の演算): 3 - 5 = 0、7 / 0 = 0、7 % 0 = 7。 -/
theorem ex_denote_sub_truncates : denoteN Env.empty (.binop "-" (.lit (.nat 3) .nat) (.lit (.nat 5) .nat) .nat) = 0 := by decide
theorem ex_denote_div_zero : denoteN Env.empty (.binop "/" (.lit (.nat 7) .nat) (.lit (.nat 0) .nat) .nat) = 0 := by decide
theorem ex_denote_mod_zero : denoteN Env.empty (.binop "%" (.lit (.nat 7) .nat) (.lit (.nat 0) .nat) .nat) = 7 := by decide

/-- Bool の比較の `Ord.compare` の形も `false < true`。 -/
theorem ex_denote_bool_order : denoteB Env.empty (.binop "<" (.lit (.bool false) .bool) (.lit (.bool true) .bool) .bool) = true := by decide

/-- 保存定理の具体例(一般定理の実例であって代用ではない): x = 4 で `let y = x + 1; y * 2` の意味は読みの値(= 10)。 -/
theorem ex_preserve_let : eval (Env.ofList [("x", .nat 4)])
    (.let_ "y" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat) (.binop "*" (.var "y") (.lit (.nat 2) .nat) .nat)) =
    some (.nat (denoteN (Env.ofList [("x", .nat 4)])
      (.let_ "y" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat) (.binop "*" (.var "y") (.lit (.nat 2) .nat) .nat)))) :=
  preserve_nat ex_wtR_let _ (Env.ty_ofList [("x", .nat 4)]).symm

/-! ## Lean での読み(C41): `match` の腕の選択と束縛 -/

/-- ガード付き match の検体(`ex_eval_match_guard` と同じ Core): `match 7 { x if x == 0 => false, _ => x == 0 }`。 -/
def exMatchGuard : Core.Expr :=
  .match_ (.lit (.nat 7) .nat) .nat
    [.mk (.bind "x") (some (.binop "==" (.var "x") (.lit (.nat 0) .nat) .nat)) (.lit (.bool false) .bool),
     .mk .wild none (.binop "==" (.var "x") (.lit (.nat 0) .nat) .nat)]

/-- x : Nat の文脈で適格で Bool(`match` は非再帰の Nat の match として対象範囲に入る)。 -/
theorem ex_wtR_match_guard : wtR (Ctx.ofList [("x", .nat)]) exMatchGuard = some .bool := by decide

/-- 読み: 腕の束縛 x = 7 でガード `x == 0` が偽 → 次の腕は外側の x = 0 を見て真(束縛は次の腕に漏れない)。 -/
theorem ex_denote_match_guard : denoteB (Env.ofList [("x", .nat 0)]) exMatchGuard = true := by decide

/-- Bool のリテラルの腕: `match false { true => 1, false => 0 }` の読みは 0。 -/
theorem ex_denote_match_bool : denoteN Env.empty (.match_ (.lit (.bool false) .bool) .bool
    [.mk (.lit (.bool true)) none (.lit (.nat 1) .nat), .mk (.lit (.bool false)) none (.lit (.nat 0) .nat)]) = 0 := by decide

/-- 保存定理の具体例(match): x = 0 で検体の意味は読みの値(= true)。 -/
theorem ex_preserve_match : eval (Env.ofList [("x", .nat 0)]) exMatchGuard =
    some (.bool (denoteB (Env.ofList [("x", .nat 0)]) exMatchGuard)) :=
  preserve_bool ex_wtR_match_guard _ (Env.ty_ofList [("x", .nat 0)]).symm

/-! ## Statements の読み(C42): 値の `let` と Bool の条件、値 / 命題の境界、同値定理の実例(`NaruSem/DenoteProp.lean`) -/

/-- `specLetVal` と同じ形: `let big = x > 10; let n = x + 1; big implies n > 11`。 -/
def exSpecLet : Core.Expr :=
  .let_ "big" .bool (.binop ">" (.var "x") (.lit (.nat 10) .nat) .nat)
    (.let_ "n" .nat (.binop "+" (.var "x") (.lit (.nat 1) .nat) .nat)
      (.binop "implies" (.var "big") (.binop ">" (.var "n") (.lit (.nat 11) .nat) .nat) .bool))

theorem ex_wtS_spec_let : wtS (SCtx.ofList [("x", .val .nat)]) exSpecLet = some (.val .bool) := by decide

/-- 基礎段階(C42)の範囲は空でない。 -/
theorem ex_basic_spec_let : basic exSpecLet = true := by decide

/-- 読みは生成形(`let «big» : Bool := decide (x > 10); let «n» : Nat := x + 1; («big» = true) → («n» > 11)`)と定義的に等しい(任意の x)。 -/
theorem ex_denoteP_spec_let (x : Nat) :
    denoteP (SEnv.ofList [("x", .val (.nat x))]) exSpecLet = ((decide (x > 10) = true) → x + 1 > 11) := rfl

/-- 同値定理の実例(一般定理の実例であって代用ではない): x の任意の値で、検体の意味は読みの命題(= 生成形)そのもの。 -/
theorem ex_Sem_spec_let (x : Nat) :
    Sem (SEnv.ofList [("x", .val (.nat x))]) exSpecLet ((decide (x > 10) = true) → x + 1 > 11) :=
  check_sound_prop [("x", .nat x)] ex_wtS_spec_let rfl (ex_denoteP_spec_let x).symm

/-- 値 / 命題の境界の実例: 命題の読みは Bool の読み(Model の読み)が `true` であることと同値。 -/
theorem ex_denoteP_iff_denoteB_let (x : Nat) :
    denoteP (SEnv.ofList [("x", .val (.nat x))]) exSpecLet ↔ denoteB (SEnv.ofList [("x", .val (.nat x))]).vals exSpecLet = true :=
  denoteP_iff_denoteB exSpecLet ex_basic_spec_let _ (by rw [SEnv.ctx_ofList]; exact SCtx.NoProp.ofList [("x", Val.nat x)] Val.ty)

/-- 値の等値と命題の同値の区別: 論理の位置の `a == b`(両辺が Bool の値)。 -/
def exEqBool : Core.Expr := .binop "==" (.var "a") (.var "b") .bool

/-- 読み(= 生成形)は値の等値 `a = b`。 -/
theorem ex_denoteP_eq_bool (a b : Bool) :
    denoteP (SEnv.ofList [("a", .val (.bool a)), ("b", .val (.bool b))]) exEqBool = (a = b) := rfl

/-- 意味は両辺の命題の同値 `(a = true) ↔ (b = true)`。 -/
theorem ex_Sem_eq_bool (a b : Bool) :
    Sem (SEnv.ofList [("a", .val (.bool a)), ("b", .val (.bool b))]) exEqBool ((a = true) ↔ (b = true)) :=
  Sem.eqForm (k := .eq) rfl (.varVal rfl) (.varVal rfl)

/-- 同値定理の実例: 意味と読みは同値(命題の同値と値の等値は、Bool の値では一致する)。 -/
theorem ex_Sem_denote_eq_bool (a b : Bool) : ((a = true) ↔ (b = true)) ↔ (a = b) := by
  have h1 := ex_Sem_eq_bool a b
  have h2 : Sem (SEnv.ofList [("a", .val (.bool a)), ("b", .val (.bool b))]) exEqBool (a = b) :=
    check_sound_prop [("a", .bool a), ("b", .bool b)]
      (by decide : wtS (SCtx.ofList [("a", .val .bool), ("b", .val .bool)]) exEqBool = some (.val .bool))
      rfl (ex_denoteP_eq_bool a b).symm
  rw [Sem_unique h1 h2]

/-! ## Statements の読み(C43): 命題の `let` を隠すパターン束縛、Bool の全要素の量化、値 / 命題の境界の一般形 -/

/-- `specPatShadow` と同じ形: `let p = forall n: Nat { n >= 0 }; match x { p if p == 0 => true, _ => p }`。腕の束縛 `p`(値)はガードと本体だけで有効で、
残りの腕の `p` は外側の命題(束縛は他の腕へ漏れない)。 -/
def exPatShadow : Core.Expr :=
  .let_ "p" .bool (.quant .forall_ [("n", .nat)] (.binop ">=" (.var "n") (.lit (.nat 0) .nat) .nat))
    (.match_ (.var "x") .nat
      [ .mk (.bind "p") (some (.binop "==" (.var "p") (.lit (.nat 0) .nat) .nat)) (.lit (.bool true) .bool),
        .mk .wild none (.var "p") ])

theorem ex_wtS_pat_shadow : wtS (SCtx.ofList [("x", .val .nat)]) exPatShadow = some .prop := by decide

/-- 読みは生成形 `let p : Prop := ∀ n, n ≥ 0; (match x with | p => (p = 0) → True) ∧ (¬ (match x with | p => p = 0) → (match x with | _ => p))` と
定義的に等しい(任意の x): ガードの `p` は値 `x`、残りの腕の `p` は命題。 -/
theorem ex_denoteP_pat_shadow (x : Nat) :
    denoteP (SEnv.ofList [("x", .val (.nat x))]) exPatShadow =
      (((x = 0) → True) ∧ (¬ (x = 0) → ∀ a : Nat, a ≥ 0)) := rfl

/-- 同値定理の実例: x の任意の値で、検体の意味は読みの命題そのもの。 -/
theorem ex_Sem_pat_shadow (x : Nat) :
    Sem (SEnv.ofList [("x", .val (.nat x))]) exPatShadow (((x = 0) → True) ∧ (¬ (x = 0) → ∀ a : Nat, a ≥ 0)) :=
  (ex_denoteP_pat_shadow x) ▸ Sem_denoteP (Γ := SCtx.ofList [("x", .val .nat)]) (τ := .prop) (by decide) rfl _ (by rw [SEnv.ctx_ofList]; rfl)

/-- `specExists` と同じ形: `exists b: Bool { b == (x > 0) }`(Bool の全要素の量化と、両辺が値の `==`)。 -/
def exExistsBool : Core.Expr :=
  .quant .exists_ [("b", .bool)] (.binop "==" (.var "b") (.binop ">" (.var "x") (.lit (.nat 0) .nat) .nat) .bool)

/-- 読みは生成形 `∃ (b : Bool), b = decide (x > 0)` と定義的に等しい。 -/
theorem ex_denoteP_exists_bool (x : Nat) :
    denoteP (SEnv.ofList [("x", .val (.nat x))]) exExistsBool = ∃ b : Bool, b = decide (x > 0) := rfl

theorem ex_Sem_exists_bool (x : Nat) :
    Sem (SEnv.ofList [("x", .val (.nat x))]) exExistsBool (∃ b : Bool, b = decide (x > 0)) :=
  (ex_denoteP_exists_bool x) ▸ Sem_denoteP (Γ := SCtx.ofList [("x", .val .nat)]) (τ := .prop) (by decide) rfl _ (by rw [SEnv.ctx_ofList]; rfl)

/-- 値 / 命題の境界の一般形の実例: 命題の束縛 `q` のある環境でも、命題でしか表せない部分を含まない `match`(C41 の検体)の命題の読みは Bool の読みが
`true` であることと同値。 -/
theorem ex_denoteP_iff_denoteB_match (x : Nat) (P : Prop) :
    denoteP (SEnv.ofList [("x", .val (.nat x)), ("q", .prop P)]) exMatchGuard ↔
      denoteB (SEnv.ofList [("x", .val (.nat x)), ("q", .prop P)]).vals exMatchGuard = true :=
  denoteP_iff_denoteB_noProp exMatchGuard _ rfl

/-! ## 不適格な Core は保証対象にならない(`wtR` / `wtS` が `none`) -/

/-- スコープ外の名前。 -/
theorem neg_wtR_unbound : wtR Ctx.empty (.var "x") = none := by decide

/-- 型の不一致(Bool + Nat)。 -/
theorem neg_wtR_ill_typed : wtR Ctx.empty (.binop "+" (.lit (.bool true) .bool) (.lit (.nat 1) .nat) .nat) = none := by decide

/-- 注釈と値の型が違う `let`。 -/
theorem neg_wtR_let_annotation : wtR Ctx.empty (.let_ "y" .bool (.lit (.nat 1) .nat) (.var "y")) = none := by decide

/-- 分岐の型が違う `if`。 -/
theorem neg_wtR_ite_branches : wtR Ctx.empty (.ite (.lit (.bool true) .bool) (.lit (.nat 1) .nat) (.lit (.bool false) .bool)) = none := by decide

/-- 対象外の構文(呼出し・文字列・lambda・Int)。 -/
theorem neg_wtR_call : wtR Ctx.empty (.call "A.f" []) = none := by decide
theorem neg_wtR_string : wtR Ctx.empty (.lit (.str "s") .string) = none := by decide
theorem neg_wtR_lambda : wtR Ctx.empty (.lambda [("x", .nat)] (.var "x")) = none := by decide
theorem neg_wtR_int : wtR Ctx.empty (.binop "+" (.lit (.nat 1) .int) (.lit (.nat 2) .int) .int) = none := by decide

/-- 網羅しない match(Nat のリテラルだけ)。 -/
theorem neg_wtR_match_not_exhaustive :
    wtR Ctx.empty (.match_ (.lit (.nat 3) .nat) .nat [.mk (.lit (.nat 0)) none (.lit (.nat 1) .nat)]) = none := by decide

/-- 必ず一致する腕があってもガード付きなら網羅と数えない。 -/
theorem neg_wtR_match_guarded_only :
    wtR Ctx.empty (.match_ (.lit (.nat 3) .nat) .nat [.mk .wild (some (.lit (.bool false) .bool)) (.lit (.nat 1) .nat)]) = none := by decide

/-- Bool の match は `true` と `false` のガード無しリテラルで網羅的だが、片方だけでは網羅しない。 -/
theorem ex_wtR_match_bool_complete :
    wtR Ctx.empty (.match_ (.lit (.bool true) .bool) .bool
      [.mk (.lit (.bool true)) none (.lit (.nat 1) .nat), .mk (.lit (.bool false)) none (.lit (.nat 0) .nat)]) = some .nat := by decide
theorem neg_wtR_match_bool_half :
    wtR Ctx.empty (.match_ (.lit (.bool true) .bool) .bool [.mk (.lit (.bool true)) none (.lit (.nat 1) .nat)]) = none := by decide

/-- spec: 命題に束ねた名前は値の位置(算術の被演算子)に置けない。 -/
theorem neg_wtS_prop_in_value : wtS (SCtx.ofList [("p", .prop)]) (.binop "+" (.var "p") (.lit (.nat 1) .nat) .nat) = none := by decide

/-- spec: 命題に束ねた名前は scrutinee に置けない。 -/
theorem neg_wtS_prop_scrutinee :
    wtS (SCtx.ofList [("p", .prop)]) (.match_ (.var "p") .bool [.mk .wild none (.lit (.bool true) .bool)]) = none := by decide

/-- spec: 量化の束縛型が Nat / Bool でなければ対象外。 -/
theorem neg_wtS_quant_string : wtS SCtx.empty (.quant .forall_ [("s", .string)] (.lit (.bool true) .bool)) = none := by decide

/-- spec: runtime の式としては適格でも、Nat の値は論理の位置の型ではない(`isForm = false`)。 -/
theorem ex_wtS_nat_not_form : wtS SCtx.empty (.lit (.nat 1) .nat) = some (.val .nat) ∧ STy.isForm (.val .nat) = false := by decide

/-! ## 評価不能を成功値に置き換えない(行き詰まりは `none`、spec は導出が無い) -/

theorem neg_eval_unbound : eval Env.empty (.var "x") = none := by decide

theorem neg_eval_ill_typed : eval Env.empty (.binop "+" (.lit (.bool true) .bool) (.lit (.nat 1) .nat) .nat) = none := by decide

/-- どの腕も一致しない match は `none`(既定値で埋めない)。 -/
theorem neg_eval_match_stuck :
    eval Env.empty (.match_ (.lit (.nat 3) .nat) .nat [.mk (.lit (.nat 0)) none (.lit (.nat 1) .nat)]) = none := by decide

/-- 最後の腕のガードが偽でも `none`。 -/
theorem neg_eval_guard_stuck :
    eval Env.empty (.match_ (.lit (.nat 3) .nat) .nat [.mk .wild (some (.lit (.bool false) .bool)) (.lit (.nat 1) .nat)]) = none := by decide

/-- 対象外の構文は `none`。 -/
theorem neg_eval_call : eval Env.empty (.call "A.f" []) = none := by decide

/-- spec: スコープ外の名前には意味が無い(導出が無い)。 -/
theorem neg_Sem_unbound : ¬ ∃ P, Sem SEnv.empty (.var "x") P := by
  rintro ⟨P, h⟩
  cases h with
  | varVal h' => simp [SEnv.empty] at h'
  | varProp h' => simp [SEnv.empty] at h'

/-- spec: Nat の値(算術)には命題としての意味が無い。 -/
theorem neg_Sem_nat_value : ¬ ∃ P, Sem SEnv.empty (.binop "+" (.lit (.nat 1) .nat) (.lit (.nat 2) .nat) .nat) P := by
  rintro ⟨P, h⟩
  cases h with
  | eqNat hk => simp [BinOp.ofString?] at hk
  | cmpNat hk => simp [BinOp.ofString?] at hk

/-- spec: どの腕も一致しない match には意味が無い。 -/
theorem neg_Sem_match_stuck :
    ¬ ∃ P, Sem SEnv.empty (.match_ (.lit (.nat 3) .nat) .nat [.mk (.lit (.nat 0)) none (.lit (.bool true) .bool)]) P := by
  rintro ⟨P, h⟩
  cases h with
  | matchSkip hs hp hr => cases hr
  | matchHit hs hp hb =>
    have : (eval SEnv.empty.vals (.lit (.nat 3) .nat)) = some (.nat 3) := by decide
    rw [this] at hs
    cases hs
    simp [matchPat] at hp

end NaruSem
