import NaruSem.SurfaceTotality

/-!
# Surface AST の対象範囲と行き詰まりの検体(IDEAL.md C48)

一般定理が空虚でないこと、不適格な AST(スコープ外・型不一致・値の位置の命題・網羅しない `match`・対象外の構文)が保証対象にならないこと、
評価不能を成功値に置き換えないことを、具体的な AST で kernel に検査させる(`decide`: `Surf.wtR` / `Surf.wtS` / `Surf.eval` は構造的再帰の関数なので
kernel が計算できる。位置情報は `{}`(既定値)で、意味には関与しない)。名前付きの定理にして `NaruSem.lean` の公理監査に載せる。
実際の構文解析の出力から得た検体は `lake exe naru_test semantics`(`tests/accept/sem_core.naru`)が引用して検査する(`SurfaceQuote.lean`)。
-/

namespace NaruSem.Surf
open Naru

/-- `Nat` の型注釈。 -/
def tyNat : Ty := .named {} ["Nat"] []
/-- `Bool` の型注釈。 -/
def tyBool : Ty := .named {} ["Bool"] []

/-! ## 適格な検体(手書き): 対象範囲は空でない -/

/-- `{ let y = x + 1; y * 2 }`(x : Nat)。構文解析の出力と同じく、fn の本体はブロックで、`let` の列と末尾式を持つ。 -/
def exBlock : Expr :=
  .block {} [.letS {} "y" none (.binop {} "+" (.var {} ["x"]) (.lit {} (.nat 1)))]
    (some (.binop {} "*" (.var {} ["y"]) (.lit {} (.nat 2))))

theorem ex_wtR_block : wtR (Ctx.ofList [("x", .nat)]) exBlock = some .nat := by decide

/-- x = 4 で評価すると 10。 -/
theorem ex_eval_block : eval (Env.ofList [("x", .nat 4)]) exBlock = some (.nat 10) := by decide

/-- 型注釈つきの `let`(`let y: Nat = x + 1; let b: Bool = y > 2; if b { y } else { 0 }`)。注釈は値の型と一致しなければならない。 -/
def exAnnot : Expr :=
  .block {} [ .letS {} "y" (some tyNat) (.binop {} "+" (.var {} ["x"]) (.lit {} (.nat 1))),
              .letS {} "b" (some tyBool) (.binop {} ">" (.var {} ["y"]) (.lit {} (.nat 2))) ]
    (some (.ite {} (.var {} ["b"]) (.block {} [] (some (.var {} ["y"]))) (.block {} [] (some (.lit {} (.nat 0))))))

theorem ex_wtR_annot : wtR (Ctx.ofList [("x", .nat)]) exAnnot = some .nat := by decide
theorem ex_eval_annot : eval (Env.ofList [("x", .nat 4)]) exAnnot = some (.nat 5) := by decide

/-- ガード付き match(同名の束縛、ガード不成立からの継続): `match 7 { x if x == 0 => false, _ => x == 0 }` は仮引数 x = 0 を見る。 -/
def exMatchGuard : Expr :=
  .matchE {} (.lit {} (.nat 7))
    [ .mk (.bind {} "x") (some (.binop {} "==" (.var {} ["x"]) (.lit {} (.nat 0)))) (.lit {} (.bool false)),
      .mk (.wild {}) none (.binop {} "==" (.var {} ["x"]) (.lit {} (.nat 0))) ]

theorem ex_wtR_match_guard : wtR (Ctx.ofList [("x", .nat)]) exMatchGuard = some .bool := by decide
theorem ex_eval_match_guard : eval (Env.ofList [("x", .nat 0)]) exMatchGuard = some (.bool true) := by decide

/-- Nat の `min` / `max`(位置引数 1 つのメソッド呼出し)。 -/
theorem ex_wtR_min : wtR (Ctx.ofList [("x", .nat), ("y", .nat)]) (.method {} (.var {} ["x"]) "min" [.var {} ["y"]]) = some .nat := by decide
theorem ex_eval_min : eval (Env.ofList [("x", .nat 4), ("y", .nat 2)]) (.method {} (.var {} ["x"]) "min" [.var {} ["y"]]) = some (.nat 2) := by decide

/-- spec: `forall n: Nat { n + x >= x }` は命題(量化の本体もブロック)。 -/
def exForall : Expr :=
  .quant {} .forall_ [{ name := "n", ty := some tyNat, span := {} }]
    (.block {} [] (some (.binop {} ">=" (.binop {} "+" (.var {} ["n"]) (.var {} ["x"])) (.var {} ["x"]))))

theorem ex_wtS_forall : wtS (SCtx.ofList [("x", .val .nat)]) exForall = some .prop := by decide

/-- spec: ブロックの `let` は値が命題なら名前を命題に束ねる(`let p = forall …; let q = p && x >= 1; q`)。 -/
def exLetProp : Expr :=
  .block {} [ .letS {} "p" none exForall,
              .letS {} "q" none (.binop {} "&&" (.var {} ["p"]) (.binop {} ">=" (.var {} ["x"]) (.lit {} (.nat 1)))) ]
    (some (.var {} ["q"]))

theorem ex_wtS_let_prop : wtS (SCtx.ofList [("x", .val .nat)]) exLetProp = some .prop := by decide

/-- spec: 注釈 `Bool` の `let` も値が命題なら命題に束ねる。値の `let` は注釈と一致(`let p: Bool = forall …; let b: Bool = x > 0; p && b`)。 -/
def exLetAnnot : Expr :=
  .block {} [ .letS {} "p" (some tyBool) exForall,
              .letS {} "b" (some tyBool) (.binop {} ">" (.var {} ["x"]) (.lit {} (.nat 0))) ]
    (some (.binop {} "&&" (.var {} ["p"]) (.var {} ["b"])))

theorem ex_wtS_let_annot : wtS (SCtx.ofList [("x", .val .nat)]) exLetAnnot = some .prop := by decide

/-- spec: 注釈の無い `==` は、両辺が Nat の値なら値の等値(Bool の値)、命題を含めば命題。 -/
theorem ex_wtS_eq_nat : wtS (SCtx.ofList [("x", .val .nat)]) (.binop {} "==" (.var {} ["x"]) (.lit {} (.nat 1))) = some (.val .bool) := by decide
theorem ex_wtS_eq_prop : wtS (SCtx.ofList [("p", .prop), ("a", .val .bool)]) (.binop {} "==" (.var {} ["p"]) (.var {} ["a"])) = some .prop := by decide

/-- spec の意味の実例: `x == 1`(x = 1)の意味は `1 = 1`(値の等値)。 -/
theorem ex_Sem_eq_nat : Sem (SEnv.ofList [("x", .val (.nat 1))]) (.binop {} "==" (.var {} ["x"]) (.lit {} (.nat 1))) ((1 : Nat) = 1) :=
  Sem.eqNat (k := .eq) rfl (by decide) (by decide)

/-- spec の意味の実例: ブロックの命題の `let`。`let p = forall n: Nat { n + x >= x }; let q = p && x >= 1; q` の意味は `(∀ n, n + x ≥ x) ∧ x ≥ 1`。 -/
theorem ex_Sem_let_prop (x : Nat) :
    Sem (SEnv.ofList [("x", .val (.nat x))]) exLetProp ((∀ n : Nat, n + x ≥ x) ∧ x ≥ 1) :=
  .blockLetProp rfl
    (.forallCons (t := .nat) (F := fun (n : Nat) => n + x ≥ x) rfl fun _ => .quantNil (.blockTail (.cmpNat (k := .ge) rfl rfl rfl)))
    (.blockLetProp rfl
      (.logic (k := .and) rfl (.varProp rfl) (.cmpNat (k := .ge) rfl rfl rfl))
      (.blockTail (.varProp rfl)))

/-! ## 最小の fn / spec 宣言の包装 -/

/-- `fn exBlockFn(x: Nat) -> Nat { let y = x + 1; y * 2 }` の形の宣言。 -/
def exFnDecl : Decl :=
  { kind := .fn, name := "exBlockFn", span := {}, params := [{ name := "x", ty := tyNat, span := {} }], ret := some tyNat, body := exBlock }

theorem ex_wtDecl_fn : wtDecl exFnDecl = some (.runtime [("x", .nat)] .nat) := by decide

/-- `predicate exLetPropPred(x: Nat) { let p = forall …; let q = p && x >= 1; q }` の形の宣言。 -/
def exPredDecl : Decl :=
  { kind := .predicate, name := "exLetPropPred", span := {}, params := [{ name := "x", ty := tyNat, span := {} }], ret := none, body := exLetProp }

theorem ex_wtDecl_pred : wtDecl exPredDecl = some (.spec [("x", .nat)] .prop) := by decide

/-- 戻り型の注釈が本体の型と違う fn、戻り型の注釈のある spec 宣言、observer、仮引数の注釈が対象外の fn は包装として不適格。 -/
theorem neg_wtDecl_ret_mismatch : wtDecl { exFnDecl with ret := some tyBool } = none := by decide
theorem neg_wtDecl_spec_ret : wtDecl { exPredDecl with ret := some tyBool } = none := by decide
theorem neg_wtDecl_observer : wtDecl { exFnDecl with kind := .observer } = none := by decide
theorem neg_wtDecl_param_string :
    wtDecl { exFnDecl with params := [{ name := "x", ty := .named {} ["String"] [], span := {} }] } = none := by decide

/-! ## 不適格な AST は保証対象にならない(`wtR` / `wtS` が `none`) -/

/-- スコープ外の名前。 -/
theorem neg_wtR_unbound : wtR Ctx.empty (.var {} ["x"]) = none := by decide

/-- 型の不一致(Bool + Nat)。 -/
theorem neg_wtR_ill_typed : wtR Ctx.empty (.binop {} "+" (.lit {} (.bool true)) (.lit {} (.nat 1))) = none := by decide

/-- 注釈と値の型が違う `let`。 -/
theorem neg_wtR_let_annotation : wtR Ctx.empty (.block {} [.letS {} "y" (some tyBool) (.lit {} (.nat 1))] (some (.var {} ["y"]))) = none := by decide

/-- 注釈の型が対象外(`String`)。 -/
theorem neg_wtR_let_string_annotation :
    wtR Ctx.empty (.block {} [.letS {} "y" (some (.named {} ["String"] [])) (.lit {} (.nat 1))] (some (.var {} ["y"]))) = none := by decide

/-- 分岐の型が違う `if`。 -/
theorem neg_wtR_ite_branches :
    wtR Ctx.empty (.ite {} (.lit {} (.bool true)) (.block {} [] (some (.lit {} (.nat 1)))) (.block {} [] (some (.lit {} (.bool false))))) = none := by decide

/-- 対象外の構文: 大域の経路名、文字列、Nat 以外のメソッド、引数の数の違う `min`、末尾式の無いブロック、runtime の量化。 -/
theorem neg_wtR_path : wtR Ctx.empty (.var {} ["A", "f"]) = none := by decide
theorem neg_wtR_string : wtR Ctx.empty (.lit {} (.str "s")) = none := by decide
theorem neg_wtR_method : wtR (Ctx.ofList [("x", .nat)]) (.method {} (.var {} ["x"]) "size" []) = none := by decide
theorem neg_wtR_min_arity : wtR (Ctx.ofList [("x", .nat)]) (.method {} (.var {} ["x"]) "min" []) = none := by decide
theorem neg_wtR_block_no_tail : wtR Ctx.empty (.block {} [.letS {} "y" none (.lit {} (.nat 1))] none) = none := by decide
theorem neg_wtR_quant : wtR Ctx.empty exForall = none := by decide

/-- 網羅しない match(Nat のリテラルだけ)。 -/
theorem neg_wtR_match_not_exhaustive :
    wtR Ctx.empty (.matchE {} (.lit {} (.nat 3)) [.mk (.lit {} (.nat 0)) none (.lit {} (.nat 1))]) = none := by decide

/-- 必ず一致する腕があってもガード付きなら網羅と数えない。 -/
theorem neg_wtR_match_guarded_only :
    wtR Ctx.empty (.matchE {} (.lit {} (.nat 3)) [.mk (.wild {}) (some (.lit {} (.bool false))) (.lit {} (.nat 1))]) = none := by decide

/-- Bool の match は `true` と `false` のガード無しリテラルで網羅的だが、片方だけでは網羅しない。 -/
theorem ex_wtR_match_bool_complete :
    wtR Ctx.empty (.matchE {} (.lit {} (.bool true))
      [.mk (.lit {} (.bool true)) none (.lit {} (.nat 1)), .mk (.lit {} (.bool false)) none (.lit {} (.nat 0))]) = some .nat := by decide
theorem neg_wtR_match_bool_half :
    wtR Ctx.empty (.matchE {} (.lit {} (.bool true)) [.mk (.lit {} (.bool true)) none (.lit {} (.nat 1))]) = none := by decide

/-- spec: 網羅しない match(Nat のリテラルだけ)は spec でも保証対象にならない。 -/
theorem neg_wtS_match_not_exhaustive :
    wtS (SCtx.ofList [("x", .val .nat)]) (.matchE {} (.var {} ["x"]) [.mk (.lit {} (.nat 0)) none (.lit {} (.bool true))]) = none := by decide

/-- spec: 命題に束ねた名前は値の位置(算術の被演算子)に置けない。 -/
theorem neg_wtS_prop_in_value : wtS (SCtx.ofList [("p", .prop)]) (.binop {} "+" (.var {} ["p"]) (.lit {} (.nat 1))) = none := by decide

/-- spec: 命題に束ねた名前は scrutinee に置けない。 -/
theorem neg_wtS_prop_scrutinee :
    wtS (SCtx.ofList [("p", .prop)]) (.matchE {} (.var {} ["p"]) [.mk (.wild {}) none (.lit {} (.bool true))]) = none := by decide

/-- spec: 命題を Nat の注釈の `let` に束ねられない(`let n: Nat = forall …`)。 -/
theorem neg_wtS_prop_nat_annotation :
    wtS (SCtx.ofList [("x", .val .nat)]) (.block {} [.letS {} "n" (some tyNat) exForall] (some (.lit {} (.bool true)))) = none := by decide

/-- spec: 量化の束縛型の注釈が無い・Nat / Bool でなければ対象外。 -/
theorem neg_wtS_quant_untyped :
    wtS SCtx.empty (.quant {} .forall_ [{ name := "s", ty := none, span := {} }] (.block {} [] (some (.lit {} (.bool true))))) = none := by decide
theorem neg_wtS_quant_string :
    wtS SCtx.empty (.quant {} .forall_ [{ name := "s", ty := some (.named {} ["String"] []), span := {} }]
      (.block {} [] (some (.lit {} (.bool true))))) = none := by decide

/-- spec: runtime の式としては適格でも、Nat の値は論理の位置の型ではない(`isForm = false`)。 -/
theorem ex_wtS_nat_not_form : wtS SCtx.empty (.lit {} (.nat 1)) = some (.val .nat) ∧ STy.isForm (.val .nat) = false := by decide

/-! ## 評価不能を成功値に置き換えない(行き詰まりは `none`、spec は導出が無い) -/

theorem neg_eval_unbound : eval Env.empty (.var {} ["x"]) = none := by decide

theorem neg_eval_ill_typed : eval Env.empty (.binop {} "+" (.lit {} (.bool true)) (.lit {} (.nat 1))) = none := by decide

/-- どの腕も一致しない match は `none`(既定値で埋めない)。 -/
theorem neg_eval_match_stuck :
    eval Env.empty (.matchE {} (.lit {} (.nat 3)) [.mk (.lit {} (.nat 0)) none (.lit {} (.nat 1))]) = none := by decide

/-- 最後の腕のガードが偽でも `none`。 -/
theorem neg_eval_guard_stuck :
    eval Env.empty (.matchE {} (.lit {} (.nat 3)) [.mk (.wild {}) (some (.lit {} (.bool false))) (.lit {} (.nat 1))]) = none := by decide

/-- 末尾式の無いブロック・`let` の値が行き詰まるブロックは `none`。 -/
theorem neg_eval_block_no_tail : eval Env.empty (.block {} [] none) = none := by decide
theorem neg_eval_block_stuck_let : eval Env.empty (.block {} [.letS {} "y" none (.var {} ["x"])] (some (.lit {} (.nat 1)))) = none := by decide

/-- 対象外の構文は `none`。 -/
theorem neg_eval_path : eval Env.empty (.var {} ["A", "f"]) = none := by decide
theorem neg_eval_quant : eval Env.empty exForall = none := by decide

/-- spec: スコープ外の名前には意味が無い(導出が無い)。 -/
theorem neg_Sem_unbound : ¬ ∃ P, Sem SEnv.empty (.var {} ["x"]) P := by
  rintro ⟨P, h⟩
  cases h with
  | varVal h' => simp [SEnv.empty] at h'
  | varProp h' => simp [SEnv.empty] at h'

/-- spec: Nat の値(算術)には命題としての意味が無い。 -/
theorem neg_Sem_nat_value : ¬ ∃ P, Sem SEnv.empty (.binop {} "+" (.lit {} (.nat 1)) (.lit {} (.nat 2))) P := by
  rintro ⟨P, h⟩
  cases h with
  | logic hk => simp [BinOp.ofString?] at hk
  | eqNat hk => simp [BinOp.ofString?] at hk
  | eqForm hk => simp [BinOp.ofString?] at hk
  | cmpNat hk => simp [BinOp.ofString?] at hk
  | cmpBool hk => simp [BinOp.ofString?] at hk

/-- spec: どの腕も一致しない match には意味が無い。 -/
theorem neg_Sem_match_stuck :
    ¬ ∃ P, Sem SEnv.empty (.matchE {} (.lit {} (.nat 3)) [.mk (.lit {} (.nat 0)) none (.lit {} (.bool true))]) P := by
  rintro ⟨P, h⟩
  cases h with
  | matchSkip hs hp hr => cases hr
  | matchHit hs hp hb =>
    have : (eval SEnv.empty.vals (.lit {} (.nat 3))) = some (.nat 3) := by decide
    rw [this] at hs
    cases hs
    simp [matchPat] at hp

/-- spec: 末尾式の無いブロックには意味が無い。 -/
theorem neg_Sem_block_no_tail : ¬ ∃ P, Sem SEnv.empty (.block {} [] none) P := by
  rintro ⟨P, h⟩
  cases h

/-- 論理の位置の式は Nat の値に評価されない(`Sem_not_nat`)の実例: `x > 0 == a`(両辺が論理の位置)の評価は Bool。 -/
theorem ex_Sem_not_nat_eq (x : Nat) (a : Bool) :
    ∀ n, eval (SEnv.ofList [("x", .val (.nat x)), ("a", .val (.bool a))]).vals
      (.binop {} "==" (.binop {} ">" (.var {} ["x"]) (.lit {} (.nat 0))) (.var {} ["a"])) ≠ some (.nat n) :=
  Sem_not_nat (.eqForm (k := .eq) rfl (.cmpNat (k := .gt) rfl rfl rfl) (.varVal rfl)) _ (Agree.vals _)

end NaruSem.Surf
