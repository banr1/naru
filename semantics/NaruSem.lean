import NaruSem.Scope
import NaruSem.Eval
import NaruSem.Sem
import NaruSem.Totality
import NaruSem.SemTotality
import NaruSem.Denote
import NaruSem.DenoteProp
import NaruSem.Examples
import NaruSem.Quote
import NaruSem.Surface
import NaruSem.SurfaceEval
import NaruSem.SurfaceTotality
import NaruSem.SurfaceExamples
import NaruSem.SurfaceQuote
import NaruSem.Lower
import NaruSem.LowerExamples
import NaruSem.LowerSpec
import NaruSem.LowerSpecExamples
import NaruSem.Call
import NaruSem.CallTotality
import NaruSem.CallExamples
import NaruSem.SurfaceCall
import NaruSem.CallQuote
import NaruSem.Audit

/-!
# `NaruSem` — naru の Core IR と Surface AST の独立した意味論とコンパイラ意味論保存の証明(IDEAL.md C39〜C47、C48〜C52)

`lake build NaruSem` が、意味論・適格性の定義、一般定理、検体、公理監査をまとめて Lean kernel に検査させる(C45 の検査入口。
走らせ方は `docs/testing.md`「コンパイラ意味論保存」、構成と定理の一覧は `docs/architecture.md`「コンパイラ意味論保存」)。
backend の出力を意味と定義せず、翻訳の正しさを仮定しない。

- `NaruSem/Scope.lean` — 今回の保存対象の範囲と整形性: 型 `Ty` / `STy`、演算 `BinOp` / `NatMethod`、文脈 `Ctx` / `SCtx`、
  runtime の型付け `wtR`(+ `wtArmsR` / `wtArmR`)、spec の型付け `wtS`(+ `wtArmsS` / `wtArmS`)、パターン `wtPat`、網羅性 `exhaustive`、
  命題の区分 `proppyS`。
- `NaruSem/Eval.lean` — runtime の表示的意味論 `eval`(値 `Val`、環境 `Env`、演算の意味、`matchPat` / `evalArms`)。
- `NaruSem/Sem.lean` — spec の評価関係 `Sem`(環境 `SEnv`: 値と命題を区別)。
- `NaruSem/Totality.lean` — runtime の全域性 `eval_total` と一意性 `Eval_unique`。
- `NaruSem/SemTotality.lean` — spec の意味の存在 `Sem_exists` と一意性 `Sem_unique`。
- `NaruSem/Denote.lean` — Model の保存(C40 / C41 / C44): 生成 Lean の読み `denoteN` / `denoteB` と腕の列の読み `denoteArmsN` / `denoteArmsB`、
  基礎段階の範囲 `basic`(段階の記録)、保存定理 `denote_sound`(`preserve_nat` / `preserve_bool`。基礎の構文と非再帰の Nat / Bool の `match`)、
  腕の列・腕の一般補題 `denoteArms_sound` / `denoteArm_sound`、腕の選択と束縛の形 `denoteArmsV_hit` / `_miss` / `_guard_true` / `_guard_false`、
  実生成宣言への接続検査の健全性 `check_sound_nat` / `check_sound_bool`。
- `NaruSem/DenoteProp.lean` — Statements の保存(C42 / C43 / C44): 生成 Lean の命題の読み `denoteP`(+ 腕の列 `denoteArmsP`、量化 `denoteQuant`)、
  値 / 命題の境界 `denoteP_iff_denoteB_noProp`(`proppyS` が偽の式すべて。`proppyS` の文脈の合同 `proppyS_congr`)、一般同値定理 `Sem_denote`
  (`wtS` で適格な式すべて: 量化・命題の `let` と shadowing・命題の条件の `if`・ガード付き `match` を含む。`Sem_denote_all` は網羅性を要求しない
  型付け `wtSNoExh` を仮定に `Sem` の導出の帰納法。`Sem_denoteP`: 読みは意味である)、腕の選択と束縛の形 `denoteArmsP_hit` / `_miss` / `_guard` /
  `_guard_true` / `_guard_false`、量化の読みの形 `denoteQuant_forall_cons` / `_exists_cons`、接続検査の健全性 `check_sound_prop`、異なる表現の対応関係
  (`CmpOp.leanBoolProp_iff` / `EqOp.propIff_bool`: 値の等値と命題の同値の区別 …)。基礎段階(C42)の `basic` / `SCtx.NoProp` は段階の記録(系)。
- `NaruSem/Examples.lean` — 対象範囲・境界の挙動・不適格な Core・行き詰まり・読みの検体(`decide`)。
- `NaruSem/Quote.lean` — 実際の compiler 経路の Core を Lean の項として引用し、一致を照合する(`lake exe naru_test semantics` が使う)。
- `NaruSem/Surface.lean` — Surface AST の保存対象(C48): 構文解析の出力の部分集合 `Surf.Expr` / `Arm` / `Stmt` / `Pat` / `Ty` / `Binder`(位置情報つき)と
  構文解析の型への埋め込み `Expr.toAst`、runtime の型付け `Surf.wtR`(+ `wtStmtsR` / `wtArmsR` / `wtArmR`)、spec の型付け `Surf.wtS`(+ `wtStmtsS` / `wtArmsS` /
  `wtArmS`)、パターン `Surf.wtPat`、網羅性 `Surf.exhaustive`、命題の区分 `Surf.proppyS`(ブロックの `let` の列と末尾式、注釈の無い `==`、位置引数の
  メソッドは AST 固有の規則)、最小の fn / spec 宣言の包装 `Surf.Decl` とその適格性 `Surf.wtDecl`(種別・仮引数と戻り型の注釈・本体の型)。
- `NaruSem/SurfaceEval.lean` — Surface AST の意味(C48): runtime の表示的意味論 `Surf.eval`(+ `evalStmts` / `evalArms`、`Surf.matchPat`)、spec の評価関係
  `Surf.Sem`(`==` / `!=` は両辺が Nat の値なら値の等しさ `eqNat`、そうでなければ命題の同値 `eqForm`)。Core の意味(`eval` / `Sem`)は参照しない。
- `NaruSem/SurfaceTotality.lean` — Surface AST の意味が定まること(C48): runtime の全域性 `Surf.eval_total` と一意性 `Surf.Eval_unique`、spec の意味の存在
  `Surf.Sem_exists` と一意性 `Surf.Sem_unique`、評価の単調性 `Surf.eval_mono`、論理の位置の式は Nat の値に評価されない `Surf.Sem_not_nat`
  (`eqNat` / `eqForm` の排他性)。
- `NaruSem/SurfaceExamples.lean` — Surface AST の対象範囲・不適格な AST・行き詰まりの検体(`decide`)。
- `NaruSem/SurfaceQuote.lean` — 実際の構文解析の出力を対象の AST に写し(`ofAst?`)、Lean の項として引用し、埋め込みと `==` で一致を照合する。
- `NaruSem/Lower.lean` — Surface AST → Core の対応(C49): frontend から独立の変換 `Surf.lower`(+ `lowerStmts` / `lowerArms` / `lowerArm` / `lowerPat`、ブロックの
  `let` の列の畳み込み `Surf.mkLets`)、一般定理 `Surf.lower_sound`(任意の適格な runtime の AST に変換が定まり、その Core は適格で、任意の環境で AST の意味と
  Core の意味が一致する。`Surf.wtR.mutual_induct` の `Surf.lower_sound_all`。系 `lower_total` / `lower_wt` / `lower_eval`)、C40 / C41 と合成した
  `Surf.preserve_nat` / `Surf.preserve_bool`(AST の意味 = 生成 Lean の読み)、接続検査の健全性 `Surf.check_sound_nat` / `Surf.check_sound_bool`
  (`low_<f>` + `conn_<f>` から AST の意味 = 実生成宣言の値)。
- `NaruSem/LowerExamples.lean` — 変換の検体(C49 / C52): 対象の各構文の変換の形、対象外の構文・型の定まらない式は変換されない、意味の異なる(適格な)Core は変換結果でない。
- `NaruSem/LowerSpec.lean` — spec の Surface AST → Core の対応(C50): frontend から独立の変換 `Surf.lowerS`(+ `lowerStmtsS` / `lowerArmsS` / `lowerArmS` /
  `lowerBinders`。論理の位置は `Surf.wtS` に導かれ、値の位置は `Surf.lower`)、一般定理 `Surf.lowerS_sound`(任意の適格な spec の AST に変換が定まり、その Core は
  適格で、対応する任意の環境で AST の意味は Core の意味。`Surf.wtS.mutual_induct` の `Surf.lowerS_sound_all`。系 `lowerS_total` / `lowerS_wt` / `lowerS_Sem`)、
  双方向の同値 `Surf.Sem_lowerS_iff`(`Surf.Sem_exists` + `NaruSem.Sem_unique`)、命題の区分の一致 `Surf.proppyS_lower` / `Surf.proppyS_lowerS`、
  C42 / C43 と合成した `Surf.preserve_prop`(AST の意味 ↔ 生成 Lean の読み)、接続検査の健全性 `Surf.check_sound_prop`(`lows_<f>` + `conn_<f>` から
  AST の意味 = 実生成宣言の命題)、量化・腕・束縛の列の対応の補題。
- `NaruSem/LowerSpecExamples.lean` — spec の変換の検体(C50 / C52): 量化・命題の `let`・注釈の無い `==`・命題のガード付き `match` の変換の形と一般定理の実例、
  対象外は変換されない、意味の異なる(適格な)Core(`forall` / `exists` の取り違え、命題の `let` の束縛の取り違え)は変換結果でない。
- `NaruSem/Audit.lean` — 公理監査 `#audit_axioms`(許容する標準公理と理由はそこに)。

## 公理監査(C45)

必須の定理・補題・検体をすべて列挙する。欠落(名前解決の失敗)・未完了(`sorryAx`)・`native_decide`(`Lean.ofReduceBool`)・
独自の公理への依存はここでビルドが失敗する。`lake env lean semantics/NaruSem.lean` の出力の `audit ok:` の行が各定数の依存する公理の一覧
(`lake exe naru_test semantics` が必須の定理の行を照合する)。
-/

-- C39: 意味論の全域性・一意性と、環境と文脈の対応の補題
#audit_axioms NaruSem.eval_total NaruSem.Eval_unique NaruSem.wtR_total_all
  NaruSem.Sem_exists NaruSem.Sem_unique NaruSem.Sem_exists_all
  NaruSem.matchPat_types NaruSem.matchPat_irrefutable NaruSem.Env.ty_ext NaruSem.Env.ty_extList
  NaruSem.SEnv.ctx_ext NaruSem.SEnv.ctx_extVals NaruSem.SEnv.ctx_vals NaruSem.evalS_total

-- C39: 対象範囲と境界の挙動・不適格な Core・行き詰まりの検体
#audit_axioms NaruSem.ex_wtR_let NaruSem.ex_eval_let NaruSem.ex_eval_match_guard NaruSem.ex_wtS_forall NaruSem.ex_wtS_prop_and
  NaruSem.ex_nat_sub_truncates NaruSem.ex_nat_div_zero NaruSem.ex_nat_mod_zero NaruSem.ex_bool_order NaruSem.ex_implies
  NaruSem.neg_wtR_unbound NaruSem.neg_wtR_ill_typed NaruSem.neg_wtR_let_annotation NaruSem.neg_wtR_ite_branches
  NaruSem.neg_wtR_call NaruSem.neg_wtR_string NaruSem.neg_wtR_lambda NaruSem.neg_wtR_int
  NaruSem.neg_wtR_match_not_exhaustive NaruSem.neg_wtR_match_guarded_only NaruSem.ex_wtR_match_bool_complete NaruSem.neg_wtR_match_bool_half
  NaruSem.neg_wtS_prop_in_value NaruSem.neg_wtS_prop_scrutinee NaruSem.neg_wtS_quant_string NaruSem.ex_wtS_nat_not_form
  NaruSem.neg_eval_unbound NaruSem.neg_eval_ill_typed NaruSem.neg_eval_match_stuck NaruSem.neg_eval_guard_stuck NaruSem.neg_eval_call
  NaruSem.neg_Sem_unbound NaruSem.neg_Sem_nat_value NaruSem.neg_Sem_match_stuck

-- C40 / C44: Model の基礎段階の保存定理と、実生成宣言への接続検査の健全性・異なる表現の対応関係
#audit_axioms NaruSem.denote_sound NaruSem.preserve_nat NaruSem.preserve_bool NaruSem.denote_sound_all
  NaruSem.check_sound_nat NaruSem.check_sound_bool NaruSem.Env.ty_ofList NaruSem.denoteV_ty
  NaruSem.CmpOp.leanBool_eq NaruSem.EqOp.leanNat_eq NaruSem.EqOp.leanBool_eq

-- C40: 基礎段階の範囲と読みの境界の検体
#audit_axioms NaruSem.ex_basic_let NaruSem.neg_basic_match NaruSem.ex_denote_sub_truncates NaruSem.ex_denote_div_zero
  NaruSem.ex_denote_mod_zero NaruSem.ex_denote_bool_order NaruSem.ex_preserve_let

-- C41 / C44: Model の match の保存 — 腕の列・腕の一般補題、腕の選択と束縛の形、腕の列の読みの展開
#audit_axioms NaruSem.denoteArms_sound NaruSem.denoteArm_sound NaruSem.denoteArmsV_hit NaruSem.denoteArmsV_miss
  NaruSem.denoteArmsV_guard_true NaruSem.denoteArmsV_guard_false NaruSem.denoteArmsN_cons NaruSem.denoteArmsB_cons NaruSem.denoteArmsV_ty

-- C41: match の読みの検体(ガード不成立からの継続と束縛の範囲、Bool のリテラルの腕、保存定理の実例)
#audit_axioms NaruSem.ex_wtR_match_guard NaruSem.ex_denote_match_guard NaruSem.ex_denote_match_bool NaruSem.ex_preserve_match

-- C42 / C44: Statements の基礎段階の同値定理、値 / 命題の境界、接続検査の健全性、異なる表現の対応関係、基礎段階の範囲の補題
#audit_axioms NaruSem.Sem_denote NaruSem.Sem_denoteP NaruSem.Sem_denote_basic NaruSem.check_sound_prop NaruSem.denoteP_iff_denoteB
  NaruSem.basic_not_proppy NaruSem.SEnv.vals_ext_val NaruSem.SEnv.ctx_ofList NaruSem.SCtx.NoProp.ofList NaruSem.SCtx.NoProp.ext_val
  NaruSem.CmpOp.leanBoolProp_iff NaruSem.CmpOp.leanBoolProp_iff_leanBool NaruSem.CmpOp.propNat_iff
  NaruSem.EqOp.propNat_iff NaruSem.EqOp.propNat_iff_leanNat NaruSem.EqOp.propBool_iff NaruSem.EqOp.propBool_iff_leanBool
  NaruSem.EqOp.propIff_bool NaruSem.LogicOp.prop_iff

-- C42: Statements の読みの検体(値の let と Bool の条件、値の等値と命題の同値の区別、同値定理の実例)
#audit_axioms NaruSem.ex_wtS_spec_let NaruSem.ex_basic_spec_let NaruSem.ex_denoteP_spec_let NaruSem.ex_Sem_spec_let
  NaruSem.ex_denoteP_iff_denoteB_let NaruSem.ex_denoteP_eq_bool NaruSem.ex_Sem_eq_bool NaruSem.ex_Sem_denote_eq_bool

-- C43 / C44: Statements の一般同値定理(量化・命題の let と shadowing・命題の条件の if・ガード付き match)、値 / 命題の境界の一般形、
-- proppyS の文脈の合同、網羅性を要求しない型付け、読みの形(局所束縛・条件・==、腕の選択と束縛、量化)
#audit_axioms NaruSem.Sem_denote_all NaruSem.Sem_denote_basic NaruSem.denoteP_iff_denoteB_all NaruSem.denoteP_iff_denoteB_noProp
  NaruSem.proppyS_congr_all NaruSem.proppyS_congr NaruSem.proppyArms_congr NaruSem.proppyArms_cons NaruSem.proppyS_var
  NaruSem.SCtx.isProp_ext NaruSem.SCtx.isProp_ext_val NaruSem.SEnv.vals_extVals
  NaruSem.wtS_noExh NaruSem.wtArmsS_head NaruSem.wtArmsS_tail
  NaruSem.denoteP_let_prop NaruSem.denoteP_let_bool NaruSem.denoteP_ite_prop NaruSem.denoteP_ite_bool NaruSem.denoteP_eq_prop NaruSem.denoteP_eq_bool
  NaruSem.denoteArmsP_hit NaruSem.denoteArmsP_miss NaruSem.denoteArmsP_guard NaruSem.denoteArmsP_guard_true NaruSem.denoteArmsP_guard_false
  NaruSem.denoteQuant_nil NaruSem.denoteQuant_forall_cons NaruSem.denoteQuant_exists_cons

-- C43: Statements の読みの検体(命題の let を隠すパターン束縛、Bool の全要素の量化、境界の一般形の実例)
#audit_axioms NaruSem.ex_wtS_pat_shadow NaruSem.ex_denoteP_pat_shadow NaruSem.ex_Sem_pat_shadow
  NaruSem.ex_denoteP_exists_bool NaruSem.ex_Sem_exists_bool NaruSem.ex_denoteP_iff_denoteB_match

-- C48: Surface AST の意味論の全域性・一意性・存在と、評価の単調性、論理の位置の式が Nat の値に評価されないこと、環境と文脈の対応・展開の補題
#audit_axioms NaruSem.Surf.eval_total NaruSem.Surf.Eval_unique NaruSem.Surf.wtR_total_all NaruSem.Surf.Sem_exists NaruSem.Surf.Sem_unique
  NaruSem.Surf.Sem_exists_all NaruSem.Surf.Sem_not_nat NaruSem.Surf.eval_mono NaruSem.Surf.eval_mono_all NaruSem.Surf.evalS_total
  NaruSem.Surf.matchPat_types NaruSem.Surf.annot_eq NaruSem.Surf.BinOp.apply_not_nat NaruSem.Surf.eval_binop_not_nat
  NaruSem.Surf.Agree.vals NaruSem.Surf.Agree.ext_val NaruSem.Surf.Agree.ext_prop NaruSem.Surf.Agree.extVals
  NaruSem.Surf.Env.Sub.ext NaruSem.Surf.Env.Sub.extList
  NaruSem.Surf.eval_block_cons NaruSem.Surf.eval_block_nil NaruSem.Surf.eval_match NaruSem.Surf.evalArms_cons NaruSem.Surf.evalStmts_cons
  NaruSem.Surf.wtArmR_mk NaruSem.Surf.wtArmS_mk

-- C48: Surface AST の対象範囲(ブロック・型注釈・ガード付き match・min / max・量化・命題の let・注釈の無い ==)、不適格な AST(スコープ外・型不一致・
-- 注釈の不一致・対象外の構文・網羅しない match・値の位置の命題・束縛型の無い量化)、行き詰まり(評価は `none`、spec は導出なし)、意味の実例
#audit_axioms NaruSem.Surf.ex_wtR_block NaruSem.Surf.ex_eval_block NaruSem.Surf.ex_wtR_annot NaruSem.Surf.ex_eval_annot
  NaruSem.Surf.ex_wtR_match_guard NaruSem.Surf.ex_eval_match_guard NaruSem.Surf.ex_wtR_min NaruSem.Surf.ex_eval_min
  NaruSem.Surf.ex_wtS_forall NaruSem.Surf.ex_wtS_let_prop NaruSem.Surf.ex_wtS_let_annot NaruSem.Surf.ex_wtS_eq_nat NaruSem.Surf.ex_wtS_eq_prop
  NaruSem.Surf.ex_Sem_eq_nat NaruSem.Surf.ex_Sem_let_prop
  NaruSem.Surf.neg_wtR_unbound NaruSem.Surf.neg_wtR_ill_typed NaruSem.Surf.neg_wtR_let_annotation NaruSem.Surf.neg_wtR_let_string_annotation
  NaruSem.Surf.neg_wtR_ite_branches NaruSem.Surf.neg_wtR_path NaruSem.Surf.neg_wtR_string NaruSem.Surf.neg_wtR_method NaruSem.Surf.neg_wtR_min_arity
  NaruSem.Surf.neg_wtR_block_no_tail NaruSem.Surf.neg_wtR_quant NaruSem.Surf.neg_wtR_match_not_exhaustive NaruSem.Surf.neg_wtR_match_guarded_only
  NaruSem.Surf.ex_wtR_match_bool_complete NaruSem.Surf.neg_wtR_match_bool_half
  NaruSem.Surf.ex_wtDecl_fn NaruSem.Surf.ex_wtDecl_pred NaruSem.Surf.neg_wtDecl_ret_mismatch NaruSem.Surf.neg_wtDecl_spec_ret
  NaruSem.Surf.neg_wtDecl_observer NaruSem.Surf.neg_wtDecl_param_string NaruSem.Surf.neg_wtS_match_not_exhaustive
  NaruSem.Surf.neg_wtS_prop_in_value NaruSem.Surf.neg_wtS_prop_scrutinee NaruSem.Surf.neg_wtS_prop_nat_annotation
  NaruSem.Surf.neg_wtS_quant_untyped NaruSem.Surf.neg_wtS_quant_string NaruSem.Surf.ex_wtS_nat_not_form
  NaruSem.Surf.neg_eval_unbound NaruSem.Surf.neg_eval_ill_typed NaruSem.Surf.neg_eval_match_stuck NaruSem.Surf.neg_eval_guard_stuck
  NaruSem.Surf.neg_eval_block_no_tail NaruSem.Surf.neg_eval_block_stuck_let NaruSem.Surf.neg_eval_path NaruSem.Surf.neg_eval_quant
  NaruSem.Surf.neg_Sem_unbound NaruSem.Surf.neg_Sem_nat_value NaruSem.Surf.neg_Sem_match_stuck NaruSem.Surf.neg_Sem_block_no_tail
  NaruSem.Surf.ex_Sem_not_nat_eq

-- C49: Surface AST → Core の対応 — 一般定理(変換の全域性・適格性の保存・値の対応)、生成 Lean への接続(C40 / C41 との合成)と接続検査の健全性、
-- パターン・演算・束縛の列の対応の補題
#audit_axioms NaruSem.Surf.lower_sound NaruSem.Surf.lower_sound_all NaruSem.Surf.lower_total NaruSem.Surf.lower_wt NaruSem.Surf.lower_eval
  NaruSem.Surf.preserve_nat NaruSem.Surf.preserve_bool NaruSem.Surf.check_sound_nat NaruSem.Surf.check_sound_bool
  NaruSem.Surf.wtR_mkLets NaruSem.Surf.eval_mkLets NaruSem.Surf.wtPat_lower NaruSem.Surf.matchPat_lower NaruSem.Surf.binopResult_result
  NaruSem.TyV.toTy?_toTyV NaruSem.Surf.lowerStmts_cons NaruSem.Surf.lowerArms_cons NaruSem.Surf.lowerArm_mk

-- C49 / C52: 変換の検体 — 対象の各構文(ブロック・型注釈・ガード付き match・min / max・Bool の比較・Nat の等値)の変換の形と一般定理の実例、
-- 対象外(量化・末尾式の無いブロック・対象外のメソッド・修飾名)と型の定まらない式(スコープ外の被演算子・値)は変換されない、
-- 意味の異なる適格な Core(&& / || の取り違え、束縛の改名)は変換結果でない
#audit_axioms NaruSem.Surf.ex_lower_block NaruSem.Surf.ex_lower_block_wt NaruSem.Surf.ex_lower_block_eval NaruSem.Surf.ex_preserve_block
  NaruSem.Surf.ex_lower_annot NaruSem.Surf.ex_lower_match_guard NaruSem.Surf.ex_lower_min NaruSem.Surf.ex_lower_cmp_bool NaruSem.Surf.ex_lower_eq_nat
  NaruSem.Surf.neg_lower_quant NaruSem.Surf.neg_lower_block_no_tail NaruSem.Surf.neg_lower_method NaruSem.Surf.neg_lower_path
  NaruSem.Surf.neg_lower_unbound NaruSem.Surf.neg_lower_let_unbound
  NaruSem.Surf.ex_wtR_logic_wrong NaruSem.Surf.neg_lower_swapped NaruSem.Surf.ex_lower_let_shadow NaruSem.Surf.ex_wtR_let_shadow_wrong
  NaruSem.Surf.neg_lower_let_shadow

-- C50: spec の Surface AST → Core の対応 — 一般定理(変換の全域性・適格性の保存・意味の対応と双方向の同値)、命題の区分の一致、生成 Lean への接続
-- (C42 / C43 との合成)と接続検査の健全性、量化・腕・束縛の列の対応と展開の補題
#audit_axioms NaruSem.Surf.lowerS_sound NaruSem.Surf.lowerS_sound_all NaruSem.Surf.lowerS_total NaruSem.Surf.lowerS_wt NaruSem.Surf.lowerS_Sem
  NaruSem.Surf.Sem_lowerS_iff NaruSem.Surf.preserve_prop NaruSem.Surf.check_sound_prop
  NaruSem.Surf.proppyS_lowerS NaruSem.Surf.proppyS_lower NaruSem.Surf.proppyS_lower_all
  NaruSem.Surf.quant_sound NaruSem.Surf.lowerBinders_sound NaruSem.Surf.exhaustiveFrom_lowerPat_cons NaruSem.Surf.proppyArms_lowerPat_cons
  NaruSem.Surf.patCtx_lower NaruSem.Surf.proppyArms_cons NaruSem.Surf.proppyStmts_cons NaruSem.Surf.stmtsCtxP_cons NaruSem.Surf.proppyS_block_some
  NaruSem.Surf.lowerStmtsS_cons NaruSem.Surf.lowerArmsS_cons NaruSem.Surf.lowerArmS_mk

-- C50 / C52: spec の変換の検体 — 量化・命題の let(注釈の有無)・注釈の無い ==(値 / 命題)・命題のガード付き match の変換の形と一般定理の実例
-- (適格性・双方向の同値・生成 Lean の読みとの同値)、対象外(束縛型の無い量化・命題の scrutinee・末尾式の無いブロック・修飾名)は変換されない、
-- 値の位置の命題は変換結果があっても Core として不適格、意味の異なる適格な Core(forall / exists の取り違え、命題の let の束縛の取り違え)は変換結果でない
#audit_axioms NaruSem.Surf.ex_lowerS_forall NaruSem.Surf.ex_lowerS_forall_wt NaruSem.Surf.ex_Sem_lowerS_forall NaruSem.Surf.ex_preserve_forall
  NaruSem.Surf.ex_lowerS_let_prop NaruSem.Surf.ex_lowerS_let_annot NaruSem.Surf.ex_lowerS_eq_nat NaruSem.Surf.ex_lowerS_eq_prop
  NaruSem.Surf.ex_wtS_match_guard_prop NaruSem.Surf.ex_lowerS_match_guard_prop
  NaruSem.Surf.neg_lowerS_quant_untyped NaruSem.Surf.neg_lowerS_prop_scrutinee NaruSem.Surf.neg_lowerS_prop_in_value
  NaruSem.Surf.neg_lowerS_block_no_tail NaruSem.Surf.neg_lowerS_path
  NaruSem.Surf.ex_wtS_forall_wrong NaruSem.Surf.neg_lowerS_swapped_quant NaruSem.Surf.ex_wtS_let_prop_wrong NaruSem.Surf.neg_lowerS_let_prop_wrong

-- C54: 関数・input を含む Core の意味論(`NaruSem.Call`)— runtime の全域性・一意性(実引数の列を含む)、spec の意味の存在・一意性、署名の phase の排他、
-- 宣言群の適格性の補題(鍵の重複なし・署名の保持)、宣言群の意味が署名を守ること(fn の全域性・spec 宣言の意味の存在と本体の意味との同値)
#audit_axioms NaruSem.Call.eval_total NaruSem.Call.Eval_unique NaruSem.Call.evalArgs_total NaruSem.Call.wtR_total_all
  NaruSem.Call.Sem_exists NaruSem.Call.Sem_unique NaruSem.Call.Sem_exists_all NaruSem.Call.evalS_total NaruSem.Call.evalArgsS_total
  NaruSem.Call.not_value_and_spec NaruSem.Call.wtProg_fresh NaruSem.Call.wtProg_mono NaruSem.Call.wtProg_sig NaruSem.Call.wtProg_cons
  NaruSem.Call.interp_Δ NaruSem.Call.interp_respects NaruSem.Call.interp_defined NaruSem.Call.fn_total NaruSem.Call.spec_defined NaruSem.Call.spec_meaning
  NaruSem.Call.interpFrom_inv NaruSem.Call.interpFrom_spec_meaning NaruSem.Call.interpFrom_stable NaruSem.Call.interpFrom_Δ NaruSem.Call.Interp.step_inv
  NaruSem.Call.bindParams_ty NaruSem.Call.bindParams_some NaruSem.Call.paramSCtx_eq NaruSem.Call.Env.toSEnv_ctx NaruSem.Call.Env.toSEnv_vals

-- C54: Core の呼出しの検体 — 対象範囲(fn / input / spec 宣言の呼出し、値の位置の呼出し、命題の let)、不適格な Core(未解決・引数の数と型・phase・
-- 値の位置の spec 宣言・命題の実引数・関数の値としての参照)、宣言群(適格な 2 段の呼出しと input、自己再帰・相互再帰・依存順でない・重複・input の
-- 引数の不一致は不適格、input の解釈による値、署名に合わない解釈は行き詰まりで前提を満たさない、fn の全域性と spec 宣言の意味の存在の実例、
-- 呼出しの規則の実例、行き詰まり)
#audit_axioms NaruSem.Call.ex_wtR_call_in_arith NaruSem.Call.ex_wtS_call_spec NaruSem.Call.ex_wtS_call_fn_bool NaruSem.Call.ex_proppyS_call_spec
  NaruSem.Call.ex_wtS_let_call_spec NaruSem.Call.neg_wtR_call_unknown NaruSem.Call.neg_wtR_call_arity NaruSem.Call.neg_wtR_call_arity2
  NaruSem.Call.neg_wtR_call_type NaruSem.Call.neg_wtR_call_spec_phase NaruSem.Call.neg_wtS_call_spec_in_value NaruSem.Call.neg_wtS_call_prop_arg
  NaruSem.Call.neg_wtR_global NaruSem.Call.ex_wtProg_A NaruSem.Call.ex_wtProg_A_sig NaruSem.Call.neg_wtProg_self_recursion
  NaruSem.Call.neg_wtProg_mutual_recursion NaruSem.Call.neg_wtProg_not_ordered NaruSem.Call.neg_wtProg_duplicate NaruSem.Call.neg_wtProg_input_arity
  NaruSem.Call.ex_interp_A NaruSem.Call.ex_interp_A_other NaruSem.Call.neg_interp_input_type NaruSem.Call.neg_Iwrong_not_respects
  NaruSem.Call.ex_I₄₁_respects NaruSem.Call.ex_fn_total NaruSem.Call.ex_wtProg_S NaruSem.Call.ex_wtProg_S_sig NaruSem.Call.ex_spec_defined
  NaruSem.Call.ex_Sem_callVal NaruSem.Call.ex_Sem_callSpec NaruSem.Call.neg_eval_call_unknown NaruSem.Call.neg_eval_call_arg_stuck
  NaruSem.Call.neg_Sem_call_unknown
