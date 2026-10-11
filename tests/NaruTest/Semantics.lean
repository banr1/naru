import NaruTest.Common
import NaruSem.Quote
import NaruSem.Denote
import NaruSem.SurfaceQuote
import NaruSem.Lower
import NaruSem.LowerSpec
import NaruSem.CallQuote
import NaruSem.SurfaceCallLower
import NaruSem.SurfaceCallLowerSpec
import NaruSem.SurfaceCallLowerSpecSound

/-!
# `naru_test semantics` — コンパイラ意味論保存の検査入口と、実際の AST・Core・実生成宣言の検査(IDEAL.md C39 / C40 / C41 / C42 / C43 / C44 / C45 / C46 / C47 / C48〜C52)

1. C45 の検査入口 `lake build NaruSem`(意味論・一般定理・検体・公理監査を Lean kernel に検査させる)が exit 0。続けて
   `lake env lean semantics/NaruSem.lean` で公理監査の出力(`audit ok: <定数> depends on axioms […]`)を取り直し、必須の定理
   (`requiredTheorems`)がすべて監査されていて、許容しない依存が 0 件であることを確かめる。
2. C39: 検体 `tests/accept/sem_core.naru` を実際の compiler 経路(`Naru.compileFiles`)でコンパイルし、`c39Decls` の各宣言(今回の保存対象の
   構文を 1 つずつ使う)の Core を Lean の項として引用した検査プログラム `.lake/naru/test/semantics/Scope.lean` を書き、モジュール `Scope` として
   `lean` でコンパイルする: 各宣言の適格性(`wtR` / `wtS` = 期待の型。`decide` で kernel が計算する)と、引用した Core が compiler の Core と一致すること
   (`NaruSem.Quote.checkDecls` が同じソースを再びコンパイルして照合する)。
3. C40 / C41 / C44 / C46(Model): 同じ検体を実際の CLI(`lake exe naru compile --out`)で `.lake/naru/test/semantics/gen/` に生成し、
   生成 Model `Model/Sem/Core.lean` をそのまま Lean のモジュールにして、検査プログラム `ModelCheck.lean` が各 runtime 宣言(`c40Decls`: 基礎の
   構文だけの宣言、`c41Decls`: 非再帰の Nat / Bool の `match` を含む宣言)について、任意の引数で実生成宣言の値が Lean での読み `denoteN` / `denoteB`
   と等しいこと(`conn_<f>`: kernel の定義的等しさ。リテラルパターンの `match` は Lean が scrutinee の場合分け `dite (x = k)` / `Bool.casesOn` に
   展開するので、scrutinee の局所名を `cases` で場合分け(Nat はリテラルの最大値 + 1 の深さ、Bool は 1 回)してから `rfl`。`proofOf`)と、そこから
   独立意味論の結果が実生成宣言の値であること(`pres_<f>`: `check_sound_nat` / `check_sound_bool`)を kernel に検査させ、公理監査に載せる。
   一般定理の量化の形(任意の文脈・式・型・環境、腕の列)も同じプログラムで照合する。
   負の検体 `ModelWrong.lean`(隔離: 実生成文字列から `&&` / `||` を取り違えた `Wrong.logic`、束縛を取り違えた `Wrong.letShadow`、Bool の腕を
   入れ替えた `Wrong.matchBool`、ガードを否定した `Wrong.matchNat`、腕の束縛が後続の腕に漏れた形の `Wrong.matchShadow` を作る)は
   Lean の型検査を通るが、同じ正しい入力 Core への接続検査だけが失敗する(正しい出力の対照は同じファイルで成功する。誤りは接続の定理の行にだけ出る)。
4. C42 / C43 / C44 / C46(Statements): 同じ生成先の生成 Statements `Statements/Sem/Core.lean` をそのまま Lean のモジュールにして、検査プログラム
   `StatementsCheck.lean` が各 spec 宣言(`c42Decls`: 基礎段階 = 量化・命題の `let`・`match` を含まない宣言、`c43Decls`: 量化・Bool / Prop の `let` と
   shadowing・Bool / Prop の条件の `if`・ガード付き `match`・Prop を含む両辺の `==` / `!=` の宣言)について、任意の引数で実生成宣言の命題が Lean での読み
   `denoteP` と等しいこと(`conn_<f>`: `Prop` の等式、kernel の定義的等しさ `rfl`。リテラルパターンの `match` は Model と同じく scrutinee の `cases` の後に `rfl`)、
   段階(`stage_<f>`: `basic` の真偽が一覧と一致)、そこから実生成宣言の命題が独立意味論の意味そのものであること(`pres_<f>`:
   `Sem (SEnv.ofList …) core_<f> (Statements.Sem.Core.<f> args)`。`check_sound_prop`)を kernel に検査させ、公理監査に載せる。一般定理 `Sem_denote`
   (任意の適格な式・対応する環境・意味の両方向の同値)、値 / 命題の境界 `denoteP_iff_denoteB_noProp`、腕の選択と束縛・量化の読みの形の量化の形も
   同じプログラムで照合する。負の検体 `StatementsWrong.lean`(`∧` / `∨` の取り違え、含意の向きの反転、Bool の値を `= false` に写した境界の誤り、`if` の
   分岐の入れ替え、`∀` / `∃` の取り違え、命題の `let` の束縛の取り違え、`match` のガードの否定、`↔` を一方向の `→` にする、Prop のガードの量化の
   取り違え、腕の束縛が後続の腕に漏れた形)は型検査を通るが接続検査だけが失敗する(どれも意味の異なる命題: 同値でない)。
5. C45: 監査が禁止依存を失敗にすることを、`sorry` / `native_decide` / 存在しない定数の 3 つの負の検体で確かめる(`lean` が exit 非 0)。
6. C47: `docs/architecture.md`「一般定理」の表に挙げた定理名がすべて監査に載っていること、`docs/testing.md` に記載した検査のコマンドがここで走らせる
   ものと一致することを照合する(文書と定理・接続・公理監査の整合)。
7. C48(Surface AST): 同じ検体の各宣言について、実際の構文解析の出力(`Checked.mods` の宣言)を最小の fn / spec 宣言の包装 `NaruSem.Surf.Decl`
   (種別・名前・位置・仮引数・戻り型・本体 `NaruSem.Surf.Expr`)に写し(`ofDeclAst?`。対象外の構文があれば FAIL)、宣言の適格性 `Surf.wtDecl`(仮引数と
   戻り型の注釈が Nat / Bool、runtime は本体が戻り型の型、spec は戻り型の注釈が無く本体が論理の位置の型)の結果の phase が `c39Decls` と、本体の型が Core の
   型付けの結果と一致することを確かめ、宣言と本体を Lean の項として引用した検査プログラム `.lake/naru/test/semantics/SurfaceScope.lean` をモジュール
   `SurfaceScope` として `lean` でコンパイルする: 本体の適格性(`wta_<f>`: `Surf.wtR` / `Surf.wtS`、`decide`)、宣言の適格性(`wtd_<f>`: `Surf.wtDecl`、`decide`)と、
   引用した宣言の埋め込み(`Decl.toAst`)が構文解析の出力と一致すること(`NaruSem.Surf.Quote.checkDecls` が同じソースを再び構文解析して `==` で照合する)。
   対象外の構文(呼出し・Option のパターン・再帰)を含む `tests/accept/guard_shadow.naru` の宣言が `ofAst?` で `none` になる(対象範囲の判定)ことも確かめる。
8. C49 / C51 / C52(Surface AST → Core → 生成 Lean、runtime): 各 runtime 宣言について、実際に構文解析された AST の独立した変換 `NaruSem.Surf.lower`(`semantics/NaruSem/Lower.lean`)
   が実際に出力された Core に等しいこと(`low_<f> : Surf.lower actx_<f> ast_<f> = some core_<f>`、kernel の定義的等しさ `rfl`。`SurfaceScope.lean`)を検査し、`ModelCheck.lean`
   (`SurfaceScope` を import)が一般定理 `Surf.lower_sound` の量化の形(任意の文脈・適格な AST・型: 変換が定まり、適格で、任意の環境で意味が一致)と、各 runtime 宣言の
   AST → 生成 Lean の合成 `apres_<f> : ∀ args, Surf.eval (Env.ofList …) ast_<f> = some (.nat (Model.Sem.Core.<f> args))`(`Surf.check_sound_nat` / `Surf.check_sound_bool` が
   `wta_<f>`・`low_<f>`・`conn_<f>` から導く)を kernel に検査させ、公理監査に載せる。負の検体 `SurfaceWrong.lean`(`coreMistranslations`: 実際の Core の値から最外の `||` を
   `&&` にした `WrongCore.logic`、2 つ目の `let_` を改名した `WrongCore.letShadow`、ガードを否定した `WrongCore.matchNat` を作る。どれも AST の意味と食い違う具体環境を
   ドライバが探して `diff_<f>_wrong`(`decide`)で kernel にも検査させる)は Core の適格性 `wtR`(`decide`)を通るが、
   同じ正しい AST の変換との一致 `conn_wrong_*`(`Surf.lower actx_<f> ast_<f> = some WrongCore.<f>`、`rfl`)だけが失敗する(対照 `conn_*_ok` は成功。定理名は Model / Statements の負の検体と共通の `wrongProgramWith` のもの)。
9. C50 / C51 / C52(Surface AST → Core → 生成 Lean、spec): 各 spec 宣言について、実際に構文解析された AST の独立した変換 `NaruSem.Surf.lowerS`(`semantics/NaruSem/LowerSpec.lean`)
   が実際に出力された Core に等しいこと(`lows_<f> : Surf.lowerS actx_<f> ast_<f> = some core_<f>`、`rfl`。`SurfaceScope.lean`)を検査し、`StatementsCheck.lean`(`SurfaceScope` を import)が
   一般定理 `Surf.lowerS_sound` / `Surf.Sem_lowerS_iff`(双方向)/ `Surf.preserve_prop` の量化の形と、各 spec 宣言の AST → 生成 Lean の合成
   `apres_<f> : ∀ args, Surf.Sem (SEnv.ofList …) ast_<f> (Statements.Sem.Core.<f> args)`(`Surf.check_sound_prop` が `wta_<f>`・`forma_<f>`・`lows_<f>`・`conn_<f>` から導く)を kernel に
   検査させ、公理監査に載せる。負の検体 `SurfaceSpecWrong.lean`(`specCoreMistranslations`: 実際の Core の値から `∀` を `∃` にした `WrongCore.specForall`、`∃` を `∀` にした
   `WrongCore.specExists`、命題の `let` の束縛を取り違えた `WrongCore.specLetProp`、ガードを否定した `WrongCore.specMatch` を作る。どれも `wtS` を通り、正しい Core の読みと意味の
   食い違う具体環境を `diff_<f>_wrong : ¬ (denoteP ρ WrongCore.<f> ↔ denoteP ρ core_<f>)` で kernel にも検査させる)は、同じ正しい AST の変換との一致 `conn_wrong_*`
   (`Surf.lowerS actx_<f> ast_<f> = some WrongCore.<f>`、`rfl`)だけが失敗する(対照 `conn_*_ok` は成功)。
10. C54(関数・input の宣言群): 検体 `tests/units/accept/sem_calls/src/Sem/Call.naru`(input・位置 / 名前付き引数・UFCS・ゼロ引数・2 段の呼出し・input の推移的な依存と共有・
   spec から runtime / spec の呼出し)の fn / input / spec 宣言すべてを、実際の Core(`NaruSem.Call.Decl`)と実際の構文解析の出力(`NaruSem.Surf.Call.Decl`)の宣言群として
   依存順(呼出し先が前。ドライバが Core の呼出しの鍵から並べる)に引用した検査プログラム `CallScope.lean` / `SurfaceCallScope.lean` を書き、宣言群の適格性
   (`NaruSem.Call.wtProg` / `NaruSem.Surf.Call.wtProg`)と各宣言の署名を kernel の `decide` で、引用の一致と宣言群全体の網羅を `checkProg` の再コンパイル / 再構文解析で
   検査する。実際の Core / AST から作った負の検体(依存順の反転、違う呼出し先、runtime から spec 宣言の呼出し、循環、重複、引数の数と型、未解決の名前、名前付き引数の
   名前・順序・二重指定の誤り)は `wtProg` が `none` / `false` になる。input の解釈を与えた宣言群の意味(`NaruSem.Call.interp`)の fn の値と、署名に合わない解釈では
   呼出しが行き詰まる(`none`)ことも kernel が計算する。
11. C55 / C56 / C57 / C58(実生成 Model への接続と宣言群の意味の合成、runtime): 同じ検体を実際の CLI で `.lake/naru/test/semantics/gencall/` に生成し、生成 Model
   `Model/Sem/Call.lean`(fn は input の引数 `name'` を名前順に先頭に取る)をモジュール `Model.Sem.Call` にして、検査プログラム `CallModelCheck.lean` が実生成宣言の表
   (`shapes_call` / `gens_call <inputs>`)から作った署名 `Δgen_call` と関数環境 `Φgen_call <inputs>` が表の署名を守ること(`Φgen_call_respects`)、宣言群の署名が表に
   含まれること(`cover_call`、`decide`)、各 fn の接続 `conn_<f>`(実生成宣言 = 読み `NaruSem.Call.denoteN` / `denoteB`。`rfl` / `cases` の後に `rfl`)と接続の証拠
   `evid_<f>`、宣言群全体の証拠 `cevid_call` と宣言群の意味と実生成定数の一致 `cgen_call`(`NaruSem.Call.interp_agree`: 任意の input 解釈で、`I` と `Φgen_call` が
   input の鍵で同じなら `interp I cprog_call` の fn / input は `Φgen_call` と署名の鍵で一致)、各 fn の値 `cval_<f>`(`fn_value`)を kernel に検査させ、公理監査に載せる。
   負の検体 `CallModelWrong.lean`(同じ署名の別の呼出し先への置換、名前付き実引数の取り違え、UFCS の受け手の誤対応、input の誤配線)は型検査を通るが接続検査だけが失敗する。
   `CallEvidenceCheck.lean` / `CallEvidenceWrong.lean` は対照の成功と公理監査、別宣言・古い Core の証拠と呼出し先の証拠が欠けた束の合成の 3 件だけの失敗を検査する(C57)。
   spec の `CallSpecEvidenceCheck.lean` / `CallSpecEvidenceWrong.lean` は元の prefix 署名と呼出し側を保持した部分証拠と、同型で非同値の古い Core の対照を検査し、
   別宣言・古い本体の証拠・呼出し先の証拠欠落による全体の命題同値の合成の 3 件だけを拒否する。
-/

namespace NaruTest.Semantics
open NaruTest

def source : String := "tests/accept/sem_core.naru"
def outDir : System.FilePath := ".lake" / "naru" / "test" / "semantics"
def genDir : System.FilePath := outDir / "gen"
def rootFile : String := "semantics/NaruSem.lean"

/-- 公理監査に現れなければならない定理(C39: 全域性・一意性。C40 / C41 / C44: 保存と接続検査の健全性、腕の列・腕の補題、異なる表現の対応関係。
C42 / C43 / C44: Statements の同値定理(一般形と基礎段階の系)、値 / 命題の境界(一般形と基礎段階の系)、`proppyS` の文脈の合同、網羅性を要求しない
型付けへの写し、接続検査の健全性、値の等値と命題の同値の区別、腕の選択と束縛・量化・局所束縛の読みの形)。 -/
def requiredTheorems : List String :=
  [ "NaruSem.Surf.Call.SpecArmsBridge.lower", "NaruSem.Surf.Call.SpecArmsBridge.sem_iff", "NaruSem.Surf.Call.lowerS_match_sem_iff", "NaruSem.Surf.Call.match_sem_wt", "NaruSem.Surf.Call.match_sem_lower", "NaruSem.Surf.Call.match_sem_bridge", "NaruSem.Surf.Call.match_sem_arbitrary", "NaruSem.Surf.Call.match_sem_ctx", "NaruSem.Surf.Call.match_sem_respects", "NaruSem.Surf.Call.match_sem_first_hit", "NaruSem.Surf.Call.match_sem_guards", "NaruSem.Surf.Call.match_sem_guard_false_restores_outer", "NaruSem.Surf.Call.match_sem_guard_true_shadows_outer", "NaruSem.Surf.Call.match_sem_missing_guard", "NaruSem.Surf.Call.match_sem_wrong_wt", "NaruSem.Surf.Call.match_sem_wrong_meaning", "NaruSem.Surf.Call.match_sem_wrong_not_preserved", "NaruSem.Surf.Call.match_sem_missing_guard_core", "NaruSem.Surf.Call.match_sem_nat_wt", "NaruSem.Surf.Call.match_sem_nat_bridge", "NaruSem.Surf.Call.match_sem_nat_arbitrary", "NaruSem.Surf.Call.match_sem_nat_successor", "NaruSem.Surf.Call.match_sem_empty",
    "NaruSem.Surf.Call.SpecSemEquiv.iff", "NaruSem.Surf.Call.SpecLetsBridge.lower", "NaruSem.Surf.Call.SpecLetsBridge.sem_iff", "NaruSem.Surf.Call.lowerStmtsS_sem_iff", "NaruSem.Surf.Call.lowerS_block_sem_iff",
    "NaruSem.Surf.Call.lets_sem_wt", "NaruSem.Surf.Call.lets_sem_lower", "NaruSem.Surf.Call.lets_sem_bridge", "NaruSem.Surf.Call.lets_sem_arbitrary", "NaruSem.Surf.Call.lets_sem_meaning", "NaruSem.Surf.Call.lets_sem_closed_respects", "NaruSem.Surf.Call.lets_sem_closed_positive", "NaruSem.Surf.Call.lets_sem_wrong_wt", "NaruSem.Surf.Call.lets_sem_wrong_meaning", "NaruSem.Surf.Call.lets_sem_wrong_not_true", "NaruSem.Surf.Call.lets_sem_wrong_not_preserved",
    "NaruSem.Surf.Call.exhaustiveFrom_lowerPat_cons", "NaruSem.Surf.Call.proppyS_lowerS", "NaruSem.Surf.Call.proppyS_lowerS_view",
    "NaruSem.Call.ValueScope.ext", "NaruSem.Call.ValueScope.pat", "NaruSem.Call.wtArgs_members", "NaruSem.Call.wtArmsR_members", "NaruSem.Call.proppyS_false_of_wtR_all", "NaruSem.Call.proppyS_false_of_wtR", "NaruSem.Surf.Call.RuntimeScope.ext", "NaruSem.Surf.Call.RuntimeScope.pat", "NaruSem.Surf.Call.RuntimeScope.ufcs", "NaruSem.Surf.Call.callTy_not_spec", "NaruSem.Surf.Call.wtArgs_members", "NaruSem.Surf.Call.wtArmsR_members", "NaruSem.Surf.Call.proppyS_false_of_wtR_all", "NaruSem.Surf.Call.proppyS_false_of_wtR", "NaruSem.Surf.Call.ScopeView.refl",
    "NaruSem.Surf.Call.lowerS_typed_all", "NaruSem.Surf.Call.lowerS_typed",
    "NaruSem.Surf.Call.lowerS_total", "NaruSem.Surf.Call.lowerS_wt",
    "NaruSem.Surf.Call.spec_lower_call", "NaruSem.Surf.Call.spec_lower_runtime_reject", "NaruSem.Surf.Call.spec_lower_missing", "NaruSem.Surf.Call.spec_lower_shadow", "NaruSem.Surf.Call.spec_lower_value_arg_reject", "NaruSem.Surf.Call.spec_lower_bool_value", "NaruSem.Surf.Call.spec_lower_bool_let", "NaruSem.Surf.Call.spec_lower_prop_let", "NaruSem.Surf.Call.spec_lower_prop_let_kind", "NaruSem.Surf.Call.spec_lower_match_guard", "NaruSem.Surf.Call.spec_lower_prop_scrutinee_reject",
    "NaruSem.Surf.Call.lowerCallS_eq", "NaruSem.Surf.Call.lowerCallS_spec_wt",
    "NaruSem.Surf.Call.lowerCallS_spec_Sem", "NaruSem.Surf.Call.lowerCallS_value_Sem",
    "NaruSem.Surf.Call.arrange_core_total",
    "NaruSem.Call.eval_agree", "NaruSem.Surf.Call.lower_eval_agree",
    "NaruSem.Surf.Call.lower_denote_sound",
    "NaruSem.Surf.Call.typed_env_agree", "NaruSem.Surf.Call.typed_env_preserve",
    "NaruSem.Surf.Call.typed_env_outside_diff",
    "NaruSem.Surf.Call.lower_typed_all", "NaruSem.Surf.Call.lower_typed",
    "NaruSem.Surf.Call.lower_total", "NaruSem.Surf.Call.lower_wt",
    "NaruSem.Surf.Call.lower_eval_all", "NaruSem.Surf.Call.lower_eval",
    "NaruSem.Surf.Call.lowerStmts_eval", "NaruSem.Surf.Call.lowerArgs_eval",
    "NaruSem.Surf.Call.lowerArms_eval_wt", "NaruSem.Surf.Call.lowerArm_eval_wt",
    "NaruSem.Surf.Call.lowerCall_eq",
    "NaruSem.Surf.Call.allSome_some", "NaruSem.Surf.Call.evalArgs_allSome",
    "NaruSem.Surf.Call.arrange_eval", "NaruSem.Surf.Call.wtArgs_of_map", "NaruSem.Surf.Call.arrange_wt",
    "NaruSem.Surf.Call.lowerCall_wt", "NaruSem.Surf.Call.lowerCall_eval",
    "NaruSem.Surf.Call.lower_call_eval", "NaruSem.Surf.Call.lower_ufcs_eval",
    "NaruSem.Surf.Call.named_call", "NaruSem.Surf.Call.ufcs_call", "NaruSem.Surf.Call.zero_args",
    "NaruSem.Surf.Call.named_wt", "NaruSem.Surf.Call.swapped_values",
    "NaruSem.Surf.Call.wtR_mkLets",
    "NaruSem.Surf.Call.eval_mkLets",
    "NaruSem.Surf.Call.lowerStmts_cons_eval",
    "NaruSem.Surf.Call.lower_block_eval",
    "NaruSem.Surf.Call.block_shadow",
    "NaruSem.Surf.Call.stmt_shadow",
    "NaruSem.Surf.Call.binds_shadow_wt",
    "NaruSem.Surf.Call.binds_missing_call",
    "NaruSem.Surf.Call.binds_wrong_annotation",
    "NaruSem.Surf.Call.binds_failed_call",
    "NaruSem.Surf.Call.binds_call_shadow",
    "NaruSem.Surf.Call.exhaustiveFrom_lowerArm",
    "NaruSem.Surf.Call.exhaustiveFrom_lowerArms",
    "NaruSem.Surf.Call.lowerArm_eval",
    "NaruSem.Surf.Call.lowerArms_eval",
    "NaruSem.Surf.Call.lower_match_eval",
    "NaruSem.Surf.Call.lower_match_wt",
    "NaruSem.Surf.Call.guard_call",
    "NaruSem.Surf.Call.guard_arms_eval",
    "NaruSem.Surf.Call.match_call_guard",
    "NaruSem.Surf.Call.bool_arms_exhaustive",
    "NaruSem.Surf.Call.guard_only_not_exhaustive",
    "NaruSem.Surf.Call.match_call_guard_wt",
    "NaruSem.Surf.Call.guard_false_restores_outer",
    "NaruSem.Surf.Call.guard_true_shadows_outer",
    "NaruSem.Surf.Call.guard_false_wrong_shadow",
    "NaruSem.Surf.Call.guard_missing_stops",
    "NaruSem.Surf.Call.guard_failure_stops",
    "NaruSem.Surf.Call.guard_nonbool_stops",
    "NaruSem.Surf.Call.guard_mismatch_skips",
    "NaruSem.eval_total", "NaruSem.Eval_unique", "NaruSem.Sem_exists", "NaruSem.Sem_unique",
    "NaruSem.denote_sound", "NaruSem.preserve_nat", "NaruSem.preserve_bool", "NaruSem.check_sound_nat", "NaruSem.check_sound_bool",
    "NaruSem.CmpOp.leanBool_eq", "NaruSem.EqOp.leanNat_eq", "NaruSem.EqOp.leanBool_eq",
    "NaruSem.denoteArms_sound", "NaruSem.denoteArm_sound", "NaruSem.denoteArmsV_hit", "NaruSem.denoteArmsV_miss",
    "NaruSem.denoteArmsV_guard_true", "NaruSem.denoteArmsV_guard_false",
    "NaruSem.Sem_denote", "NaruSem.Sem_denoteP", "NaruSem.check_sound_prop", "NaruSem.denoteP_iff_denoteB", "NaruSem.basic_not_proppy",
    "NaruSem.EqOp.propIff_bool", "NaruSem.CmpOp.leanBoolProp_iff", "NaruSem.LogicOp.prop_iff",
    "NaruSem.Sem_denote_all", "NaruSem.Sem_denote_basic", "NaruSem.denoteP_iff_denoteB_noProp", "NaruSem.proppyS_congr", "NaruSem.wtS_noExh",
    "NaruSem.denoteArmsP_hit", "NaruSem.denoteArmsP_miss", "NaruSem.denoteArmsP_guard", "NaruSem.denoteArmsP_guard_true",
    "NaruSem.denoteArmsP_guard_false", "NaruSem.denoteQuant_forall_cons", "NaruSem.denoteQuant_exists_cons",
    "NaruSem.denoteP_let_prop", "NaruSem.denoteP_let_bool", "NaruSem.denoteP_ite_prop", "NaruSem.denoteP_eq_prop",
    -- C48: Surface AST の意味論の全域性・一意性・存在、評価の単調性、論理の位置の式が Nat の値に評価されないこと
    "NaruSem.Surf.eval_total", "NaruSem.Surf.Eval_unique", "NaruSem.Surf.Sem_exists", "NaruSem.Surf.Sem_unique",
    "NaruSem.Surf.eval_mono", "NaruSem.Surf.Sem_not_nat",
    -- C49: Surface AST → Core の対応(変換の全域性・適格性の保存・値の対応)と、C40 / C41 と合成した生成 Lean への接続、接続検査の健全性
    "NaruSem.Surf.lower_sound", "NaruSem.Surf.lower_total", "NaruSem.Surf.lower_wt", "NaruSem.Surf.lower_eval",
    "NaruSem.Surf.preserve_nat", "NaruSem.Surf.preserve_bool", "NaruSem.Surf.check_sound_nat", "NaruSem.Surf.check_sound_bool",
    -- C50: spec の Surface AST → Core の対応(変換の全域性・適格性の保存・意味の対応と双方向の同値・命題の区分の一致)と、C42 / C43 と合成した生成 Lean への接続、
    -- 接続検査の健全性
    "NaruSem.Surf.lowerS_sound", "NaruSem.Surf.lowerS_total", "NaruSem.Surf.lowerS_wt", "NaruSem.Surf.lowerS_Sem", "NaruSem.Surf.Sem_lowerS_iff",
    "NaruSem.Surf.proppyS_lowerS", "NaruSem.Surf.proppyS_lower", "NaruSem.Surf.preserve_prop", "NaruSem.Surf.check_sound_prop",
    -- C54: 関数・input を含む Core の意味論の全域性・一意性・存在、宣言群の意味が署名を守ること(fn の全域性、spec 宣言の意味の存在と本体の意味)
    "NaruSem.Call.eval_total", "NaruSem.Call.Eval_unique", "NaruSem.Call.evalArgs_total", "NaruSem.Call.Sem_exists", "NaruSem.Call.Sem_unique",
    "NaruSem.Call.interp_respects", "NaruSem.Call.interp_defined", "NaruSem.Call.fn_total", "NaruSem.Call.spec_defined", "NaruSem.Call.spec_meaning",
    -- C54: 関数・input を含む Surface AST の意味論の全域性・一意性・存在(名前付き引数の並べ替えと payload の写像の可換、評価の単調性、論理の位置の式が
    -- Nat の値に評価されないこと)、宣言群の意味が宣言表の署名を守ること(fn の全域性、spec 宣言の意味の存在と本体の意味)
    "NaruSem.Surf.Call.eval_total", "NaruSem.Surf.Call.Eval_unique", "NaruSem.Surf.Call.evalArgs_total", "NaruSem.Surf.Call.Sem_exists",
    "NaruSem.Surf.Call.Sem_unique", "NaruSem.Surf.Call.eval_mono", "NaruSem.Surf.Call.Sem_not_nat", "NaruSem.Surf.Call.arrange_map",
    "NaruSem.Surf.Call.interp_respects", "NaruSem.Surf.Call.interp_defined", "NaruSem.Surf.Call.fn_total", "NaruSem.Surf.Call.spec_defined",
    "NaruSem.Surf.Call.spec_meaning",
    -- C55 / C56 / C57(runtime): 関数・input を含む Model の保存(独立意味論の結果 = 実生成定数の環境での読み。評価の環境と読みの環境は署名の鍵で一致すれば
    -- よい)、腕の列の保存、接続検査の健全性、実生成定数を包む `wrap` が署名を守ること、実生成宣言の表から作った環境が表の署名を守ること、宣言群の意味と
    -- 実生成定数の一致(呼出し先の証拠の呼出し側への合成)と fn の値の系、署名の包含、接続検査の形から接続の証拠へ
    "NaruSem.Call.denote_sound", "NaruSem.Call.denote_sound_self", "NaruSem.Call.preserve_nat", "NaruSem.Call.preserve_bool", "NaruSem.Call.denoteArms_sound",
    "NaruSem.Call.check_sound_nat", "NaruSem.Call.check_sound_bool", "NaruSem.Call.wrap_respects", "NaruSem.Call.ofGens_respects",
    "NaruSem.Call.interp_agree", "NaruSem.Call.fn_value", "NaruSem.Call.SubV_of_cover", "NaruSem.Call.fnConn_of_curried",
    -- C56: 任意の署名を守る解釈をLeanの値/関数へ写す。型外の挙動の等式は要求しない。
    "NaruSem.Call.SameInputs.agree",
    "NaruSem.Call.interpFrom_inputs_agree",
    "NaruSem.Call.interp_inputs_agree",
    "NaruSem.Call.fn_value_inputs",
    "NaruSem.Call.interpFrom_prop_inputs_agree",
    "NaruSem.Call.interp_prop_inputs_agree",
    "NaruSem.Call.inputs_generated_agree",
    "NaruSem.Call.typed_only_agree",
    "NaruSem.Call.typed_only_not_same",
    "NaruSem.Call.exists_fn", "NaruSem.Call.input_representable", "NaruSem.Call.inputs_representable",
    "NaruSem.Call.illtyped_total", "NaruSem.Call.illtyped_not_equal",
    -- C55(spec): 式の一般同値。宣言群のspec環境の一致はprefix証拠から合成。Surface合成は未完了。
    "NaruSem.Call.Sem_denote_all", "NaruSem.Call.Sem_denote", "NaruSem.Call.Sem_denoteP", "NaruSem.Call.Sem_denote_self", "NaruSem.Call.check_sound_prop",
    "NaruSem.Call.interpFrom_prop_agree", "NaruSem.Call.interp_prop_agree", "NaruSem.Call.curried_wrapP", "NaruSem.Call.specConn_of_curried",
    "NaruSem.Call.PEnv.Agree.refl", "NaruSem.Call.PEnv.Agree.defined", "NaruSem.Call.PEnv.Defined.mono", "NaruSem.Call.SigEnv.SubP.refl" ]

/-- C54 の検体 `tests/units/accept/sem_calls/src/Sem/Call.naru` の宣言群(修飾名, 種別): input 4、fn 17、spec 宣言 10。欠けていれば FAIL。 -/
def c54Decls : List (String × Naru.DeclKind) :=
  [ ("Sem.Inputs.seed", .input), ("Sem.Inputs.bias", .input), ("Sem.Inputs.otherBias", .input), ("Sem.Inputs.flag", .input),
    ("Sem.Callees.base", .fn), ("Sem.Callees.zero", .fn), ("Sem.Callees.addTo", .fn), ("Sem.Call.callBase", .fn), ("Sem.Call.callNamed", .fn),
    ("Sem.Call.callMixed", .fn), ("Sem.Call.ufcs", .fn), ("Sem.Call.ufcsNamed", .fn), ("Sem.Call.useInput", .fn), ("Sem.Call.useInputArg", .fn),
    ("Sem.Call.twoStep", .fn), ("Sem.Call.boolCall", .fn), ("Sem.Call.zeroCall", .fn), ("Sem.Call.callInLet", .fn), ("Sem.Call.callInMatch", .fn),
    ("Sem.Call.inputPair", .fn), ("Sem.Call.sharedInputs", .fn),
    ("Sem.Callees.posBase", .predicate), ("Sem.Call.specCallSpec", .predicate), ("Sem.Call.specInput", .predicate), ("Sem.Call.specNamed", .predicate),
    ("Sem.Call.specUfcs", .predicate), ("Sem.Call.specBoolCall", .predicate), ("Sem.Call.specLetCall", .predicate), ("Sem.Call.specQuantCall", .predicate),
    ("Sem.Call.specTwoStep", .predicate), ("Sem.Call.specSharedInputs", .predicate) ]

/-- 検体の宣言(修飾名, spec か)。今回の保存対象の各構文を 1 つずつ。欠けていれば FAIL。 -/
def c39Decls : List (String × Bool) :=
  [ ("Sem.Core.litNat", false), ("Sem.Core.litBool", false), ("Sem.Core.useVar", false), ("Sem.Core.useLet", false),
    ("Sem.Core.letShadow", false), ("Sem.Core.useIf", false), ("Sem.Core.arith", false), ("Sem.Core.minMax", false),
    ("Sem.Core.cmpNat", false), ("Sem.Core.cmpBool", false), ("Sem.Core.eqNat", false), ("Sem.Core.eqBool", false),
    ("Sem.Core.logic", false), ("Sem.Core.letAnnot", false), ("Sem.Core.nestedBlock", false),
    ("Sem.Core.matchNat", false), ("Sem.Core.matchBool", false), ("Sem.Core.matchShadow", false),
    ("Sem.Core.matchLetShadow", false), ("Sem.Core.matchScrut", false), ("Sem.Core.matchLits", false), ("Sem.Core.matchBoolGuard", false),
    ("Sem.Core.specLit", true), ("Sem.Core.specVar", true), ("Sem.Core.specCmp", true), ("Sem.Core.specCmpBool", true),
    ("Sem.Core.specLogic", true), ("Sem.Core.specEq", true), ("Sem.Core.specArith", true), ("Sem.Core.specLetVal", true),
    ("Sem.Core.specLetProp", true), ("Sem.Core.specLetShadow", true), ("Sem.Core.specLetAnnot", true), ("Sem.Core.specIfBool", true), ("Sem.Core.specIfProp", true),
    ("Sem.Core.specForall", true), ("Sem.Core.specExists", true), ("Sem.Core.specMatch", true), ("Sem.Core.specMatchProp", true),
    ("Sem.Core.specIffProp", true), ("Sem.Core.specQuantShadow", true), ("Sem.Core.specPatShadow", true), ("Sem.Core.specGuardBool", true),
    ("Sem.Core.specGuardProp", true), ("Sem.Core.specMatchBool", true), ("Sem.Core.specMatchShadow", true) ]

/-- C40 の基礎段階の runtime 宣言(リテラル・局所名・let・if・算術・min / max・比較・等値・論理)。`NaruSem.basic` が真でなければならない。 -/
def c40Decls : List String :=
  [ "Sem.Core.litNat", "Sem.Core.litBool", "Sem.Core.useVar", "Sem.Core.useLet", "Sem.Core.letShadow", "Sem.Core.useIf",
    "Sem.Core.arith", "Sem.Core.minMax", "Sem.Core.cmpNat", "Sem.Core.cmpBool", "Sem.Core.eqNat", "Sem.Core.eqBool", "Sem.Core.logic",
    "Sem.Core.letAnnot", "Sem.Core.nestedBlock" ]

/-- C41 の非再帰の Nat / Bool の `match` の runtime 宣言(同名の仮引数・外側の let・scrutinee の中の名前の束縛、複数のガード不成立からの継続、
Bool のリテラルの腕と Bool の scrutinee のガード、Nat のリテラル 0 / 1 の腕)。`NaruSem.basic` が偽(段階の境界)で、接続と保存を検査する。 -/
def c41Decls : List String :=
  [ "Sem.Core.matchNat", "Sem.Core.matchBool", "Sem.Core.matchShadow", "Sem.Core.matchLetShadow", "Sem.Core.matchScrut",
    "Sem.Core.matchLits", "Sem.Core.matchBoolGuard" ]

/-- C42 の基礎段階の spec 宣言(Bool の値の命題への境界、論理、Nat / Bool の比較・等値、値の `let`、Bool の条件の `if`)。`NaruSem.basic` が真で
なければならず、実生成 Statements への接続と保存を検査する。 -/
def c42Decls : List String :=
  [ "Sem.Core.specLit", "Sem.Core.specVar", "Sem.Core.specCmp", "Sem.Core.specCmpBool", "Sem.Core.specLogic", "Sem.Core.specEq",
    "Sem.Core.specArith", "Sem.Core.specLetVal", "Sem.Core.specIfBool" ]

/-- C43 の spec 宣言(Nat / Bool の量化、命題の `let` と shadowing(値の `let`・量化の束縛・パターン束縛が同名の命題の束縛を隠す)、命題の条件の `if`、
Nat / Bool の scrutinee のガード付き `match`(Bool / Prop のガードの成功と失敗、Bool のリテラルの腕、仮引数と同名のパターン束縛)、Prop を含む両辺の
`==` / `!=`)。`NaruSem.basic` が偽(段階の境界)で、実生成 Statements への接続と保存を検査する。 -/
def c43Decls : List String :=
  [ "Sem.Core.specLetProp", "Sem.Core.specLetShadow", "Sem.Core.specLetAnnot", "Sem.Core.specIfProp", "Sem.Core.specForall", "Sem.Core.specExists",
    "Sem.Core.specMatch", "Sem.Core.specMatchProp", "Sem.Core.specIffProp", "Sem.Core.specQuantShadow", "Sem.Core.specPatShadow",
    "Sem.Core.specGuardBool", "Sem.Core.specGuardProp", "Sem.Core.specMatchBool", "Sem.Core.specMatchShadow" ]

def heading (title : String) : M Unit := IO.println s!"== {title}"

def elapsed (start : Nat) : IO String := do
  let ms := (← IO.monoMsNow) - start
  return s!"{ms / 1000}.{(ms % 1000) / 100}s"

/-- 子プロセスを 1 項目として走らせ、exit code を期待と照合する。 -/
def step (label : String) (cmd : String) (args : Array String) (expectExit : UInt32 := 0)
    (cwd : Option System.FilePath := none) (env : Array (String × Option String) := #[]) : M IO.Process.Output := do
  let t ← IO.monoMsNow
  let r ← runProc cmd args cwd env
  let shown := s!"{cmd} {" ".intercalate args.toList}"
  if r.exitCode == expectExit then ok s!"{label}: `{shown}` exit {r.exitCode} ({← elapsed t})"
  else fail s!"{label}: `{shown}` exit {r.exitCode} (expected {expectExit})\n{tail r.stdout 1500}\n{tail r.stderr 1500}"
  return r

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

def ctxOfParams (ps : List Naru.Core.Param) : NaruSem.Ctx :=
  NaruSem.Ctx.ofList (ps.filterMap fun p => match p.ty with
    | .nat => some (p.name, .nat)
    | .bool => some (p.name, .bool)
    | _ => none)

def sctxOfParams (ps : List Naru.Core.Param) : NaruSem.SCtx :=
  NaruSem.SCtx.ofList (ps.filterMap fun p => match p.ty with
    | .nat => some (p.name, .val .nat)
    | .bool => some (p.name, .val .bool)
    | _ => none)

def tyTerm : NaruSem.Ty → String
  | .nat => "NaruSem.Ty.nat"
  | .bool => "NaruSem.Ty.bool"

def styTerm : NaruSem.STy → String
  | .val t => s!"(NaruSem.STy.val {tyTerm t})"
  | .prop => "NaruSem.STy.prop"

/-- 修飾名 `A.B.f` → 検査プログラムの中の名前 `f`。 -/
def shortName (key : String) : String := (key.splitOn ".").getLast!

/-- 公理監査の出力から監査された定数の名前。 -/
def auditedNames (out : String) : List String :=
  ((out.splitOn "\n").filter fun l => contains l "audit ok:").filterMap fun l =>
    ((l.splitOn "audit ok: ").getD 1 "").splitOn " " |>.head?

/-- `docs/architecture.md`「一般定理」の表の第 1 列(`` `名前` ``)に挙げた定理名(C47: 文書に挙げた定理はすべて公理監査に載っていなければならない)。 -/
def docTheoremNames (doc : String) : List String := Id.run do
  let mut inSection := false
  let mut names : List String := []
  for l in doc.splitOn "\n" do
    if l.startsWith "### 一般定理" then inSection := true
    else if l.startsWith "### " then inSection := false
    else if inSection && l.startsWith "| `" then
      let cell := (l.splitOn "|").getD 1 ""
      let mut i := 0
      for p in cell.splitOn "`" do
        if i % 2 == 1 && !p.isEmpty && p.all (fun c => c.isAlphanum || c == '_' || c == '.') then names := names ++ [p]
        i := i + 1
  return names.eraseDups

/-- `docs/testing.md`「コンパイラ意味論保存」に記載した検査のコマンド(C47: ここで実際に走らせるものと一致しなければならない)。 -/
def documentedCommands : List String :=
  [ "lake build NaruSem", "lake env lean semantics/NaruSem.lean", "lake exe naru_test semantics" ]

/-- `lean` の出力の `<file>:<line>:<col>: error:` の行の行番号。 -/
def errorLines (out : String) : List Nat :=
  ((out.splitOn "\n").filter fun l => contains l ": error:").filterMap fun l =>
    ((l.splitOn ":").getD 1 "").trimAscii.toString.toNat?

/-- 検査プログラム `Scope.lean`(モジュール `Scope`): 引用した Core(`core_<f>`)と文脈(`ctx_<f>`)、適格性の定理(`decide`)、引用の一致の照合(`run_cmd`)。 -/
def scopeProgram (quoted : List (String × String × String × String × Bool)) : String :=
  let defs := quoted.map fun (key, core, ctx, ty, spec) =>
    let n := shortName key
    let wt := if spec then
      s!"theorem wt_{n} : NaruSem.wtS ctx_{n} core_{n} = some {ty} := by decide\n" ++
      s!"theorem form_{n} : NaruSem.STy.isForm {ty} = true := by decide\n"
    else s!"theorem wt_{n} : NaruSem.wtR ctx_{n} core_{n} = some {ty} := by decide\n"
    s!"-- {key}\ndef core_{n} : Naru.Core.Expr :=\n  {core}\ndef ctx_{n} := {ctx}\n{wt}\n"
  let pairs := quoted.map fun (key, _, _, _, _) => s!"({key.quote}, core_{shortName key})"
  s!"-- naru_test semantics (C39): generated from NaruTest/Semantics.lean. The Core of each declaration of {source} as produced by the compiler.\n" ++
  "import NaruSem\n\n" ++
  "".intercalate defs ++
  s!"-- the quoted Core is the Core the compiler produces for the same source (C44)\nrun_cmd NaruSem.Quote.checkDecls {source.quote} [{", ".intercalate pairs}]\n"

/-- C48: 引用した Surface AST の宣言 1 つ分: 修飾名、本体の項、仮引数の文脈の項、本体の型の項、spec か、宣言の項(本体は `ast_<f>` を指す)、宣言の適格性の結果の項。 -/
structure QuotedDecl where
  key : String
  ast : String
  ctx : String
  ty : String
  spec : Bool
  decl : String
  declTy : String

/-- C48 / C49: 検査プログラム `SurfaceScope.lean`(モジュール `SurfaceScope`): 引用した Surface AST の本体(`ast_<f>`)と仮引数の文脈(`actx_<f>`)、本体の適格性
(`wta_<f>`: `decide`)、宣言の包装(`decl_<f>`: 種別・名前・位置・仮引数・戻り型・本体)とその適格性(`wtd_<f>`: `decide`)、runtime 宣言の AST の独立した変換が
実際の Core に等しいこと(`low_<f>`: `Surf.lower actx_<f> ast_<f> = some core_<f>`、kernel の定義的等しさ `rfl`。C49 / C51)、引用した宣言と構文解析の出力の
一致の照合(`run_cmd`)。`Scope` を import するので、同じモジュールで引用した Core(`core_<f>`)と並ぶ。 -/
def surfaceProgram (quoted : List QuotedDecl) : String :=
  let defs := quoted.map fun q =>
    let n := shortName q.key
    let wt := if q.spec then
      s!"theorem wta_{n} : NaruSem.Surf.wtS actx_{n} ast_{n} = some {q.ty} := by decide\n" ++
      s!"theorem forma_{n} : NaruSem.STy.isForm {q.ty} = true := by decide\n" ++
      s!"-- the lowering of the parsed spec AST is the Core the compiler produced (C50 / C51)\ntheorem lows_{n} : NaruSem.Surf.lowerS actx_{n} ast_{n} = some core_{n} := rfl\n"
    else
      s!"theorem wta_{n} : NaruSem.Surf.wtR actx_{n} ast_{n} = some {q.ty} := by decide\n" ++
      s!"-- the lowering of the parsed AST is the Core the compiler produced (C49 / C51)\ntheorem low_{n} : NaruSem.Surf.lower actx_{n} ast_{n} = some core_{n} := rfl\n"
    let declCtx := if q.spec then "declSCtx?" else "declCtx?"
    s!"-- {q.key}\ndef ast_{n} : NaruSem.Surf.Expr :=\n  {q.ast}\ndef actx_{n} := {q.ctx}\n{wt}" ++
    s!"def decl_{n} : NaruSem.Surf.Decl :=\n  {q.decl}\ntheorem wtd_{n} : NaruSem.Surf.wtDecl decl_{n} = some {q.declTy} := by decide\n" ++
    s!"-- the context of the body is the one the declaration's parameters give (C51)\ntheorem actx_{n}_decl : NaruSem.Surf.{declCtx} decl_{n} = some actx_{n} := rfl\n\n"
  let pairs := quoted.map fun q => s!"({q.key.quote}, decl_{shortName q.key})"
  s!"-- naru_test semantics (C48 / C49 / C50): generated from NaruTest/Semantics.lean. The Surface AST of each declaration of {source} as produced by the parser.\n" ++
  "import Scope\n\n" ++
  "".intercalate defs ++
  s!"-- the quoted declarations embed (`Decl.toAst`) to the declarations the parser produces for the same source (C48 / C51)\nrun_cmd NaruSem.Surf.Quote.checkDecls {source.quote} [{", ".intercalate pairs}]\n"

/-- 仮引数 → (Lean の束縛, 環境の項目, 実引数)。Nat / Bool 以外は `none`。 -/
def binderOf (p : Naru.Core.Param) : Option (String × String × String) :=
  match p.ty with
  | .nat => some (s!"(«{p.name}» : Nat)", s!"({p.name.quote}, NaruSem.Val.nat «{p.name}»)", s!"«{p.name}»")
  | .bool => some (s!"(«{p.name}» : Bool)", s!"({p.name.quote}, NaruSem.Val.bool «{p.name}»)", s!"«{p.name}»")
  | _ => none

/-! ### 接続の証明(C41 / C44)

生成形(`Backend.Model.emitMatchGuarded`)の `match` は、リテラルパターンの腕を Lean が scrutinee の場合分け(`dite (x = k)` / `Bool.casesOn`)
に展開するので、自由変数のままでは読み(`matchPat` の `if`)と定義的に等しくない。scrutinee に現れる局所名を、パターンの Nat リテラルの最大値 + 1 の
深さ(Bool は 1 回)だけ `cases` で場合分けすると、両辺が同じ形(ガード付きの腕の `match (if g then some b else none) with …`、残りの腕の読み)に
簡約して `rfl` で閉じる。`match` の無い宣言(と変数・`_` のパターンだけの `match`)は `rfl` の項。 -/

/-- 式の中の局所名(`.var`)。 -/
partial def varsOf : Naru.Core.Expr → List String
  | .var x => [x]
  | .let_ _ _ v b => varsOf v ++ varsOf b
  | .ite c t e => varsOf c ++ varsOf t ++ varsOf e
  | .binop _ l r _ => varsOf l ++ varsOf r
  | .unop _ a => varsOf a
  | .method _ _ r as _ => varsOf r ++ as.flatMap varsOf
  | .match_ s _ arms => varsOf s ++ arms.flatMap fun | .mk _ g b => (g.map varsOf).getD [] ++ varsOf b
  | _ => []

/-- 腕のパターンのリテラルから場合分けの深さ: Nat リテラルの最大値 + 1、Bool のリテラルは 1、リテラルが無ければ 0。 -/
def litDepth (arms : List Naru.Core.Arm) : Nat :=
  arms.foldl (init := 0) fun d arm => match arm with
    | .mk (.lit (.nat n)) _ _ => max d (n + 1)
    | .mk (.lit (.bool _)) _ _ => max d 1
    | _ => d

/-- `match` の scrutinee に現れる局所名と、そのパターンのリテラルから要る場合分けの深さ。 -/
partial def casesOf : Naru.Core.Expr → List (String × Nat)
  | .match_ s _ arms =>
    let d := litDepth arms
    (if d == 0 then [] else (varsOf s).map (·, d)) ++ casesOf s ++
      arms.flatMap fun | .mk _ g b => (g.map casesOf).getD [] ++ casesOf b
  | .let_ _ _ v b => casesOf v ++ casesOf b
  | .ite c t e => casesOf c ++ casesOf t ++ casesOf e
  | .binop _ l r _ => casesOf l ++ casesOf r
  | .unop _ a => casesOf a
  | .method _ _ r as _ => casesOf r ++ as.flatMap casesOf
  | _ => []

def depthOf (cs : List (String × Nat)) (x : String) : Nat :=
  cs.foldl (fun d (y, k) => if y == x then max d k else d) 0

/-- Nat の局所名の `depth` 段の場合分け(`cases x with | zero => tail | succ x => …`)。 -/
def natCases (x : String) (tail : String) : Nat → String
  | 0 => tail
  | d + 1 => s!"(cases «{x}» with | zero => {tail} | succ «{x}» => {natCases x tail d})"

/-- 場合分けの列(局所名, Nat か, 深さ)を tactic の文字列に。 -/
def casesScript : List (String × Bool × Nat) → String → String
  | [], tail => tail
  | (x, true, d) :: rest, tail => natCases x (casesScript rest tail) d
  | (x, false, _) :: rest, tail => s!"(cases «{x}» with | false => {casesScript rest tail} | true => {casesScript rest tail})"

/-- 接続の証明(仮引数と Core の本文から): 場合分けが要れば `by intro …; cases …` の tactic、要らなければ `rfl` の項。 -/
def proofOf (params : List Naru.Core.Param) (body : Naru.Core.Expr) : String :=
  let bs := params.filterMap binderOf
  let args := " ".intercalate (bs.map (·.2.2))
  let cs := casesOf body
  let targets := params.filterMap fun p =>
    let d := depthOf cs p.name
    if d == 0 then none
    else match p.ty with
      | .nat => some (p.name, true, d)
      | .bool => some (p.name, false, 1)
      | _ => none
  if targets.isEmpty then (if bs.isEmpty then "rfl" else s!"fun {args} => rfl")
  else s!"by intro {args}; {casesScript targets "rfl"}"

/-- 接続の定理 1 つ分(1 行): `<thm> : ∀ args, <call> = <読み> (Env.ofList …) <core> := <proof>`。 -/
def connStmt (thm lean : String) (params : List Naru.Core.Param) (t : NaruSem.Ty) (coreName proof : String) : String :=
  let bs := params.filterMap binderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let args := " ".intercalate (bs.map (·.2.2))
  let den := match t with | .nat => "NaruSem.denoteN" | .bool => "NaruSem.denoteB"
  let call := if bs.isEmpty then lean else s!"{lean} {args}"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  s!"theorem {thm} : {quant s!"{call} = {den} (NaruSem.Env.ofList {env}) {coreName}"} := {proof}"

/-- 1 つの runtime 宣言の接続と保存: `conn_<f>`(実生成宣言 = 読み)と `pres_<f>`(独立意味論の結果 = 実生成宣言の値)。 -/
def connOf (key : String) (params : List Naru.Core.Param) (t : NaruSem.Ty) (body : Naru.Core.Expr) : String :=
  let n := shortName key
  let lean := Naru.Backend.Model.leanName key
  let bs := params.filterMap binderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let args := " ".intercalate (bs.map (·.2.2))
  let (val, sound, asound) := match t with
    | .nat => ("NaruSem.Val.nat", "NaruSem.check_sound_nat", "NaruSem.Surf.check_sound_nat")
    | .bool => ("NaruSem.Val.bool", "NaruSem.check_sound_bool", "NaruSem.Surf.check_sound_bool")
  let call := if bs.isEmpty then lean else s!"{lean} {args}"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  let lam (body : String) : String := if bs.isEmpty then body else s!"fun {args} => {body}"
  let conn := if bs.isEmpty then s!"conn_{n}" else s!"conn_{n} {args}"
  s!"-- {key}: the generated declaration `{lean}` is definitionally the Lean reading of its Core; hence its value is the meaning of the Core\n" ++
  connStmt s!"conn_{n}" lean params t s!"core_{n}" (proofOf params body) ++ "\n" ++
  s!"theorem pres_{n} : {quant s!"NaruSem.eval (NaruSem.Env.ofList {env}) core_{n} = some ({val} ({call}))"} :=\n" ++
  s!"  {lam s!"{sound} {env} wt_{n} ({conn})"}\n" ++
  s!"-- the parsed AST's meaning is the value of the generated declaration: AST → Core (`low_{n}`) → generated Lean (`conn_{n}`) (C49 / C51)\n" ++
  s!"theorem apres_{n} : {quant s!"NaruSem.Surf.eval (NaruSem.Env.ofList {env}) ast_{n} = some ({val} ({call}))"} :=\n" ++
  s!"  {lam s!"{asound} {env} wta_{n} low_{n} ({conn})"}\n\n"

/-- 検査プログラム `ModelCheck.lean`: 実生成 Model を import し、一般定理の量化の形と、各 runtime 宣言の接続・保存、AST → 生成 Lean の合成を kernel に
検査させて監査する。 -/
def modelProgram (decls : List (String × List Naru.Core.Param × NaruSem.Ty × Naru.Core.Expr)) : String :=
  let names := decls.flatMap fun (key, _, _, _) => [s!"conn_{shortName key}", s!"pres_{shortName key}", s!"apres_{shortName key}"]
  s!"-- naru_test semantics (C40 / C41 / C44 / C49): generated from NaruTest/Semantics.lean. Connection of the generated Model of {source} to the Core semantics and to the Surface AST semantics.\n" ++
  "import SurfaceScope\nimport Model.Sem.Core\n\n" ++
  "-- the general theorem quantifies over any context, expression, type and matching environment (C40 / C41)\n" ++
  "example : ∀ (Γ : NaruSem.Ctx) (e : Naru.Core.Expr) (t : NaruSem.Ty) (ρ : NaruSem.Env),\n" ++
  "    NaruSem.wtR Γ e = some t → Γ = ρ.ty → NaruSem.eval ρ e = some (NaruSem.denoteV ρ t e) :=\n" ++
  "  fun _ _ _ _ h hρ => NaruSem.denote_sound h _ hρ\n" ++
  "-- the arms theorem quantifies over any well-formed exhaustive arms, environment and scrutinee value (C41)\n" ++
  "example : ∀ (Γ : NaruSem.Ctx) (ts t : NaruSem.Ty) (arms : List Naru.Core.Arm) (ρ : NaruSem.Env) (v : NaruSem.Val),\n" ++
  "    NaruSem.wtArmsR Γ ts arms = some t → NaruSem.exhaustive ts arms = true → Γ = ρ.ty → v.ty = ts →\n" ++
  "    NaruSem.evalArms ρ v arms = some (NaruSem.denoteArmsV ρ t v arms) :=\n" ++
  "  fun _ _ _ _ _ _ h hex hρ hv => NaruSem.denoteArms_sound h hex _ hρ _ hv\n" ++
  "-- the AST → Core theorem quantifies over any context, well-formed runtime Surface AST and type: the lowering is defined, its Core is\n" ++
  "-- well-formed in the same context, and the AST's meaning equals the Core's meaning in every environment (C49)\n" ++
  "example : ∀ (Γ : NaruSem.Ctx) (e : NaruSem.Surf.Expr) (t : NaruSem.Ty), NaruSem.Surf.wtR Γ e = some t →\n" ++
  "    ∃ c, NaruSem.Surf.lower Γ e = some c ∧ NaruSem.wtR Γ c = some t ∧ ∀ ρ : NaruSem.Env, NaruSem.Surf.eval ρ e = NaruSem.eval ρ c :=\n" ++
  "  fun _ _ _ h => NaruSem.Surf.lower_sound h\n" ++
  "-- composed with C40 / C41: the AST's meaning is the Lean reading of the lowered Core, for any matching environment (C49)\n" ++
  "example : ∀ (Γ : NaruSem.Ctx) (e : NaruSem.Surf.Expr) (c : Naru.Core.Expr) (ρ : NaruSem.Env), NaruSem.Surf.wtR Γ e = some .nat →\n" ++
  "    NaruSem.Surf.lower Γ e = some c → Γ = ρ.ty → NaruSem.Surf.eval ρ e = some (.nat (NaruSem.denoteN ρ c)) :=\n" ++
  "  fun _ _ _ _ h hl hρ => NaruSem.Surf.preserve_nat h hl _ hρ\n\n" ++
  "".intercalate (decls.map fun (key, params, t, body) => connOf key params t body) ++
  s!"#audit_axioms {" ".intercalate names}\n"

/-! ### Statements の接続(C42 / C43 / C44)

生成 Statements の spec 宣言は `Prop` の定数 / 関数なので、接続は `Prop` の等式 `Statements.Sem.Core.f args = denoteP (SEnv.ofList …) core_f`
(kernel の定義的等しさ)。証明は Model と同じ `proofOf`: `match` の無い宣言(と変数・`_` のパターンだけの `match`。量化・命題の `let`・命題の条件の `if` は
生成形 `∀ (x : T), …` / `let x : Prop := …` / `(C → P) ∧ (¬ C → Q)` が読みと定義的に等しい)は `rfl` の項、リテラルパターンの `match` は scrutinee の
`cases` の後に `rfl`。 -/

/-- 仮引数 → (Lean の束縛, spec の環境の項目(値), 実引数)。 -/
def specBinderOf (p : Naru.Core.Param) : Option (String × String × String) :=
  match p.ty with
  | .nat => some (s!"(«{p.name}» : Nat)", s!"({p.name.quote}, NaruSem.SVal.val (NaruSem.Val.nat «{p.name}»))", s!"«{p.name}»")
  | .bool => some (s!"(«{p.name}» : Bool)", s!"({p.name.quote}, NaruSem.SVal.val (NaruSem.Val.bool «{p.name}»))", s!"«{p.name}»")
  | _ => none

/-- 接続の定理 1 つ分(1 行、Statements): `<thm> : ∀ args, <call> = denoteP (SEnv.ofList …) <core> := <proof>`(`proofOf`: `rfl` か scrutinee の `cases`)。 -/
def specConnStmt (thm lean : String) (params : List Naru.Core.Param) (body : Naru.Core.Expr) (coreName : String) : String :=
  let bs := params.filterMap specBinderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let args := " ".intercalate (bs.map (·.2.2))
  let call := if bs.isEmpty then lean else s!"{lean} {args}"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  s!"theorem {thm} : {quant s!"{call} = NaruSem.denoteP (NaruSem.SEnv.ofList {env}) {coreName}"} := {proofOf params body}"

/-- 1 つの spec 宣言の接続と保存: `conn_<f>`(実生成宣言の命題 = 読み)、`stage_<f>`(段階: 基礎段階なら `basic` が真、C43 の段階なら偽)、
`pres_<f>`(実生成宣言の命題は独立意味論の意味)。 -/
def specConnOf (key : String) (params : List Naru.Core.Param) (body : Naru.Core.Expr) (isBasic : Bool) : String :=
  let n := shortName key
  let lean := Naru.Backend.Statements.stmtName key
  let bs := params.filterMap specBinderOf
  let vals := params.filterMap binderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let valsEnv := "[" ++ ", ".intercalate (vals.map (·.2.1)) ++ "]"
  let args := " ".intercalate (bs.map (·.2.2))
  let call := if bs.isEmpty then lean else s!"{lean} {args}"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  let lam (body : String) : String := if bs.isEmpty then body else s!"fun {args} => {body}"
  let conn := if bs.isEmpty then s!"conn_{n}" else s!"conn_{n} {args}"
  let stage := if isBasic then "basic stage (C42)" else "quantifier / Prop let / Prop if / guarded match stage (C43)"
  s!"-- {key} ({stage}): the generated declaration `{lean}` is definitionally the Lean reading of its Core; hence it is the meaning of the Core\n" ++
  specConnStmt s!"conn_{n}" lean params body s!"core_{n}" ++ "\n" ++
  s!"theorem stage_{n} : NaruSem.basic core_{n} = {isBasic} := by decide\n" ++
  s!"theorem pres_{n} : {quant s!"NaruSem.Sem (NaruSem.SEnv.ofList {env}) core_{n} ({call})"} :=\n" ++
  s!"  {lam s!"NaruSem.check_sound_prop {valsEnv} wt_{n} form_{n} ({conn})"}\n" ++
  s!"-- the parsed AST's meaning is the proposition of the generated declaration: AST → Core (`lows_{n}`) → generated Lean (`conn_{n}`) (C50 / C51)\n" ++
  s!"theorem apres_{n} : {quant s!"NaruSem.Surf.Sem (NaruSem.SEnv.ofList {env}) ast_{n} ({call})"} :=\n" ++
  s!"  {lam s!"NaruSem.Surf.check_sound_prop {valsEnv} wta_{n} forma_{n} lows_{n} ({conn})"}\n\n"

/-- 検査プログラム `StatementsCheck.lean`: 実生成 Statements を import し、一般定理の量化の形と、各 spec 宣言の接続・段階・保存を kernel に検査させて監査する。 -/
def statementsProgram (decls : List (String × List Naru.Core.Param × Naru.Core.Expr × Bool)) : String :=
  let names := decls.flatMap fun (key, _, _, _) => [s!"conn_{shortName key}", s!"stage_{shortName key}", s!"pres_{shortName key}", s!"apres_{shortName key}"]
  s!"-- naru_test semantics (C42 / C43 / C44 / C50): generated from NaruTest/Semantics.lean. Connection of the generated Statements of {source} to the Core semantics and to the Surface AST semantics.\n" ++
  "import SurfaceScope\nimport Statements.Sem.Core\n\n" ++
  "-- the spec AST → Core theorem quantifies over any context, well-formed spec Surface AST and type: the lowering is defined, its Core is\n" ++
  "-- well-formed in the same context, and in every matching environment the AST's meaning is the Core's meaning (C50)\n" ++
  "example : ∀ (Γ : NaruSem.SCtx) (e : NaruSem.Surf.Expr) (τ : NaruSem.STy), NaruSem.Surf.wtS Γ e = some τ →\n" ++
  "    ∃ c, NaruSem.Surf.lowerS Γ e = some c ∧ NaruSem.wtS Γ c = some τ ∧\n" ++
  "      ∀ (ρ : NaruSem.SEnv), Γ = ρ.ctx → ∀ (P : Prop), NaruSem.Surf.Sem ρ e P → NaruSem.Sem ρ c P :=\n" ++
  "  fun _ _ _ h => NaruSem.Surf.lowerS_sound h\n" ++
  "-- the correspondence is an equivalence in both directions for any proposition (C50)\n" ++
  "example : ∀ (Γ : NaruSem.SCtx) (e : NaruSem.Surf.Expr) (τ : NaruSem.STy) (c : Naru.Core.Expr) (ρ : NaruSem.SEnv) (P : Prop),\n" ++
  "    NaruSem.Surf.wtS Γ e = some τ → τ.isForm = true → NaruSem.Surf.lowerS Γ e = some c → Γ = ρ.ctx →\n" ++
  "    (NaruSem.Surf.Sem ρ e P ↔ NaruSem.Sem ρ c P) :=\n" ++
  "  fun _ _ _ _ _ P h hf hl hρ => NaruSem.Surf.Sem_lowerS_iff h hf hl _ hρ P\n" ++
  "-- composed with C42 / C43: the AST's meaning is equivalent to the Lean reading of the lowered Core, for any matching environment (C50)\n" ++
  "example : ∀ (Γ : NaruSem.SCtx) (e : NaruSem.Surf.Expr) (τ : NaruSem.STy) (c : Naru.Core.Expr) (ρ : NaruSem.SEnv) (P : Prop),\n" ++
  "    NaruSem.Surf.wtS Γ e = some τ → NaruSem.Surf.lowerS Γ e = some c → Γ = ρ.ctx → NaruSem.Surf.Sem ρ e P → (P ↔ NaruSem.denoteP ρ c) :=\n" ++
  "  fun _ _ _ _ _ _ h hl hρ hP => NaruSem.Surf.preserve_prop h hl _ hρ hP\n" ++
  "-- the general theorem quantifies over any context, well-formed spec expression (quantifiers, Prop lets, Prop ifs, guarded matches included),\n" ++
  "-- matching environment (Prop bindings included) and meaning, and is an equivalence (C42 / C43)\n" ++
  "example : ∀ (Γ : NaruSem.SCtx) (e : Naru.Core.Expr) (τ : NaruSem.STy) (ρ : NaruSem.SEnv) (P : Prop),\n" ++
  "    NaruSem.wtS Γ e = some τ → Γ = ρ.ctx → NaruSem.Sem ρ e P → (P ↔ NaruSem.denoteP ρ e) :=\n" ++
  "  fun _ _ _ _ _ hw hρ h => NaruSem.Sem_denote hw _ hρ h\n" ++
  "-- the value / proposition boundary quantifies over any expression without quantifiers / Prop locals and any environment (C43)\n" ++
  "example : ∀ (e : Naru.Core.Expr) (ρ : NaruSem.SEnv), NaruSem.proppyS ρ.ctx e = false →\n" ++
  "    (NaruSem.denoteP ρ e ↔ NaruSem.denoteB ρ.vals e = true) :=\n" ++
  "  fun e ρ hp => NaruSem.denoteP_iff_denoteB_noProp e ρ hp\n" ++
  "-- the arm lemmas quantify over any environment, scrutinee value, pattern, guard, body and remaining arms: a matched guarded arm reads\n" ++
  "-- `(G → B) ∧ (¬ G → R)` with the bindings in scope for G and B only, and the remaining arms in the outer environment (C43)\n" ++
  "example : ∀ (ρ : NaruSem.SEnv) (v : NaruSem.Val) (p : Naru.Core.Pat) (g b : Naru.Core.Expr) (rest : List Naru.Core.Arm)\n" ++
  "    (bs : List (String × NaruSem.Val)), NaruSem.matchPat p v = some bs →\n" ++
  "    (NaruSem.denoteArmsP ρ v (.mk p (some g) b :: rest) ↔\n" ++
  "      ((NaruSem.denoteP (ρ.extVals bs) g → NaruSem.denoteP (ρ.extVals bs) b) ∧ (¬ NaruSem.denoteP (ρ.extVals bs) g → NaruSem.denoteArmsP ρ v rest))) :=\n" ++
  "  fun ρ v p g b rest bs hm => NaruSem.denoteArmsP_guard ρ v p g b rest bs hm\n" ++
  "-- the quantifier lemma quantifies over any environment, binder and continuation: `forall x: T` ranges over all of T (C43)\n" ++
  "example : ∀ (ρ : NaruSem.SEnv) (x : String) (tv : Naru.TyV) (t : NaruSem.Ty) (bs : List (String × Naru.TyV)) (k : NaruSem.SEnv → Prop),\n" ++
  "    NaruSem.TyV.toTy? tv = some t →\n" ++
  "    NaruSem.denoteQuant .forall_ ρ ((x, tv) :: bs) k = ∀ a : t.carrier, NaruSem.denoteQuant .forall_ (ρ.ext x (.val (NaruSem.Val.of t a))) bs k :=\n" ++
  "  fun ρ x tv t bs k ht => NaruSem.denoteQuant_forall_cons ρ x tv t bs k ht\n\n" ++
  "".intercalate (decls.map fun (key, params, body, isBasic) => specConnOf key params body isBasic) ++
  s!"#audit_axioms {" ".intercalate names}\n"

/-- 生成ファイルの中の 1 つの宣言の本文(`def <名前> ` で始まる行から空行まで)。 -/
def declText (content : String) (leanName : String) : Option String := Id.run do
  let lines := content.splitOn "\n"
  let mut acc : List String := []
  let mut inside := false
  for l in lines do
    if !inside then
      if l.startsWith s!"def {leanName} " || l.startsWith s!"def {leanName} :" then
        inside := true
        acc := [l]
    else
      if l.trimAscii.isEmpty then break
      acc := acc ++ [l]
  if acc.isEmpty then none else some ("\n".intercalate acc)

/-- 2 つの部分文字列を取り違える。 -/
def swapText (a b : String) (s : String) : String :=
  ((s.replace a "\x01").replace b a).replace "\x01" b

/-- `&&` と `||` を取り違える。 -/
def swapAndOr : String → String := swapText "&&" "||"

/-- 負の検体の作り方: (検体の宣言, `Wrong.<名前>`, 実生成文字列に要る部分 `good`, 誤出力に現れる部分 `bad`, 変換, 説明)。 -/
structure Mistranslation where
  key : String
  wrong : String
  good : String
  bad : String
  transform : String → String
  note : String

def mistranslations : List Mistranslation :=
  [ { key := "Sem.Core.logic", wrong := "Wrong.logic", good := "&&", bad := "||", transform := swapAndOr,
      note := "`&&` and `||` swapped in the generated text of `logic`" },
    { key := "Sem.Core.letShadow", wrong := "Wrong.letShadow", good := "let «x» : Nat := «x» * (2 : Nat)", bad := "let «y» : Nat := «x» * (2 : Nat)",
      transform := fun s => s.replace "let «x» : Nat := «x» * (2 : Nat)" "let «y» : Nat := «x» * (2 : Nat)",
      note := "the second binding renamed in the generated text of `letShadow` (the result refers to the wrong binding)" },
    { key := "Sem.Core.matchBool", wrong := "Wrong.matchBool", good := "| true =>", bad := "| false =>", transform := swapText "| true =>" "| false =>",
      note := "the `true` and `false` arms swapped in the generated text of `matchBool` (arm order / selection)" },
    { key := "Sem.Core.matchNat", wrong := "Wrong.matchNat", good := "if Decidable.decide («n» < (10 : Nat)) then", bad := "if !Decidable.decide («n» < (10 : Nat)) then",
      transform := fun s => s.replace "if Decidable.decide («n» < (10 : Nat)) then" "if !Decidable.decide («n» < (10 : Nat)) then",
      note := "the guard negated in the generated text of `matchNat` (guard success / failure swapped)" },
    { key := "Sem.Core.matchShadow", wrong := "Wrong.matchShadow", good := "«n» == «x»", bad := "«x» == «x»",
      transform := fun s => s.replace "«n» == «x»" "«x» == «x»",
      note := "the arm binding leaked into the following arm in the generated text of `matchShadow` (`n == x` reads the pattern's `n` = `x` instead of the parameter)" } ]

/-- 負の検体(Statements、C46): 実生成文字列から作る誤翻訳。論理の取り違え、含意の向き、Bool の値の命題への境界、`if` の分岐。 -/
def specMistranslations : List Mistranslation :=
  [ { key := "Sem.Core.specLogic", wrong := "Wrong.specLogic", good := "∧", bad := "∨", transform := swapText "∧" "∨",
      note := "`∧` and `∨` swapped in the generated text of `specLogic`" },
    { key := "Sem.Core.specCmp", wrong := "Wrong.specCmp", good := "(«x» < «y») → («x» ≤ «y»)", bad := "(«x» ≤ «y») → («x» < «y»)",
      transform := fun s => s.replace "(«x» < «y») → («x» ≤ «y»)" "(«x» ≤ «y») → («x» < «y»)",
      note := "the implication reversed in the generated text of `specCmp` (a one-directional error the equivalence must reject)" },
    { key := "Sem.Core.specVar", wrong := "Wrong.specVar", good := "«a» = true", bad := "«a» = false",
      transform := fun s => s.replace "«a» = true" "«a» = false",
      note := "the Bool value mapped to the wrong proposition (`= false`) in the generated text of `specVar` (value / proposition boundary)" },
    { key := "Sem.Core.specIfBool", wrong := "Wrong.specIfBool", good := "«x» > (0 : Nat)", bad := "«x» = (0 : Nat)",
      transform := swapText "«x» > (0 : Nat)" "«x» = (0 : Nat)",
      note := "the `then` and `else` branches swapped in the generated text of `specIfBool`" },
    -- C43: 量化・命題の let・ガード・↔
    { key := "Sem.Core.specForall", wrong := "Wrong.specForall", good := "∀ («n» : Nat)", bad := "∃ («n» : Nat)",
      transform := fun s => s.replace "∀ («n» : Nat)" "∃ («n» : Nat)",
      note := "`∀` replaced by `∃` in the generated text of `specForall` (`∀ n, n ≥ x` holds only for x = 0, `∃ n, n ≥ x` always: the quantifier must range over all of Nat)" },
    { key := "Sem.Core.specLetProp", wrong := "Wrong.specLetProp", good := "\n  «q»", bad := "\n  «p»",
      transform := fun s => s.replace "\n  «q»" "\n  «p»",
      note := "the body refers to the wrong Prop binding (`p` instead of `q`) in the generated text of `specLetProp` (Prop let binding mix-up)" },
    { key := "Sem.Core.specMatch", wrong := "Wrong.specMatch", good := "«n» < (3 : Nat)", bad := "«n» ≥ (3 : Nat)",
      transform := fun s => s.replace "«n» < (3 : Nat)" "«n» ≥ (3 : Nat)",
      note := "the guard negated in the generated text of `specMatch` (guard success / failure swapped in both places it is emitted)" },
    { key := "Sem.Core.specIffProp", wrong := "Wrong.specIffProp", good := "↔", bad := "→",
      transform := fun s => s.replace "↔" "→",
      note := "`↔` replaced by the one-directional `→` in the generated text of `specIffProp` (Prop `==` / `!=` must be an equivalence)" },
    { key := "Sem.Core.specGuardProp", wrong := "Wrong.specGuardProp", good := "∃ («m» : Nat)", bad := "∀ («m» : Nat)",
      transform := fun s => s.replace "∃ («m» : Nat)" "∀ («m» : Nat)",
      note := "the Prop guard's `∃` replaced by `∀` in the generated text of `specGuardProp` (guard success / failure changed)" },
    { key := "Sem.Core.specMatchShadow", wrong := "Wrong.specMatchShadow", good := "«n» = «x»", bad := "«x» = «x»",
      transform := fun s => s.replace "«n» = «x»" "«x» = «x»",
      note := "the arm binding leaked into the following arm in the generated text of `specMatchShadow` (`n = x` reads the pattern's `n` = `x` instead of the parameter)" } ]

/-- 負の検体のプログラムと、接続検査が失敗しなければならない行(1 始まり)。誤出力(型検査は通る)の宣言の後に、正しい出力の対照 `conn_<f>_ok` と
誤出力への接続 `conn_wrong_<f>` を置く(`connOf 定理名 Lean 名 検体の宣言名` が接続の定理 1 行を返す。宣言が無ければ `none`)。 -/
def wrongProgramWith (what : String) (imports : List String) (wrongs : List (Mistranslation × String))
    (connOf : String → String → String → Option String) : String × List Nat := Id.run do
  let mut lines : List String :=
    [ s!"-- naru_test semantics (C46): generated from NaruTest/Semantics.lean. Isolated mistranslations of the generated {what} (they type-check) must fail the connection check." ] ++
    imports.map (s!"import {·}") ++ [""]
  for (m, text) in wrongs do
    lines := lines ++ [s!"-- {m.note}"] ++ text.splitOn "\n" ++ [""]
  lines := lines ++ ["-- controls: the correct generated declarations connect"]
  for (m, _) in wrongs do
    if let some stmt := connOf s!"conn_{shortName m.key}_ok" "" m.key then lines := lines ++ [stmt]
  lines := lines ++ ["", "-- the mistranslations must not connect to the same (correct) input Core"]
  let mut failing : List Nat := []
  for (m, _) in wrongs do
    if let some stmt := connOf s!"conn_wrong_{shortName m.key}" m.wrong m.key then
      lines := lines ++ [stmt]
      failing := failing ++ [lines.length]
  return ("\n".intercalate lines ++ "\n", failing)

/-- 負の検体 `ModelWrong.lean`(Model)。Lean 名が空なら正しい実生成宣言(対照)。 -/
def wrongProgram (decls : List (String × List Naru.Core.Param × NaruSem.Ty × Naru.Core.Expr))
    (wrongs : List (Mistranslation × String)) : String × List Nat :=
  wrongProgramWith "Model" ["Scope", "Model.Sem.Core"] wrongs fun thm lean key =>
    (decls.find? fun (k, _, _, _) => k == key).map fun (key, params, t, body) =>
      let name := if lean.isEmpty then Naru.Backend.Model.leanName key else lean
      connStmt thm name params t s!"core_{shortName key}" (proofOf params body)

/-- 負の検体 `StatementsWrong.lean`(Statements)。 -/
def specWrongProgram (decls : List (String × List Naru.Core.Param × Naru.Core.Expr × Bool)) (wrongs : List (Mistranslation × String)) :
    String × List Nat :=
  wrongProgramWith "Statements" ["Scope", "Statements.Sem.Core"] wrongs fun thm lean key =>
    (decls.find? fun (k, _, _, _) => k == key).map fun (key, params, body, _) =>
      let name := if lean.isEmpty then Naru.Backend.Statements.stmtName key else lean
      specConnStmt thm name params body s!"core_{shortName key}"

/-! ### AST → Core の負の検体(C49 / C52)

実際の Core から、型と Core の適格性(`wtR`)は保つが意味の異なる Core を作り(`Core.Expr` の値の変換。文字列の置換ではない)、同じ正しい AST の
変換 `Surf.lower` との一致 `conn_wrong_<f> : Surf.lower actx_<f> ast_<f> = some WrongCore.<f> := rfl` だけが失敗することを確かめる(対照 `conn_<f>_ok` は成功。定理名は `wrongProgramWith` のもの)。 -/

/-- 負の検体の作り方(Core): (検体の宣言, `WrongCore.<名前>`, Core の変換, 説明)。 -/
structure CoreMistranslation where
  key : String
  wrong : String
  transform : Naru.Core.Expr → Naru.Core.Expr
  note : String

/-- 最外の `&&` / `||` を取り違える(`logic` の `(a && b) || (!a implies b)` は `(a && b) && (!a implies b)` = `a && b` になり、`a || b` と意味が違う。
式全体で取り違えると `(a || b) && (!a implies b)` = `a || b` で意味が同じになってしまう — 負の検体は意味の異なる Core にする)。 -/
def swapTopAndOr : Naru.Core.Expr → Naru.Core.Expr
  | .binop op l r t => .binop (if op == "&&" then "||" else if op == "||" then "&&" else op) l r t
  | e => e

/-- 2 つ目の `let_` の束縛名を `y` に改名する(`letShadow`: 以後の `x` は 1 つ目の束縛を指すので、型は合うが意味が違う)。 -/
def renameSecondLet : Naru.Core.Expr → Naru.Core.Expr
  | .let_ x ty v (.let_ _ ty2 v2 b) => .let_ x ty v (.let_ "y" ty2 v2 b)
  | e => e

/-- `match` のすべてのガードを否定する(ガードの成功と失敗の取り違え)。 -/
partial def negateGuards : Naru.Core.Expr → Naru.Core.Expr
  | .match_ s st arms => .match_ s st (arms.map fun | .mk p g b => .mk p (g.map fun g => .unop "!" g) b)
  | .let_ x ty v b => .let_ x ty v (negateGuards b)
  | e => e

def coreMistranslations : List CoreMistranslation :=
  [ { key := "Sem.Core.logic", wrong := "WrongCore.logic", transform := swapTopAndOr,
      note := "the outermost `||` replaced by `&&` in the Core of `logic` (well-formed; `a && b` instead of `a || b`)" },
    { key := "Sem.Core.letShadow", wrong := "WrongCore.letShadow", transform := renameSecondLet,
      note := "the second `let_` renamed to `y` in the Core of `letShadow` (well-formed; the result refers to the wrong binding)" },
    { key := "Sem.Core.matchNat", wrong := "WrongCore.matchNat", transform := negateGuards,
      note := "the guard negated in the Core of `matchNat` (well-formed; guard success / failure swapped)" } ]

/-- 負の検体 `SurfaceWrong.lean`(AST → Core): 誤った Core の定義と適格性(`decide`)の後に、対照 `conn_<f>_ok` と誤った Core への対応 `conn_wrong_<f>`(`rfl`)。 -/
def surfaceWrongProgram (decls : List (String × List Naru.Core.Param × NaruSem.Ty × Naru.Core.Expr)) (wrongs : List (Mistranslation × String)) :
    String × List Nat :=
  wrongProgramWith "Core" ["Scope", "SurfaceScope"] wrongs fun thm lean key =>
    (decls.find? fun (k, _, _, _) => k == key).map fun (key, _, _, _) =>
      let n := shortName key
      let target := if lean.isEmpty then s!"core_{n}" else lean
      s!"theorem {thm} : NaruSem.Surf.lower actx_{n} ast_{n} = some {target} := rfl"

/-- 仮引数の小さな値の環境をすべて列挙する(Nat は 0〜4、Bool は両方): 誤った Core の意味が AST の意味と食い違う環境の探索に使う。 -/
def witnessEnvs (params : List Naru.Core.Param) : List (List (String × NaruSem.Val)) :=
  params.foldr (init := [[]]) fun p acc =>
    let choices : List NaruSem.Val := match p.ty with
      | .nat => (List.range 5).map NaruSem.Val.nat
      | .bool => [.bool false, .bool true]
      | _ => []
    choices.flatMap fun v => acc.map fun env => (p.name, v) :: env

def valTerm : NaruSem.Val → String
  | .nat n => s!"NaruSem.Val.nat {n}"
  | .bool b => s!"NaruSem.Val.bool {b}"

def envTerm (env : List (String × NaruSem.Val)) : String :=
  "NaruSem.Env.ofList [" ++ ", ".intercalate (env.map fun (x, v) => s!"({x.quote}, {valTerm v})") ++ "]"

/-- 実際の Core から負の検体を作る: 変換が実際に Core を変え、変えた Core が同じ文脈で適格(`wtR` が同じ型)で、正しい AST の変換(= 実際の Core)と異なり、
AST の意味と食い違う環境(`witnessEnvs`)があることをドライバで確かめてから、Lean の定義・適格性の定理・意味の食い違いの定理(`diff_<f>`: その環境で
`Surf.eval ast ≠ eval wrong`、`decide`)の文面を返す(失敗が構文の不一致だけでなく意味の不一致によることの照合)。 -/
def deriveCoreWrongs (decls : List (String × List Naru.Core.Param × NaruSem.Ty × Naru.Core.Expr)) (asts : List (String × NaruSem.Surf.Expr))
    (mts : List CoreMistranslation) : M (List (Mistranslation × String)) := do
  let mut wrongs : List (Mistranslation × String) := []
  for mt in mts do
    match decls.find? fun (k, _, _, _) => k == mt.key, asts.lookup mt.key with
    | some (key, params, t, body), some ast =>
      let n := shortName key
      let wrong := mt.transform body
      let ctx := ctxOfParams params
      let witness := (witnessEnvs params).find? fun env =>
        NaruSem.Surf.eval (NaruSem.Env.ofList env) ast != NaruSem.eval (NaruSem.Env.ofList env) wrong
      match witness with
      | some env =>
        if wrong != body && NaruSem.wtR ctx wrong == some t && NaruSem.Surf.lower ctx ast == some body && NaruSem.Surf.lower ctx ast != some wrong then
          ok s!"C52: `{mt.wrong}` is the Core of `{key}` with {mt.note}: well-formed (wtR = {tyTerm t}), not the lowering of the parsed AST, and its meaning differs from the AST's at {env.map fun (x, v) => s!"{x} = {valTerm v}"}"
          let text := s!"def {mt.wrong} : Naru.Core.Expr :=\n  {NaruSem.Quote.expr wrong}\n" ++
            s!"theorem wt_{n}_wrong : NaruSem.wtR ctx_{n} {mt.wrong} = some {tyTerm t} := by decide\n" ++
            s!"theorem diff_{n}_wrong : NaruSem.Surf.eval ({envTerm env}) ast_{n} ≠ NaruSem.eval ({envTerm env}) {mt.wrong} := by decide"
          let m : Mistranslation := { key := key, wrong := mt.wrong, good := "", bad := "", transform := id, note := mt.note }
          wrongs := wrongs ++ [(m, text)]
        else fail s!"C52: could not derive `{mt.wrong}` from the Core of `{key}`: changed {wrong != body}, wtR {(NaruSem.wtR ctx wrong).map tyTerm}, lowering agrees {NaruSem.Surf.lower ctx ast == some body}"
      | none => fail s!"C52: `{mt.wrong}` has the same meaning as the parsed AST of `{key}` on all small environments (a negative specimen must differ in meaning): {NaruSem.Quote.expr wrong}"
    | _, _ => fail s!"C52: `{mt.key}` is not a connected runtime declaration with a parsed AST"
  return wrongs

/-! ### spec の AST → Core の負の検体(C50 / C52)

実際の spec の Core から、Core の適格性(`wtS`)は保つが意味の異なる Core を作り(`Core.Expr` の値の変換)、同じ正しい AST の変換 `Surf.lowerS` との一致
`conn_wrong_<f> : Surf.lowerS actx_<f> ast_<f> = some WrongCore.<f> := rfl` だけが失敗することを確かめる。意味の食い違いは、命題の意味は `decide` で評価できないので、
具体環境での読み `denoteP` の非同値 `diff_<f>_wrong : ¬ (denoteP ρ WrongCore.<f> ↔ denoteP ρ core_<f>)` を明示の命題(`show`)と証明で kernel に検査させる
(`Sem_denote` により読みは意味そのものなので、これは意味の食い違い)。 -/

/-- 負の検体の作り方(spec の Core): (検体の宣言, `WrongCore.<名前>`, Core の変換, 食い違う環境, その環境での非同値の証明, 説明)。 -/
structure SpecCoreMistranslation where
  key : String
  wrong : String
  transform : Naru.Core.Expr → Naru.Core.Expr
  witnessEnv : List (String × NaruSem.Val)
  witness : String
  note : String

/-- 最外の量化の `forall` / `exists` を取り違える。 -/
def swapTopQuant : Naru.Core.Expr → Naru.Core.Expr
  | .quant .forall_ bs b => .quant .exists_ bs b
  | .quant .exists_ bs b => .quant .forall_ bs b
  | e => e

/-- 2 つの `let_` の末尾の局所名が 2 つ目の束縛なら 1 つ目の束縛に取り違える(`specLetProp`: `q` の代わりに `p`)。 -/
def retargetLetTail : Naru.Core.Expr → Naru.Core.Expr
  | .let_ x ty v (.let_ y ty2 v2 (.var z)) => .let_ x ty v (.let_ y ty2 v2 (.var (if z == y then x else z)))
  | e => e

def specCoreMistranslations : List SpecCoreMistranslation :=
  [ { key := "Sem.Core.specForall", wrong := "WrongCore.specForall", transform := swapTopQuant, witnessEnv := [("x", .nat 1)],
      witness := "by\n  show ¬ ((∃ a : Nat, a ≥ 1) ↔ (∀ a : Nat, a ≥ 1))\n  exact fun h => absurd (h.1 ⟨1, Nat.le_refl 1⟩ 0) (by decide)",
      note := "`forall` replaced by `exists` in the Core of `specForall` (well-formed; at x = 1 `∃ n, n ≥ 1` holds but `∀ n, n ≥ 1` does not)" },
    { key := "Sem.Core.specExists", wrong := "WrongCore.specExists", transform := swapTopQuant, witnessEnv := [("x", .nat 0)],
      witness := "by\n  show ¬ ((∀ b : Bool, b = false) ↔ (∃ b : Bool, b = false))\n  exact fun h => absurd (h.2 ⟨false, rfl⟩ true) (by decide)",
      note := "`exists` replaced by `forall` in the Core of `specExists` (well-formed; at x = 0 `∃ b, b = (x > 0)` holds but `∀ b, …` does not)" },
    { key := "Sem.Core.specLetProp", wrong := "WrongCore.specLetProp", transform := retargetLetTail, witnessEnv := [("x", .nat 0)],
      witness := "by\n  show ¬ ((∀ a : Nat, a + 0 ≥ 0) ↔ ((∀ a : Nat, a + 0 ≥ 0) ∧ 0 ≥ 1))\n  exact fun h => absurd (h.1 (fun a => Nat.zero_le _)).2 (by decide)",
      note := "the body refers to the wrong Prop binding (`p` instead of `q`) in the Core of `specLetProp` (well-formed; at x = 0 `p` holds but `q = p && x >= 1` does not)" },
    { key := "Sem.Core.specMatch", wrong := "WrongCore.specMatch", transform := negateGuards, witnessEnv := [("x", .nat 1)],
      witness := "by\n  show ¬ (((¬ (1 < 3) → 1 + 1 ≤ 3) ∧ (¬ ¬ (1 < 3) → 1 ≥ 3)) ↔ (((1 < 3) → 1 + 1 ≤ 3) ∧ (¬ (1 < 3) → 1 ≥ 3)))\n  decide",
      note := "the guard negated in the Core of `specMatch` (well-formed; at x = 1 the negated guard sends the arm to the following arm `x >= 3`)" } ]

def senvTerm (env : List (String × NaruSem.Val)) : String :=
  "NaruSem.SEnv.ofList [" ++ ", ".intercalate (env.map fun (x, v) => s!"({x.quote}, NaruSem.SVal.val ({valTerm v}))") ++ "]"

/-- 負の検体 `SurfaceSpecWrong.lean`(spec の AST → Core): 誤った Core の定義と適格性(`decide`)・意味の食い違い(kernel)の後に、対照 `conn_<f>_ok` と誤った Core への対応
`conn_wrong_<f>`(`rfl`)。 -/
def surfaceSpecWrongProgram (decls : List (String × List Naru.Core.Param × Naru.Core.Expr × Bool)) (wrongs : List (Mistranslation × String)) :
    String × List Nat :=
  wrongProgramWith "spec Core" ["Scope", "SurfaceScope"] wrongs fun thm lean key =>
    (decls.find? fun (k, _, _, _) => k == key).map fun (key, _, _, _) =>
      let n := shortName key
      let target := if lean.isEmpty then s!"core_{n}" else lean
      s!"theorem {thm} : NaruSem.Surf.lowerS actx_{n} ast_{n} = some {target} := rfl"

/-- 実際の spec の Core から負の検体を作る: 変換が実際に Core を変え、変えた Core が同じ文脈で適格(`wtS` が同じ型)で、正しい AST の変換(= 実際の Core)と
異なることをドライバで確かめてから、Lean の定義・適格性の定理・意味の食い違いの定理(`diff_<f>_wrong`: 食い違う環境での読みの非同値。明示の命題と証明)の文面を返す。 -/
def deriveSpecCoreWrongs (decls : List (String × List Naru.Core.Param × Naru.Core.Expr × Bool)) (asts : List (String × NaruSem.Surf.Expr))
    (mts : List SpecCoreMistranslation) : M (List (Mistranslation × String)) := do
  let mut wrongs : List (Mistranslation × String) := []
  for mt in mts do
    match decls.find? fun (k, _, _, _) => k == mt.key, asts.lookup mt.key with
    | some (key, params, body, _), some ast =>
      let n := shortName key
      let wrong := mt.transform body
      let ctx := sctxOfParams params
      match NaruSem.wtS ctx body with
      | some τ =>
        if wrong != body && NaruSem.wtS ctx wrong == some τ && NaruSem.Surf.lowerS ctx ast == some body && NaruSem.Surf.lowerS ctx ast != some wrong then
          ok s!"C52: `{mt.wrong}` is the Core of `{key}` with {mt.note}: well-formed (wtS = {styTerm τ}), not the lowering of the parsed AST; its reading differs at {mt.witnessEnv.map fun (x, v) => s!"{x} = {valTerm v}"} (kernel)"
          let ρ := senvTerm mt.witnessEnv
          let text := s!"def {mt.wrong} : Naru.Core.Expr :=\n  {NaruSem.Quote.expr wrong}\n" ++
            s!"theorem wt_{n}_wrong : NaruSem.wtS ctx_{n} {mt.wrong} = some {styTerm τ} := by decide\n" ++
            s!"-- the reading (= meaning, by `Sem_denote`) of the wrong Core is not equivalent to that of the correct Core in this environment\n" ++
            s!"theorem diff_{n}_wrong : ¬ (NaruSem.denoteP ({ρ}) {mt.wrong} ↔ NaruSem.denoteP ({ρ}) core_{n}) := {mt.witness}"
          let m : Mistranslation := { key := key, wrong := mt.wrong, good := "", bad := "", transform := id, note := mt.note }
          wrongs := wrongs ++ [(m, text)]
        else fail s!"C52: could not derive `{mt.wrong}` from the Core of `{key}`: changed {wrong != body}, wtS {(NaruSem.wtS ctx wrong).map styTerm}, lowering agrees {NaruSem.Surf.lowerS ctx ast == some body}"
      | none => fail s!"C52: the Core of `{key}` is not in scope (wtS = none)"
    | _, _ => fail s!"C52: `{mt.key}` is not a connected spec declaration with a parsed AST"
  return wrongs

/-- 実生成文字列から負の検体を作る(型検査は通るが接続は失敗する誤出力)。`good` が元の文字列にあり、変換後に `bad` が現れ、変換が実際に変えたことを確かめる。 -/
def deriveWrongs (what : String) (text : String) (leanNameOf : String → String) (mts : List Mistranslation) : M (List (Mistranslation × String)) := do
  let mut wrongs : List (Mistranslation × String) := []
  for mt in mts do
    let leanName := leanNameOf mt.key
    match declText text leanName with
    | some decl =>
      let renamed := decl.replace leanName mt.wrong
      let wrong := mt.transform renamed
      if contains decl mt.good && contains wrong mt.bad && wrong != renamed then
        ok s!"C46: `{mt.wrong}` is the generated text of `{leanName}` with {mt.note}"
        wrongs := wrongs ++ [(mt, wrong)]
      else fail s!"C46: could not derive `{mt.wrong}` from the generated text:\n{decl}"
    | none => fail s!"C46: the generated {what} does not contain `{leanName}`"
  return wrongs

/-- 負の検体のプログラムを `lean` に掛け、ちょうど `conn_wrong_*` の行だけで失敗することを確かめる(構文 / import の誤りではなく、意味の対応の不成立)。 -/
def checkWrong (what : String) (file : System.FilePath) (program : String × List Nat) (wrongs : List (Mistranslation × String)) (lp : String)
    (audits : List String := []) : M Unit := do
  let (wrongText, failing) := program
  IO.FS.writeFile file wrongText
  let w ← step s!"C46: lean {file} must fail (the {wrongs.length} mistranslations of the generated {what} type-check but do not connect)" "lean" #[file.toString]
    (expectExit := 1) (env := #[("LEAN_PATH", some lp)])
  let out := w.stdout ++ "\n" ++ w.stderr
  let errs := errorLines out
  let onlyWrong := errs.all failing.contains
  let allWrong := failing.all errs.contains
  let named := wrongs.all fun (mt, _) => contains out mt.wrong
  let syntactic := contains out "unknown" || contains out "unexpected token" || contains out "import" || contains out "sorry"
  let missingAudits := audits.filter fun n => !(auditedNames out).contains n
  if w.exitCode != 0 && failing.length == wrongs.length && onlyWrong && allWrong && named && !syntactic && missingAudits.isEmpty then
    ok s!"C46: exactly the {wrongs.length} connection checks of the mistranslations of the {what} fail (lines {failing}: the reading of the correct Core is not reached), the controls succeed, no syntax / import error"
    if !audits.isEmpty then ok s!"C58: all {audits.length} semantic counterexamples are kernel-checked and audited with 0 forbidden dependencies"
  else fail s!"C46: expected the connection failures exactly on lines {failing}: exit {w.exitCode}, error lines {errs}, missing audits {missingAudits}\n{tail out 2500}"

/-! ### 宣言群の引用と適格性(C54)

検体 `tests/units/accept/sem_calls/src/Sem/Call.naru`(関数・input の保存対象)の fn / input / spec 宣言すべてを、Core(`NaruSem.Call.Decl`)と Surface AST(`NaruSem.Surf.Call.Decl`)の
宣言群として依存順(呼出し先が前)に引用し、宣言群の適格性 `wtProg` と各宣言の署名を kernel の `decide` で、引用の一致と宣言群全体の網羅を `checkProg` の
再コンパイル / 再構文解析で検査する。負の検体は実際の Core / AST の値から作る(文字列の置換ではない)。 -/

def callSource : String := "tests/units/accept/sem_calls/src/Sem/Call.naru"
def callInputSource : String := "tests/units/accept/sem_calls/src/Sem/Inputs.naru"
def callCalleeSource : String := "tests/units/accept/sem_calls/src/Sem/Callees.naru"
def callSources : List String := [callSource, callInputSource, callCalleeSource]

/-- Core の式の中の呼出し先の鍵(出現順、重複あり)。 -/
partial def callKeysOf : Naru.Core.Expr → List String
  | .call k args => k :: args.flatMap callKeysOf
  | .let_ _ _ v b => callKeysOf v ++ callKeysOf b
  | .ite c t e => callKeysOf c ++ callKeysOf t ++ callKeysOf e
  | .binop _ l r _ => callKeysOf l ++ callKeysOf r
  | .unop _ a => callKeysOf a
  | .method _ _ r as _ => callKeysOf r ++ as.flatMap callKeysOf
  | .match_ s _ arms => callKeysOf s ++ arms.flatMap fun | .mk _ g b => (g.map callKeysOf).getD [] ++ callKeysOf b
  | .quant _ _ b => callKeysOf b
  | _ => []

def declCallKeys : NaruSem.Call.Decl → List String
  | .fn _ _ _ b => callKeysOf b
  | .spec _ _ b => callKeysOf b
  | .input .. => []

/-- 依存順(呼出し先が前)に並べる: 置ける宣言(呼出し先がすべて置かれている)を元の順で置いていく。置けなければ `none`(循環・未解決)。 -/
partial def dependencyOrder (decls : List (String × NaruSem.Call.Decl)) : Option (List (String × NaruSem.Call.Decl)) := Id.run do
  let mut placed : List String := []
  let mut out : List (String × NaruSem.Call.Decl) := []
  let mut rest := decls
  while !rest.isEmpty do
    match rest.find? (fun (_, d) => (declCallKeys d).all placed.contains) with
    | some (k, d) =>
      placed := placed ++ [k]
      out := out ++ [(k, d)]
      rest := rest.filter fun (k', _) => k' != k
    | none => return none
  return some out

/-- Core の式の呼出し先 `from` を `to` に置き換える(負の検体: 違う呼出し先・phase の誤り)。 -/
partial def retargetCalls (src dst : String) : Naru.Core.Expr → Naru.Core.Expr
  | .call k args => .call (if k == src then dst else k) (args.map (retargetCalls src dst))
  | .let_ x ty v b => .let_ x ty (retargetCalls src dst v) (retargetCalls src dst b)
  | .ite c t e => .ite (retargetCalls src dst c) (retargetCalls src dst t) (retargetCalls src dst e)
  | .binop op l r ty => .binop op (retargetCalls src dst l) (retargetCalls src dst r) ty
  | .unop op a => .unop op (retargetCalls src dst a)
  | .method tn n r as rt => .method tn n (retargetCalls src dst r) (as.map (retargetCalls src dst)) rt
  | .match_ s st arms => .match_ (retargetCalls src dst s) st (arms.map fun | .mk p g b => .mk p (g.map (retargetCalls src dst)) (retargetCalls src dst b))
  | .quant q bs b => .quant q bs (retargetCalls src dst b)
  | e => e

/-- 鍵 `k` の呼出しに実引数を足す(負の検体: 引数の数)。 -/
partial def addArgTo (k : String) (a : Naru.Core.Expr) : Naru.Core.Expr → Naru.Core.Expr
  | .call k' args => .call k' ((args.map (addArgTo k a)) ++ (if k' == k then [a] else []))
  | .let_ x ty v b => .let_ x ty (addArgTo k a v) (addArgTo k a b)
  | .ite c t e => .ite (addArgTo k a c) (addArgTo k a t) (addArgTo k a e)
  | .binop op l r ty => .binop op (addArgTo k a l) (addArgTo k a r) ty
  | .unop op x => .unop op (addArgTo k a x)
  | .method tn n r as rt => .method tn n (addArgTo k a r) (as.map (addArgTo k a)) rt
  | .match_ s st arms => .match_ (addArgTo k a s) st (arms.map fun | .mk p g b => .mk p (g.map (addArgTo k a)) (addArgTo k a b))
  | .quant q bs b => .quant q bs (addArgTo k a b)
  | e => e

def mapBody (f : Naru.Core.Expr → Naru.Core.Expr) : NaruSem.Call.Decl → NaruSem.Call.Decl
  | .fn k ps t b => .fn k ps t (f b)
  | .spec k ps b => .spec k ps (f b)
  | d => d

/-- 鍵 `k` の宣言の本体だけを変える。 -/
def mapDecl (k : String) (f : Naru.Core.Expr → Naru.Core.Expr) (prog : List NaruSem.Call.Decl) : List NaruSem.Call.Decl :=
  prog.map fun d => if d.key == k then mapBody f d else d

/-- Core の宣言群の負の検体: (名前, 説明, 宣言群)。どれも `wtProg` が `none` でなければドライバが FAIL にする。 -/
def coreWrongProgs (prog : List NaruSem.Call.Decl) : List (String × String × List NaruSem.Call.Decl) :=
  let callBase := prog.filter fun d => d.key == "Sem.Call.callBase"
  let others := prog.filter fun d => d.key != "Sem.Call.callBase"
  [ ("reversed", "the declarations in reverse order (callees after their callers: not in dependency order)", prog.reverse),
    ("retarget", "`callBase` calling `addTo` (a different callee with 2 parameters) instead of `base`",
      mapDecl "Sem.Call.callBase" (retargetCalls "Sem.Callees.base" "Sem.Callees.addTo") prog),
    ("phase", "`callBase` (runtime) calling the spec declaration `posBase` instead of `base` (placed after `posBase`)",
      others ++ (callBase.map (mapBody (retargetCalls "Sem.Callees.base" "Sem.Callees.posBase")))),
    ("cycle", "`base` calling `callBase`, which calls `base` (a cycle: the callee is not an earlier declaration)",
      mapDecl "Sem.Callees.base" (fun _ => .call "Sem.Call.callBase" [.var "x"]) prog),
    ("duplicate", "`base` declared twice", prog ++ (prog.filter fun d => d.key == "Sem.Callees.base")),
    ("arity", "`useInput` calling the input `seed` with an argument (its signature has none)",
      mapDecl "Sem.Call.useInput" (addArgTo "Sem.Inputs.seed" (.var "x")) prog),
    ("argtype", "`callBase` passing a Bool to `base` (whose parameter is Nat)",
      mapDecl "Sem.Call.callBase" (fun _ => .binop "*" (.call "Sem.Callees.base" [.lit (.bool true) .bool]) (.lit (.nat 2) .nat) .nat) prog) ]

/-- Core の宣言群の項。本体は引用した Core をその場に書く(`named = false`。負の検体)か、`ccore_<f>` の名前で参照する(`named = true`。実際の宣言群:
`CallModelCheck.lean` の接続の定理が同じ `ccore_<f>` を指す)。 -/
def coreProgTerm (prog : List NaruSem.Call.Decl) (named : Bool := false) : String :=
  "[ " ++ ",\n    ".intercalate (prog.map fun d =>
    match d with
    | .fn _ _ _ b | .spec _ _ b => NaruSem.Call.Quote.declWith d (if named then s!"ccore_{shortName d.key}" else NaruSem.Quote.expr b)
    | .input .. => NaruSem.Call.Quote.declWith d "") ++ " ]"

/-- 実際の宣言群の各 fn / spec 宣言の本体の Core の引用 `ccore_<f>`(`CallScope.lean`)。 -/
def coreBodyDefs (prog : List NaruSem.Call.Decl) : String :=
  "".intercalate (prog.filterMap fun d =>
    match d with
    | .fn k _ _ b | .spec k _ b => some s!"-- {k}\ndef ccore_{shortName k} : Naru.Core.Expr :=\n  {NaruSem.Quote.expr b}\n"
    | .input .. => none)

def valTerm' : NaruSem.Val → String
  | .nat n => s!"(NaruSem.Val.nat {n})"
  | .bool b => s!"(NaruSem.Val.bool {b})"

def valsTerm (vs : List NaruSem.Val) : String := "[" ++ ", ".intercalate (vs.map valTerm') ++ "]"

/-- 検査に使う input の解釈: `seed() = 41`、`bias(n) = n * 2`、`otherBias(n) = n + 3`、`flag(b) = !b`(署名を守る解釈の一例)。 -/
def callInterp : NaruSem.Call.FEnv :=
  (((NaruSem.Call.FEnv.empty.ext "Sem.Inputs.seed" fun _ => some (.nat 41)).ext "Sem.Inputs.bias"
    fun vs => match vs with | [.nat n] => some (.nat (n * 2)) | _ => none).ext "Sem.Inputs.flag"
    fun vs => match vs with | [.bool b] => some (.bool (!b)) | _ => none).ext "Sem.Inputs.otherBias"
    fun vs => match vs with | [.nat n] => some (.nat (n + 3)) | _ => none

def callInterpTerm : String :=
  "(((NaruSem.Call.FEnv.empty.ext \"Sem.Inputs.seed\" fun _ => some (NaruSem.Val.nat 41)).ext \"Sem.Inputs.bias\"\n" ++
  "    fun vs => match vs with | [NaruSem.Val.nat n] => some (NaruSem.Val.nat (n * 2)) | _ => none).ext \"Sem.Inputs.flag\"\n" ++
  "    fun vs => match vs with | [NaruSem.Val.bool b] => some (NaruSem.Val.bool (!b)) | _ => none).ext \"Sem.Inputs.otherBias\"\n" ++
  "    fun vs => match vs with | [NaruSem.Val.nat n] => some (NaruSem.Val.nat (n + 3)) | _ => none"

/-- 署名に合わない解釈: `seed()` が Bool を返す。 -/
def callInterpWrong : NaruSem.Call.FEnv := NaruSem.Call.FEnv.empty.ext "Sem.Inputs.seed" fun _ => some (.bool true)

def callInterpWrongTerm : String := "(NaruSem.Call.FEnv.empty.ext \"Sem.Inputs.seed\" fun _ => some (NaruSem.Val.bool true))"

/-- 宣言群の意味で fn を呼ぶ(ドライバの実行)。 -/
def callValue (I : NaruSem.Call.FEnv) (prog : List NaruSem.Call.Decl) (k : String) (args : List NaruSem.Val) : Option NaruSem.Val :=
  ((NaruSem.Call.interp I prog).Φ k).bind fun f => f args

/-- 期待する値(fn, 実引数, 値): `twoStep(1) = callBase(useInput(1)) = base(1 + 41) * 2 = 86`、`useInputArg(3) = bias(3) + bias(seed()) = 6 + 82`、
`callNamed(1, 2) = addTo(y = 1, x = 2) = 2 + 1 * 2`、`callMixed(1, 2) = addTo(1, y = 2) = 1 + 4`、`ufcsNamed(2, 1) = addTo(2, y = 1) = 4`、
`boolCall(true) = flag(true) && !flag(false) = false`、`boolCall(false) = flag(false) && !flag(true) = true`、`zeroCall() = 0`、`callInLet(3) = 5`、
`callInMatch(1) = zero() = 0`(腕 `1`)、`callInMatch(5) = base(5) = 6`(ガード `callBase(5) > 4` の腕)、`callInMatch(0) = callBase(0) = 2`(ガード不成立の後の `_` の腕)。 -/
def expectedCallValues : List (String × List NaruSem.Val × NaruSem.Val) :=
  [ ("Sem.Call.twoStep", [.nat 1], .nat 86), ("Sem.Call.useInputArg", [.nat 3], .nat 88), ("Sem.Call.callNamed", [.nat 1, .nat 2], .nat 4),
    ("Sem.Call.callMixed", [.nat 1, .nat 2], .nat 5), ("Sem.Call.ufcsNamed", [.nat 2, .nat 1], .nat 4), ("Sem.Call.boolCall", [.bool true], .bool false),
    ("Sem.Call.boolCall", [.bool false], .bool true), ("Sem.Call.zeroCall", [], .nat 0), ("Sem.Call.callInLet", [.nat 3], .nat 5),
    ("Sem.Call.callInMatch", [.nat 1], .nat 0), ("Sem.Call.callInMatch", [.nat 5], .nat 6), ("Sem.Call.callInMatch", [.nat 0], .nat 2),
    ("Sem.Call.inputPair", [.nat 3], .nat 94), ("Sem.Call.sharedInputs", [.nat 3], .nat 182) ]

/-- 検査プログラム `CallScope.lean`(モジュール `CallScope`): 依存順の Core の宣言群 `cprog_call`、適格性(`decide`)、各宣言の署名(`decide`)、負の検体(`wtProg = none`、`decide`)、
input の解釈の下の値(`decide`)と署名に合わない解釈の行き詰まり、引用の一致と網羅の照合(`run_cmd`)。 -/
def callScopeProgram (prog : List NaruSem.Call.Decl) (Δ : NaruSem.Call.SigEnv) (wrongs : List (String × String × String))
    (values : List (Nat × String × List NaruSem.Val × NaruSem.Val)) : String :=
  let sigs := prog.map fun d =>
    let n := shortName d.key
    let sig := match Δ d.key with
      | some s => NaruSem.Call.Quote.sig s
      | none => "none"
    s!"theorem csig_{n} : (NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call).bind (fun Δ => Δ {d.key.quote}) = some {sig} := by decide\n"
  let negs := wrongs.map fun (name, note, term) =>
    s!"-- {note}\ntheorem cneg_{name} : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty\n  {term} = none := by decide\n"
  let vals := values.map fun (i, k, args, v) =>
    s!"theorem cval_{i} : ((NaruSem.Call.interp I_call cprog_call).Φ {k.quote}).bind (fun f => f {valsTerm args}) = some {valTerm' v} := by decide\n"
  s!"-- naru_test semantics (C54): generated from NaruTest/Semantics.lean. The Core declaration group of {callSource} as produced by the compiler, in dependency order.\n" ++
  "import NaruSem\n\n" ++
  "-- the Core of each fn / spec declaration (quoted; `checkProg` below re-compiles the source and compares)\n" ++
  coreBodyDefs prog ++
  s!"\ndef cprog_call : NaruSem.Call.Prog :=\n  {coreProgTerm prog (named := true)}\n\n" ++
  "-- the declaration group is well-formed: dependency order, no duplicate keys, every body typed against the signatures of the earlier declarations (C54)\n" ++
  "theorem cwt_call : (NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call).isSome = true := by decide\n" ++
  "-- the signature of each declaration (identity, phase, parameter types, return type)\n" ++
  "".intercalate sigs ++
  "\n-- negative specimens made from the actual Core: not well-formed (not in dependency order / wrong callee / phase / cycle / duplicate / arity / argument type)\n" ++
  "".intercalate negs ++
  s!"\n-- an input interpretation respecting the signatures (seed() = 41, bias(n) = n * 2, otherBias(n) = n + 3, flag(b) = !b); the meaning of the group under it\ndef I_call : NaruSem.Call.FEnv :=\n  {callInterpTerm}\n" ++
  "".intercalate vals ++
  s!"-- an interpretation not respecting the signature of `seed` (Bool instead of Nat): the call is stuck (`none`), not a default value\ndef I_call_wrong : NaruSem.Call.FEnv := {callInterpWrongTerm}\n" ++
  "theorem cstuck_useInput : ((NaruSem.Call.interp I_call_wrong cprog_call).Φ \"Sem.Call.useInput\").bind (fun f => f [NaruSem.Val.nat 1]) = none := by decide\n" ++
  "\n-- the general theorems apply to the actual group: under any input interpretation respecting its signatures, the meaning of the group respects\n" ++
  "-- the signatures (every fn is total on well-typed arguments) and every spec declaration has a meaning (C54)\n" ++
  "theorem cΔ_call : ∃ Δ, NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call = some Δ := Option.isSome_iff_exists.mp cwt_call\n" ++
  "theorem cresp_call : ∀ I : NaruSem.Call.FEnv, I.RespectsInputs cprog_call →\n" ++
  "    (NaruSem.Call.interp I cprog_call).Φ.Respects (Classical.choose cΔ_call) :=\n" ++
  "  fun I hI => NaruSem.Call.interp_respects (Classical.choose_spec cΔ_call) hI\n" ++
  "theorem cdef_call : ∀ I : NaruSem.Call.FEnv, I.RespectsInputs cprog_call →\n" ++
  "    (NaruSem.Call.interp I cprog_call).Ψ.Defined (Classical.choose cΔ_call) :=\n" ++
  "  fun I hI => NaruSem.Call.interp_defined (Classical.choose_spec cΔ_call) hI\n" ++
  "#audit_axioms cwt_call cΔ_call cresp_call cdef_call cstuck_useInput\n" ++
  s!"\n-- the quoted declarations are the Core the compiler produces for the same source, and cover all its fn / input / spec declarations (C54 / C57)\nrun_cmd NaruSem.Call.Quote.checkProg {callSource.quote} cprog_call [{callInputSource.quote}, {callCalleeSource.quote}]\n"

/-- Surface AST の式の呼出し先・UFCS のメソッド名 `from` を `to` に(負の検体: 未解決の名前)。 -/
partial def renameCallee (src dst : String) : NaruSem.Surf.Call.Expr → NaruSem.Surf.Call.Expr
  | .call sp (.var vsp [x]) args => .call sp (.var vsp [if x == src then dst else x]) (args.map (renameCalleeArg src dst))
  | .call sp f args => .call sp (renameCallee src dst f) (args.map (renameCalleeArg src dst))
  | .method sp r m args => .method sp (renameCallee src dst r) (if m == src then dst else m) (args.map (renameCalleeArg src dst))
  | .binop sp op l r => .binop sp op (renameCallee src dst l) (renameCallee src dst r)
  | .unop sp op a => .unop sp op (renameCallee src dst a)
  | .ite sp c t e => .ite sp (renameCallee src dst c) (renameCallee src dst t) (renameCallee src dst e)
  | .matchE sp s arms => .matchE sp (renameCallee src dst s) (arms.map fun | .mk p g b => .mk p (g.map (renameCallee src dst)) (renameCallee src dst b))
  | .block sp stmts tail => .block sp (stmts.map fun | .letS lsp x ty v => .letS lsp x ty (renameCallee src dst v)) (tail.map (renameCallee src dst))
  | .quant sp q bs b => .quant sp q bs (renameCallee src dst b)
  | e => e
where
  renameCalleeArg (src dst : String) : NaruSem.Surf.Call.Arg → NaruSem.Surf.Call.Arg
    | .pos e => .pos (renameCallee src dst e)
    | .named n e => .named n (renameCallee src dst e)

/-- すべての呼出し(と UFCS)の実引数の列を変える(負の検体: 名前付き引数の名前・順序・二重指定)。 -/
partial def mapArgs (f : List NaruSem.Surf.Call.Arg → List NaruSem.Surf.Call.Arg) : NaruSem.Surf.Call.Expr → NaruSem.Surf.Call.Expr
  | .call sp g args => .call sp (mapArgs f g) (f (args.map (mapArgsArg f)))
  | .method sp r m args => .method sp (mapArgs f r) m (f (args.map (mapArgsArg f)))
  | .binop sp op l r => .binop sp op (mapArgs f l) (mapArgs f r)
  | .unop sp op a => .unop sp op (mapArgs f a)
  | .ite sp c t e => .ite sp (mapArgs f c) (mapArgs f t) (mapArgs f e)
  | .matchE sp s arms => .matchE sp (mapArgs f s) (arms.map fun | .mk p g b => .mk p (g.map (mapArgs f)) (mapArgs f b))
  | .block sp stmts tail => .block sp (stmts.map fun | .letS lsp x ty v => .letS lsp x ty (mapArgs f v)) (tail.map (mapArgs f))
  | .quant sp q bs b => .quant sp q bs (mapArgs f b)
  | e => e
where
  mapArgsArg (f : List NaruSem.Surf.Call.Arg → List NaruSem.Surf.Call.Arg) : NaruSem.Surf.Call.Arg → NaruSem.Surf.Call.Arg
    | .pos e => .pos (mapArgs f e)
    | .named n e => .named n (mapArgs f e)

def renameNamed (src dst : String) : List NaruSem.Surf.Call.Arg → List NaruSem.Surf.Call.Arg :=
  List.map fun | .named n e => .named (if n == src then dst else n) e | a => a

/-- 鍵 `k` の Surface 宣言の本体だけを変える。 -/
def mapSDecl (k : String) (f : NaruSem.Surf.Call.Expr → NaruSem.Surf.Call.Expr) (prog : List NaruSem.Surf.Call.Decl) : List NaruSem.Surf.Call.Decl :=
  prog.map fun d => if d.key == k then { d with body := d.body.map f } else d

/-- Surface の宣言群の負の検体: (名前, 説明, 宣言群)。どれも `wtProg` が `false` でなければドライバが FAIL にする。 -/
def surfWrongProgs (prog : List NaruSem.Surf.Call.Decl) : List (String × String × List NaruSem.Surf.Call.Decl) :=
  [ ("reversed", "the declarations in reverse order (callees after their callers)", prog.reverse),
    ("unknown", "`callNamed` calling `addTwo` (no such declaration: unresolved)", mapSDecl "Sem.Call.callNamed" (renameCallee "addTo" "addTwo") prog),
    ("named", "`callNamed` passing the named argument `z = a` (`addTo` has no parameter `z`)", mapSDecl "Sem.Call.callNamed" (mapArgs (renameNamed "y" "z")) prog),
    ("order", "`callMixed` passing the positional argument after the named one", mapSDecl "Sem.Call.callMixed" (mapArgs List.reverse) prog),
    ("twice", "`callMixed` passing `y` both positionally and by name", mapSDecl "Sem.Call.callMixed" (mapArgs fun args => args ++ [.named "y" (.lit {} (.nat 0))]) prog),
    ("ufcs", "`ufcs` calling `a.addTwo(b)` (no declaration `addTwo` and not a Nat method)", mapSDecl "Sem.Call.ufcs" (renameCallee "addTo" "addTwo") prog) ]

def surfProgTerm (prog : List NaruSem.Surf.Call.Decl) : String :=
  "[ " ++ ",\n    ".intercalate (prog.map fun d =>
    NaruSem.Surf.Call.Quote.declWith d (match d.body with | some b => s!"(some {NaruSem.Surf.Call.Quote.expr b})" | none => "none")) ++ " ]"

/-- 検査プログラム `SurfaceCallScope.lean`(モジュール `SurfaceCallScope`): 依存順の Surface AST の宣言群 `sprog_call`、適格性(`decide`)、負の検体(`wtProg = false`、`decide`)、
引用の一致と網羅の照合(`run_cmd`)。 -/
def surfaceCallScopeProgram (prog : List NaruSem.Surf.Call.Decl) (wrongs : List (String × String × String)) : String :=
  let negs := wrongs.map fun (name, note, term) =>
    s!"-- {note}\ntheorem sneg_{name} : NaruSem.Surf.Call.wtProg\n  {term} = false := by decide\n"
  s!"-- naru_test semantics (C54): generated from NaruTest/Semantics.lean. The Surface AST declaration group of {callSource} as produced by the parser, in dependency order.\n" ++
  "import CallScope\n\n" ++
  s!"def sprog_call : NaruSem.Surf.Call.Prog :=\n  {surfProgTerm prog}\n\n" ++
  "-- the parsed declaration group is well-formed: names resolve to earlier declarations (or inputs), named arguments match the parameters, UFCS receivers\n" ++
  "-- become the first argument, every body is typed against the earlier signatures (C54)\n" ++
  "theorem swt_call : NaruSem.Surf.Call.wtProg sprog_call = true := by decide\n" ++
  "\n-- the general theorems apply to the actual parsed group: under any input interpretation respecting its signatures, the meaning of the group\n" ++
  "-- respects the signatures of the whole table (every fn is total on well-typed arguments) and every spec declaration has a meaning (C54)\n" ++
  "theorem sresp_call : ∀ I : NaruSem.Call.FEnv, NaruSem.Surf.Call.RespectsInputs I sprog_call →\n" ++
  "    (NaruSem.Surf.Call.interp I sprog_call).Φ.Respects (NaruSem.Surf.Call.tableOf sprog_call sprog_call).Δ :=\n" ++
  "  fun I hI => NaruSem.Surf.Call.interp_respects swt_call hI\n" ++
  "theorem sdef_call : ∀ I : NaruSem.Call.FEnv, NaruSem.Surf.Call.RespectsInputs I sprog_call →\n" ++
  "    (NaruSem.Surf.Call.interp I sprog_call).Ψ.Defined (NaruSem.Surf.Call.tableOf sprog_call sprog_call).Δ :=\n" ++
  "  fun I hI => NaruSem.Surf.Call.interp_defined swt_call hI\n" ++
  "#audit_axioms swt_call sresp_call sdef_call\n" ++
  "\n-- negative specimens made from the actual AST: not well-formed\n" ++
  "".intercalate negs ++
  s!"\n-- the quoted declarations embed to the declarations the parser produces for the same source, and cover all its fn / input / spec declarations (C54 / C57)\nrun_cmd NaruSem.Surf.Call.Quote.checkProg {callSource.quote} sprog_call [{callInputSource.quote}, {callCalleeSource.quote}]\n"

/-- 現在の runtime AST と Core の対応。宣言表は各宣言の prefix、
文脈はその宣言の仮引数から取り、包装・本体・型・変換の一致と、
同じ環境・型内で一致する別々の環境での評価保存とCoreの読みへの保存を kernel 検査する。
Surface/Core の宣言群の意味の合成はこの本体の証拠とは区別する。 -/
def callRuntimeLowerProgram (sprog : NaruSem.Surf.Call.Prog) : String := Id.run do
  let mut text := "import SurfaceCallScope\nimport NaruSem.SurfaceCallLowerSound\n\n"
  for (i, d) in sprog.zipIdx |>.map (fun (d, i) => (i, d)) do
    if d.kind != .fn then continue
    let n := shortName d.key
    let decl := NaruSem.Surf.Call.Quote.declWith d (match d.body with
      | some b => s!"(some {NaruSem.Surf.Call.Quote.expr b})"
      | none => "none")
    match d.sig?, d.body with
    | some (.fn ps t), some b =>
      let ctx := NaruSem.Surf.Quote.ctxTerm ps true
      let ast := NaruSem.Surf.Call.Quote.expr b
      text := text ++ s!"def sdecl_{n} : NaruSem.Surf.Call.Decl := {decl}\n" ++
        s!"theorem spack_{n} : sprog_call[{i}]? = some sdecl_{n} := rfl\n" ++
        s!"def stable_{n} := NaruSem.Surf.Call.tableOf sprog_call (sprog_call.take {i})\n" ++
        s!"def sctx_{n} := {ctx}\ndef sast_{n} : NaruSem.Surf.Call.Expr := {ast}\n" ++
        s!"theorem sparams_{n} : NaruSem.Surf.paramsCtx sdecl_{n}.params = some {NaruSem.Call.Quote.params ps} := rfl\n" ++
        s!"theorem sbody_{n} : sdecl_{n}.body = some sast_{n} := rfl\n" ++
        s!"theorem stype_{n} : NaruSem.Surf.Call.wtR stable_{n} sctx_{n} sast_{n} = some {tyTerm t} := by decide\n" ++
        s!"theorem slow_{n} : NaruSem.Surf.Call.lower stable_{n} sctx_{n} sast_{n} = some ccore_{n} := rfl\n" ++
        s!"theorem sctyped_{n} : NaruSem.Call.wtR stable_{n}.Δ sctx_{n}.vals ccore_{n} = some {tyTerm t} := NaruSem.Surf.Call.lower_wt stype_{n} slow_{n}\n" ++
        s!"theorem seval_{n} : ∀ (Φ : NaruSem.Call.FEnv) (ρ : NaruSem.SEnv), sctx_{n} = ρ.ctx → Φ.Respects stable_{n}.Δ → NaruSem.Surf.Call.eval stable_{n} Φ ρ sast_{n} = NaruSem.Call.eval Φ ρ.vals ccore_{n} := fun Φ ρ hΓ hΦ => NaruSem.Surf.Call.lower_eval stype_{n} slow_{n} hΓ hΦ\n" ++
        s!"theorem seval_agree_{n} : ∀ (Φ Φ' : NaruSem.Call.FEnv) (ρ : NaruSem.SEnv), sctx_{n} = ρ.ctx → Φ'.Respects stable_{n}.Δ → NaruSem.Call.FEnv.Agree Φ Φ' stable_{n}.Δ → NaruSem.Surf.Call.eval stable_{n} Φ ρ sast_{n} = NaruSem.Call.eval Φ' ρ.vals ccore_{n} := fun Φ Φ' ρ hΓ hΦ' hA => NaruSem.Surf.Call.lower_eval_agree stype_{n} slow_{n} hΓ hΦ' hA\n" ++
        s!"theorem sread_{n} : ∀ (Δ' : NaruSem.Call.SigEnv) (Φ Φ' : NaruSem.Call.FEnv) (ρ : NaruSem.SEnv), sctx_{n} = ρ.ctx → NaruSem.Call.SigEnv.SubV stable_{n}.Δ Δ' → Φ'.Respects Δ' → NaruSem.Call.FEnv.Agree Φ Φ' stable_{n}.Δ → NaruSem.Surf.Call.eval stable_{n} Φ ρ sast_{n} = some (NaruSem.Call.denoteV Δ' Φ' ρ.vals {tyTerm t} ccore_{n}) := fun Δ' Φ Φ' ρ hΓ hΔ hΦ' hA => NaruSem.Surf.Call.lower_denote_sound stype_{n} slow_{n} hΓ hΔ hΦ' hA\n" ++
        s!"#audit_axioms spack_{n} sparams_{n} sbody_{n} stype_{n} slow_{n} sctyped_{n} seval_{n} seval_agree_{n} sread_{n}\n\n"
    | _, _ => text := text ++ s!"#audit_axioms missing_runtime_body_{n}\n"
  return text

/-- 型が合う別callee・名前付き引数/UFCS/同型inputの交換・ガード否定。
変換の一致の負検体であり、一般保存定理や非同値の証明の代用ではない。 -/
def swapCallArgs : Naru.Core.Expr → Naru.Core.Expr
  | .call k [a, b] => .call k [b, a]
  | e => e

def callLowerWrongs : List CoreMistranslation :=
  [ { key := "Sem.Call.twoStep", wrong := "WrongCore.twoStep",
      transform := retargetCalls "Sem.Call.callBase" "Sem.Callees.base", note := "same-signature different callee" },
    { key := "Sem.Call.callNamed", wrong := "WrongCore.callNamed", transform := swapCallArgs, note := "named arguments exchanged" },
    { key := "Sem.Call.ufcs", wrong := "WrongCore.ufcs", transform := swapCallArgs, note := "UFCS receiver exchanged" },
    { key := "Sem.Call.inputPair", wrong := "WrongCore.inputPair",
      transform := retargetCalls "Sem.Inputs.otherBias" "Sem.Inputs.bias", note := "same-signature input exchanged" },
    { key := "Sem.Call.callInMatch", wrong := "WrongCore.callInMatch", transform := negateGuards, note := "match guard negated" } ]

def checkCallRuntimeLower (sprog : NaruSem.Surf.Call.Prog) (cprog : NaruSem.Call.Prog) (lp : String) : M Unit := do
  heading "C55: runtime Surface AST to actual Core (evaluation under agreeing typed environments and Core reading; declaration-group composition remains unfinished)"
  let mut count := 0
  let mut wrongs : List (Mistranslation × String) := []
  for (d, i) in sprog.zipIdx do
    if d.kind != .fn then continue
    match d.sig?, d.body, cprog[i]? with
    | some (.fn ps t), some ast, some (.fn k cps ct body) =>
      let T := NaruSem.Surf.Call.tableOf sprog (sprog.take i)
      let Γ := NaruSem.SCtx.ofList (ps.map fun (x, ty) => (x, .val ty))
      if d.key == k && ps == cps && t == ct && NaruSem.Surf.Call.lower T Γ ast == some body then
        ok s!"C55: `{k}`: current runtime AST lowers to its actual Core, with the actual prefix table and parameters"
        count := count + 1
      else fail s!"C55: `{d.key}`: runtime AST / Core packaging or lowering mismatch"
      for m in callLowerWrongs.filter (fun m => m.key == k) do
        let b := m.transform body
        if b == body || NaruSem.Call.wtR T.Δ Γ.vals b != some t then
          fail s!"C55: `{k}`: negative lowering specimen must differ and have the same Core type"
        else
          let n := shortName k
          let desc : Mistranslation := { key := k, wrong := m.wrong, good := "", bad := "", transform := id, note := m.note }
          let text := s!"def {m.wrong} : Naru.Core.Expr := {NaruSem.Quote.expr b}\n" ++
            s!"theorem wrong_wt_{n} : NaruSem.Call.wtR stable_{n}.Δ sctx_{n}.vals {m.wrong} = some {tyTerm t} := by decide\n"
          wrongs := wrongs ++ [(desc, text)]
          ok s!"C55: `{k}`: {m.note} preserves the Core type but differs from the correct lowering"
    | _, _, _ => fail s!"C55: `{d.key}`: missing or mismatched runtime AST / Core declaration"
  let expected := (c54Decls.filter fun (_, k) => k == .fn).map (fun (k, _) => shortName k)
  if count != expected.length then fail s!"C55: runtime lowering covers {count} of {expected.length} required declarations"
  let file := outDir / "SurfaceCallLowerCheck.lean"
  IO.FS.writeFile file (callRuntimeLowerProgram sprog)
  let r ← step "C55: kernel-check current runtime AST / Core lowering, evaluation and declaration packaging" "lean"
    #[s!"--root={outDir}", "-o", (outDir / "SurfaceCallLowerCheck.olean").toString, file.toString] (env := #[("LEAN_PATH", some lp)])
  let required := expected.flatMap fun n => [s!"spack_{n}", s!"sparams_{n}", s!"sbody_{n}", s!"stype_{n}", s!"slow_{n}", s!"sctyped_{n}", s!"seval_{n}", s!"seval_agree_{n}", s!"sread_{n}"]
  let missing := required.filter fun n => !(auditedNames r.stdout).contains n
  if r.exitCode == 0 && missing.isEmpty then
    ok s!"C55: {required.length} runtime lowering / packaging certificates for all {expected.length} actual fn declarations audited"
  else fail s!"C55: runtime lowering certificates missing: {missing}\n{tail r.stdout 1500}\n{tail r.stderr 1500}"
  if wrongs.length != callLowerWrongs.length then fail "C55: a required negative runtime lowering specimen is missing"
  let wp := wrongProgramWith "call Core" ["SurfaceCallLowerCheck"] wrongs fun thm lean key =>
    let n := shortName key
    let target := if lean.isEmpty then s!"ccore_{n}" else lean
    some s!"theorem {thm} : NaruSem.Surf.Call.lower stable_{n} sctx_{n} sast_{n} = some {target} := rfl"
  checkWrong "runtime AST / Core lowering" (outDir / "SurfaceCallLowerWrong.lean") wp wrongs lp

/-- 現在の spec AST の包装・適格性と独立 lowering の実Core一致。
一般の spec 保存定理の代用にはしない。 -/
def callSpecLowerProgram (sprog : NaruSem.Surf.Call.Prog) : String := Id.run do
  let mut text := "import SurfaceCallScope\nimport NaruSem.SurfaceCallLowerSpecSound\n\n"
  for (d, i) in sprog.zipIdx do
    if d.kind.phase != .spec then continue
    let n := shortName d.key
    let decl := NaruSem.Surf.Call.Quote.declWith d (match d.body with
      | some b => s!"(some {NaruSem.Surf.Call.Quote.expr b})"
      | none => "none")
    match d.sig?, d.body with
    | some (.spec ps), some b =>
      let ctx := NaruSem.Surf.Quote.ctxTerm ps true
      let T := NaruSem.Surf.Call.tableOf sprog (sprog.take i)
      let Γ := NaruSem.SCtx.ofList (ps.map fun (x, ty) => (x, .val ty))
      let some τ := NaruSem.Surf.Call.wtS T Γ b
        | text := text ++ s!"#audit_axioms missing_spec_lower_type_{n}\n"
          continue
      text := text ++ s!"def ssdecl_{n} : NaruSem.Surf.Call.Decl := {decl}\n" ++
        s!"theorem sspack_{n} : sprog_call[{i}]? = some ssdecl_{n} := rfl\n" ++
        s!"def sstable_{n} := NaruSem.Surf.Call.tableOf sprog_call (sprog_call.take {i})\n" ++
        s!"def ssctx_{n} := {ctx}\ndef ssast_{n} : NaruSem.Surf.Call.Expr := {NaruSem.Surf.Call.Quote.expr b}\n" ++
        s!"theorem ssparams_{n} : NaruSem.Surf.paramsCtx ssdecl_{n}.params = some {NaruSem.Call.Quote.params ps} := rfl\n" ++
        s!"theorem ssbody_{n} : ssdecl_{n}.body = some ssast_{n} := rfl\n" ++
        s!"def ssty_{n} := NaruSem.Surf.Call.wtS sstable_{n} ssctx_{n} ssast_{n}\n" ++
        s!"theorem sstype_{n} : ssty_{n}.isSome = true := by decide\n" ++
        s!"theorem ssform_{n} : (ssty_{n}.map NaruSem.STy.isForm) = some true := by decide\n" ++
        s!"theorem sslower_{n} : NaruSem.Surf.Call.lowerS sstable_{n} ssctx_{n} ssast_{n} = some ccore_{n} := rfl\n" ++
        s!"theorem ssctype_{n} : NaruSem.Call.wtS sstable_{n}.Δ ssctx_{n} ccore_{n} = ssty_{n} := by decide\n" ++
        s!"theorem sswtype_{n} : NaruSem.Surf.Call.wtS sstable_{n} ssctx_{n} ssast_{n} = some {styTerm τ} := by decide\n" ++
        s!"theorem ssctyped_{n} : NaruSem.Call.wtS sstable_{n}.Δ ssctx_{n} ccore_{n} = some {styTerm τ} := NaruSem.Surf.Call.lowerS_wt sswtype_{n} sslower_{n}\n" ++
        s!"#audit_axioms sspack_{n} ssparams_{n} ssbody_{n} sstype_{n} ssform_{n} sslower_{n} ssctype_{n} sswtype_{n} ssctyped_{n}\n\n"
    | _, _ => text := text ++ s!"#audit_axioms missing_spec_lower_body_{n}\n"
  return text

partial def swapArgsAt (target : String) : Naru.Core.Expr → Naru.Core.Expr
  | .call k args => .call k (let xs := args.map (swapArgsAt target); if k == target then xs.reverse else xs)
  | .let_ x ty v b => .let_ x ty (swapArgsAt target v) (swapArgsAt target b)
  | .ite c t e => .ite (swapArgsAt target c) (swapArgsAt target t) (swapArgsAt target e)
  | .binop op l r ty => .binop op (swapArgsAt target l) (swapArgsAt target r) ty
  | .unop op a => .unop op (swapArgsAt target a)
  | .method tn n r as rt => .method tn n (swapArgsAt target r) (as.map (swapArgsAt target)) rt
  | .match_ s st arms => .match_ (swapArgsAt target s) st (arms.map fun | .mk p g b => .mk p (g.map (swapArgsAt target)) (swapArgsAt target b))
  | .quant q bs b => .quant q bs (swapArgsAt target b)
  | e => e


/-- 命題letの束縛を保持して末尾の含意の結論を否定する。 -/
partial def negateLetConclusion : Naru.Core.Expr → Naru.Core.Expr
  | .let_ x t v b => .let_ x t v (negateLetConclusion b)
  | .binop "implies" l r t => .binop "implies" l (.unop "!" r) t
  | e => e

/-- 型を保つ spec 呼出し・名前付き引数・UFCS・input・命題letの誤対応。 -/
def callSpecLowerWrongs : List CoreMistranslation :=
  [ { key := "Sem.Call.specTwoStep", wrong := "WrongCore.specTwoStep",
      transform := retargetCalls "Sem.Call.specInput" "Sem.Call.specCallSpec", note := "same-signature spec callee exchanged" },
    { key := "Sem.Call.specNamed", wrong := "WrongCore.specNamed",
      transform := swapArgsAt "Sem.Callees.addTo", note := "named arguments exchanged" },
    { key := "Sem.Call.specUfcs", wrong := "WrongCore.specUfcs",
      transform := swapArgsAt "Sem.Callees.addTo", note := "UFCS receiver exchanged" },
    { key := "Sem.Call.specSharedInputs", wrong := "WrongCore.specSharedInputs",
      transform := retargetCalls "Sem.Inputs.otherBias" "Sem.Inputs.bias", note := "same-signature input exchanged" },
    { key := "Sem.Call.specLetCall", wrong := "WrongCore.specLetCall",
      transform := negateLetConclusion, note := "Prop let conclusion negated" } ]

def checkCallSpecLower (sprog : NaruSem.Surf.Call.Prog) (cprog : NaruSem.Call.Prog) (lp : String) : M Unit := do
  heading "C55: spec Surface AST to actual Core (general type preservation; equivalence remains unfinished)"
  let mut count := 0
  let mut wrongs : List (Mistranslation × String) := []
  for (d, i) in sprog.zipIdx do
    if d.kind.phase != .spec then continue
    match d.sig?, d.body, cprog[i]? with
    | some (.spec ps), some ast, some (.spec k cps body) =>
      let T := NaruSem.Surf.Call.tableOf sprog (sprog.take i)
      let Γ := NaruSem.SCtx.ofList (ps.map fun (x, ty) => (x, .val ty))
      let ty := NaruSem.Surf.Call.wtS T Γ ast
      if d.key == k && ps == cps && ty.isSome && (ty.map NaruSem.STy.isForm) == some true &&
          NaruSem.Surf.Call.lowerS T Γ ast == some body && NaruSem.Call.wtS T.Δ Γ body == ty then
        ok s!"C55: `{k}`: current spec AST lowers to its actual Core with matching packaging, logical type and prefix table"
        count := count + 1
      else fail s!"C55: `{d.key}`: spec AST / Core packaging, type or lowering mismatch"
      for m in callSpecLowerWrongs.filter (fun m => m.key == k) do
        let b := m.transform body
        if b == body || NaruSem.Call.wtS T.Δ Γ b != ty then
          fail s!"C55: `{k}`: negative spec lowering specimen must differ and have the same Core type"
        else
          let n := shortName k
          let desc : Mistranslation := { key := k, wrong := m.wrong, good := "", bad := "", transform := id, note := m.note }
          let text := s!"def {m.wrong} : Naru.Core.Expr := {NaruSem.Quote.expr b}\n" ++
            s!"theorem wrong_wt_{n} : NaruSem.Call.wtS sstable_{n}.Δ ssctx_{n} {m.wrong} = ssty_{n} := by decide\n"
          wrongs := wrongs ++ [(desc, text)]
          ok s!"C55: `{k}`: {m.note} preserves the Core type but differs from the correct lowering"
    | _, _, _ => fail s!"C55: `{d.key}`: missing or mismatched spec AST / Core declaration"
  let expected := (c54Decls.filter fun (_, k) => k.phase == .spec).map (fun (k, _) => shortName k)
  if count != expected.length then fail s!"C55: spec lowering covers {count} of {expected.length} required declarations"
  let file := outDir / "SurfaceCallLowerSpecCheck.lean"
  IO.FS.writeFile file (callSpecLowerProgram sprog)
  let r ← step "C55: kernel-check current spec AST / Core lowering and packaging" "lean"
    #[s!"--root={outDir}", "-o", (outDir / "SurfaceCallLowerSpecCheck.olean").toString, file.toString] (env := #[("LEAN_PATH", some lp)])
  let required := expected.flatMap fun n => [s!"sspack_{n}", s!"ssparams_{n}", s!"ssbody_{n}", s!"sstype_{n}", s!"ssform_{n}", s!"sslower_{n}", s!"ssctype_{n}", s!"sswtype_{n}", s!"ssctyped_{n}"]
  let missing := required.filter fun n => !(auditedNames r.stdout).contains n
  if r.exitCode == 0 && missing.isEmpty then
    ok s!"C55: {required.length} spec lowering / packaging certificates for all {expected.length} actual spec declarations audited"
  else fail s!"C55: spec lowering certificates missing: {missing}\n{tail r.stdout 1500}\n{tail r.stderr 1500}"
  if wrongs.length != callSpecLowerWrongs.length then fail "C55: a required negative spec lowering specimen is missing"
  let wp := wrongProgramWith "call spec Core" ["SurfaceCallLowerSpecCheck"] wrongs fun thm lean key =>
    let n := shortName key
    let target := if lean.isEmpty then s!"ccore_{n}" else lean
    some s!"theorem {thm} : NaruSem.Surf.Call.lowerS sstable_{n} ssctx_{n} ssast_{n} = some {target} := rfl"
  checkWrong "spec AST / Core lowering" (outDir / "SurfaceCallLowerSpecWrong.lean") wp wrongs lp

/-! ### 実生成 Model への接続と宣言群の意味の合成(C55 / C56 / C57 / C58、runtime)

検体 `tests/units/accept/sem_calls/src/Sem/Call.naru` を実際の CLI で生成した Model(`Model.Sem.Call`: fn は input の引数 `name'` を名前順に先頭に取る Lean の定義、ゼロ引数の fn は定数、
呼出しは呼出し先の定数への適用)をそのまま Lean のモジュールにし、検査プログラム `CallModelCheck.lean`(モジュール `CallModelCheck`。`CallScope` を import)が:
- 実生成宣言の表 `shapes_call` / `gens_call <inputs>`(`NaruSem.Call.Shape` / `Gen`: 鍵・input か・仮引数の型・戻り型・実生成の関数。input は解釈の Lean の値、
  fn は生成定数に(推移的に)使う input の引数を適用したもの)から署名 `Δgen_call` と関数環境 `Φgen_call <inputs>` を作り、`Φgen_call_respects`(表の環境は表の署名を守る:
  `ofGens_respects`)と `cover_call`(宣言群の各 fn / input の署名が表にある: `decide`)、
- 各 fn の接続 `conn_<f> <inputs> : ∀ args, Model.Sem.Call.<f> <fn の input 引数> args = denoteN Δgen_call (Φgen_call <inputs>) (Env.ofList …) ccore_<f>`(kernel の定義的
  等しさ。`proofOf`: リテラルパターンの `match` は scrutinee の `cases` の後に `rfl`)と、それを接続の証拠に写した `evid_<f>`(`fnConn_of_curried`)、
- 宣言群全体の証拠 `cevid_call`(`Evidence`: 各 fn に `evid_<f>`)と、宣言群の意味と実生成定数の一致 `cgen_call`(`interp_agree`: 適格な宣言群・input の署名を守る任意の
  解釈 `I`・`I` と `Φgen_call` が input の鍵で同じ(`SameInputs`)なら `(interp I cprog_call).Φ` は `Φgen_call` と署名の鍵で一致)、各 fn の値 `cval_<f>`(`fn_value`: 宣言群の
  意味の fn は型の合う任意の実引数で実生成定数の値)
を kernel に検査させ、公理監査に載せる。負の検体 `CallModelWrong.lean`(C58)は実生成文字列から作る誤出力(同じ署名の別の呼出し先、名前付き実引数の取り違え、
UFCS の受け手の誤対応、input の誤配線)が型検査を通りつつ接続検査だけで失敗することを確かめる。 -/

def callGenDir : System.FilePath := outDir / "gencall"

/-- 実際の宣言群の fn 1 つ: 修飾名、Core の仮引数、戻り型、本体、推移的に使う input の鍵(名前順)、宣言群の中の位置。 -/
structure CallFn where
  key : String
  params : List Naru.Core.Param
  ret : NaruSem.Ty
  body : Naru.Core.Expr
  inputs : List String
  index : Nat

def tyLean : NaruSem.Ty → String
  | .nat => "Nat"
  | .bool => "Bool"

/-- input の Lean の型(カリー化。backend の `inputTy` と同じ形): `Nat`、`(Nat → Nat)`、`(Bool → Bool)`。 -/
def inputTyLean (ps : List NaruSem.Ty) (t : NaruSem.Ty) : String :=
  if ps.isEmpty then tyLean t else "(" ++ " → ".intercalate (ps.map tyLean ++ [tyLean t]) ++ ")"

/-- fn / spec 宣言が(推移的に)使う input の鍵(名前順。backend の `Env.inputs` と同じ規則: 直接呼ぶ input と、呼ぶ fn の input の和)。依存順の宣言群を前から畳み込む。 -/
def inputsOf (prog : List NaruSem.Call.Decl) : List (String × List String) := Id.run do
  let inputKeys := prog.filterMap fun d => match d with | .input k .. => some k | _ => none
  let mut table : List (String × List String) := []
  for d in prog do
    match d with
    | .input .. => pure ()
    | _ =>
      let calls := declCallKeys d
      let direct := calls.filter inputKeys.contains
      let via := calls.flatMap fun g => (table.lookup g).getD []
      table := table ++ [(d.key, (direct ++ via).eraseDups.mergeSort (· ≤ ·))]
  return table

/-- 仮引数 → 値の項(`NaruSem.Val.nat «x»`)。 -/
def valOfParam (p : Naru.Core.Param) : Option String :=
  match p.ty with
  | .nat => some s!"NaruSem.Val.nat «{p.name}»"
  | .bool => some s!"NaruSem.Val.bool «{p.name}»"
  | _ => none

/-- `d ∈ cprog_call` の証明の項(`i` 番目の宣言)。 -/
def memTerm : Nat → String
  | 0 => "(List.mem_cons_self ..)"
  | i + 1 => s!"(List.mem_cons_of_mem _ {memTerm i})"

/-- input の束縛(定理の引数)と実引数: `(bias' : (Nat → Nat)) (flag' : (Bool → Bool)) (seed' : Nat)` / `bias' flag' seed'`(名前順)。 -/
def inputBinders (inputs : List (String × List NaruSem.Ty × NaruSem.Ty)) : String × String :=
  let sorted := inputs.mergeSort fun a b => a.1 ≤ b.1
  (" ".intercalate (sorted.map fun (k, ps, t) => s!"({Naru.Backend.Model.inputBinder k} : {inputTyLean ps t})"),
   " ".intercalate (sorted.map fun (k, _, _) => Naru.Backend.Model.inputBinder k))

/-- 接続の定理 1 つ分(呼出しを含む宣言、1 行): input の束縛を定理の引数に取り、
`<thm> <inputs> : ∀ args, <Lean 名> <fn の input 引数> args = denoteN Δgen_call (Φgen_call <inputs>) (Env.ofList …) <core> := <proof>`。 -/
def callConnStmt (ib ia : String) (thm lean : String) (f : CallFn) (coreName proof : String) : String :=
  let bs := f.params.filterMap binderOf
  let binders := " ".intercalate (bs.map (·.1))
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let den := match f.ret with | .nat => "NaruSem.Call.denoteN" | .bool => "NaruSem.Call.denoteB"
  let call := " ".intercalate ([lean] ++ f.inputs.map Naru.Backend.Model.inputBinder ++ bs.map (·.2.2))
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  let hdr := if ib.isEmpty then s!"theorem {thm} :" else s!"theorem {thm} {ib} :"
  s!"{hdr} {quant s!"{call} = {den} Δgen_call (Φgen_call {ia}) (NaruSem.Env.ofList {env}) {coreName}"} := {proof}"

/-- 1 つの fn の接続 `conn_<f>` と接続の証拠 `evid_<f>`。 -/
def callConnOf (ib ia : String) (f : CallFn) : String :=
  let n := shortName f.key
  let lean := Naru.Backend.Model.leanName f.key
  let applied := " ".intercalate ([lean] ++ f.inputs.map Naru.Backend.Model.inputBinder)
  let appliedT := if f.inputs.isEmpty then lean else s!"({applied})"
  let ps := NaruSem.Call.Quote.params (f.params.filterMap NaruSem.Call.Quote.paramOf?)
  let hdr (name : String) := if ib.isEmpty then s!"theorem {name} :" else s!"theorem {name} {ib} :"
  s!"-- {f.key}: the generated declaration `{lean}` (input arguments {f.inputs.map Naru.Backend.Model.inputBinder}) is definitionally the reading of its Core in the generated-constant environment (C55 / C57)\n" ++
  callConnStmt ib ia s!"conn_{n}" lean f s!"ccore_{n}" (proofOf f.params f.body) ++ "\n" ++
  s!"{hdr s!"evid_{n}"} NaruSem.Call.FnConn Δgen_call (Φgen_call {ia}) {f.key.quote} {ps} {tyTerm f.ret} ccore_{n} :=\n" ++
  s!"  NaruSem.Call.fnConn_of_curried Δgen_call (Φgen_call {ia}) {f.key.quote} {ps} {tyTerm f.ret} ccore_{n} {appliedT} (conn_{n} {ia}) rfl\n\n"

/-- 1 つの fn の値 `cval_<f>`: 宣言群の意味の fn は型の合う任意の実引数で実生成定数の値(`fn_value`。呼出し先の証拠は `cevid_call` で合成済み)。 -/
def callValOf (ib ia : String) (f : CallFn) : String :=
  let n := shortName f.key
  let lean := Naru.Backend.Model.leanName f.key
  let bs := f.params.filterMap binderOf
  let vals := "[" ++ ", ".intercalate (f.params.filterMap valOfParam) ++ "]"
  let binders := " ".intercalate (bs.map (·.1))
  let args := " ".intercalate (bs.map (·.2.2))
  let call := " ".intercalate ([lean] ++ f.inputs.map Naru.Backend.Model.inputBinder ++ bs.map (·.2.2))
  let val := match f.ret with | .nat => "NaruSem.Val.nat" | .bool => "NaruSem.Val.bool"
  let quant (body : String) : String := if bs.isEmpty then body else s!"∀ {binders}, {body}"
  let lam (body : String) : String := if bs.isEmpty then body else s!"fun {args} => {body}"
  let hdr := if ib.isEmpty then s!"theorem cval_{n}" else s!"theorem cval_{n} {ib}"
  s!"-- {f.key}: under any input interpretation agreeing with the inputs, the meaning of the group gives `{lean}` on any well-typed arguments (C55)\n" ++
  s!"{hdr} (I : NaruSem.Call.FEnv) (Δ : NaruSem.Call.SigEnv) (hP : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call = some Δ)\n" ++
  s!"    (hI : I.RespectsInputs cprog_call) (hin : NaruSem.Call.SameInputs I (Φgen_call {ia}) cprog_call) :\n" ++
  s!"    {quant s!"∃ f, (NaruSem.Call.interp I cprog_call).Φ {f.key.quote} = some f ∧ f {vals} = some ({val} ({call}))"} :=\n" ++
  s!"  {lam s!"NaruSem.Call.fn_value hP hI (NaruSem.Call.SubV_of_cover hP cover_call) (Φgen_call_respects {ia}) hin (cevid_call {ia}) {memTerm f.index} rfl rfl rfl"}\n\n"

/-- 現在のCoreから得た一つのinputの鍵・署名で、任意の解釈のLean表現を検査する。 -/
def inputReprOf (k : String) (ps : List (String × NaruSem.Ty)) (t : NaruSem.Ty) (i : Nat) : String :=
  let pts := NaruSem.Call.Quote.list (ps.map fun p => tyTerm p.2)
  s!"theorem irepr_{shortName k} (I : NaruSem.Call.FEnv) (hI : I.RespectsInputs cprog_call) :\n" ++
  s!"    ∃ g : NaruSem.Call.Fn {pts} {tyTerm t}, ∃ f, I {k.quote} = some f ∧\n" ++
  s!"      ∀ vs, vs.map NaruSem.Val.ty = {pts} → NaruSem.Call.wrap {pts} {tyTerm t} g vs = f vs :=\n" ++
  s!"  NaruSem.Call.input_representable hI {memTerm i}\n\n"

/-- 任意の署名を守る解釈から選んだ値を、現在の実生成 input 引数へ渡す。 -/
def callInputGenerated (prog : NaruSem.Call.Prog) : String :=
  let actual := prog.zipIdx |>.filterMap fun (d, i) => match d with
    | .input k ps t => some (k, ps, t, i)
    | _ => none
  let sorted := actual.mergeSort fun a b => a.1 ≤ b.1
  let inputs := sorted.map fun (k, ps, t, _) => (k, ps.map (·.2), t)
  let (ib, ia) := inputBinders inputs
  let selected := sorted.map fun (k, ps, t, i) =>
    s!"(gs {k.quote} {NaruSem.Call.Quote.params ps} {tyTerm t} {memTerm i})"
  let ga := " ".intercalate selected
  let rcasesPat := " | ".intercalate (prog.map fun _ => "hd")
  "-- Arbitrary signature-respecting input interpretation, including arbitrary behavior outside its typed domain.\n" ++
  "theorem cinputs_generated (I : NaruSem.Call.FEnv) (hI : I.RespectsInputs cprog_call) :\n" ++
  s!"    ∃ {ib}, NaruSem.Call.InputsAgree I (Φgen_call {ia}) cprog_call := by\n" ++
  s!"  obtain ⟨gs, hg⟩ := NaruSem.Call.inputs_generated_agree hI (fun gs => Φgen_call {ga}) (by\n" ++
  "    intro gs k ps t hd\n" ++
  "    simp only [cprog_call, List.mem_cons, List.mem_nil_iff, or_false] at hd\n" ++
  s!"    rcases hd with {rcasesPat}\n" ++
  "    all_goals cases hd\n" ++
  "    all_goals rfl)\n" ++
  s!"  exact ⟨{", ".intercalate selected}, hg⟩\n\n"

/-- 検査プログラム `CallModelCheck.lean`。 -/
def callModelProgram (fns : List CallFn) (inputs : List (String × List NaruSem.Ty × NaruSem.Ty)) (prog : List NaruSem.Call.Decl) : String :=
  let (ib, ia) := inputBinders inputs
  let sortedInputs := inputs.mergeSort fun a b => a.1 ≤ b.1
  let shapeOf (k : String) (input : Bool) (ps : List NaruSem.Ty) (t : NaruSem.Ty) : String :=
    s!"⟨{k.quote}, {input}, {NaruSem.Call.Quote.list (ps.map tyTerm)}, {tyTerm t}⟩"
  let fnTys (f : CallFn) : List NaruSem.Ty := f.params.filterMap fun p => (NaruSem.Call.Quote.paramOf? p).map (·.2)
  let shapes := sortedInputs.map (fun (k, ps, t) => shapeOf k true ps t) ++ fns.map fun f => shapeOf f.key false (fnTys f) f.ret
  let gens := sortedInputs.map (fun (k, ps, t) => s!"⟨{shapeOf k true ps t}, {Naru.Backend.Model.inputBinder k}⟩") ++ fns.map fun f =>
    let applied := " ".intercalate ([Naru.Backend.Model.leanName f.key] ++ f.inputs.map Naru.Backend.Model.inputBinder)
    s!"⟨{shapeOf f.key false (fnTys f) f.ret}, {applied}⟩"
  let hdr (kw name : String) := if ib.isEmpty then s!"{kw} {name}" else s!"{kw} {name} {ib}"
  let bullets := prog.map fun d => match d with
    | .fn k .. => s!"  · exact evid_{shortName k} {ia}"
    | _ => "  · trivial"
  let rcasesPat := " | ".intercalate (prog.map fun _ => "rfl")
  let reprs := prog.zipIdx |>.filterMap fun (d, i) => match d with
    | .input k ps t => some (s!"irepr_{shortName k}", inputReprOf k ps t i)
    | _ => none
  let names := ["Φgen_call_respects", "cover_call"] ++ fns.flatMap (fun f => [s!"conn_{shortName f.key}", s!"evid_{shortName f.key}"]) ++
    ["cevid_call", "cgen_call", "cgen_inputs_call", "ireprs_call", "cinputs_generated"] ++ reprs.map (·.1) ++ fns.map (fun f => s!"cval_{shortName f.key}")
  s!"-- naru_test semantics (C55 / C56 / C57 / C58): generated from NaruTest/Semantics.lean. Connection of the generated Model of {callSource} (calls and inputs) to the Core semantics and to the meaning of the declaration group.\n" ++
  "import CallScope\nimport Model.Sem.Call\n\n" ++
  "-- the general theorem quantifies over any signatures, well-formed expression, matching environment and function environments agreeing on the signatures (C55)\n" ++
  "example : ∀ (Δ Δ' : NaruSem.Call.SigEnv) (Φ Φ' : NaruSem.Call.FEnv) (Γ : NaruSem.Ctx) (e : Naru.Core.Expr) (t : NaruSem.Ty) (ρ : NaruSem.Env),\n" ++
  "    NaruSem.Call.SigEnv.SubV Δ Δ' → Φ'.Respects Δ' → NaruSem.Call.FEnv.Agree Φ Φ' Δ → NaruSem.Call.wtR Δ Γ e = some t → Γ = ρ.ty →\n" ++
  "    NaruSem.Call.eval Φ ρ e = some (NaruSem.Call.denoteV Δ' Φ' ρ t e) :=\n" ++
  "  fun _ _ _ _ _ _ _ _ hΔ hΦ' hA h hρ => NaruSem.Call.denote_sound hΔ hΦ' hA h _ hρ\n" ++
  "-- the group theorem quantifies over any well-formed declaration group, any input interpretation respecting its signatures and any generated-constant\n" ++
  "-- environment with the same inputs and per-fn evidence: the group's meaning agrees with the generated constants on every signature (C55 / C56)\n" ++
  "example : ∀ (P : NaruSem.Call.Prog) (Δ Δ' : NaruSem.Call.SigEnv) (I Φ' : NaruSem.Call.FEnv),\n" ++
  "    NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty P = some Δ → I.RespectsInputs P → NaruSem.Call.SigEnv.SubV Δ Δ' → Φ'.Respects Δ' →\n" ++
  "    NaruSem.Call.SameInputs I Φ' P → NaruSem.Call.Evidence Δ' Φ' P → NaruSem.Call.FEnv.Agree (NaruSem.Call.interp I P).Φ Φ' Δ :=\n" ++
  "  fun _ _ _ _ _ hP hI hΔ hΦ' hin hev => NaruSem.Call.interp_agree hP hI hΔ hΦ' hin hev\n\n" ++
  "-- the shapes (key, input?, parameter types, return type) of the fn / input declarations of the group\n" ++
  s!"def shapes_call : List NaruSem.Call.Shape :=\n  [ {",\n    ".intercalate shapes} ]\n" ++
  "-- the table of generated constants, parametrized by the inputs (name order, as the generated functions take them): an input is its interpretation as a Lean\n" ++
  "-- value, a fn is the generated constant applied to the input arguments it (transitively) uses\n" ++
  s!"{hdr "def" "gens_call"} : List NaruSem.Call.Gen :=\n  [ {",\n    ".intercalate gens} ]\n" ++
  "def Δgen_call : NaruSem.Call.SigEnv := NaruSem.Call.SigEnv.ofShapes shapes_call\n" ++
  s!"{hdr "def" "Φgen_call"} : NaruSem.Call.FEnv := NaruSem.Call.FEnv.ofGens (gens_call {ia})\n" ++
  s!"{hdr "theorem" "gens_call_shape"} : (gens_call {ia}).map NaruSem.Call.Gen.shape = shapes_call := rfl\n" ++
  "-- the generated-constant environment respects the signatures of the table, for any inputs (C56)\n" ++
  s!"{hdr "theorem" "Φgen_call_respects"} : (Φgen_call {ia}).Respects Δgen_call := NaruSem.Call.ofGens_respects (gens_call {ia})\n" ++
  "-- every fn / input of the group has its signature in the table, so the group's signatures are included in the table's (`SubV_of_cover`)\n" ++
  "theorem cover_call : ∀ d ∈ cprog_call, d.sig.value?.isSome = true → Δgen_call d.key = some d.sig := by decide\n\n" ++
  "-- representations of all actual inputs, under any signature-respecting interpretation (C56)\n" ++
  "".intercalate (reprs.map (·.2)) ++
  "theorem ireprs_call (I : NaruSem.Call.FEnv) (hI : I.RespectsInputs cprog_call) :\n" ++
  "    ∃ gs : NaruSem.Call.InputValues cprog_call, ∀ k ps t (hd : NaruSem.Call.Decl.input k ps t ∈ cprog_call),\n" ++
  "      ∃ f, I k = some f ∧ ∀ vs, vs.map NaruSem.Val.ty = ps.map (·.2) →\n" ++
  "        NaruSem.Call.wrap (ps.map (·.2)) t (gs k ps t hd) vs = f vs := NaruSem.Call.inputs_representable hI\n\n" ++
  callInputGenerated prog ++
  "".intercalate (fns.map (callConnOf ib ia)) ++
  "-- every fn of the group has its connection evidence (C57)\n" ++
  s!"{hdr "theorem" "cevid_call"} : NaruSem.Call.Evidence Δgen_call (Φgen_call {ia}) cprog_call := by\n" ++
  "  intro d hd\n  simp only [cprog_call, List.mem_cons, List.mem_nil_iff, or_false] at hd\n" ++
  s!"  rcases hd with {rcasesPat}\n" ++ "\n".intercalate bullets ++ "\n\n" ++
  "-- the meaning of the actual group under any input interpretation agreeing with the inputs agrees with the generated constants on every signature (C55 / C56 / C57)\n" ++
  s!"{hdr "theorem" "cgen_call"} (I : NaruSem.Call.FEnv) (Δ : NaruSem.Call.SigEnv) (hP : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call = some Δ)\n" ++
  s!"    (hI : I.RespectsInputs cprog_call) (hin : NaruSem.Call.SameInputs I (Φgen_call {ia}) cprog_call) :\n" ++
  s!"    NaruSem.Call.FEnv.Agree (NaruSem.Call.interp I cprog_call).Φ (Φgen_call {ia}) Δ :=\n" ++
  s!"  NaruSem.Call.interp_agree hP hI (NaruSem.Call.SubV_of_cover hP cover_call) (Φgen_call_respects {ia}) hin (cevid_call {ia})\n\n" ++
  s!"{hdr "theorem" "cgen_inputs_call"} (I : NaruSem.Call.FEnv) (Δ : NaruSem.Call.SigEnv) (hP : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call = some Δ)\n" ++
  s!"    (hI : I.RespectsInputs cprog_call) (hin : NaruSem.Call.InputsAgree I (Φgen_call {ia}) cprog_call) :\n" ++
  s!"    NaruSem.Call.FEnv.Agree (NaruSem.Call.interp I cprog_call).Φ (Φgen_call {ia}) Δ :=\n" ++
  s!"  NaruSem.Call.interp_inputs_agree hP hI (NaruSem.Call.SubV_of_cover hP cover_call) (Φgen_call_respects {ia}) hin (cevid_call {ia})\n\n" ++
  "".intercalate (fns.map (callValOf ib ia)) ++
  s!"#audit_axioms {" ".intercalate names}\n"

/-- 呼出しを含む実生成 Statements と、その宣言より前の署名での読みへの接続。 -/
def callSpecConnStmt (ib ia thm lean : String) (f : CallFn) : String :=
  let bs := f.params.filterMap specBinderOf
  let quant (s : String) := if bs.isEmpty then s else s!"∀ {" ".intercalate (bs.map (·.1))}, {s}"
  let env := "[" ++ ", ".intercalate (bs.map (·.2.1)) ++ "]"
  let call := " ".intercalate ([lean] ++ f.inputs.map Naru.Backend.Model.inputBinder ++ bs.map (·.2.2))
  let hdr := if ib.isEmpty then s!"theorem {thm}" else s!"theorem {thm} {ib}"
  s!"{hdr} : {quant s!"{call} ↔ NaruSem.Call.denoteP Δprefix_{shortName f.key} (Φgen_call {ia}) (Ψgen_call {ia}) (NaruSem.SEnv.ofList {env}) ccore_{shortName f.key}"} := " ++
  (if bs.isEmpty then "Iff.rfl" else s!"fun {" ".intercalate (bs.map (·.2.2))} => Iff.rfl")

def callStatementsProgram (specs : List CallFn) (inputs : List (String × List NaruSem.Ty × NaruSem.Ty)) (prog : List NaruSem.Call.Decl) : String :=
  let (ib, ia) := inputBinders inputs
  let hdr (kw name : String) := if ib.isEmpty then s!"{kw} {name}" else s!"{kw} {name} {ib}"
  let pg (f : CallFn) :=
    let ps := f.params.filterMap fun p => (NaruSem.Call.Quote.paramOf? p).map (·.2)
    let applied := " ".intercalate ([Naru.Backend.Statements.stmtName f.key] ++ f.inputs.map Naru.Backend.Model.inputBinder)
    s!"({f.key.quote}, wrapP {NaruSem.Call.Quote.list (ps.map tyTerm)} ({applied}))"
  "-- Current generated Statements versus the reading of the current quoted Core, for arbitrary inputs and parameters.\n" ++
  "-- This is an expression connection check; per-spec prefix evidence is composed into declaration-group proposition equivalence; Surface preservation is a separate obligation.\n" ++
  "import CallModelCheck\nimport Statements.Sem.Call\n\n" ++
  "-- General equivalence: any well-formed expression and matching environment, with value equality and proposition equivalence on callee signatures.\n" ++
  "example {Δ Δ' : NaruSem.Call.SigEnv} {Φ Φ' : NaruSem.Call.FEnv} {Ψ Ψ' : NaruSem.Call.PEnv}\n" ++
  "    (hΔ : NaruSem.Call.SigEnv.SubV Δ Δ') (hΦ' : Φ'.Respects Δ') (hA : NaruSem.Call.FEnv.Agree Φ Φ' Δ) (hPA : NaruSem.Call.PEnv.Agree Ψ Ψ' Δ)\n" ++
  "    {Γ : NaruSem.SCtx} {e : Naru.Core.Expr} {τ : NaruSem.STy} (hw : NaruSem.Call.wtS Δ Γ e = some τ)\n" ++
  "    (ρ : NaruSem.SEnv) (hρ : Γ = ρ.ctx) {P : Prop} (h : NaruSem.Call.Sem Δ Φ Ψ ρ e P) : P ↔ NaruSem.Call.denoteP Δ Φ' Ψ' ρ e :=\n" ++
  "  NaruSem.Call.Sem_denote hΔ hΦ' hA hPA hw ρ hρ h\n\n" ++
  "open NaruSem.Call (wrapP)\n" ++
  "def prefix_call (n : Nat) : NaruSem.Call.SigEnv := (cprog_call.take n).foldl (fun Δ d => Δ.ext d.key d.sig) NaruSem.Call.SigEnv.empty\n" ++
  "".intercalate (specs.map fun f => s!"def Δprefix_{shortName f.key} : NaruSem.Call.SigEnv := prefix_call {f.index}\n") ++
  s!"{hdr "def" "props_call"} : List (String × (List NaruSem.Val → Prop)) :=\n  [{",\n   ".intercalate (specs.map pg)}]\n" ++
  s!"{hdr "def" "Ψgen_call"} : NaruSem.Call.PEnv := fun k => (props_call {ia}).lookup k\n\n" ++
  "\n".intercalate (specs.map fun f => callSpecConnStmt ib ia s!"read_{shortName f.key}" (Naru.Backend.Statements.stmtName f.key) f) ++ "\n" ++
  "\n".intercalate (specs.map fun f =>
    let n := shortName f.key
    let ps := NaruSem.Call.Quote.params (f.params.filterMap NaruSem.Call.Quote.paramOf?)
    let applied := " ".intercalate ([Naru.Backend.Statements.stmtName f.key] ++ f.inputs.map Naru.Backend.Model.inputBinder)
    s!"{hdr "theorem" s!"spevid_{n}"} : NaruSem.Call.SpecConn Δprefix_{n} (Φgen_call {ia}) (Ψgen_call {ia}) {f.key.quote} {ps} ccore_{n} :=\n" ++
    s!"  NaruSem.Call.specConn_of_curried Δprefix_{n} (Φgen_call {ia}) (Ψgen_call {ia}) {f.key.quote} {ps} ccore_{n} ({applied}) (read_{n} {ia}) rfl\n") ++
  s!"{hdr "theorem" "spevid_call"} : NaruSem.Call.SpecEvidence (Φgen_call {ia}) (Ψgen_call {ia}) NaruSem.Call.SigEnv.empty cprog_call := by\n" ++
  "".intercalate (prog.map fun d => match d with
    | .spec k .. => s!"  refine ⟨spevid_{shortName k} {ia}, ?_⟩\n"
    | _ => "  refine ⟨True.intro, ?_⟩\n") ++ "  trivial\n\n" ++
  s!"{hdr "theorem" "cprops_call"} (I : NaruSem.Call.FEnv) (Δ : NaruSem.Call.SigEnv) (hP : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call = some Δ)\n" ++
  s!"    (hI : I.RespectsInputs cprog_call) (hin : NaruSem.Call.SameInputs I (Φgen_call {ia}) cprog_call) :\n" ++
  s!"    NaruSem.Call.PEnv.Agree (NaruSem.Call.interp I cprog_call).Ψ (Ψgen_call {ia}) Δ :=\n" ++
  s!"  NaruSem.Call.interp_prop_agree hP hI (NaruSem.Call.SubV_of_cover hP cover_call) (Φgen_call_respects {ia}) hin (cevid_call {ia}) (spevid_call {ia})\n\n" ++
  s!"{hdr "theorem" "cprops_inputs_call"} (I : NaruSem.Call.FEnv) (Δ : NaruSem.Call.SigEnv) (hP : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call = some Δ)\n" ++
  s!"    (hI : I.RespectsInputs cprog_call) (hin : NaruSem.Call.InputsAgree I (Φgen_call {ia}) cprog_call) :\n" ++
  s!"    NaruSem.Call.PEnv.Agree (NaruSem.Call.interp I cprog_call).Ψ (Ψgen_call {ia}) Δ :=\n" ++
  s!"  NaruSem.Call.interp_prop_inputs_agree hP hI (NaruSem.Call.SubV_of_cover hP cover_call) (Φgen_call_respects {ia}) hin (cevid_call {ia}) (spevid_call {ia})\n\n" ++
  "theorem cinputs_connect (I : NaruSem.Call.FEnv) (Δ : NaruSem.Call.SigEnv) (hP : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call = some Δ)\n" ++
  "    (hI : I.RespectsInputs cprog_call) :\n" ++
  s!"    ∃ {ib}, NaruSem.Call.InputsAgree I (Φgen_call {ia}) cprog_call ∧\n" ++
  s!"      NaruSem.Call.FEnv.Agree (NaruSem.Call.interp I cprog_call).Φ (Φgen_call {ia}) Δ ∧\n" ++
  s!"      NaruSem.Call.PEnv.Agree (NaruSem.Call.interp I cprog_call).Ψ (Ψgen_call {ia}) Δ := by\n" ++
  s!"  obtain ⟨{", ".intercalate (inputs.mergeSort (fun a b => a.1 ≤ b.1) |>.map fun (k, _, _) => Naru.Backend.Model.inputBinder k)}, hin⟩ := cinputs_generated I hI\n" ++
  s!"  exact ⟨{", ".intercalate (inputs.mergeSort (fun a b => a.1 ≤ b.1) |>.map fun (k, _, _) => Naru.Backend.Model.inputBinder k)}, hin, cgen_inputs_call {ia} I Δ hP hI hin, cprops_inputs_call {ia} I Δ hP hI hin⟩\n\n" ++
  s!"#audit_axioms spevid_call cprops_call cprops_inputs_call cinputs_connect {" ".intercalate (specs.flatMap fun f => [s!"read_{shortName f.key}", s!"spevid_{shortName f.key}"])}\n"

/-- C58: 実生成 spec 出力の論理・呼出し先・名前付き引数・UFCS・推移的 input の誤配線。 -/
def callSpecMistranslations : List Mistranslation :=
  [ { key := "Sem.Call.specCallSpec", wrong := "Wrong.specCallSpec",
      good := "(Statements.Sem.Callees.posBase «x») ∧ («x» < (10 : Nat))",
      bad := "(Statements.Sem.Callees.posBase «x») ∨ («x» < (10 : Nat))",
      transform := fun s => s.replace "(Statements.Sem.Callees.posBase «x») ∧ («x» < (10 : Nat))"
        "(Statements.Sem.Callees.posBase «x») ∨ («x» < (10 : Nat))",
      note := "the conjunction in specCallSpec replaced by disjunction (well-typed but a weaker proposition)" },
    { key := "Sem.Call.specTwoStep", wrong := "Wrong.specTwoStep",
      good := "Statements.Sem.Call.specInput seed' «x»", bad := "Statements.Sem.Call.specCallSpec «x»",
      transform := fun s => s.replace "Statements.Sem.Call.specInput seed' «x»" "Statements.Sem.Call.specCallSpec «x»",
      note := "the spec callee replaced by another Nat-to-Prop declaration, after its input argument is applied" },
    { key := "Sem.Call.specNamed", wrong := "Wrong.specNamed",
      good := "Model.Sem.Callees.addTo «b» «a»", bad := "Model.Sem.Callees.addTo «a» «b»",
      transform := fun s => s.replace "Model.Sem.Callees.addTo «b» «a»" "Model.Sem.Callees.addTo «a» «b»",
      note := "the two Nat named arguments are swapped in the spec's runtime call" },
    { key := "Sem.Call.specUfcs", wrong := "Wrong.specUfcs",
      good := "Model.Sem.Callees.addTo «a» «b»", bad := "Model.Sem.Callees.addTo «b» «a»",
      transform := fun s => s.replace "Model.Sem.Callees.addTo «a» «b»" "Model.Sem.Callees.addTo «b» «a»",
      note := "the UFCS receiver and its Nat argument are swapped in the spec's runtime call" },
    { key := "Sem.Call.specBoolCall", wrong := "Wrong.specBoolCall",
      good := "Model.Sem.Call.boolCall flag' «b»", bad := "Model.Sem.Call.boolCall (fun v => flag' (!v)) «b»",
      transform := fun s => s.replace "Model.Sem.Call.boolCall flag' «b»" "Model.Sem.Call.boolCall (fun v => flag' (!v)) «b»",
      note := "a different Bool-to-Bool input interpretation is passed through spec -> runtime -> input" },
    { key := "Sem.Call.specSharedInputs", wrong := "Wrong.specSharedInputs",
      good := "Model.Sem.Call.sharedInputs bias' otherBias' seed'", bad := "Model.Sem.Call.sharedInputs otherBias' bias' seed'",
      transform := fun s => s.replace "Model.Sem.Call.sharedInputs bias' otherBias' seed'" "Model.Sem.Call.sharedInputs otherBias' bias' seed'",
      note := "the two distinct Nat-to-Nat inputs are swapped through spec -> runtime -> runtime -> input" } ]

/-- 閉じた反例は非同値を補助的に示す。任意 input/仮引数での正しい接続の代用にはしない。 -/
def callSpecCounterexample (m : Mistranslation) : String :=
  let (args, unfolds) := match m.key with
    | "Sem.Call.specCallSpec" => ("10", "Statements.Sem.Callees.posBase Model.Sem.Callees.base")
    | "Sem.Call.specTwoStep" => ("0 10", "Statements.Sem.Call.specCallSpec Statements.Sem.Callees.posBase Statements.Sem.Call.specInput Model.Sem.Call.useInput Model.Sem.Callees.base")
    | "Sem.Call.specNamed" => ("0 1", "Model.Sem.Callees.addTo Model.Sem.Call.callNamed")
    | "Sem.Call.specUfcs" => ("0 1", "Model.Sem.Callees.addTo Model.Sem.Call.ufcs")
    | "Sem.Call.specBoolCall" => ("(fun b => b) false", "Model.Sem.Call.boolCall")
    | "Sem.Call.specSharedInputs" => ("(fun n => n * 10) (fun _ => 1) 0 1", "Model.Sem.Call.sharedInputs Model.Sem.Call.inputPair Model.Sem.Call.useInputArg")
    | _ => ("", "")
  let name := s!"different_{shortName m.key}"
  let original := Naru.Backend.Statements.stmtName m.key
  s!"theorem {name} : ¬ ({original} {args} ↔ {m.wrong} {args}) := by unfold {original} {m.wrong} {unfolds}; decide\n#audit_axioms {name}\n"

def callSpecWrongProgram (ib ia : String) (specs : List CallFn) (wrongs : List (Mistranslation × String)) : String × List Nat :=
  let witnessed := wrongs.map fun (m, text) => (m, text ++ "\n" ++ callSpecCounterexample m)
  wrongProgramWith "Statements (calls and inputs)" ["CallStatementsReadCheck"] witnessed fun thm lean key =>
    (specs.find? fun f => f.key == key).map fun f => callSpecConnStmt ib ia thm (if lean.isEmpty then Naru.Backend.Statements.stmtName f.key else lean) f

/-- 負の検体(C58): 実生成 Model(呼出しと input)の文字列から作る、型は合うが意味の異なる誤出力。同じ署名の別の呼出し先への置換、同型の名前付き実引数の
取り違え、UFCS の受け手の誤対応、複数段の input の誤配線。 -/
def callMistranslations : List Mistranslation :=
  [ { key := "Sem.Call.twoStep", wrong := "Wrong.twoStep", good := "Model.Sem.Call.callBase (", bad := "Model.Sem.Callees.base (",
      transform := fun s => s.replace "Model.Sem.Call.callBase (" "Model.Sem.Callees.base (",
      note := "`twoStep` calling `base` instead of `callBase` (a different callee with the same signature Nat → Nat)" },
    { key := "Sem.Call.callNamed", wrong := "Wrong.callNamed", good := "Model.Sem.Callees.addTo «b» «a»", bad := "Model.Sem.Callees.addTo «a» «b»",
      transform := fun s => s.replace "Model.Sem.Callees.addTo «b» «a»" "Model.Sem.Callees.addTo «a» «b»",
      note := "the named arguments of `callNamed` (`addTo(y = a, x = b)`) passed in parameter order instead of by name (same-typed named arguments swapped)" },
    { key := "Sem.Call.ufcs", wrong := "Wrong.ufcs", good := "Model.Sem.Callees.addTo «a» «b»", bad := "Model.Sem.Callees.addTo «b» «a»",
      transform := fun s => s.replace "Model.Sem.Callees.addTo «a» «b»" "Model.Sem.Callees.addTo «b» «a»",
      note := "the UFCS receiver of `ufcs` (`a.addTo(b)`) passed as the second argument instead of the first" },
    { key := "Sem.Call.useInputArg", wrong := "Wrong.useInputArg", good := "(bias' (seed'))", bad := "(bias' «x») + (bias' «x»)",
      transform := fun s => s.replace "(bias' (seed'))" "(bias' «x»)",
      note := "the input `seed` mis-wired in `useInputArg` (`bias(seed())` reads the parameter `x` instead of the input argument `seed'`: a multi-stage input mis-wiring)" },
    { key := "Sem.Call.sharedInputs", wrong := "Wrong.sharedInputs",
      good := "Model.Sem.Call.inputPair bias' otherBias' seed'", bad := "Model.Sem.Call.inputPair otherBias' bias' seed'",
      transform := fun s => s.replace "Model.Sem.Call.inputPair bias' otherBias' seed'" "Model.Sem.Call.inputPair otherBias' bias' seed'",
      note := "the same-signature inputs are swapped in one runtime callee, while the other callee still shares the original bias/seed interpretation" } ]

/-- 負の検体 `CallModelWrong.lean`(Model、呼出し)。`CallModelCheck` を import して同じ `Δgen_call` / `Φgen_call` で接続する。 -/
def callWrongProgram (ib ia : String) (fns : List CallFn) (wrongs : List (Mistranslation × String)) : String × List Nat :=
  let witnessed := wrongs.map fun (m, text) =>
    if m.key == "Sem.Call.sharedInputs" then
      (m, text ++ "\ntheorem different_sharedInputs : Model.Sem.Call.sharedInputs (fun n => n * 2) (fun n => n + 3) 41 3 ≠ Wrong.sharedInputs (fun n => n * 2) (fun n => n + 3) 41 3 := by decide\n#audit_axioms different_sharedInputs\n")
    else (m, text)
  wrongProgramWith "Model (calls and inputs)" ["CallScope", "Model.Sem.Call", "CallModelCheck"] witnessed fun thm lean key =>
    (fns.find? fun f => f.key == key).map fun f =>
      let name := if lean.isEmpty then Naru.Backend.Model.leanName key else lean
      callConnStmt ib ia thm name f s!"ccore_{shortName key}" (proofOf f.params f.body)

/-- C57: 正しい接続証拠を違う宣言・古い本体に使う、または呼出し先の証拠を抜いた束で宣言群の保存を合成する検体。
対照は別ファイルで exit 0 と公理監査を要求する。負のファイルはその対照に 3 つの不正な証拠の使用だけを加える。 -/
def checkCallEvidence (ib ia : String) (fns : List CallFn) (lp : String) : M Unit := do
  match fns.find? (fun f => f.key == "Sem.Callees.base"), fns.find? (fun f => f.key == "Sem.Call.callBase") with
  | some base, some caller =>
    match base.body with
    | .binop op lhs (.lit (.nat n) ty) resultTy =>
      let stale := Naru.Core.Expr.binop op lhs (.lit (.nat (n + 1)) ty) resultTy
      let ps := NaruSem.Call.Quote.params (base.params.filterMap NaruSem.Call.Quote.paramOf?)
      let callerPs := caller.params.filterMap NaruSem.Call.Quote.paramOf?
      if callerPs.map (·.2) != (base.params.filterMap NaruSem.Call.Quote.paramOf?).map (·.2) || caller.ret != base.ret ||
          !(declCallKeys (.fn caller.key callerPs caller.ret caller.body)).contains base.key then
        fail "C57: the missing/wrong evidence specimen must remove a real callee with the same signature as its caller"
        return
      let conn (body : String) := s!"NaruSem.Call.FnConn Δgen_call (Φgen_call {ia}) {base.key.quote} {ps} {tyTerm base.ret} {body}"
      let group (name evidence : String) :=
        s!"theorem {name} {ib} (I : NaruSem.Call.FEnv) (Δ : NaruSem.Call.SigEnv) (hP : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call = some Δ)\n" ++
        s!"    (hI : I.RespectsInputs cprog_call) (hin : NaruSem.Call.SameInputs I (Φgen_call {ia}) cprog_call) :\n" ++
        s!"    NaruSem.Call.FEnv.Agree (NaruSem.Call.interp I cprog_call).Φ (Φgen_call {ia}) Δ :=\n" ++
        s!"  NaruSem.Call.interp_agree hP hI (NaruSem.Call.SubV_of_cover hP cover_call) (Φgen_call_respects {ia}) hin ({evidence} {ia})\n"
      let audited := ["callee_absent", "caller_present", "partial_evidence", "stale_wt", "stale_diff", "current_evidence", "complete_group"]
      let control := "-- C57: isolated evidence controls, generated from the current compiler input and output\nimport CallModelCheck\n\n" ++
        s!"def partial_prog : NaruSem.Call.Prog := cprog_call.filter (fun d => d.key != {base.key.quote})\n" ++
        s!"theorem callee_absent : ¬ ∃ d ∈ partial_prog, d.key = {base.key.quote} := by decide\n" ++
        s!"theorem caller_present : ∃ d ∈ partial_prog, d.key = {caller.key.quote} := by decide\n" ++
        s!"theorem partial_evidence {ib} : NaruSem.Call.Evidence Δgen_call (Φgen_call {ia}) partial_prog :=\n" ++
        s!"  fun d hd => cevid_call {ia} d (List.mem_filter.mp hd).1\n" ++
        s!"def stale_base : Naru.Core.Expr := {NaruSem.Quote.expr stale}\n" ++
        s!"theorem stale_wt : NaruSem.Call.wtR Δgen_call (NaruSem.Ctx.ofList {ps}) stale_base = some {tyTerm base.ret} := by decide\n" ++
        s!"theorem stale_diff : NaruSem.Call.eval NaruSem.Call.FEnv.empty (NaruSem.Env.ofList [(\"x\", NaruSem.Val.nat 0)]) stale_base ≠ NaruSem.Call.eval NaruSem.Call.FEnv.empty (NaruSem.Env.ofList [(\"x\", NaruSem.Val.nat 0)]) ccore_base := by decide\n" ++
        s!"theorem current_evidence {ib} : {conn "ccore_base"} := evid_base {ia}\n" ++
        group "complete_group" "cevid_call" ++
        s!"#audit_axioms {" ".intercalate audited}\n"
      let controlFile := outDir / "CallEvidenceCheck.lean"
      IO.FS.writeFile controlFile control
      let c ← step "C57: complete evidence composes; the incomplete bundle and stale Core are well-typed; controls are audited" "lean" #[controlFile.toString]
        (env := #[("LEAN_PATH", some lp)])
      let missing := audited.filter fun name => !(auditedNames c.stdout).contains name
      if c.exitCode == 0 && missing.isEmpty && !(contains (c.stdout ++ c.stderr) "forbidden") then
        ok s!"C57: all {audited.length} evidence controls are kernel-checked and audited; the omitted declaration is a real callee, the stale Core has the same type but a different meaning"
      else fail s!"C57: evidence controls failed or audit missing {missing}\n{tail (c.stdout ++ c.stderr) 2000}"
      let negatives :=
        [s!"theorem wrong_declaration {ib} : {conn "ccore_base"} := evid_callBase {ia}\n",
         s!"theorem stale_evidence {ib} : {conn "stale_base"} := evid_base {ia}\n",
         group "missing_callee" "partial_evidence"]
      let mut text := control
      let mut failing : List Nat := []
      for negative in negatives do
        text := text ++ negative
        failing := failing ++ [(text.splitOn "\n").length - 1]
      let wrongFile := outDir / "CallEvidenceWrong.lean"
      IO.FS.writeFile wrongFile text
      let w ← step "C57: wrong declaration, stale Core evidence and missing callee evidence must fail" "lean" #[wrongFile.toString]
        (expectExit := 1) (env := #[("LEAN_PATH", some lp)])
      let output := w.stdout ++ "\n" ++ w.stderr
      let errors := errorLines output
      let syntaxError := ["unknown", "unexpected token", "import", "sorry"].any (contains output)
      if w.exitCode == 1 && failing.length == 3 && errors.length == 3 && errors.all failing.contains && failing.all errors.contains &&
          (output.splitOn "Type mismatch").length + (output.splitOn "Application type mismatch").length >= 5 && !syntaxError then
        ok s!"C57: exactly the 3 invalid evidence uses fail (lines {failing}); complete controls succeed, no syntax/import error or forbidden proof placeholder"
      else fail s!"C57: expected exactly 3 evidence type mismatches on lines {failing}, got {errors}\n{tail output 3000}"
    | _ => fail "C57: cannot derive a stale body from the current base declaration"
  | _, _ => fail "C57: required current base/callBase declarations are missing"

/-- C57(spec): 現在の prefix 接続証拠の別宣言/古い本体への流用と、呼出し先を証明しない suffix の証拠による全体の合成を拒否する。
suffix の署名は元の prefix を保持する。署名に呼出し先があるだけでは、その接続証拠を持つことにはならない。 -/
def checkCallSpecEvidence (ib ia : String) (specs : List CallFn) (prog : NaruSem.Call.Prog) (lp : String) : M Unit := do
  match specs.find? (fun f => f.key == "Sem.Callees.posBase"), specs.find? (fun f => f.key == "Sem.Call.specCallSpec") with
  | some base, some caller =>
    match base.body with
    | .binop op lhs (.lit (.nat n) ty) resultTy =>
      let stale := Naru.Core.Expr.binop op lhs (.lit (.nat (n + 1)) ty) resultTy
      let ps := NaruSem.Call.Quote.params (base.params.filterMap NaruSem.Call.Quote.paramOf?)
      let callerPs := caller.params.filterMap NaruSem.Call.Quote.paramOf?
      let suffix := prog.drop caller.index
      let suffixKeys := suffix.filterMap fun d => match d with | .spec k .. => some k | _ => none
      if callerPs.map (·.2) != (base.params.filterMap NaruSem.Call.Quote.paramOf?).map (·.2) ||
          !(declCallKeys (.spec caller.key callerPs caller.body)).contains base.key ||
          caller.index != base.index + 1 || suffixKeys != (specs.filter (·.key != base.key)).map (·.key) then
        fail "C57(spec): the incomplete bundle must omit exactly the current spec callee, retain its real caller and preserve their signatures"
        return
      let conn (body : String) := s!"NaruSem.Call.SpecConn Δprefix_posBase (Φgen_call {ia}) (Ψgen_call {ia}) {base.key.quote} {ps} {body}"
      let group (name evidence : String) :=
        s!"theorem {name} {ib} (I : NaruSem.Call.FEnv) (Δ : NaruSem.Call.SigEnv) (hP : NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog_call = some Δ)\n" ++
        s!"    (hI : I.RespectsInputs cprog_call) (hin : NaruSem.Call.SameInputs I (Φgen_call {ia}) cprog_call) :\n" ++
        s!"    NaruSem.Call.PEnv.Agree (NaruSem.Call.interp I cprog_call).Ψ (Ψgen_call {ia}) Δ :=\n" ++
        s!"  NaruSem.Call.interp_prop_agree hP hI (NaruSem.Call.SubV_of_cover hP cover_call) (Φgen_call_respects {ia}) hin (cevid_call {ia}) ({evidence} {ia})\n"
      let audited := ["spec_callee_absent", "spec_caller_present", "spec_prefix_has_callee", "partial_spec_evidence", "stale_spec_wt", "stale_spec_diff", "current_spec_evidence", "complete_spec_group"]
      let control := "-- C57: current spec evidence controls; original prefix signatures and arbitrary inputs are retained\nimport CallStatementsReadCheck\n\n" ++
        s!"def partial_spec_prog : NaruSem.Call.Prog := cprog_call.drop {caller.index}\n" ++
        s!"theorem spec_callee_absent : ¬ ∃ d ∈ partial_spec_prog, d.key = {base.key.quote} := by decide\n" ++
        s!"theorem spec_caller_present : ∃ d ∈ partial_spec_prog, d.key = {caller.key.quote} := by decide\n" ++
        s!"theorem spec_prefix_has_callee : NaruSem.Call.specSig? Δprefix_specCallSpec {base.key.quote} = some {(NaruSem.Call.Quote.list (callerPs.map (fun p => tyTerm p.2)))} := by decide\n" ++
        s!"theorem partial_spec_evidence {ib} : NaruSem.Call.SpecEvidence (Φgen_call {ia}) (Ψgen_call {ia}) Δprefix_specCallSpec partial_spec_prog := by\n" ++
        "".intercalate (suffix.map fun d => match d with
          | .spec k .. => s!"  refine ⟨spevid_{shortName k} {ia}, ?_⟩\n"
          | _ => "  refine ⟨True.intro, ?_⟩\n") ++ "  trivial\n" ++
        s!"def stale_posBase : Naru.Core.Expr := {NaruSem.Quote.expr stale}\n" ++
        s!"theorem stale_spec_wt : NaruSem.Call.wtS Δprefix_posBase (NaruSem.Call.paramSCtx {ps}) stale_posBase = some (NaruSem.STy.val .bool) := by decide\n" ++
        s!"theorem stale_spec_diff {ib} : ¬ (NaruSem.Call.denoteP Δprefix_posBase (Φgen_call {ia}) (Ψgen_call {ia}) (NaruSem.SEnv.ofList [(\"x\", NaruSem.SVal.val (.nat 0))]) stale_posBase ↔ NaruSem.Call.denoteP Δprefix_posBase (Φgen_call {ia}) (Ψgen_call {ia}) (NaruSem.SEnv.ofList [(\"x\", NaruSem.SVal.val (.nat 0))]) ccore_posBase) := by change ¬ ((1 : Nat) > {n + 1} ↔ (1 : Nat) > {n}); decide\n" ++
        s!"theorem current_spec_evidence {ib} : {conn "ccore_posBase"} := spevid_posBase {ia}\n" ++
        group "complete_spec_group" "spevid_call" ++ s!"#audit_axioms {" ".intercalate audited}\n"
      let controlFile := outDir / "CallSpecEvidenceCheck.lean"
      IO.FS.writeFile controlFile control
      let c ← step "C57(spec): complete evidence composes; the suffix retains the caller and original prefix; stale Core is well-typed and non-equivalent" "lean" #[controlFile.toString]
        (env := #[("LEAN_PATH", some lp)])
      let missing := audited.filter fun name => !(auditedNames c.stdout).contains name
      if c.exitCode == 0 && missing.isEmpty && !(contains (c.stdout ++ c.stderr) "forbidden") then
        ok s!"C57(spec): all {audited.length} evidence controls are kernel-checked and audited; exactly the real callee's spec evidence is omitted"
      else fail s!"C57(spec): evidence controls failed or audit missing {missing}\n{tail (c.stdout ++ c.stderr) 2000}"
      let negatives :=
        [s!"theorem wrong_spec_declaration {ib} : {conn "ccore_posBase"} := spevid_specCallSpec {ia}\n",
         s!"theorem stale_spec_evidence {ib} : {conn "stale_posBase"} := spevid_posBase {ia}\n",
         group "missing_spec_callee" "partial_spec_evidence"]
      let mut text := control
      let mut failing : List Nat := []
      for negative in negatives do
        text := text ++ negative
        failing := failing ++ [(text.splitOn "\n").length - 1]
      let wrongFile := outDir / "CallSpecEvidenceWrong.lean"
      IO.FS.writeFile wrongFile text
      let w ← step "C57(spec): wrong declaration, stale Core evidence and missing spec callee evidence must fail" "lean" #[wrongFile.toString]
        (expectExit := 1) (env := #[("LEAN_PATH", some lp)])
      let output := w.stdout ++ "\n" ++ w.stderr
      let errors := errorLines output
      let syntaxError := ["unknown", "unexpected token", "import", "sorry"].any (contains output)
      if w.exitCode == 1 && failing.length == 3 && errors.length == 3 && errors.all failing.contains && failing.all errors.contains &&
          (output.splitOn "Type mismatch").length + (output.splitOn "Application type mismatch").length >= 5 && !syntaxError then
        ok s!"C57(spec): exactly the 3 invalid spec evidence uses fail (lines {failing}); complete controls succeed, no syntax/import error or forbidden proof placeholder"
      else fail s!"C57(spec): expected exactly 3 evidence type mismatches on lines {failing}, got {errors}\n{tail output 3000}"
    | _ => fail "C57(spec): cannot derive a stale body from the current posBase declaration"
  | _, _ => fail "C57(spec): required current posBase/specCallSpec declarations are missing"

def checks : M Unit := do
  let t0 ← IO.monoMsNow
  IO.FS.createDirAll outDir
  heading "C45 entry point"
  let _ ← step "C45: build the semantics, the general theorems, the specimens and the axiom audit" "lake" #["build", "NaruSem"]
  let a ← step "C45: re-run the axiom audit of the root file" "lake" #["env", "lean", rootFile]
  let auditLines := (a.stdout.splitOn "\n").filter fun l => contains l "audit ok:"
  let audited := auditedNames a.stdout
  let missing := requiredTheorems.filter fun n => !audited.contains n
  if a.exitCode == 0 && missing.isEmpty && !(contains a.stdout "forbidden") && !(contains a.stderr "forbidden") then
    ok s!"C45: the audit covers {auditLines.length} constant(s) including {requiredTheorems} with 0 forbidden dependencies (allowed: propext / Classical.choice / Quot.sound)"
  else fail s!"C45: audit: exit {a.exitCode}, required theorems not audited: {missing}\n{tail a.stdout 1500}\n{tail a.stderr 1500}"
  -- C47: 文書に挙げた定理はすべて監査に載り、文書の検査コマンドはここで走らせるものと一致する
  let archDoc ← IO.FS.readFile "docs/architecture.md"
  let docNames := docTheoremNames archDoc
  let docMissing := docNames.filter fun n => !audited.contains s!"NaruSem.{n}"
  if docNames.length >= 20 && docMissing.isEmpty then
    ok s!"C47: the {docNames.length} theorems named in the table of docs/architecture.md「一般定理」are all audited"
  else fail s!"C47: theorems named in docs/architecture.md「一般定理」but not audited: {docMissing} ({docNames.length} named)"
  let testingDoc ← IO.FS.readFile "docs/testing.md"
  let undocumented := documentedCommands.filter fun c => !contains testingDoc c
  if undocumented.isEmpty then ok s!"C47: docs/testing.md「コンパイラ意味論保存」documents the commands run here: {documentedCommands}"
  else fail s!"C47: commands run here but not documented in docs/testing.md: {undocumented}"
  let _ ← step "C44: build the Model stdlib the generated Model imports" "lake" #["build", "NaruStd"]
  let e ← runProc "lake" #["env", "printenv", "LEAN_PATH"]
  let leanPath := e.stdout.trimAscii.toString
  if e.exitCode == 0 && !leanPath.isEmpty then ok "lake env printenv LEAN_PATH" else fail s!"lake env printenv LEAN_PATH: exit {e.exitCode}"
  heading "C39 scope of the Core produced by the compiler"
  let (diags, checked) ← Naru.compileFiles [source]
  if diags.isEmpty then ok s!"C39: {source} compiles without diagnostics ({checked.core.size} module(s))"
  else
    fail s!"C39: {source}: {diags.size} diagnostic(s): {diags.toList.map (·.msg)}"
    return
  let mut quoted : List (String × String × String × String × Bool) := []
  let mut connected : List (String × List Naru.Core.Param × NaruSem.Ty × Naru.Core.Expr) := []
  let mut specConnected : List (String × List Naru.Core.Param × Naru.Core.Expr × Bool) := []
  for (key, spec) in c39Decls do
    match NaruSem.Quote.fnOf? key checked.core with
    | none => fail s!"C39: {source} has no declaration `{key}`"
    | some (_, none) => fail s!"C39: `{key}` has no body"
    | some (params, some body) =>
      match NaruSem.Quote.ctxOf params spec with
      | none => fail s!"C39: `{key}` has a parameter outside Nat / Bool"
      | some ctx =>
        if spec then
          match NaruSem.wtS (sctxOfParams params) body with
          | some τ =>
            if τ.isForm then
              ok s!"C39: `{key}` (spec) is in scope: wtS = {styTerm τ}"
              quoted := quoted ++ [(key, NaruSem.Quote.expr body, ctx, styTerm τ, true)]
              -- C42 / C43: 段階の境界(`basic`)は期待の一覧と一致し、どちらの段階の宣言も接続・保存を検査する
              let isBasic := NaruSem.basic body
              if c42Decls.contains key then
                if isBasic then
                  ok s!"C42: `{key}` is a basic spec expression (NaruSem.basic = true)"
                  specConnected := specConnected ++ [(key, params, body, true)]
                else fail s!"C42: `{key}` is expected to be basic but NaruSem.basic = false: {NaruSem.Quote.expr body}"
              else if c43Decls.contains key then
                if !isBasic then
                  ok s!"C43: `{key}` is outside the basic stage (quantifier / Prop let / Prop if / guarded match; NaruSem.basic = false); connection proof: `{proofOf params body}`"
                  specConnected := specConnected ++ [(key, params, body, false)]
                else fail s!"C43: `{key}` is expected to contain a quantifier / Prop let / Prop if / guarded match but NaruSem.basic = true"
              else fail s!"C42 / C43: `{key}` is a spec declaration listed in neither c42Decls nor c43Decls"
            else fail s!"C39: `{key}` (spec) has the value type {styTerm τ}, not a logical type"
          | none => fail s!"C39: `{key}` (spec) is not in scope (wtS = none): {NaruSem.Quote.expr body}"
        else
          match NaruSem.wtR (ctxOfParams params) body with
          | some t =>
            ok s!"C39: `{key}` (runtime) is in scope: wtR = {tyTerm t}"
            quoted := quoted ++ [(key, NaruSem.Quote.expr body, ctx, tyTerm t, false)]
            -- C40 / C41: 段階の境界(`basic`)は期待の一覧と一致し、どちらの段階の宣言も接続・保存を検査する
            let isBasic := NaruSem.basic body
            if c40Decls.contains key then
              if isBasic then
                ok s!"C40: `{key}` is a basic expression (NaruSem.basic = true)"
                connected := connected ++ [(key, params, t, body)]
              else fail s!"C40: `{key}` is expected to be basic but NaruSem.basic = false: {NaruSem.Quote.expr body}"
            else if c41Decls.contains key then
              if !isBasic then
                ok s!"C41: `{key}` is outside the basic stage (match; NaruSem.basic = false); connection proof: `{proofOf params body}`"
                connected := connected ++ [(key, params, t, body)]
              else fail s!"C41: `{key}` is expected to contain a match but NaruSem.basic = true"
            else fail s!"C40 / C41: `{key}` is a runtime declaration listed in neither c40Decls nor c41Decls"
          | none => fail s!"C39: `{key}` (runtime) is not in scope (wtR = none): {NaruSem.Quote.expr body}"
  for key in c40Decls ++ c41Decls do
    unless c39Decls.contains (key, false) do fail s!"C40 / C41: `{key}` is not a runtime declaration of c39Decls"
  for key in c42Decls ++ c43Decls do
    unless c39Decls.contains (key, true) do fail s!"C42 / C43: `{key}` is not a spec declaration of c39Decls"
  let scopeFile := outDir / "Scope.lean"
  IO.FS.writeFile scopeFile (scopeProgram quoted)
  let r ← step s!"C39: lean {scopeFile} as module `Scope` (well-formedness of {quoted.length} quoted Core expressions by `decide`, identity with the compiler's Core)"
    "lean" #[s!"--root={outDir}", "-o", (outDir / "Scope.olean").toString, scopeFile.toString] (env := #[("LEAN_PATH", some leanPath)])
  let agree := s!"checkDecls: {quoted.length} quoted Core expression(s) agree"
  if r.exitCode == 0 && (contains r.stdout agree || contains r.stderr agree) then
    ok s!"C39 / C44: the {quoted.length} quoted Core expressions are the Core the compiler produces for {source}"
  else fail s!"C39 / C44: identity of the quoted Core: expected `{agree}` in the output of lean {scopeFile}\n{tail r.stdout 1500}"
  heading "C48 / C49 scope of the Surface AST produced by the parser and its lowering to the compiler's Core"
  let mut quotedAst : List QuotedDecl := []
  let mut parsedAsts : List (String × NaruSem.Surf.Expr) := []
  let mut parsedSpecAsts : List (String × NaruSem.Surf.Expr) := []
  for (key, spec) in c39Decls do
    match NaruSem.Surf.Quote.declOf? key checked.mods with
    | none => fail s!"C48: {source} has no fn / spec declaration `{key}` in the parsed AST"
    | some (decl, _) =>
      match NaruSem.Surf.Quote.ofDeclAst? decl with
      | none => fail s!"C48: the parsed declaration `{key}` is outside the Surface AST subset (ofDeclAst? = none)"
      | some sd =>
        let n := shortName key
        let declTerm := NaruSem.Surf.Quote.declWith sd s!"ast_{n}"
        -- 宣言の適格性(種別・仮引数と戻り型の注釈・本体の型)と、Core の型付けの結果(上の Scope の段)との照合
        let coreTy := (quoted.find? fun (k, _, _, _, _) => k == key).map fun (_, _, _, ty, _) => ty
        match NaruSem.Surf.wtDecl sd with
        | none => fail s!"C48: the parsed declaration `{key}` is not well-formed as a minimal fn / spec declaration (Surf.wtDecl = none): {declTerm}"
        | some dty =>
          match dty, spec with
          | .runtime entries t, false =>
            if coreTy == some (tyTerm t) then
              ok s!"C48: the parsed `{key}` (fn, {entries.length} Nat / Bool parameter(s), return type {tyTerm t}) is a well-formed runtime declaration: Surf.wtDecl / Surf.wtR = {tyTerm t} (= the Core's wtR)"
              let q : QuotedDecl :=
                { key := key, ast := NaruSem.Surf.Quote.expr sd.body, ctx := NaruSem.Surf.Quote.ctxTerm entries false, ty := (tyTerm t),
                  spec := false, decl := declTerm, declTy := NaruSem.Surf.Quote.declTy dty }
              quotedAst := quotedAst ++ [q]
              parsedAsts := parsedAsts ++ [(key, sd.body)]
              -- C49 / C51: 独立した変換 `Surf.lower` が実際の Core に等しい(ドライバの照合。kernel の検査は `SurfaceScope.lean` の `low_<f>`)
              match connected.find? fun (k, _, _, _) => k == key with
              | some (_, params, _, body) =>
                let lowered := NaruSem.Surf.lower (ctxOfParams params) sd.body
                if lowered == some body then ok s!"C49: the lowering `Surf.lower` of the parsed `{key}` is the Core the compiler produced"
                else fail s!"C49: the lowering of the parsed `{key}` differs from the compiler's Core:\n  lowered: {lowered.map NaruSem.Quote.expr}\n  actual: {NaruSem.Quote.expr body}"
              | none => fail s!"C49: `{key}` is not among the connected runtime declarations"
            else fail s!"C48: `{key}` (runtime): Surf.wtDecl = {tyTerm t} but the Core's wtR = {coreTy}"
          | .spec entries τ, true =>
            if coreTy == some (styTerm τ) then
              ok s!"C48: the parsed `{key}` ({decl.kind.describe}, {entries.length} Nat / Bool parameter(s), no return type) is a well-formed spec declaration: Surf.wtDecl / Surf.wtS = {styTerm τ} (= the Core's wtS)"
              let q : QuotedDecl :=
                { key := key, ast := NaruSem.Surf.Quote.expr sd.body, ctx := NaruSem.Surf.Quote.ctxTerm entries true, ty := (styTerm τ),
                  spec := true, decl := declTerm, declTy := NaruSem.Surf.Quote.declTy dty }
              quotedAst := quotedAst ++ [q]
              parsedSpecAsts := parsedSpecAsts ++ [(key, sd.body)]
              -- C50 / C51: 独立した変換 `Surf.lowerS` が実際の Core に等しい(ドライバの照合。kernel の検査は `SurfaceScope.lean` の `lows_<f>`)
              match specConnected.find? fun (k, _, _, _) => k == key with
              | some (_, params, body, _) =>
                let lowered := NaruSem.Surf.lowerS (sctxOfParams params) sd.body
                if lowered == some body then ok s!"C50: the lowering `Surf.lowerS` of the parsed `{key}` is the Core the compiler produced"
                else fail s!"C50: the lowering of the parsed `{key}` differs from the compiler's Core:\n  lowered: {lowered.map NaruSem.Quote.expr}\n  actual: {NaruSem.Quote.expr body}"
              | none => fail s!"C50: `{key}` is not among the connected spec declarations"
            else fail s!"C48: `{key}` (spec): Surf.wtDecl = {styTerm τ} but the Core's wtS = {coreTy}"
          | _, _ => fail s!"C48: the phase of `{key}` per Surf.wtDecl does not match c39Decls (spec = {spec})"
  -- 対象外の構文(呼出し・Option のパターン・再帰 …)を含む宣言は対象の AST に写らない
  let (gdiags, gchecked) ← Naru.compileFiles ["tests/accept/guard_shadow.naru"]
  let outside := gchecked.mods.toList.flatMap fun m => m.decls.toList.filterMap fun d =>
    match d.body with
    | some b => if Naru.Typecheck.isFnLike d.kind && (NaruSem.Surf.Quote.ofAst? b).isNone then some d.name else none
    | none => none
  if gdiags.isEmpty && outside.length >= 3 then
    ok s!"C48: {outside.length} declarations of tests/accept/guard_shadow.naru with calls / Option patterns / recursion are outside the Surface scope (ofAst? = none): {outside}"
  else fail s!"C48: expected declarations of tests/accept/guard_shadow.naru outside the Surface scope, got {outside} ({gdiags.size} diagnostics)"
  let surfaceFile := outDir / "SurfaceScope.lean"
  IO.FS.writeFile surfaceFile (surfaceProgram quotedAst)
  let lpScope := s!"{outDir}:{leanPath}"
  let runtimeAsts := quotedAst.filter fun q => !q.spec
  let specAsts := quotedAst.filter fun q => q.spec
  let r2 ← step s!"C48 / C49 / C50: lean {surfaceFile} as module `SurfaceScope` (well-formedness of {quotedAst.length} quoted Surface AST declarations and bodies by `decide`, the lowering of the {runtimeAsts.length} runtime ASTs (`Surf.lower`) and of the {specAsts.length} spec ASTs (`Surf.lowerS`) is the compiler's Core by `rfl`, identity with the parser's AST)"
    "lean" #[s!"--root={outDir}", "-o", (outDir / "SurfaceScope.olean").toString, surfaceFile.toString] (env := #[("LEAN_PATH", some lpScope)])
  let agreeAst := s!"checkDecls: {quotedAst.length} quoted Surface AST declaration(s) agree"
  if r2.exitCode == 0 && quotedAst.length == c39Decls.length && runtimeAsts.length == c40Decls.length + c41Decls.length &&
      specAsts.length == c42Decls.length + c43Decls.length && parsedSpecAsts.length == specAsts.length && (contains r2.stdout agreeAst || contains r2.stderr agreeAst) then
    ok s!"C48 / C49 / C50 / C51: the {quotedAst.length} quoted Surface AST declarations (kind, name, span, parameters, return type, body) embed to the declarations the parser produces for {source}; the lowering of the {runtimeAsts.length} runtime ASTs and {specAsts.length} spec ASTs is the compiler's Core (kernel)"
  else fail s!"C48 / C49 / C50 / C51: identity of the quoted Surface AST / lowering: expected `{agreeAst}` in the output of lean {surfaceFile} ({quotedAst.length} of {c39Decls.length} quoted, {runtimeAsts.length} runtime, {specAsts.length} spec)\n{tail r2.stdout 1500}\n{tail r2.stderr 1500}"
  heading "C40 / C41 / C44 connection of the generated Model to the Core semantics"
  -- 実際の CLI で生成し、生成 Model をそのまま Lean のモジュールにする
  if ← genDir.pathExists then IO.FS.removeDirAll genDir
  let _ ← step "C44: generate the Model of the specimen with the real CLI" "lake" #["exe", "naru", "compile", "--out", genDir.toString, source]
  let modelFile := genDir / "Model" / "Sem" / "Core.lean"
  let modelText ← if ← modelFile.pathExists then IO.FS.readFile modelFile else pure ""
  if modelText.isEmpty then
    fail s!"C44: the generated Model {modelFile} is missing or empty"
    return
  ok s!"C44: the generated Model {modelFile} exists ({(modelText.splitOn "\n").length} lines)"
  let lp := s!"{genDir}:{outDir}:{leanPath}"
  let _ ← step "C44: compile the generated Model as the Lean module `Model.Sem.Core`" "lean"
    #[s!"--root={genDir}", "-o", (genDir / "Model" / "Sem" / "Core.olean").toString, modelFile.toString] (env := #[("LEAN_PATH", some lp)])
  let modelCheck := outDir / "ModelCheck.lean"
  IO.FS.writeFile modelCheck (modelProgram connected)
  let m ← step s!"C40 / C41 / C44 / C49: lean {modelCheck} (shape of the general theorems; connection and preservation of {connected.length} generated declarations; AST → generated Lean composition)"
    "lean" #[modelCheck.toString] (env := #[("LEAN_PATH", some lp)])
  let connAudited := auditedNames m.stdout
  let expectedConn := connected.flatMap fun (key, _, _, _) => [s!"conn_{shortName key}", s!"pres_{shortName key}", s!"apres_{shortName key}"]
  let missingConn := expectedConn.filter fun n => !connAudited.contains n
  if m.exitCode == 0 && missingConn.isEmpty && !(contains m.stdout "forbidden") && !(contains m.stderr "forbidden") then
    ok s!"C44 / C45 / C49 / C51: the connection and preservation evidence of {connected.length} generated declarations ({expectedConn.length} theorems; {c41Decls.length} with a match; `apres_*` composes AST → Core → generated Lean) is audited with 0 forbidden dependencies"
  else fail s!"C44 / C45 / C49: connection evidence: exit {m.exitCode}, not audited: {missingConn}\n{tail m.stdout 1500}\n{tail m.stderr 1500}"
  -- C46: 隔離した誤出力(実生成文字列から作る)は型検査を通るが接続検査に失敗する
  let wrongs ← deriveWrongs "Model" modelText Naru.Backend.Model.leanName mistranslations
  checkWrong "Model" (outDir / "ModelWrong.lean") (wrongProgram connected wrongs) wrongs lp
  -- C52: 隔離した誤った Core(実際の Core の値から作る)は Core の適格性を通るが、正しい AST の変換との一致に失敗する
  let coreWrongs ← deriveCoreWrongs connected parsedAsts coreMistranslations
  checkWrong "Core" (outDir / "SurfaceWrong.lean") (surfaceWrongProgram connected coreWrongs) coreWrongs lp
  heading "C42 / C43 / C44 connection of the generated Statements to the Core semantics"
  let stmtFile := genDir / "Statements" / "Sem" / "Core.lean"
  let stmtText ← if ← stmtFile.pathExists then IO.FS.readFile stmtFile else pure ""
  if stmtText.isEmpty then
    fail s!"C44: the generated Statements {stmtFile} is missing or empty"
    return
  ok s!"C44: the generated Statements {stmtFile} exists ({(stmtText.splitOn "\n").length} lines)"
  let _ ← step "C44: compile the generated Statements as the Lean module `Statements.Sem.Core`" "lean"
    #[s!"--root={genDir}", "-o", (genDir / "Statements" / "Sem" / "Core.olean").toString, stmtFile.toString] (env := #[("LEAN_PATH", some lp)])
  let stmtCheck := outDir / "StatementsCheck.lean"
  IO.FS.writeFile stmtCheck (statementsProgram specConnected)
  let s ← step s!"C42 / C43 / C44: lean {stmtCheck} (shape of the general equivalence theorem, the value / proposition boundary, the arm and quantifier lemmas; connection and preservation of {specConnected.length} generated spec declarations)"
    "lean" #[stmtCheck.toString] (env := #[("LEAN_PATH", some lp)])
  let specAudited := auditedNames s.stdout
  let expectedSpec := specConnected.flatMap fun (key, _, _, _) => [s!"conn_{shortName key}", s!"stage_{shortName key}", s!"pres_{shortName key}", s!"apres_{shortName key}"]
  let missingSpec := expectedSpec.filter fun n => !specAudited.contains n
  let c43Connected := specConnected.filter fun (_, _, _, isBasic) => !isBasic
  if s.exitCode == 0 && missingSpec.isEmpty && !(contains s.stdout "forbidden") && !(contains s.stderr "forbidden") then
    ok s!"C44 / C45 / C50 / C51: the connection and preservation evidence of {specConnected.length} generated spec declarations ({expectedSpec.length} theorems; {c43Connected.length} with a quantifier / Prop let / Prop if / guarded match; `apres_*` composes AST → Core → generated Lean) is audited with 0 forbidden dependencies"
  else fail s!"C44 / C45 / C50: connection evidence (Statements): exit {s.exitCode}, not audited: {missingSpec}\n{tail s.stdout 1500}\n{tail s.stderr 1500}"
  if specConnected.length != c42Decls.length + c43Decls.length || c43Connected.length != c43Decls.length then
    fail s!"C42 / C43: expected the {c42Decls.length} basic and {c43Decls.length} C43 spec declarations to be connected, got {specConnected.length} ({c43Connected.length} C43)"
  let specWrongs ← deriveWrongs "Statements" stmtText Naru.Backend.Statements.stmtName specMistranslations
  checkWrong "Statements" (outDir / "StatementsWrong.lean") (specWrongProgram specConnected specWrongs) specWrongs lp
  -- C52: 隔離した誤った spec の Core(実際の Core の値から作る)は Core の適格性を通るが、正しい AST の変換との一致に失敗する
  let specCoreWrongs ← deriveSpecCoreWrongs specConnected parsedSpecAsts specCoreMistranslations
  checkWrong "spec Core" (outDir / "SurfaceSpecWrong.lean") (surfaceSpecWrongProgram specConnected specCoreWrongs) specCoreWrongs lp
  heading "C54 declaration groups with calls and inputs (Core and Surface AST)"
  let (cdiags, cchecked) ← Naru.compileFiles callSources
  if cdiags.isEmpty then ok s!"C54: {callSource} compiles without diagnostics"
  else
    fail s!"C54: {callSource}: {cdiags.size} diagnostic(s): {cdiags.toList.map (·.msg)}"
    return
  let cdecls := NaruSem.Call.Quote.declsOf cchecked.core
  for (key, kind) in c54Decls do
    match cdecls.lookup key with
    | some d =>
      let okKind : Bool := match d, kind with
        | .fn .., .fn => true
        | .input .., .input => true
        | .spec .., k => k.phase == .spec
        | _, _ => false
      if okKind then ok s!"C54: `{key}` ({kind.describe}) is an in-scope declaration of the group"
      else fail s!"C54: `{key}` has an unexpected kind in the Core"
    | none => fail s!"C54: {callSource} has no in-scope fn / input / spec declaration `{key}`"
  -- These edges are part of the intended fixture, independent of the generated proof text.
  for (caller, callee) in [("Sem.Call.callBase", "Sem.Callees.base"),
      ("Sem.Call.zeroCall", "Sem.Callees.zero"), ("Sem.Call.callNamed", "Sem.Callees.addTo"),
      ("Sem.Call.ufcs", "Sem.Callees.addTo"), ("Sem.Call.specCallSpec", "Sem.Callees.posBase"),
      ("Sem.Call.specLetCall", "Sem.Callees.posBase"), ("Sem.Call.specQuantCall", "Sem.Callees.base")] do
    match cdecls.lookup caller, cdecls.lookup callee with
    | some d, some _ =>
      if (declCallKeys d).contains callee then
        ok s!"C55: actual cross-module call `{caller}` → `{callee}` (runtime/spec, qualified/named/UFCS/zero-argument coverage)"
      else fail s!"C55: expected actual cross-module call `{caller}` → `{callee}` is absent"
    | _, _ => fail s!"C55: cross-module call specimen lacks `{caller}` or `{callee}`"
  if cdecls.length != c54Decls.length then
    fail s!"C54: expected {c54Decls.length} in-scope declarations, found {cdecls.length}: {cdecls.map (·.1)}"
  -- Stable specimen order preserves the prefix used by the missing-callee evidence controls.
  -- All actual declarations are checked above and again by Quote.checkProg.
  let ranked := c54Decls.filterMap fun (k, _) => (cdecls.lookup k).map fun d => (k, d)
  match dependencyOrder ranked with
  | none => fail "C54: the declarations cannot be ordered by dependency (a cycle or an unresolved callee)"
  | some ordered =>
    let cprog := ordered.map (·.2)
    ok s!"C54: dependency order (callees first): {ordered.map fun (k, _) => shortName k}"
    match NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty cprog with
    | none => fail "C54: the Core declaration group is not well-formed (NaruSem.Call.wtProg = none)"
    | some Δ =>
      ok s!"C54: the Core declaration group ({cprog.length} declarations) is well-formed (NaruSem.Call.wtProg = some Δ; every body typed against the earlier signatures)"
      let mut cwrongs : List (String × String × String) := []
      for (name, note, wp) in coreWrongProgs cprog do
        if (NaruSem.Call.wtProg NaruSem.Call.SigEnv.empty wp).isNone then
          ok s!"C54: the Core group with {note} is not well-formed (wtProg = none)"
          cwrongs := cwrongs ++ [(name, note, coreProgTerm wp)]
        else fail s!"C54: the Core group with {note} is unexpectedly well-formed"
      let mut values : List (Nat × String × List NaruSem.Val × NaruSem.Val) := []
      let mut i := 0
      for (k, args, v) in expectedCallValues do
        let got := callValue callInterp cprog k args
        if got == some v then
          ok s!"C54: under the interpretation seed = 41 / bias(n) = 2n / otherBias(n) = n+3 / flag(b) = !b, `{shortName k}` {args.map valTerm'} = {valTerm' v} (NaruSem.Call.interp)"
          values := values ++ [(i, k, args, v)]
          i := i + 1
        else fail s!"C54: `{shortName k}` {args.map valTerm'}: expected {valTerm' v}, got {got.map valTerm'}"
      if callValue callInterpWrong cprog "Sem.Call.useInput" [.nat 1] == none then
        ok "C54: under an interpretation where `seed()` returns a Bool (not respecting its signature), `useInput(1)` is stuck (none), not a default value"
      else fail "C54: a call with an ill-typed input interpretation did not get stuck"
      let callScope := outDir / "CallScope.lean"
      IO.FS.writeFile callScope (callScopeProgram cprog Δ cwrongs values)
      let rc ← step s!"C54: lean {callScope} as module `CallScope` (well-formedness of the quoted Core declaration group and the signatures of its {cprog.length} declarations by `decide`, {cwrongs.length} negative groups, {values.length} values under an input interpretation, identity with the compiler's Core)"
        "lean" #[s!"--root={outDir}", "-o", (outDir / "CallScope.olean").toString, callScope.toString] (env := #[("LEAN_PATH", some leanPath)])
      let agreeC := s!"checkProg: {cprog.length} quoted Core declaration(s) agree"
      if rc.exitCode == 0 && (contains rc.stdout agreeC || contains rc.stderr agreeC) then
        ok s!"C54 / C57: the {cprog.length} quoted Core declarations are the Core the compiler produces for {callSource} and cover all its fn / input / spec declarations"
      else fail s!"C54 / C57: identity of the quoted Core group: expected `{agreeC}` in the output of lean {callScope}\n{tail rc.stdout 1500}\n{tail rc.stderr 1500}"
      -- Surface AST の宣言群(同じ依存順)
      let sdecls := NaruSem.Surf.Call.Quote.declsOf cchecked.mods
      let mut sprog : List NaruSem.Surf.Call.Decl := []
      for (k, _) in ordered do
        match sdecls.lookup k with
        | some sd => sprog := sprog ++ [sd]
        | none => fail s!"C54: the parsed declaration `{k}` is outside the Surface AST subset with calls (ofDeclAst? = none)"
      if sprog.length == cprog.length then
        ok s!"C54: all {sprog.length} declarations of {callSource} are in the Surface AST subset with calls (ofDeclAst?)"
      else fail s!"C54: only {sprog.length} of {cprog.length} declarations are in the Surface AST subset"
      if NaruSem.Surf.Call.wtProg sprog then
        ok s!"C54: the parsed declaration group is well-formed (NaruSem.Surf.Call.wtProg = true: names resolve to earlier declarations, named arguments match the parameters, UFCS receivers become the first argument)"
      else fail "C54: the parsed declaration group is not well-formed (NaruSem.Surf.Call.wtProg = false)"
      for d in sprog do
        let ssig := (NaruSem.Surf.Call.sigsOf sprog d.key).map NaruSem.Surf.Call.DeclSig.toSig
        if ssig == Δ d.key then ok s!"C54: the signature of the parsed `{shortName d.key}` is the signature of its Core"
        else fail s!"C54: the signature of the parsed `{shortName d.key}` differs from its Core's"
      let mut swrongs : List (String × String × String) := []
      for (name, note, wp) in surfWrongProgs sprog do
        if !(NaruSem.Surf.Call.wtProg wp) then
          ok s!"C54: the parsed group with {note} is not well-formed (wtProg = false)"
          swrongs := swrongs ++ [(name, note, surfProgTerm wp)]
        else fail s!"C54: the parsed group with {note} is unexpectedly well-formed"
      let surfaceCallScope := outDir / "SurfaceCallScope.lean"
      IO.FS.writeFile surfaceCallScope (surfaceCallScopeProgram sprog swrongs)
      let rs ← step s!"C54: lean {surfaceCallScope} as module `SurfaceCallScope` (well-formedness of the quoted Surface AST declaration group by `decide`, {swrongs.length} negative groups, identity with the parser's AST)"
        "lean" #[s!"--root={outDir}", "-o", (outDir / "SurfaceCallScope.olean").toString, surfaceCallScope.toString] (env := #[("LEAN_PATH", some s!"{outDir}:{leanPath}")])
      let agreeS := s!"checkProg: {sprog.length} quoted Surface AST declaration(s) agree"
      if rs.exitCode == 0 && (contains rs.stdout agreeS || contains rs.stderr agreeS) then
        ok s!"C54 / C57: the {sprog.length} quoted Surface AST declarations embed to the declarations the parser produces for {callSource} and cover all its fn / input / spec declarations"
      else fail s!"C54 / C57: identity of the quoted Surface AST group: expected `{agreeS}` in the output of lean {surfaceCallScope}\n{tail rs.stdout 1500}\n{tail rs.stderr 1500}"
      checkCallRuntimeLower sprog cprog s!"{outDir}:{leanPath}"
      checkCallSpecLower sprog cprog s!"{outDir}:{leanPath}"
      -- C55 / C56 / C57 / C58: 実生成 Model(呼出しと input)への接続と、宣言群の意味との合成
      heading "C55 / C56 / C57 connection of the generated Model with calls and inputs to the meaning of the declaration group"
      if ← callGenDir.pathExists then IO.FS.removeDirAll callGenDir
      let _ ← step "C57: generate the Model of the call specimen with the real CLI" "lake" (#["exe", "naru", "compile", "--out", callGenDir.toString] ++ callSources.toArray)
      let _ ← checkOmission "C56: input-only module with arbitrary interpretations" callGenDir cchecked.core
      let callModelFile := callGenDir / "Model" / "Sem" / "Call.lean"
      let callModelText ← if ← callModelFile.pathExists then IO.FS.readFile callModelFile else pure ""
      if callModelText.isEmpty then
        fail s!"C57: the generated Model {callModelFile} is missing or empty"
      else
        ok s!"C57: the generated Model {callModelFile} exists ({(callModelText.splitOn "\n").length} lines)"
        let lpCall := s!"{callGenDir}:{outDir}:{leanPath}"
        let calleeModelFile := callGenDir / "Model" / "Sem" / "Callees.lean"
        let _ ← step "C55: compile the actual cross-module runtime callees as `Model.Sem.Callees`" "lean"
          #[s!"--root={callGenDir}", "-o", (callGenDir / "Model" / "Sem" / "Callees.olean").toString, calleeModelFile.toString] (env := #[("LEAN_PATH", some lpCall)])
        let _ ← step "C57: compile the generated Model as the Lean module `Model.Sem.Call`" "lean"
          #[s!"--root={callGenDir}", "-o", (callGenDir / "Model" / "Sem" / "Call.olean").toString, callModelFile.toString] (env := #[("LEAN_PATH", some lpCall)])
        let inputsTable := inputsOf cprog
        for key in ["Sem.Call.inputPair", "Sem.Call.sharedInputs", "Sem.Call.specSharedInputs"] do
          let expected := ["Sem.Inputs.bias", "Sem.Inputs.otherBias", "Sem.Inputs.seed"]
          if inputsTable.lookup key == some expected then
            ok s!"C56: `{shortName key}` carries the two same-signature inputs distinctly and shares bias/seed exactly once, in name order"
          else fail s!"C56: `{key}`: expected distinct and deduplicated transitive inputs {expected}, got {inputsTable.lookup key}"
        let mut fns : List CallFn := []
        let mut idx := 0
        for d in cprog do
          match d with
          | .fn k _ t b =>
            match NaruSem.Quote.fnOf? k cchecked.core with
            | some (cparams, _) =>
              let ins := (inputsTable.lookup k).getD []
              fns := fns ++ [{ key := k, params := cparams, ret := t, body := b, inputs := ins, index := idx }]
              ok s!"C56: `{shortName k}` takes the input arguments {ins.map Naru.Backend.Model.inputBinder} (transitive inputs, name order); connection proof: `{proofOf cparams b}`"
            | none => fail s!"C57: the Core of `{k}` was not found in the compiled unit"
          | _ => pure ()
          idx := idx + 1
        let inputs := cprog.filterMap fun d => match d with | .input k ps t => some (k, ps.map (·.2), t) | _ => none
        let callCheck := outDir / "CallModelCheck.lean"
        IO.FS.writeFile callCheck (callModelProgram fns inputs cprog)
        let mc ← step s!"C55 / C56 / C57: lean {callCheck} as module `CallModelCheck` (shape of the general theorems; the table of {inputs.length} inputs and {fns.length} generated fn declarations respects the signatures; connection `conn_*` of the {fns.length} generated declarations with calls and inputs; evidence `evid_*` composed into the meaning of the group `cevid_call` / `cgen_call`; values `cval_*`)"
          "lean" #[s!"--root={outDir}", "-o", (outDir / "CallModelCheck.olean").toString, callCheck.toString] (env := #[("LEAN_PATH", some lpCall)])
        let callAudited := auditedNames mc.stdout
        let expectedCall := ["Φgen_call_respects", "cover_call", "cevid_call", "cgen_call", "cgen_inputs_call", "ireprs_call", "cinputs_generated"] ++
          inputs.map (fun (k, _, _) => s!"irepr_{shortName k}") ++
          fns.flatMap fun f => [s!"conn_{shortName f.key}", s!"evid_{shortName f.key}", s!"cval_{shortName f.key}"]
        let missingCall := expectedCall.filter fun n => !callAudited.contains n
        let fnCount := (c54Decls.filter fun (_, k) => k == .fn).length
        if mc.exitCode == 0 && missingCall.isEmpty && fns.length == fnCount && !(contains mc.stdout "forbidden") && !(contains mc.stderr "forbidden") then
          ok s!"C55 / C56 / C57: the connection evidence of {fns.length} generated fn declarations with calls and inputs ({expectedCall.length} theorems: per-fn `conn_` / `evid_` / `cval_`, the group's `cevid_call` / `cgen_call`; {inputs.length} input representations `irepr_*` / `ireprs_call` for any signature-respecting interpretation) is audited with 0 forbidden dependencies"
        else fail s!"C55 / C56 / C57: connection evidence (calls): exit {mc.exitCode}, not audited: {missingCall} ({fns.length} of {fnCount} fn)\n{tail mc.stdout 1500}\n{tail mc.stderr 1500}"
        -- C55(spec): 現在の実生成 Statements と現在の引用 Core の読みを任意の input / 仮引数で接続する。
        let calleeStmtFile := callGenDir / "Statements" / "Sem" / "Callees.lean"
        let _ ← step "C55: compile the actual cross-module spec callee as `Statements.Sem.Callees`" "lean"
          #[s!"--root={callGenDir}", "-o", (callGenDir / "Statements" / "Sem" / "Callees.olean").toString, calleeStmtFile.toString] (env := #[("LEAN_PATH", some lpCall)])
        let callStmtFile := callGenDir / "Statements" / "Sem" / "Call.lean"
        let _ ← step "C55: compile the generated Statements as the Lean module `Statements.Sem.Call`" "lean"
          #[s!"--root={callGenDir}", "-o", (callGenDir / "Statements" / "Sem" / "Call.olean").toString, callStmtFile.toString] (env := #[("LEAN_PATH", some lpCall)])
        let mut specs : List CallFn := []
        let mut specIdx := 0
        for d in cprog do
          match d with
          | .spec k _ b =>
            match NaruSem.Quote.fnOf? k cchecked.core with
            | some (cparams, _) => specs := specs ++ [{ key := k, params := cparams, ret := .bool, body := b, inputs := (inputsTable.lookup k).getD [], index := specIdx }]
            | none => fail s!"C55: the spec Core of `{k}` was not found in the current compiled unit"
          | _ => pure ()
          specIdx := specIdx + 1
        let callStmtCheck := outDir / "CallStatementsReadCheck.lean"
        IO.FS.writeFile callStmtCheck (callStatementsProgram specs inputs cprog)
        let sc ← step s!"C55: lean {callStmtCheck} (connection of {specs.length} current generated spec declarations to the reading of their current Core; arbitrary input interpretations and parameters)"
          "lean" #[s!"--root={outDir}", "-o", (outDir / "CallStatementsReadCheck.olean").toString, callStmtCheck.toString] (env := #[("LEAN_PATH", some lpCall)])
        let stmtAudited := auditedNames sc.stdout
        let stmtRequired := ["spevid_call", "cprops_call", "cprops_inputs_call", "cinputs_connect"] ++ specs.flatMap fun f => [s!"read_{shortName f.key}", s!"spevid_{shortName f.key}"]
        let stmtMissing := stmtRequired.filter fun n => !stmtAudited.contains n
        let stmtCount := (c54Decls.filter fun (_, k) => k != .fn && k != .input).length
        if sc.exitCode == 0 && stmtMissing.isEmpty && specs.length == stmtCount && stmtCount > 0 &&
            !(contains sc.stdout "forbidden") && !(contains sc.stderr "forbidden") then
          ok s!"C55: all {specs.length} generated spec prefix connections and declaration-group proposition equivalence are audited with 0 forbidden dependencies (Surface preservation remains a separate obligation)"
        else fail s!"C55: spec reading connections: exit {sc.exitCode}, missing audits {stmtMissing}, {specs.length} of {stmtCount} declarations\n{tail sc.stdout 1500}\n{tail sc.stderr 1500}"
        let specText ← IO.FS.readFile callStmtFile
        let specReadWrongs ← deriveWrongs "Statements (calls)" specText Naru.Backend.Statements.stmtName callSpecMistranslations
        let (sib, sia) := inputBinders inputs
        checkWrong "Statements (calls)" (outDir / "CallStatementsReadWrong.lean")
          (callSpecWrongProgram sib sia specs specReadWrongs) specReadWrongs lpCall
          ["different_specCallSpec", "different_specTwoStep", "different_specNamed", "different_specUfcs", "different_specBoolCall", "different_specSharedInputs"]
        -- C58: 隔離した誤出力(同じ署名の別の呼出し先・名前付き実引数の取り違え・UFCS の受け手の誤対応・input の誤配線)は型検査を通るが接続検査に失敗する
        let (ib, ia) := inputBinders inputs
        let callWrongs ← deriveWrongs "Model (calls and inputs)" callModelText Naru.Backend.Model.leanName callMistranslations
        checkWrong "Model (calls and inputs)" (outDir / "CallModelWrong.lean") (callWrongProgram ib ia fns callWrongs) callWrongs lpCall ["different_sharedInputs"]
        checkCallEvidence ib ia fns lpCall
        checkCallSpecEvidence ib ia specs cprog lpCall
  heading "C45 the audit rejects forbidden dependencies"
  let negatives : List (String × String × String) :=
    [ ("sorry", "theorem bad : (1 : Nat) = 1 := sorry\n#audit_axioms bad\n", "sorryAx"),
      -- `native_decide` は Lean 4.34 では定理ごとの補助公理 `<名前>._native.native_decide.ax_*`(`Lean.ofReduceBool` を内包)に依存する
      ("native_decide", "theorem viaNative : (2 : Nat) + 2 = 4 := by native_decide\n#audit_axioms viaNative\n", "native_decide"),
      ("missing", "#audit_axioms NaruSem.thisTheoremDoesNotExist\n", "unknown") ]
  for (name, body, expectedText) in negatives do
    let f := outDir / s!"Audit_{name}.lean"
    IO.FS.writeFile f ("import NaruSem.Audit\n" ++ body)
    let r ← step s!"C45: {name}: lean {f} must fail" "lean" #[f.toString] (expectExit := 1) (env := #[("LEAN_PATH", some leanPath)])
    if r.exitCode != 0 && (contains r.stdout expectedText || contains r.stderr expectedText) then
      ok s!"C45: the audit rejects `{name}` (mentions `{expectedText}`)"
    else fail s!"C45: the audit did not reject `{name}` with `{expectedText}`: exit {r.exitCode}\n{tail r.stdout 800}\n{tail r.stderr 800}"
  IO.println s!"semantics: total {← elapsed t0}"

def run : IO UInt32 := runGroup "naru_test semantics" checks

end NaruTest.Semantics
