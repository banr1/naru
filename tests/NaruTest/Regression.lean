import Naru
import NaruTest.Common
import NaruTest.Grammar
import NaruTest.Zed
import NaruTest.Lsp
import NaruTest.Golden
import NaruTest.Statements
import NaruTest.Repo

/-!
# `naru_test regression` — 非対話の回帰・最終検証の入口(IDEAL.md C36)

リポジトリのルートで `lake exe naru_test regression` と実行する(約 12 分。末尾の C10 の golden(horizon 100)が約 9 分)。
`/tmp` のスクリプトや過去の端末出力に頼らず、この 1 コマンドが次を順に走らせ、1 つでも期待と違えば `FAIL:` を出して exit 1。
出力は段ごとに `== 段` の見出しと `ok:` / `FAIL:`(所要秒つき)。一時ファイルは `.lake/naru/test/regression/`(追跡対象外)。

1. compiler / naru_test のビルド(`lake build naru naru_test`)。
2. 受理例 `tests/accept/*.naru` の `naru compile`(exit 0)と、反例 `tests/reject/*.naru` の `naru check-reject`(先頭コメントが名指しする E 番号)。
3. C35: 全反例で `compile <file>`(出力指定なし)と `compile --out <dir> <file>` がともに exit 1 で同じ診断を出し、`--out` には何も書かれない
   (生成に進まない)。行末に `// E0dd` の印のある反例(`tests/reject/prop_as_value.naru`(先頭は `truthLost`。量化・spec 宣言の呼出し・Prop に
   束ねた局所名の、fn / メソッドの実引数・コレクションの要素・record の欄・lambda の戻り値・scrutinee への流入と、Prop の条件で選ぶ値)と
   `tests/reject/type_name_as_value.naru`(型別名 `Count` の値使用、`Count \{}` / `Nat \{ … }` のレコードリテラル))は、印の (行, E 番号) の集合と
   診断の集合が一致する(LSP が同じ箇所に返すことは `lsp` 群が CLI と照合する)。Core の健全性: 全受理例と各ソースルートを検査して診断 0 で、
   生成対象 Core の全宣言を再帰的に走査して `.unknown` / 型メタ変数 / エラー用ノードが 0 件。
4. `grammar`(C16)/ `zed`(C17)/ `lsp`(C18。受理例の `didOpen` で診断 0 件を含む)の各群と、golden の短い予行(`--finality-horizon 40`)。
5. C1 の決定性: `lake exe naru compile` を 2 回走らせ、生成先の全ファイルの sha256 が一致、各ファイルの先頭 5 行にコンパイラ版・stdlib 版・
   ソースの hash があり、ソースのパスがソースルートからの相対(ルートのディレクトリ名で始まらない)で、各ソースの sha256 がヘッダと一致。
6. `lake build Model`(C6。`noncomputable` / `unsafe` / `axiom` / `sorry` / `partial` が 0 件)、`lake build Statements`(C8。`sorry` 0 件)、
   `statements` 群(C8 の依存境界 / C9 の claim surface)。
7. 受理例ごとに `--out` へ生成して生成 Lean を型検査(Model の olean → Statements)。生成ファイルは `<lib>/<モジュールのパス>.lean` で、
   宣言は `<lib>.<モジュール名>.*`(モジュール名の一般規則、C37)。`tests/accept/guard_shadow.naru` は C34 の検体、`tests/accept/prop_bool.naru` は
   C35 の検体: 生成した Model / Statements を import する検査プログラム(`semanticsProgram`。期待結果は `c34Values` / `c34Props` / `c34Equations`、
   `c35Values` / `c35Props` / `c35Equations`)を `lean --run` し、実際の戻り値の行が期待とすべて一致し、命題の真偽(真になる入力と、偽になる
   対照入力の否定)を Lean kernel が `example` で検査する。
   `tests/accept/legacy_module_name.naru` は C37 の検体: 移植ソースの改名前と同じ形の利用者モジュール名が、特別扱いなしに同じ規則で
   `Model/` と `Statements/` の両方に生成され、ルートの集約ファイルが import する。
8. C37 の改名: 改名前の最後の commit(`c37BaseCommit`)のソースルートを `git archive` で取り出して現在のコンパイラで `--out` に生成し、
   現在のソースの生成物と、生成パスの集合と各ファイルのヘッダ以下の内容(宣言・import・本体)がモジュール名の置換を除いて一致する
   ことを照合する。現在の生成物のパス・内容に改名前の名前が無い。
9. C7 の simulate: ソースルート配下の scenario を持つ全ファイルの `naru simulate`(exit 0。`basic.naru` の出力に time / node / confirmed /
   stable / finalized)、ルート外のファイルと scenario の無いファイルは exit 2、C26(simulate の後の生成先のファイル集合が直前の `naru compile` の
   出力と一致する(runner・一時ファイルが無い)、`git status --porcelain --ignored` に compile の出力の外の追跡対象外・ignore の項目が無い、
   `.gitignore` に `Simulate` の行が無い、runner は `.lake/naru/simulate/Simulate.lean`)。
10. C7 / C24 / C26 の設定変更: 設定変更プロジェクト `tests/config_change/`(`naru.toml` は `sources = ["src"]`・`generated = "generated"`、
    `src/Counter.naru` の observer `current()` が fn `value()` の値を表示する)の複製(`.lake/naru/test/regression/c7/`)を cwd にして
    `<ルート>/.lake/build/bin/naru simulate src/Counter.naru` を走らせる: 既定の生成先・値 1(`current() = 1`)→ `generated = "custom"`・値 2 で、
    古い `generated/` とビルドキャッシュが残る場合と、設定した生成先だけが存在する場合(値 1 に戻してから `generated/` を消す)の双方で
    `current() = 2` を表示して exit 0(C7)。`custom/` は再生成した `naru compile` の出力と sha256 まで一致し、プロジェクトに runner・一時ファイルが無く、
    runner はルートの `.lake/naru/simulate/Simulate.lean` のまま(C26)。Lake が読む生成ソースの link `.lake/naru/generated` が `custom/` を指し、
    ルートの `lake build Model Statements` が exit 0 で、その実行ファイルが `current() = 2` を表示する(C24: lakefile の手修正なし)。
    現在のソースを不正にすると exit 1(E011)で observer の行を表示せず、`custom/` も書き換えない(C7)。最後にルートの `naru compile` で
    link をルートの生成先に戻して `lake build Model Statements`。
11. C24: `compiler/` にソースルートのディレクトリ名の直書きが無い、`naru.toml` の `sources` を別名のコピーに向けても生成先の sha256 が一致
    (`naru.toml` は必ず元に戻し、`git diff --exit-code` で確かめる)。
12. `repo` 群(C21 / C23 / C25 / C37 の旧名検索)、C28 / C22 / C27。
13. C10: `golden`(引数なし = horizon 100、全 16 ケース)。

`zed-install`(C19。人間の Zed を操作する)と C20(画面観測)は非対話回帰に入れない(IDEAL.md C36)。
-/

namespace NaruTest.Regression

def workDir : System.FilePath := ".lake" / "naru" / "test" / "regression"
def acceptDir : System.FilePath := "tests" / "accept"
def rejectDir : System.FilePath := "tests" / "reject"
def compilerDir : System.FilePath := "compiler"

/-! ## 補助 -/

def heading (title : String) : M Unit := IO.println s!"== {title}"

def elapsed (start : Nat) : IO String := do
  let now ← IO.monoMsNow
  let ms := now - start
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

/-- 別の群を同じプロセスで走らせ、その PASS / FAIL を 1 項目にする。 -/
def subgroup (label : String) (run : IO UInt32) : M Unit := do
  let t ← IO.monoMsNow
  IO.println s!"-- {label}"
  let code ← run
  if code == 0 then ok s!"{label}: PASS ({← elapsed t})" else fail s!"{label}: FAIL (exit {code})"

/-- ディレクトリ配下の全ファイル(パス順)。 -/
def allFiles (dir : System.FilePath) : IO (List String) := do
  if !(← dir.isDir) then return []
  let all ← dir.walkDir
  let mut out : Array String := #[]
  for p in all do
    if !(← p.isDir) then out := out.push p.toString
  return (out.qsort (· < ·)).toList

/-- ディレクトリ配下の全ファイルの (パス, sha256)。 -/
def shaSnapshot (dir : System.FilePath) : IO (List (String × String)) := do
  (← allFiles dir).mapM fun (f : String) => do
    let bytes ← IO.FS.readBinFile (System.FilePath.mk f)
    return (f, Naru.sha256Hex bytes)

def contains (s : String) (sub : String) : Bool := (s.splitOn sub).length > 1

/-- `<root>/` の接頭辞。 -/
def prefixOf (root : System.FilePath) : String :=
  let r := root.toString
  if r.endsWith "/" then r else r ++ "/"

/-! ## C34 の検体の期待結果(`tests/accept/guard_shadow.naru`) -/

def c34Source : String := (acceptDir / "guard_shadow.naru").toString
def c34Module : String := "Accept.GuardShadow"

/-- 実際の戻り値: (表示ラベル, Lean の式, 期待する表示)。検査プログラムは `ラベル = 値` の行を表示し、期待の行と照合する。
IDEAL.md C34 の必須: `runtimeShadow(0, 7) = true`、`fuelShadow(0, 7) = 7`。 -/
def c34Values : List (String × String × String) :=
  [ ("runtimeShadow(0, 7)", "runtimeShadow 0 7", "true"),
    ("runtimeShadow(7, 0)", "runtimeShadow 7 0", "false"),
    ("letShadow(7)", "letShadow 7", "true"),
    ("scrutShadow(7)", "scrutShadow 7", "7"),
    ("multiShadow(5, 7)", "multiShadow 5 7", "5"),
    ("fuelShadow(0, 7)", "fuelShadow 0 7", "7"),
    ("fuelShadow(101, 7)", "fuelShadow 101 7", "101"),
    ("fuelMulti(0, 7)", "fuelMulti 0 7", "7"),
    ("fuelMulti(150, 7)", "fuelMulti 150 7", "0"),
    ("shadowValues()", "shadowValues", "[1, 1, 7, 5, 7, 101, 7, 0]") ]

/-- 命題の真偽(Lean kernel が `example` で検査する): (命題, tactic)。真になる入力と、偽になる対照入力の否定。
IDEAL.md C34 の必須: `specShadow(0, 7)` が真。 -/
def c34Props : List (String × String) :=
  [ ("specShadow 0 7", "unfold specShadow; decide"),
    ("¬ specShadow 7 0", "unfold specShadow; decide"),
    ("specBody 0 7", "unfold specBody; decide"),
    ("¬ specBody 7 0", "unfold specBody; decide"),
    ("specMulti 5 7", "unfold specMulti; decide"),
    ("¬ specMulti 5 1", "unfold specMulti; decide"),
    ("specLead 0 (some 7)", "unfold specLead; decide"),
    ("specLead 0 none", "unfold specLead; decide"),
    ("¬ specLead 7 (some 0)", "unfold specLead; decide"),
    ("specLet 7", "unfold specLet; decide"),
    ("specScrut 7", "unfold specScrut; decide") ]

/-- 戻り値の等式(Lean kernel が検査する): (等式, tactic)。再帰 fn は等式補題で展開する。 -/
def c34Equations : List (String × String) :=
  [ ("runtimeShadow 0 7 = true", "decide"),
    ("runtimeShadow 7 0 = false", "decide"),
    ("letShadow 7 = true", "decide"),
    ("scrutShadow 7 = 7", "decide"),
    ("multiShadow 5 7 = 5", "decide"),
    ("fuelShadow 0 7 = 7", "simp [fuelShadow]"),
    ("fuelShadow 101 7 = 101", "simp [fuelShadow]"),
    ("fuelMulti 0 7 = 7", "simp [fuelMulti]"),
    ("fuelMulti 150 7 = 0", "simp [fuelMulti]") ]

/-- 検査プログラム(生成した Model / Statements を import し、`example` と `main` で確かめる)。C34 / C35 の検体で共用。 -/
def semanticsProgram (label source module : String) (values : List (String × String × String))
    (props eqs : List (String × String)) : String :=
  let examples := (props ++ eqs).map fun (p, tac) => s!"example : {p} := by {tac}\n"
  let prints := values.map fun (l, expr, _) => s!"  IO.println s!\"{l} = \{{expr}}\"\n"
  s!"-- naru_test regression ({label}): generated from NaruTest/Regression.lean. Imports the Model / Statements generated from {source}.\n" ++
  s!"import Model.{module}\nimport Statements.{module}\n\nopen Model.{module}\nopen Statements.{module}\n\n" ++
  "-- 命題の真偽と戻り値の等式(Lean kernel が検査する)\n" ++ "".intercalate examples ++
  "\n-- 実際の戻り値(表示して期待の行と照合する)\ndef main : IO Unit := do\n" ++ "".intercalate prints

def expectedLines (values : List (String × String × String)) : List String := values.map fun (l, _, v) => s!"{l} = {v}"

/-- 検査プログラムを `--out` のディレクトリで `lean --run` し、戻り値の行が期待とすべて一致して余計な行が無く、`example` がすべて
通る(exit 0)ことを確かめる。 -/
def runSemantics (label source module : String) (outAbs : System.FilePath) (lp : String)
    (values : List (String × String × String)) (props eqs : List (String × String)) : M Unit := do
  IO.FS.writeFile (outAbs / "Check.lean") (semanticsProgram label source module values props eqs)
  let r ← step s!"{label}: lean --run Check.lean" "lean" #["--run", "Check.lean"] (cwd := some outAbs) (env := #[("LEAN_PATH", some lp)])
  let lines := (r.stdout.splitOn "\n").filter (!·.isEmpty)
  let want := expectedLines values
  let mut good := true
  for e in want do
    if lines.contains e then ok s!"{label}: {e}"
    else
      good := false
      fail s!"{label}: expected `{e}`, got {lines.filter fun l => l.startsWith ((e.splitOn " = ").head!)}"
  let extra := lines.filter fun l => !want.contains l
  if !extra.isEmpty then
    good := false
    fail s!"{label}: unexpected output lines {extra}"
  if good && r.exitCode == 0 then
    ok s!"{label}: {values.length} return values agree, {props.length} propositions and {eqs.length} equations checked by the Lean kernel ({source})"

/-! ## C35 の検体: Prop / Bool の境界・型名の値使用・Core の健全性 -/

/-- 反例: Prop 相当の式(量化・spec 宣言の呼出し・Prop に束ねた局所名)の値の位置への流入(先頭は `truthLost`)。 -/
def c35PropSource : String := (rejectDir / "prop_as_value.naru").toString
/-- 反例: 型別名の値使用(`Count`)と、record でない型へのレコードリテラル(`Count \{}`)。 -/
def c35TypeSource : String := (rejectDir / "type_name_as_value.naru").toString
/-- 受理例: 論理式・量化・Prop と値の let・Prop の if / match・型別名の正常な使用。 -/
def c35AcceptSource : String := (acceptDir / "prop_bool.naru").toString
def c35Module : String := "Accept.PropBool"

/-- C35 の受理例の実際の戻り値(表示ラベル, Lean の式, 期待する表示)。 -/
def c35Values : List (String × String × String) :=
  [ ("within(fresh(1))", "within (fresh 1)", "true"),
    ("bump(fresh(1)).count", "(bump (fresh 1)).count", "2"),
    ("total([fresh(1), fresh(2)])", "total [fresh 1, fresh 2]", "3"),
    ("allWithin([fresh(1), fresh(11)])", "allWithin [fresh 1, fresh 11]", "false"),
    ("tallyValues()", "tallyValues", "[1, 2, 3, 0]") ]

/-- C35 の受理例の命題の真偽(真になる入力と、偽になる対照入力の否定)。量化は `intro` / `omega` / `exact ⟨…⟩` で、量化しないものは
`unfold` → `decide` で Lean kernel が検査する(`native_decide` / `sorry` 不使用)。 -/
def c35Props : List (String × String) :=
  [ ("Bounded (fresh 1)", "unfold Bounded; decide"),
    ("¬ Bounded (fresh 11)", "unfold Bounded; decide"),
    ("UpTo 10", "unfold UpTo; intro n h; omega"),
    ("¬ UpTo 11", "unfold UpTo; intro h; have := h 10 (by omega); omega"),
    ("Reaches 5", "unfold Reaches; exact ⟨4, rfl⟩"),
    ("¬ Reaches 0", "unfold Reaches; intro ⟨n, h⟩; omega"),
    ("Mixed (fresh 1)", "unfold Mixed Bounded; decide"),
    ("¬ Mixed (fresh 11)", "unfold Mixed Bounded; decide"),
    ("SameTruth (fresh 1)", "unfold SameTruth Bounded; decide"),
    ("¬ SameTruth (Tally.mk 5 3)", "unfold SameTruth Bounded; decide"),
    ("DiffTruth (Tally.mk 5 3)", "unfold DiffTruth Bounded; decide"),
    ("¬ DiffTruth (fresh 1)", "unfold DiffTruth Bounded; decide"),
    ("LetBoth (fresh 1)", "unfold LetBoth Bounded; decide"),
    ("¬ LetBoth (fresh 11)", "unfold LetBoth Bounded; decide"),
    ("IfProp (fresh 1)", "unfold IfProp Bounded; decide"),
    ("¬ IfProp (Tally.mk 5 3)", "unfold IfProp Bounded; decide"),
    ("IfBool (fresh 1)", "unfold IfBool Bounded; decide"),
    ("¬ IfBool (Tally.mk 11 20)", "unfold IfBool Bounded; decide"),
    ("GuardProp (fresh 1) (some 5)", "unfold GuardProp Bounded; decide"),
    ("GuardProp (fresh 1) none", "unfold GuardProp Bounded; decide"),
    ("¬ GuardProp (Tally.mk 5 3) (some 7)", "unfold GuardProp Bounded; decide"),
    ("ValuesOk [fresh 1, fresh 2]", "unfold ValuesOk; decide"),
    ("¬ ValuesOk [fresh 1, fresh 11]", "unfold ValuesOk; decide") ]

def c35Equations : List (String × String) :=
  [ ("within (fresh 1) = true", "decide"),
    ("(bump (fresh 1)).count = 2", "decide"),
    ("total [fresh 1, fresh 2] = 3", "decide"),
    ("allWithin [fresh 1, fresh 11] = false", "decide") ]

/-- 反例の行末の `// E0dd`(コードの後ろのコメント)が印す期待: (1 始まりの行, E 番号)。先頭のコメント行(コードの無い行)は印ではない。 -/
def markedDiagnostics (text : String) : List (Nat × String) := Id.run do
  let mut out : List (Nat × String) := []
  let mut i := 1
  for l in text.splitOn "\n" do
    let parts := l.splitOn "//"
    if parts.length ≥ 2 then
      let code := parts.head!
      let comment := (parts.getLast!).trimAscii.toString
      if !code.trimAscii.toString.isEmpty then
        if let some c := NaruTest.Lsp.firstCode comment then
          if comment.startsWith c then out := out ++ [(i, c)]
    i := i + 1
  return out

/-- CLI の標準エラーの診断行 `file:line:col: error[E0dd]: …` → (行, 列, E 番号)。 -/
def parseDiags (stderr : String) : List (Nat × Nat × String) :=
  (stderr.splitOn "\n").filterMap fun l =>
    if !(contains l ": error[") then none
    else
      let parts := l.splitOn ":"
      match parts[1]?.bind (·.trimAscii.toString.toNat?), parts[2]?.bind (·.trimAscii.toString.toNat?),
            NaruTest.Lsp.firstCode ((l.splitOn ": error[").getLast!) with
      | some line, some col, some code => some (line, col, code)
      | _, _, _ => none

def sortMarks (xs : List (Nat × String)) : List (Nat × String) :=
  xs.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- 3. C35 の反例: 全反例で `compile <file>`(出力指定なし)と `compile --out <dir> <file>` がともに exit 1 で同じ診断を出し、`--out` には
何も書かれない(生成に進まない)。行末に `// E0dd` の印のある反例は、印の (行, 番号) の集合と診断の (行, 番号) の集合が一致する
(`naru_test lsp` が LSP の診断を CLI と照合するので、LSP も同じ箇所に返す)。 -/
def checkRejectDiagnostics : M Unit := do
  heading "C35 reject diagnostics (CLI with / without --out, marked lines)"
  let rejects ← Naru.listFiles rejectDir "naru"
  let mut nMarked := 0
  for f in rejects do
    let name := ((System.FilePath.mk f).fileStem).getD f
    let out := workDir / "reject" / name
    if ← out.isDir then IO.FS.removeDirAll out
    let r1 ← step s!"reject {name}: compile (no output)" "lake" #["exe", "naru", "compile", f] (expectExit := 1)
    let r2 ← step s!"reject {name}: compile --out" "lake" #["exe", "naru", "compile", "--out", out.toString, f] (expectExit := 1)
    let d1 := parseDiags r1.stderr
    let d2 := parseDiags r2.stderr
    if !d1.isEmpty && d1 == d2 then ok s!"reject {name}: {d1.length} diagnostic(s), identical with and without --out"
    else fail s!"reject {name}: diagnostics differ or are empty: without --out {d1}, with --out {d2}"
    let written ← allFiles out
    if written.isEmpty then ok s!"reject {name}: --out {out} received no file (generation did not run)"
    else fail s!"reject {name}: --out wrote {written.take 5}"
    let marks := markedDiagnostics (← IO.FS.readFile f)
    if !marks.isEmpty then
      nMarked := nMarked + 1
      let got := sortMarks (d1.map fun (l, _, c) => (l, c)).eraseDups
      let want := sortMarks marks.eraseDups
      if got == want then ok s!"reject {name}: the diagnostics are exactly the marked lines {want.map (·.1)} ({(want.map (·.2)).eraseDups})"
      else fail s!"reject {name}: marked {want} vs reported {got}"
  for f in [c35PropSource, c35TypeSource] do
    if !rejects.contains f then fail s!"C35: {f} is missing"
  if nMarked ≥ 2 then ok s!"C35: {nMarked} reject file(s) carry line marks and match them"
  else fail s!"C35: expected at least 2 reject files with line marks, found {nMarked}"

/-- 3'. Core の健全性(C35): 全受理例(単独の単位)と各ソースルート(1 単位)を `compileFiles` で検査し、診断が無く、生成対象 Core の
全宣言を再帰的に走査して `.unknown` / 型メタ変数 / エラー用ノードが 0 件(`Core.Module.unsound`)。 -/
def checkCoreSoundness (roots : List System.FilePath) : M Unit := do
  heading "C35 Core soundness (no .unknown / metavariable / error node)"
  let mut units : List (String × List String) := []
  for f in (← Naru.listFiles acceptDir "naru") do units := units ++ [(f, [f])]
  for r in roots do units := units ++ [(s!"source root {r}", ← Naru.listFiles r "naru")]
  let mut total := 0
  for (label, files) in units do
    let (diags, checked) ← Naru.compileFiles files
    if !diags.isEmpty then
      fail s!"C35: {label}: {diags.size} diagnostic(s) (expected a clean unit)"
      continue
    let issues := checked.core.toList.flatMap fun (m : Naru.Core.Module) => m.unsound
    let nDecls := checked.core.toList.foldl (init := 0) fun n (m : Naru.Core.Module) => n + m.decls.size
    total := total + nDecls
    if nDecls == 0 then fail s!"C35: {label}: no Core declaration"
    else if issues.isEmpty then ok s!"C35: {label}: {nDecls} Core declaration(s) walked, 0 unsound node(s)"
    else fail s!"C35: {label}: unsound Core: {issues.take 5}"
  if total > 0 then ok s!"C35: {total} Core declarations across {units.length} units are sound"
  else fail "C35: no Core declaration walked"

/-! ## C37 の検体: 改名前後の宣言構造と、モジュール名の一般規則 -/

/-- 移植ソースの spec 側が改名前のディレクトリにあった最後の commit(周回 33 の改名の直前の HEAD)。この commit のソースルートを
`git archive` で取り出し、現在のコンパイラで `--out` に生成して、現在のソースの生成物とモジュール名の置換(`c37OldMod` → `c37NewMod`、
`c37OldDir` → `c37NewDir`)を除いて照合する。移植ソースの宣言を正当に変える周回は、この基準をその変更の直前の commit に進める。 -/
def c37BaseCommit : String := "8e7eed5a6676cd19f24ea1b2cbc7255fbf4c7589"
def c37NewDir : String := "Consensus/Spec"
def c37NewMod : String := "Consensus.Spec"
/-- 改名前の名前。この検査自身が旧名の検索(`naru_test repo`)に掛からないよう連結で作る。 -/
def c37OldDir : String := "Consensus/" ++ "Statements"
def c37OldMod : String := "Consensus." ++ "Statements"
/-- 一般規則の検体: 改名前と同じ形の利用者モジュール名を持つ受理例(意図的な旧名。`naru_test repo` の旧名検索が除外する)。 -/
def c37LegacySource : String := (acceptDir / "legacy_module_name.naru").toString
def c37LegacyModule : String := c37OldMod ++ ".Legacy"

/-- 生成 Lean の宣言の行数(`def` / `structure` / `inductive` / `instance` / `abbrev` / `theorem` で始まる行)。 -/
def countDecls (c : String) : Nat :=
  ((c.splitOn "\n").filter fun l =>
    ["def ", "structure ", "inductive ", "instance ", "abbrev ", "theorem "].any (l.startsWith ·)).length

/-- 受理例の生成ファイルがモジュール名の一般規則に従う: `<lib>/<モジュールのパス>.lean` は、その受理例のモジュール `<名前>` のもので、
見出し行(naru module `<名前>`)と `<lib>.<名前>.` を接頭辞に持つ宣言を含む。 -/
def checkModuleRule (name : String) (src : String) (out : System.FilePath) : M Unit := do
  let (diags, checked) ← Naru.compileFiles [src]
  if !diags.isEmpty then
    fail s!"accept {name}: {diags.size} diagnostic(s) when reading its modules"
    return
  let modNames := checked.core.toList.map fun (m : Naru.Core.Module) => ".".intercalate m.name
  for sub in ["Model", "Statements"] do
    for f in (← Naru.listFiles (out / sub) "lean") do
      let rel := (f.drop ((out / sub).toString.length + 1)).toString
      let modName := ((rel.dropEnd ".lean".length).toString.replace "/" ".")
      let c ← IO.FS.readFile f
      if modNames.contains modName && contains c s!"/-! naru module `{modName}`" && contains c s!"{sub}.{modName}." then
        ok s!"accept {name}: {sub}/{rel} is naru module `{modName}` and declares `{sub}.{modName}.*`"
      else fail s!"accept {name}: {sub}/{rel} does not follow `<lib>/<module path>.lean` with `{sub}.<module>.*` declarations (modules of the source: {modNames})"
  if src == c37LegacySource then
    let relPath := System.FilePath.mk (c37LegacyModule.replace "." "/" ++ ".lean")
    for lib in ["Model", "Statements"] do
      let f := out / lib / relPath
      if ← f.pathExists then
        let c ← IO.FS.readFile f
        if contains c s!"def {lib}.{c37LegacyModule}." then
          ok s!"C37: {f} declares `{lib}.{c37LegacyModule}.*` (the general rule applies unchanged to a user module named like the old port)"
        else fail s!"C37: {f} has no `def {lib}.{c37LegacyModule}.`"
      else fail s!"C37: {f} is missing (the general rule must not special-case this module name)"
    let mroot ← IO.FS.readFile (out / "Model.lean")
    let sroot ← IO.FS.readFile (out / "Statements.lean")
    if contains mroot s!"import Model.{c37LegacyModule}\n" && contains sroot s!"import Statements.{c37LegacyModule}\n" then
      ok s!"C37: the root Model.lean / Statements.lean of {name} import `{c37LegacyModule}` under their prefixes"
    else fail s!"C37: the root Model.lean / Statements.lean of {name} do not import `{c37LegacyModule}`"

/-- 8. C37: 改名前の commit のソースを現在のコンパイラで生成し、現在の生成物とモジュール名の置換を除いて照合する。 -/
def checkRenameStructure (roots : List System.FilePath) : M Unit := do
  heading "C37 rename: declaration structure modulo module names"
  let some root := roots.head? | fail "C37: naru.toml lists no source root"; return
  let dir := workDir / "c37"
  if ← dir.isDir then IO.FS.removeDirAll dir
  IO.FS.createDirAll (dir / "old")
  let tar := dir / "old.tar"
  let _ ← step s!"C37: git archive {c37BaseCommit.take 7} {root}" "git" #["archive", "--format=tar", "-o", tar.toString, c37BaseCommit, root.toString]
  let _ ← step "C37: extract the archive" "tar" #["-xf", tar.toString, "-C", (dir / "old").toString]
  let oldRoot := dir / "old" / root
  let oldFiles ← Naru.listFiles oldRoot "naru"
  let newFiles ← Naru.listFiles root "naru"
  if oldFiles.isEmpty then
    fail s!"C37: no .naru under {oldRoot}"
    return
  let oldSpec := oldFiles.filter fun f => contains f (c37OldDir ++ "/")
  let newSpec := newFiles.filter fun f => contains f (c37NewDir ++ "/")
  if !oldSpec.isEmpty && oldSpec.length == newSpec.length then
    ok s!"C37: {oldSpec.length} spec source files under {c37OldDir}/ before and under {c37NewDir}/ after the rename"
  else fail s!"C37: {oldSpec.length} spec source files under {c37OldDir}/ before vs {newSpec.length} under {c37NewDir}/ after"
  let oldGen := dir / "old-gen"
  let newGen := dir / "new-gen"
  let _ ← step "C37: compile the base commit's sources with the current compiler" "lake" (#["exe", "naru", "compile", "--out", oldGen.toString] ++ oldFiles.toArray)
  let _ ← step "C37: compile the current sources" "lake" (#["exe", "naru", "compile", "--out", newGen.toString] ++ newFiles.toArray)
  let oldPrefix := prefixOf (dir / "old")
  let normalize (s : String) : String := ((s.replace oldPrefix "").replace c37OldMod c37NewMod).replace c37OldDir c37NewDir
  let body (c : String) : String := "\n".intercalate ((c.splitOn "\n").drop 5)
  let relOf (base : System.FilePath) (f : String) : String := (f.drop (prefixOf base).length).toString
  let oldOut ← allFiles oldGen
  let newOut ← allFiles newGen
  let oldRels := (oldOut.map fun f => normalize (relOf oldGen f)).mergeSort (· ≤ ·)
  let newRels := (newOut.map (relOf newGen ·)).mergeSort (· ≤ ·)
  if !newRels.isEmpty && oldRels == newRels then
    ok s!"C37: the same {newRels.length} generated paths before and after (substituting {c37OldDir} → {c37NewDir})"
  else
    let onlyOld := oldRels.filter (!newRels.contains ·)
    let onlyNew := newRels.filter (!oldRels.contains ·)
    fail s!"C37: generated paths differ: only before {onlyOld.take 5}, only after {onlyNew.take 5}"
  let mut differ : List String := []
  let mut compared := 0
  for f in oldOut do
    let rel := normalize (relOf oldGen f)
    let newPath := newGen / rel
    if !(← newPath.pathExists) then continue
    compared := compared + 1
    let a := normalize (body (← IO.FS.readFile f))
    let b := body (← IO.FS.readFile newPath)
    if a != b then differ := differ ++ [rel]
  if compared > 0 && differ.isEmpty then
    ok s!"C37: {compared} generated files are identical below the 5-line header after substituting {c37OldMod} → {c37NewMod} (imports, declarations, bodies)"
  else fail s!"C37: generated files differ beyond the module names ({differ.length}): {differ.take 10}"
  -- 宣言数(spec 側のモジュールの Model / Statements)
  let mut nModel := 0
  let mut nStmt := 0
  for f in newOut do
    let rel := relOf newGen f
    if rel.startsWith s!"Model/{c37NewDir}/" then nModel := nModel + countDecls (← IO.FS.readFile f)
    if rel.startsWith s!"Statements/{c37NewDir}/" then nStmt := nStmt + countDecls (← IO.FS.readFile f)
  if nStmt > 0 then ok s!"C37: the {c37NewDir} modules generate {nStmt} Statements declaration(s) and {nModel} Model declaration(s) (same as before the rename, by the comparison above)"
  else fail s!"C37: no Statements declaration under Statements/{c37NewDir}/"
  -- 現在の生成物に旧名が無い
  let mut hits : List String := []
  for f in newOut do
    if contains f c37OldDir then hits := hits ++ [f]
    else if contains (← IO.FS.readFile f) c37OldMod then hits := hits ++ [f]
  if hits.isEmpty then ok s!"C37: no generated path or content of the current sources mentions {c37OldDir} / {c37OldMod} ({newOut.length} files)"
  else fail s!"C37: old names in the current generated output: {hits.take 10}"

/-! ## C7 / C24 / C26 の検体: 設定変更プロジェクト(`tests/config_change/`) -/

/-- 設定変更プロジェクト: `naru.toml`(`sources = ["src"]`、`generated = "generated"`)と `src/Counter.naru`(fn `value()` の値を observer
`current()` が表示する scenario `counter` と spec 宣言 1 つ)。回帰は複製を `.lake/naru/test/regression/c7/` に作り、その複製を cwd にして
`<ルート>/.lake/build/bin/naru` を直接呼ぶ(`naru.toml` は cwd のもの、stdlib・Lake・実行入口・link はホーム = ルートのもの)。 -/
def c7Fixture : System.FilePath := "tests" / "config_change"
def c7Project : System.FilePath := workDir / "c7"
def c7Source : String := "src/Counter.naru"
/-- 値を決める行(回帰がこの行の 1 を 2 に書き換える)。 -/
def c7ValueLine (n : Nat) : String := s!"fn value() -> Nat \{ {n} }"
/-- `naru simulate` の出力に現れる observer の行。 -/
def c7Observed (n : Nat) : String := s!"current() = {n}"
/-- Lake が読む生成ソース(lakefile の lean_lib `Model` / `Statements` の `srcDir`)。`naru compile` / `simulate` が有効な生成先への symlink にする。 -/
def lakeGeneratedLink : System.FilePath := ".lake" / "naru" / "generated"

/-- `naru.toml` の `generated` の行を書き換える(コメントは触らない)。 -/
def setGenerated (text : String) (dir : String) : String :=
  "\n".intercalate ((text.splitOn "\n").map fun l =>
    if l.trimAscii.toString.startsWith "generated" then s!"generated = \"{dir}\"" else l)

/-- 値の行を `a` から `b` に書き換える。 -/
def setValue (text : String) (a b : Nat) : String := text.replace (c7ValueLine a) (c7ValueLine b)

/-- 10. C7 / C24 / C26 の設定変更回帰(docstring の 10)。設定変更プロジェクトの複製で、既定の生成先・値 1 → `generated = "custom"`・値 2 を、
古い既定の生成先とビルドキャッシュが残る場合と設定した生成先だけが存在する場合の双方で `naru simulate` し(observer が 2、exit 0)、`custom/` が
再生成した `compile` の出力と一致して runner・一時ファイルを含まず、runner はルートの `.lake/naru/simulate/Simulate.lean` のまま(C26)、Lake が
読む生成ソースの link が `custom/` を指してルートの `lake build Model Statements` が exit 0、その実行ファイルが 2 を表示し(C24)、ソースを不正に
すると exit 1 で observer の行を表示しない(C7)。最後にルートの生成先に戻す。 -/
def checkGeneratedDirChange (generated : System.FilePath) : M Unit := do
  heading "C7 / C24 / C26 generated-dir change (tests/config_change)"
  let root ← IO.FS.realPath "."
  let naruBin := (root / ".lake" / "build" / "bin" / "naru").toString
  let simBin := (root / ".lake" / "build" / "bin" / "naru_simulate").toString
  if ← c7Project.isDir then IO.FS.removeDirAll c7Project
  IO.FS.createDirAll workDir
  let _ ← step "C7: copy the config-change project" "cp" #["-R", c7Fixture.toString, c7Project.toString]
  let proj ← IO.FS.realPath c7Project
  let srcPath := proj / c7Source
  let cfgPath := proj / "naru.toml"
  let src0 ← IO.FS.readFile srcPath
  if contains src0 (c7ValueLine 1) then ok s!"C7: {c7Fixture}/{c7Source} has the line `{c7ValueLine 1}`"
  else fail s!"C7: {c7Fixture}/{c7Source} lacks the line `{c7ValueLine 1}`"
  let cfg0 ← IO.FS.readFile cfgPath
  let cfgLines := (cfg0.splitOn "\n").map (·.trimAscii.toString)
  if cfgLines.contains "sources = [\"src\"]" && cfgLines.contains "generated = \"generated\"" then
    ok s!"C7: {c7Fixture}/naru.toml has sources = [\"src\"] and generated = \"generated\""
  else fail s!"C7: {c7Fixture}/naru.toml must have `sources = [\"src\"]` and `generated = \"generated\"`"
  let gen := proj / "generated"
  let custom := proj / "custom"
  let setup (value : Nat) (dir : String) : IO Unit := do
    IO.FS.writeFile srcPath (setValue src0 1 value)
    IO.FS.writeFile cfgPath (setGenerated cfg0 dir)
  let simulate (label : String) (expectExit : UInt32) : M IO.Process.Output :=
    step label naruBin #["simulate", c7Source] expectExit (cwd := some proj)
  let expectValue (label : String) (out : String) (n other : Nat) : M Unit := do
    if contains out (c7Observed n) && !(contains out (c7Observed other)) then
      ok s!"{label}: prints `{c7Observed n}` and not `{c7Observed other}`"
    else fail s!"{label}: expected `{c7Observed n}` without `{c7Observed other}`\n{tail out 600}"
  let expectLink (label : String) (want : System.FilePath) : M Unit := do
    try
      let t ← IO.FS.realPath lakeGeneratedLink
      if t == want then ok s!"{label}: {lakeGeneratedLink} -> {want}"
      else fail s!"{label}: {lakeGeneratedLink} -> {t} (expected {want})"
    catch e => fail s!"{label}: {lakeGeneratedLink} is missing or dangling ({e})"
  -- 1. 既定の生成先、値 1(ビルドキャッシュと実行ファイルは値 1 になる)
  let r1 ← simulate "C7: simulate (generated = \"generated\", value 1)" 0
  expectValue "C7 baseline" r1.stdout 1 2
  if ← (gen / "Model" / "Counter.lean").pathExists then ok s!"C7: {gen}/Model/Counter.lean generated"
  else fail s!"C7: {gen}/Model/Counter.lean is missing"
  expectLink "C24 after the baseline" gen
  let genSnapshot ← shaSnapshot gen
  -- 2. 値 2・generated = "custom": 古い既定の生成先(値 1)とビルドキャッシュ(値 1 の Model / 実行ファイル)が残る
  setup 2 "custom"
  let r2 ← simulate "C7: simulate (generated = \"custom\", value 2; the old generated/ and the build cache remain)" 0
  expectValue "C7 with the old default dir and build cache left" r2.stdout 2 1
  if (← shaSnapshot gen) == genSnapshot then ok s!"C7: the old {gen}/ is untouched (still the value-1 output; simulate wrote only custom/)"
  else fail s!"C7: {gen}/ changed although naru.toml points at custom/"
  if ← (custom / "Model" / "Counter.lean").pathExists then ok s!"C7: {custom}/Model/Counter.lean generated"
  else fail s!"C7: {custom}/Model/Counter.lean is missing"
  expectLink "C24 after switching to custom" custom
  -- 3. 既定の生成先・値 1 に戻す(ビルドキャッシュと実行ファイルを値 1 に戻す)
  setup 1 "generated"
  let r3 ← simulate "C7: simulate (back to generated = \"generated\", value 1: the build cache holds value 1 again)" 0
  expectValue "C7 back to the baseline" r3.stdout 1 2
  -- 4. 設定した生成先だけが存在する場合: 古い既定の生成先(と前の custom/)を消してから、値 2・custom
  IO.FS.removeDirAll gen
  if ← custom.isDir then IO.FS.removeDirAll custom
  setup 2 "custom"
  let r4 ← simulate "C7: simulate (generated = \"custom\", value 2; only the configured dir exists, the build cache held value 1)" 0
  expectValue "C7 with only the configured dir" r4.stdout 2 1
  if ← gen.pathExists then fail s!"C7: {gen}/ reappeared" else ok s!"C7: no {gen}/ (simulate writes only the configured generated dir)"
  -- C26: custom/ は再生成した compile の出力と一致し、runner・一時ファイルを含まない。runner はルートの .lake/naru/simulate のまま
  let s1 ← shaSnapshot custom
  let _ ← step "C26: naru compile in the project (regenerate custom/)" naruBin #["compile"] (cwd := some proj)
  let s2 ← shaSnapshot custom
  if !s1.isEmpty && s1 == s2 then ok s!"C26: after simulate, {custom}/ holds exactly the {s1.length} files naru compile writes (sha256 identical to a fresh compile)"
  else fail s!"C26: {custom}/ after simulate differs from a fresh compile: simulate {(s1.map (·.1)).take 5}, compile {(s2.map (·.1)).take 5}"
  let nonLean := (s1.map (·.1)).filter fun f => !f.endsWith ".lean"
  let runners := (← allFiles proj).filter fun f => (System.FilePath.mk f).fileName == some "Simulate.lean"
  if nonLean.isEmpty && runners.isEmpty then ok s!"C26: no runner / temporary file under {proj}/ (only .lean output)"
  else fail s!"C26: runner / temporary files under the project: {nonLean ++ runners}"
  let runner := root / ".lake" / "naru" / "simulate" / "Simulate.lean"
  if ← runner.pathExists then
    if contains (← IO.FS.readFile runner) "Model.Counter" then ok s!"C26: the runner is still {runner} and runs the project's scenario"
    else fail s!"C26: {runner} does not mention Model.Counter"
  else fail s!"C26: {runner} not found"
  -- C24: Lake が読む生成ソースは有効な生成先(custom/)で、Model / Statements がビルドでき、実行ファイルが現在の値を表示する
  expectLink "C24 effective generated dir" custom
  let _ ← step "C24: lake build Model Statements at the root (reads the project's custom/ through the link)" "lake" #["build", "Model", "Statements"]
  let rb ← step "C24: run the simulate binary built from the effective generated dir" simBin #[]
  expectValue "C24 binary" rb.stdout 2 1
  -- 5. 現在のソースを不正にする: 検査で止まり(exit 1)、古い実行ファイルを実行しない
  IO.FS.writeFile srcPath (setValue src0 1 2 ++ "\nfn broken() -> Nat { undefinedName }\n")
  let r5 ← simulate "C7: simulate with an invalid current source (exit 1)" 1
  if !(contains r5.stdout "current() =") && contains r5.stderr "error[E011]" then
    ok "C7: an invalid source stops before building / running (E011 reported, no observer line, the old binary is not run)"
  else fail s!"C7: invalid source: stdout {tail r5.stdout 300}, stderr {tail r5.stderr 300}"
  if (← shaSnapshot custom) == s2 then ok s!"C7: {custom}/ keeps the last good output (not rewritten by the failed run)"
  else fail s!"C7: {custom}/ changed after the failed run"
  -- 6. ルートの生成先に戻す
  let _ ← step "restore: lake exe naru compile (the link points back at the root's generated dir)" "lake" #["exe", "naru", "compile"]
  expectLink "C24 restored" (← IO.FS.realPath generated)
  let _ ← step "restore: lake build Model Statements" "lake" #["build", "Model", "Statements"]

/-! ## 段 -/

/-- 2. 受理例と反例。 -/
def checkAcceptReject : M Unit := do
  heading "accept / reject"
  let accepts ← Naru.listFiles acceptDir "naru"
  for f in accepts do
    let _ ← step s!"accept {f}" "lake" #["exe", "naru", "compile", f]
  if accepts.isEmpty then fail s!"{acceptDir}: no .naru files" else ok s!"{acceptDir}: {accepts.length} files compile"
  let rejects ← Naru.listFiles rejectDir "naru"
  for f in rejects do
    match NaruTest.Lsp.namedCode (← IO.FS.readFile f) with
    | none => fail s!"{f}: the header comment names no E number"
    | some code =>
      let _ ← step s!"reject {f} ({code})" "lake" #["exe", "naru", "check-reject", f, code]
  if rejects.isEmpty then fail s!"{rejectDir}: no .naru files" else ok s!"{rejectDir}: {rejects.length} files"

/-- 5. C1: 決定性とヘッダ。 -/
def checkDeterminism (roots : List System.FilePath) (generated : System.FilePath) : M Unit := do
  heading "C1 determinism"
  let _ ← step "compile 1" "lake" #["exe", "naru", "compile"]
  let s1 ← shaSnapshot generated
  let _ ← step "compile 2" "lake" #["exe", "naru", "compile"]
  let s2 ← shaSnapshot generated
  if s1.isEmpty then fail s!"{generated}: no generated files"
  else if s1 == s2 then ok s!"C1: {s1.length} generated files, sha256 identical across two runs"
  else
    let differ := (s1.zip s2).filter (fun (a, b) => a != b) |>.map (·.1.1)
    fail s!"C1: sha256 differs across two runs ({differ.length} files): {differ.take 5}"
  -- ヘッダ
  let mut bad : List String := []
  let mut contents : List (String × String) := []
  for (f, _) in s2 do
    let c ← IO.FS.readFile f
    contents := contents ++ [(f, c)]
    let head := "\n".intercalate ((c.splitOn "\n").take 5)
    if !(contains head "naru-compiler: " && contains head "naru-stdlib: " && contains head "naru-source: ") then bad := bad ++ [f]
  if bad.isEmpty then ok s!"C1: all {s2.length} files have naru-compiler / naru-stdlib / naru-source in the first 5 lines"
  else fail s!"C1: header missing in {bad}"
  -- ソースのパスはルートからの相対(ルートのディレクトリ名で始まらない)
  let mut rooted : List String := []
  for (f, c) in contents do
    for l in c.splitOn "\n" do
      if l.startsWith "-- naru-source: " then
        let p := (l.drop "-- naru-source: ".length).toString
        if roots.any fun r => p.startsWith (prefixOf r) then rooted := rooted ++ [f]
  if rooted.isEmpty then ok s!"C1: no naru-source path starts with a source root ({", ".intercalate (roots.map prefixOf)})"
  else fail s!"C1: naru-source paths start with the source root in {rooted}"
  -- 各ソースの sha256 がヘッダにある
  let all := "\n".intercalate (contents.map (·.2))
  let mut nSrc := 0
  let mut missing : List String := []
  for r in roots do
    for f in (← Naru.listFiles r "naru") do
      nSrc := nSrc + 1
      let rel := if f.startsWith (prefixOf r) then (f.drop (prefixOf r).length).toString else f
      let h := Naru.sha256Hex (← IO.FS.readBinFile f)
      if !(contains all s!"naru-source: {rel} sha256:{h}") then missing := missing ++ [f]
  if nSrc == 0 then fail "C1: no sources under the source roots"
  else if missing.isEmpty then ok s!"C1: {nSrc} sources, each `naru-source: <root-relative path> sha256:<hash>` appears in the generated headers"
  else fail s!"C1: source hash not found in the headers for {missing}"

/-- 6. C6 / C8 のビルドと grep、statements 群。 -/
def checkBuilds (generated : System.FilePath) : M Unit := do
  heading "C6 / C8 builds"
  let _ ← step "C6 lake build Model" "lake" #["build", "Model"]
  let modelDir := generated / "Model"
  let modelRoot := generated / "Model.lean"
  let g ← step "C6 grep (expect no match)" "grep" #["-rwE", "noncomputable|unsafe|axiom|sorry|partial", modelDir.toString, modelRoot.toString] (expectExit := 1)
  if g.exitCode == 0 then IO.println (tail g.stdout 1000)
  let _ ← step "C8 lake build Statements" "lake" #["build", "Statements"]
  let g2 ← step "C8 grep sorry (expect no match)" "grep" #["-rw", "sorry", (generated / "Statements.lean").toString, (generated / "Statements").toString] (expectExit := 1)
  if g2.exitCode == 0 then IO.println (tail g2.stdout 1000)
  subgroup "naru_test statements (C8 / C9)" NaruTest.Statements.run

/-- 7. 受理例の生成 Lean の型検査と、C34 / C35 の検体の意味。 -/
def checkGeneratedAccepts (leanPath : String) : M Unit := do
  heading "generated Lean of the accept examples (+ C34 semantics)"
  let accepts ← Naru.listFiles acceptDir "naru"
  for src in accepts do
    let name := ((System.FilePath.mk src).fileStem).getD src
    let out := workDir / "accept" / name
    if ← out.isDir then IO.FS.removeDirAll out
    IO.FS.createDirAll out
    let outAbs ← IO.FS.realPath out
    let lp := s!"{outAbs}:{leanPath}"
    let _ ← step s!"accept {name}: generate" "lake" #["exe", "naru", "compile", "--out", out.toString, src]
    for sub in ["Model", "Statements"] do
      for f in (← Naru.listFiles (out / sub) "lean") do
        let rel := (f.drop (out.toString.length + 1)).toString
        let olean := (rel.dropEnd ".lean".length).toString ++ ".olean"
        let _ ← step s!"accept {name}: lean {rel}" "lean" #[s!"--root={outAbs}", "-o", (outAbs / olean).toString, rel]
          (cwd := some outAbs) (env := #[("LEAN_PATH", some lp)])
    checkModuleRule name src out
    if src == c34Source then
      runSemantics "C34" c34Source c34Module outAbs lp c34Values c34Props c34Equations
    if src == c35AcceptSource then
      runSemantics "C35" c35AcceptSource c35Module outAbs lp c35Values c35Props c35Equations
  if !accepts.contains c34Source then fail s!"C34: {c34Source} is missing"
  if !accepts.contains c35AcceptSource then fail s!"C35: {c35AcceptSource} is missing"
  if !accepts.contains c37LegacySource then fail s!"C37: {c37LegacySource} is missing"

/-- 9. C7 の simulate と C26。 -/
def checkSimulate (roots : List System.FilePath) (generated : System.FilePath) : M Unit := do
  heading "C7 simulate / C26"
  let mut scenarioFiles : List String := []
  let mut plainFile : Option String := none
  for r in roots do
    for f in (← Naru.listFiles r "naru") do
      let text ← IO.FS.readFile f
      let hasScenario := (text.splitOn "\n").any (·.startsWith "scenario ")
      if hasScenario then scenarioFiles := scenarioFiles ++ [f]
      else if plainFile.isNone then plainFile := some f
  if scenarioFiles.isEmpty then fail "C7: no file under the source roots declares a scenario"
  -- C26 の基準: 直前の `naru compile` が生成先に書くファイルの集合
  let _ ← step "C26: compile (the files naru compile writes are the only ones allowed under the generated dir)" "lake" #["exe", "naru", "compile"]
  let expected ← allFiles generated
  let words := ["time", "node", "confirmed", "stable", "finalized"]
  let mut basicSeen := false
  for f in scenarioFiles do
    let r ← step s!"C7 simulate {f}" "lake" #["exe", "naru", "simulate", f]
    if (System.FilePath.mk f).fileName == some "basic.naru" then
      basicSeen := true
      let missing := words.filter fun w => !(contains r.stdout w)
      if missing.isEmpty then ok s!"C7: {f} prints {", ".intercalate words}"
      else fail s!"C7: {f}: output lacks {missing}\n{tail r.stdout 800}"
  if !basicSeen then fail "C7: no `basic.naru` scenario under the source roots"
  ok s!"C7: {scenarioFiles.length} scenario files simulated"
  let _ ← step "C7 simulate outside the source roots (exit 2)" "lake" #["exe", "naru", "simulate", (acceptDir / "smoke.naru").toString] (expectExit := 2)
  match plainFile with
  | some f => let _ ← step s!"C7 simulate a file without scenario (exit 2)" "lake" #["exe", "naru", "simulate", f] (expectExit := 2)
  | none => fail "C7: every file under the source roots declares a scenario (no probe for exit 2)"
  -- C26: 生成先には `naru compile` の決定的な出力だけがある。simulate の後の生成先のファイル集合が直前の compile の出力と一致し
  -- (runner・一時ファイルが増えていない)、`git status --porcelain --ignored` の追跡対象外(`??`)の項目は compile の出力のパス
  -- (この周回で新しくできた生成パス。次の commit が追跡する)だけ、ignore(`!!`)の項目は無い(` D` は作業木に無い旧パス、` M` は内容の更新)。
  let after ← allFiles generated
  let extra := after.filter (!expected.contains ·)
  let missing := expected.filter (!after.contains ·)
  if expected.isEmpty then fail s!"C26: {generated}/ is empty after compile"
  else if extra.isEmpty && missing.isEmpty then ok s!"C26: after simulate, {generated}/ holds exactly the {expected.length} files that naru compile writes (no runner / temporary file)"
  else fail s!"C26: {generated}/ differs from the compile output after simulate: extra {extra.take 5}, missing {missing.take 5}"
  let st ← runProc "git" #["status", "--porcelain", "--ignored", "--", generated.toString ++ "/"]
  let entries := (st.stdout.splitOn "\n").filter (!·.isEmpty)
  let isOutput (p : String) : Bool :=
    if p.endsWith "/" then expected.any (·.startsWith p) else expected.contains p
  let mut stray : List String := []
  let mut newOutput : List String := []
  for l in entries do
    let status := (l.take 2).toString
    let path := (l.drop 3).toString
    if status == " M" || status == " D" then continue
    else if status == "??" && isOutput path then newOutput := newOutput ++ [path]
    else stray := stray ++ [l]
  if st.exitCode == 0 && stray.isEmpty then
    ok s!"C26: git status --porcelain --ignored -- {generated}/ has no untracked / ignored entry outside the compile output ({newOutput.length} untracked entries are new compile output paths: {newOutput})"
  else fail s!"C26: untracked / ignored entries outside the compile output under {generated}/ (exit {st.exitCode}): {stray}"
  let ignore ← IO.FS.readFile ".gitignore"
  let simLines := (ignore.splitOn "\n").filter (contains · "Simulate")
  if simLines.isEmpty then ok "C26: .gitignore has no line containing `Simulate`" else fail s!"C26: .gitignore mentions Simulate: {simLines}"
  let runner : System.FilePath := ".lake" / "naru" / "simulate" / "Simulate.lean"
  if ← runner.pathExists then ok s!"C26: the simulate runner is {runner}" else fail s!"C26: {runner} not found after simulate"

/-- 11. C24: 直書きの不在と別名のコピー。 -/
def checkConfig (roots : List System.FilePath) (generated : System.FilePath) : M Unit := do
  heading "C24 naru.toml"
  let g ← step "C24 grep compiler/ for a hard-coded root name (expect no match)" "grep" #["-rn", "\"dsl\\|\"specs", compilerDir.toString] (expectExit := 1)
  if g.exitCode == 0 then IO.println (tail g.stdout 1000)
  let some root := roots.head? | fail "C24: naru.toml lists no source root"; return
  let aliasDir := workDir / "alias"
  if ← aliasDir.isDir then IO.FS.removeDirAll aliasDir
  IO.FS.createDirAll workDir
  let _ ← step "C24 alias: copy the source root" "cp" #["-R", root.toString, aliasDir.toString]
  let before ← shaSnapshot generated
  let cfgPath : System.FilePath := Naru.configFileName
  let original ← IO.FS.readFile cfgPath
  let others := roots.tail.map fun r => s!", \"{r}\""
  let alt := s!"sources = [\"./{aliasDir}/\"{"".intercalate others}]\ngenerated = \"{generated}\"\n"
  try
    IO.FS.writeFile cfgPath alt
    let _ ← step "C24 alias: compile with the alias root (written with ./ and a trailing /)" "lake" #["exe", "naru", "compile"]
    let after ← shaSnapshot generated
    if before == after && !before.isEmpty then ok s!"C24: {before.length} generated files have the same sha256 with the alias root"
    else fail s!"C24: generated files differ with the alias root ({(before.zip after).filter (fun (a, b) => a != b) |>.map (·.1.1) |>.take 5})"
  finally
    IO.FS.writeFile cfgPath original
  let _ ← step "C24: naru.toml restored" "git" #["diff", "--exit-code", "--stat", cfgPath.toString]
  let _ ← step "C24: compile with the restored naru.toml" "lake" #["exe", "naru", "compile"]
  let restored ← shaSnapshot generated
  if restored == before then ok "C24: generated files restored (sha256 identical)" else fail "C24: generated files differ after restoring naru.toml"

/-- 12. C28 / C22 / C27。 -/
def checkLayout : M Unit := do
  heading "C28 / C22 / C27"
  let r ← step "C28 git ls-files tests/golden" "git" #["ls-files", "tests/golden"]
  if r.stdout.trimAscii.toString == "tests/golden/Golden.lean" then ok "C28: tests/golden has only Golden.lean"
  else fail s!"C28: tests/golden lists {r.stdout.trimAscii}"
  let _ ← step "C22 cmp LICENSE" "cmp" #["LICENSE", "third_party/verified-consensus/LICENSE"]
  let a ← step "C27 linguist-generated" "git" #["check-attr", "linguist-generated", "generated/Model.lean", "editors/tree-sitter-naru/src/parser.c"]
  let setLines := (a.stdout.splitOn "\n").filter (·.endsWith "linguist-generated: set")
  if setLines.length == 2 then ok "C27: generated/Model.lean and editors/tree-sitter-naru/src/parser.c are linguist-generated"
  else fail s!"C27: linguist-generated: {a.stdout.trimAscii}"
  let b ← step "C27 linguist-vendored" "git" #["check-attr", "linguist-vendored", "third_party/README.md", "third_party/verified-consensus"]
  let vLines := (b.stdout.splitOn "\n").filter (·.endsWith "linguist-vendored: set")
  if vLines.length == 2 then ok "C27: third_party/README.md and third_party/verified-consensus are linguist-vendored"
  else fail s!"C27: linguist-vendored: {b.stdout.trimAscii}"

def checks : M Unit := do
  let t0 ← IO.monoMsNow
  heading "build"
  let _ ← step "lake build naru naru_test" "lake" #["build", "naru", "naru_test"]
  let (roots, generated) ← match ← sourceRoots with
    | .ok rs =>
      match ← Naru.readConfig Naru.configFileName with
      | .ok cfg => pure (rs, cfg.generatedPath)
      | .error e => fail e; return
    | .error e => fail e; return
  ok s!"naru.toml: sources {roots}, generated {generated}"
  checkAcceptReject
  checkRejectDiagnostics
  checkCoreSoundness roots
  heading "editor support groups"
  subgroup "naru_test grammar (C16)" NaruTest.Grammar.run
  subgroup "naru_test zed (C17)" NaruTest.Zed.run
  subgroup "naru_test lsp (C18)" NaruTest.Lsp.run
  heading "golden rehearsal"
  subgroup "naru_test golden --finality-horizon 40 (rehearsal, not the C10 evidence)" (NaruTest.Golden.run 40)
  checkDeterminism roots generated
  checkBuilds generated
  let e ← runProc "lake" #["env", "printenv", "LEAN_PATH"]
  let leanPath := e.stdout.trimAscii.toString
  if e.exitCode == 0 && !leanPath.isEmpty then ok "lake env printenv LEAN_PATH" else fail s!"lake env printenv LEAN_PATH: exit {e.exitCode}"
  checkGeneratedAccepts leanPath
  checkRenameStructure roots
  checkSimulate roots generated
  checkGeneratedDirChange generated
  checkConfig roots generated
  heading "repository"
  subgroup "naru_test repo (C21 / C23 / C25 / C37)" (NaruTest.Repo.run none)
  checkLayout
  let st ← runProc "git" #["status", "--short"]
  IO.println s!"git status --short:\n{st.stdout}"
  heading "C10 golden (horizon 100)"
  subgroup "naru_test golden (C10)" (NaruTest.Golden.run NaruTest.Golden.c10Horizon)
  IO.println s!"regression: total {← elapsed t0}"

def run : IO UInt32 := runGroup "naru_test regression" checks

end NaruTest.Regression
