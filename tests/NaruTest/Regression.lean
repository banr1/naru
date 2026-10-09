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
3. `grammar`(C16)/ `zed`(C17)/ `lsp`(C18)の各群と、golden の短い予行(`--finality-horizon 40`)。
4. C1 の決定性: `lake exe naru compile` を 2 回走らせ、生成先の全ファイルの sha256 が一致、各ファイルの先頭 5 行にコンパイラ版・stdlib 版・
   ソースの hash があり、ソースのパスがソースルートからの相対(ルートのディレクトリ名で始まらない)で、各ソースの sha256 がヘッダと一致。
5. `lake build Model`(C6。`noncomputable` / `unsafe` / `axiom` / `sorry` / `partial` が 0 件)、`lake build Statements`(C8。`sorry` 0 件)、
   `statements` 群(C8 の依存境界 / C9 の claim surface)。
6. 受理例ごとに `--out` へ生成して生成 Lean を型検査(Model の olean → Statements)。生成ファイルは `<lib>/<モジュールのパス>.lean` で、
   宣言は `<lib>.<モジュール名>.*`(モジュール名の一般規則、C37)。`tests/accept/guard_shadow.naru` は C34 の検体: 生成した
   Model / Statements を import する検査プログラム(`c34Program`。期待結果は `c34Values` / `c34Props` / `c34Equations`)を `lean --run` し、
   実際の戻り値の行が期待とすべて一致し、命題の真偽(真になる入力と、偽になる対照入力の否定)を Lean kernel が `example` で検査する。
   `tests/accept/legacy_module_name.naru` は C37 の検体: 移植ソースの改名前と同じ形の利用者モジュール名が、特別扱いなしに同じ規則で
   `Model/` と `Statements/` の両方に生成され、ルートの集約ファイルが import する。
7. C37 の改名: 改名前の最後の commit(`c37BaseCommit`)のソースルートを `git archive` で取り出して現在のコンパイラで `--out` に生成し、
   現在のソースの生成物と、生成パスの集合と各ファイルのヘッダ以下の内容(宣言・import・本体)がモジュール名の置換を除いて一致する
   ことを照合する。現在の生成物のパス・内容に改名前の名前が無い。
8. C7 の simulate: ソースルート配下の scenario を持つ全ファイルの `naru simulate`(exit 0。`basic.naru` の出力に time / node / confirmed /
   stable / finalized)、ルート外のファイルと scenario の無いファイルは exit 2、C26(simulate の後の生成先のファイル集合が直前の `naru compile` の
   出力と一致する(runner・一時ファイルが無い)、`git status --porcelain --ignored` に compile の出力の外の追跡対象外・ignore の項目が無い、
   `.gitignore` に `Simulate` の行が無い、runner は `.lake/naru/simulate/Simulate.lean`)。
9. C24: `compiler/` にソースルートのディレクトリ名の直書きが無い、`naru.toml` の `sources` を別名のコピーに向けても生成先の sha256 が一致
   (`naru.toml` は必ず元に戻し、`git diff --exit-code` で確かめる)。
10. `repo` 群(C21 / C23 / C25 / C37 の旧名検索)、C28 / C22 / C27。
11. C10: `golden`(引数なし = horizon 100、全 16 ケース)。

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

/-- 検査プログラム(生成した Model / Statements を import し、`example` と `main` で確かめる)。 -/
def c34Program : String :=
  let examples := (c34Props ++ c34Equations).map fun (p, tac) => s!"example : {p} := by {tac}\n"
  let prints := c34Values.map fun (label, expr, _) => s!"  IO.println s!\"{label} = \{{expr}}\"\n"
  s!"-- naru_test regression (C34): generated from NaruTest/Regression.lean. Imports the Model / Statements generated from {c34Source}.\n" ++
  s!"import Model.{c34Module}\nimport Statements.{c34Module}\n\nopen Model.{c34Module}\nopen Statements.{c34Module}\n\n" ++
  "-- 命題の真偽と戻り値の等式(Lean kernel が検査する)\n" ++ "".intercalate examples ++
  "\n-- 実際の戻り値(表示して期待の行と照合する)\ndef main : IO Unit := do\n" ++ "".intercalate prints

def c34ExpectedLines : List String := c34Values.map fun (label, _, v) => s!"{label} = {v}"

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

/-- 7. C37: 改名前の commit のソースを現在のコンパイラで生成し、現在の生成物とモジュール名の置換を除いて照合する。 -/
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

/-- 4. C1: 決定性とヘッダ。 -/
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

/-- 5. C6 / C8 のビルドと grep、statements 群。 -/
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

/-- 6. 受理例の生成 Lean の型検査と、C34 の検体の意味。 -/
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
      let prog := out / "Check.lean"
      IO.FS.writeFile prog c34Program
      let r ← step "C34: lean --run Check.lean" "lean" #["--run", "Check.lean"] (cwd := some outAbs) (env := #[("LEAN_PATH", some lp)])
      let lines := (r.stdout.splitOn "\n").filter (!·.isEmpty)
      let mut good := true
      for e in c34ExpectedLines do
        if lines.contains e then ok s!"C34: {e}"
        else
          good := false
          fail s!"C34: expected `{e}`, got {lines.filter fun l => l.startsWith ((e.splitOn " = ").head!)}"
      let extra := lines.filter fun l => !c34ExpectedLines.contains l
      if !extra.isEmpty then
        good := false
        fail s!"C34: unexpected output lines {extra}"
      if good && r.exitCode == 0 then
        ok s!"C34: {c34Values.length} return values agree, {c34Props.length} propositions and {c34Equations.length} equations checked by the Lean kernel ({c34Source})"
  if !accepts.contains c34Source then fail s!"C34: {c34Source} is missing"
  if !accepts.contains c37LegacySource then fail s!"C37: {c37LegacySource} is missing"

/-- 8. C7 の simulate と C26。 -/
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

/-- 9. C24: 直書きの不在と別名のコピー。 -/
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

/-- 10. C28 / C22 / C27。 -/
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
