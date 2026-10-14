import Lean.Data.Json
import Naru
import NaruTest.Common
import NaruTest.Statements

/-!
# `naru_test proofs` — プロトコル証明の分離基盤の検査(IDEAL.md C68 / C69 / C70 / C72)

リポジトリのルートで `lake exe naru_test proofs` と実行する。`lake build naru` の後、`.lake/build/bin/naru` を走らせて次を確かめる。一時ファイルは
`.lake/naru/test/proofs/`。

- C69(義務の一覧 `obligations.json`): 現在のソースをソースルートを cwd にして `naru compile --out <一時ディレクトリ> <相対パス…>` で別々の一時ディレクトリへ 2 回生成して
  `obligations.json` が byte 一致(決定性)し、`naru.toml` からの `lake exe naru compile` の `generated/obligations.json` とも一致、先頭の 3 値(`naru-compiler` / `naru-stdlib` /
  `sources`。パスがソースルートのディレクトリ名で始まらず、各 sha256 が実際のファイルの hash、件数がファイル数と一致)、consensus の義務が 14 件(13 claims の名前と順序が
  用語「claim surface」と一致し、最後が bundle `Consensus`。各 claim の `bundles` がその bundle)、束縛 hash をこの検査が独立に再計算(Lean の `importModules` で取った
  Statements モジュールの import 閉包を生成モジュールに絞り、先頭の `--` のコメント行を除いた本文の sha256 と stdlib の hash を連ねる)して一致。手で書いた期待 JSON の検体
  `tests/proofs/sample/`(複製を cwd にして `naru compile`。`naru-compiler-sha256` / `naru-stdlib-sha256` の値だけ実際の値に置き換える)が byte 一致し、宣言コメントだけを
  変えた複製では束縛 hash が変わらず、claim が依存する fn の本体を変えた複製では変わり、閉包の外のモジュールを変えた複製では変わらない。claim の無い単位
  `tests/proofs/noclaims/` では義務 0 件の一覧。
- C68(Lake ライブラリ `Proofs` と依存方向): 検体の複製で `naru.toml` の `proofs` を空のディレクトリに向けても `naru compile --out` の出力が byte 一致(`compile` は
  `proofs/` を読まない)。ホームで `lake exe naru proofs` が exit 0 → `lake build Proofs` が exit 0、`Proofs` の import 閉包(`importModules` でモジュール名を列挙する
  Lean スクリプト)の全モジュールが `Proofs` / `Model` / `Statements` / `NaruStd` / Lean 本体 / mathlib とその依存パッケージのどれかに属し `DecoupledConsensus` / `NaruSem` /
  `Naru.` / `NaruTest` が 0 件、逆に `Model` / `Statements` / `NaruStd` / `NaruSem` / `Naru` の import 閉包(同じスクリプト。`lake build NaruSem` の後)に `Proofs` と
  mathlib(とその依存パッケージ)が 0 件、`grep -rnwE 'sorry|admit'` が `proofs/` で 0 件(C71 の一部)。
- C70(証明状況 `naru proofs`): 検体の複製で `naru proofs` が exit 1 で表示が `expected/proofs.txt` と一致し、`--json` が `expected/proofs.json` と byte 一致し、状況と件数
  (proved 2 / missing 3 / sorry 1 / stale 2 / invalid 5)が明示の期待と一致、`Proofs/Invalid.lean` を除いた複製では exit 0(`other` / `viaAxiom` / `mixed` / `coerced` が
  missing)、`naru.toml` の `proofs` を別名の複製ディレクトリに向けても同じ結果、実行の前後で生成先と証明ディレクトリの全ファイルの sha256 が同じ。ソースを変えて
  `naru compile` し直していない複製(一覧が古い)とルート `Proofs.lean` の無い複製では exit 2。consensus の現在の一覧に対して invalid 0 件。
- C72(文書): `proofs/README.md` が義務・束縛行・失効・`sorry`・mathlib・禁止・`naru proofs`・`naru_test proofs` の語を含み、`git grep -l --untracked 'naru proofs'` が
  README と docs 3 本と `proofs/README.md` の 5 件。
- C71(進捗): 証明済みの consensus の義務の一覧 `consensusProved`(いまは `constants` / `nested` / `finalizedMonotone` / `certificatesAccountable` /
  `finalizedAccountable` / `finalizedSafe` / `honestNeverSlashed` の 7 件)が、ホームの `naru proofs --json` で `proved`
  であることを確かめる(`stale` / `sorry` / `invalid` に退行したら FAIL)。14 件すべて証明済みの検査は、証明が揃った周回でこの一覧を全件にして加える
  (未実装の検査を PASS にしない)。
- 最後にホームで `lake exe naru compile` と `lake exe naru proofs` を走らせ、Lake が読む link を元に戻す。
-/

namespace NaruTest.Proofs
open Lean (Json)

def workDir : System.FilePath := ".lake" / "naru" / "test" / "proofs"
def fixturesDir : System.FilePath := "tests" / "proofs"
def docsWithProofs : List String := ["README.md", "docs/cli.md", "docs/architecture.md", "docs/testing.md", "proofs/README.md"]
def readmeWords : List String := ["義務", "束縛行", "失効", "sorry", "mathlib", "禁止", "naru proofs", "naru_test proofs"]
/-- mathlib とその依存パッケージのモジュールのルート。 -/
def mathlibRoots : List String := ["Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "ImportGraph", "LeanSearchClient", "Plausible", "Cli"]
/-- `Proofs` の import 閉包に許すモジュールのルート(Lean 本体・生成物・stdlib・mathlib とその依存パッケージ)。 -/
def allowedRoots : List String := ["Proofs", "Model", "Statements", "NaruStd", "Init", "Lean", "Std", "Lake"] ++ mathlibRoots
def forbidden : List String := ["DecoupledConsensus", "NaruSem", "Naru.", "NaruTest"]
/-- `Proofs` を import してはならないライブラリのルート(逆依存の検査)。 -/
def reverseRoots : List String := ["Model", "Statements", "NaruStd", "NaruSem", "Naru"]
def expectedStatuses : List (String × String) :=
  [ ("Sample.FarRules.farClaim", "missing"), ("Sample.Rules.incPositive", "proved"), ("Sample.Rules.seeded", "sorry"),
    ("Sample.Rules.biased", "stale"), ("Sample.Rules.tautology", "stale"), ("Sample.Rules.lonely", "missing"),
    ("Sample.Rules.other", "invalid"), ("Sample.Rules.viaAxiom", "invalid"), ("Sample.Rules.mixed", "invalid"), ("Sample.Rules.coerced", "invalid"),
    ("Sample.Rules.Inner", "proved"), ("Sample.Rules.Outer", "missing") ]
/-- `Proofs/Invalid.lean` の theorem(missing になる)。 -/
def invalidSample : List String := ["Sample.Rules.other", "Sample.Rules.viaAxiom", "Sample.Rules.mixed", "Sample.Rules.coerced"]
/-- 検体の件数(名前順)。 -/
def expectedCounts : List (String × Nat) := [("invalid", 5), ("missing", 3), ("proved", 2), ("sorry", 1), ("stale", 2)]
/-- 不正の検体 `Proofs/Invalid.lean` を除いた複製の件数(名前順)。 -/
def expectedCountsValid : List (String × Nat) := [("invalid", 0), ("missing", 7), ("proved", 2), ("sorry", 1), ("stale", 2)]
def expectedCountsLine : String := "proved 2 / missing 3 / sorry 1 / stale 2 / invalid 5 (of 12 obligation(s); 1 line(s) counted as invalid)"
/-- consensus の義務のうち証明済みのもの(C71 の進捗。`proofs/Proofs/Consensus/Spec/Claims.lean` の theorem と束縛行)。証明が増えたらここに足し、
14 件揃ったら C71 の「全件 proved」の検査になる。 -/
def consensusProved : List String :=
  ["Consensus.Spec.Claims.constants", "Consensus.Spec.Claims.nested", "Consensus.Spec.Claims.finalizedMonotone",
   "Consensus.Spec.Claims.certificatesAccountable", "Consensus.Spec.Claims.finalizedAccountable",
   "Consensus.Spec.Claims.finalizedSafe", "Consensus.Spec.Claims.honestNeverSlashed"]
def consensusObligations : Nat := 14

structure Env where
  root : System.FilePath
  bin : System.FilePath

def runNaru (env : Env) (cwd : System.FilePath) (args : Array String) : IO IO.Process.Output :=
  runProc env.bin.toString args (cwd := some cwd)

def freshDir (p : System.FilePath) : IO System.FilePath := do
  if ← p.isDir then IO.FS.removeDirAll p
  IO.FS.createDirAll p
  IO.FS.realPath p

/-- 検体をコピーする(`cp -R src/. dst`)。 -/
def copyFixture (src dst : System.FilePath) : IO Bool := do
  let r ← runProc "cp" #["-R", src.toString ++ "/.", dst.toString]
  return r.exitCode == 0

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')
def isSha (s : String) : Bool := s.length == 64 && s.toList.all isHex
def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

def replaceInFile (path : System.FilePath) (old new : String) : IO Bool := do
  let text ← IO.FS.readFile path
  if !(contains text old) then return false
  IO.FS.writeFile path (text.replace old new)
  return true

def findInRoots (roots : List System.FilePath) (rel : String) : IO (Option System.FilePath) := do
  for r in roots do
    let f := r / System.FilePath.mk rel
    if ← f.pathExists then return some f
  return none

/-- ソースルート配下の `.naru` のルート相対パス。 -/
def relativeSources (root : System.FilePath) : IO (List String) := do
  let pre := root.toString ++ "/"
  return (← Naru.listFiles root "naru").map fun f => if f.startsWith pre then (f.drop pre.length).toString else f

/-! ## JSON の読み -/

structure JOb where
  name : String
  kind : String
  module : String
  lean : String
  thm : String
  type : String
  hash : String
  summary : String
  bundles : List String
deriving Inhabited

structure ParsedObligations where
  compilerVersion : String
  compilerHash : String
  stdlibVersion : String
  stdlibHash : String
  sources : List (String × String)
  obligations : List JOb
deriving Inhabited

def getStr (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def getNat (j : Json) (k : String) : Except String Nat := do (← j.getObjVal? k).getNat?
def getArr (j : Json) (k : String) : Except String (List Json) := do return (← (← j.getObjVal? k).getArr?).toList

def parseObligations (text : String) : Except String ParsedObligations := do
  let j ← Json.parse text
  let sources ← (← getArr j "sources").mapM fun s => do return (← getStr s "path", ← getStr s "sha256")
  let obligations ← (← getArr j "obligations").mapM fun o => do
    let bundles ← (← getArr o "bundles").mapM (·.getStr?)
    let r : JOb := { name := ← getStr o "name", kind := ← getStr o "kind", module := ← getStr o "module", lean := ← getStr o "lean",
                     thm := ← getStr o "theorem", type := ← getStr o "type", hash := ← getStr o "sha256", summary := ← getStr o "summary", bundles }
    return r
  return { compilerVersion := ← getStr j "naru-compiler", compilerHash := ← getStr j "naru-compiler-sha256",
           stdlibVersion := ← getStr j "naru-stdlib", stdlibHash := ← getStr j "naru-stdlib-sha256", sources, obligations }

/-- `naru proofs --json` の読み: (status ごとの件数(名前順), 義務ごとの (name, status), build). -/
def parseProofsJson (text : String) : Except String (List (String × Nat) × List (String × String) × String) := do
  let j ← Json.parse text
  let results ← (← getArr j "results").mapM fun r => do return (← getStr r "name", ← getStr r "status")
  let counts ← (← j.getObjVal? "counts").getObj?
  let cs ← counts.toList.mapM fun (k, v) => do return (k, ← v.getNat?)
  return (cs.mergeSort fun a b => a.1 ≤ b.1, results, ← getStr j "build")

/-! ## import 閉包(Lean の `importModules`) -/

/-- `importModules` で閉包のモジュール名を列挙する Lean スクリプト。 -/
def closureScript : String :=
  "import Lean\n\n/-! naru_test proofs (C68 / C69): print the import closure of the given modules. Written by `lake exe naru_test proofs`. -/\n\n" ++
  "open Lean in\ndef main (args : List String) : IO UInt32 := do\n  initSearchPath (← findSysroot)\n" ++
  "  let imports := args.toArray.map fun a => ({ module := a.toName } : Import)\n" ++
  "  let env ← importModules imports {} 0\n  for m in env.header.moduleNames do IO.println m\n  return 0\n"

def closureScriptPath : System.FilePath := workDir / "Closure.lean"

/-- `mods` の import 閉包(モジュール名。`lake env lean --run`: oleans がビルド済みであること)。 -/
def leanClosure (mods : List String) : IO (Except String (List String)) := do
  IO.FS.createDirAll workDir
  IO.FS.writeFile closureScriptPath closureScript
  let c ← runProc "lake" (#["env", "lean", "--run", closureScriptPath.toString] ++ mods.toArray)
  if c.exitCode != 0 then return .error s!"closure script exit {c.exitCode}\n{tail (c.stdout ++ c.stderr)}"
  return .ok ((c.stdout.splitOn "\n").filter (!·.isEmpty))

/-! ## 束縛 hash の独立な再計算(IDEAL.md 用語「束縛 hash」) -/

/-- 生成先の全 Lean ファイル(モジュール名 → 本文)。 -/
def generatedModules (generated : System.FilePath) : IO (List (String × String)) := do
  let mut out : List (String × String) := []
  for sub in ["Model", "Statements"] do
    let rootFile := generated / (sub ++ ".lean")
    if ← rootFile.pathExists then out := out ++ [(sub, ← IO.FS.readFile rootFile)]
    for f in (← Naru.listFiles (generated / sub) "lean") do
      let rel := (f.drop (generated.toString.length + 1)).toString
      let m := ((rel.dropEnd ".lean".length).toString.replace "/" ".")
      out := out ++ [(m, ← IO.FS.readFile f)]
  return out

/-- 束縛 hash をこの検査が独自に計算する: Lean の `importModules` で取った `stmtModule` の import 閉包(自分を含む)のうち生成モジュール(`Model.*` / `Statements.*`)を
名前順に並べ、各モジュールの本文(先頭の `--` のコメント行 = ヘッダを除く)の sha256 を `名前\n hash\n` の形で連ね、先頭に `naru-stdlib\n<stdlib の hash>\n` を置いた
文字列の sha256。生成側(`Naru.Obligations.bindingHash`: `import` 行を自分で辿り、先頭 5 行を落とす)とは閉包の取り方とヘッダの見分け方が違う。 -/
def recomputeHash (mods : List (String × String)) (stdlibHash : String) (stmtModule : String) : IO (Except String String) := do
  match ← leanClosure [stmtModule] with
  | .error e => return .error e
  | .ok names =>
    let closure := (names.filter fun n => n.startsWith "Model." || n.startsWith "Statements." || n == "Model" || n == "Statements").mergeSort (· ≤ ·)
    let body (c : String) : String := "\n".intercalate ((c.splitOn "\n").dropWhile (·.startsWith "--"))
    let mut entries := ""
    for m in closure do
      match mods.lookup m with
      | some c => entries := entries ++ s!"{m}\n{Naru.sha256HexOfString (body c)}\n"
      | none => return .error s!"module {m} of the closure of {stmtModule} is not a generated file"
    return .ok (Naru.sha256HexOfString (s!"naru-stdlib\n{stdlibHash}\n" ++ entries))

/-- 全義務の束縛 hash が独立な再計算と一致する(生成 Statements の oleans がビルド済みの状態で呼ぶ)。 -/
def checkHashRecomputation (label : String) (generated : System.FilePath) (p : ParsedObligations) : M Unit := do
  let mods ← generatedModules generated
  let mut mismatched : List String := []
  let mut errors : List String := []
  let mut checked : List String := []
  for o in p.obligations do
    let m := "Statements." ++ o.module
    if checked.contains m then continue
    checked := checked ++ [m]
    match ← recomputeHash mods p.stdlibHash m with
    | .error e => errors := errors ++ [s!"{m}: {e}"]
    | .ok h =>
      for q in p.obligations do
        if "Statements." ++ q.module == m && q.hash != h then mismatched := mismatched ++ [q.name]
  if errors.isEmpty && mismatched.isEmpty then
    ok s!"{label}: the binding hash of all {p.obligations.length} obligation(s) ({checked.length} Statements module(s)) equals an independent recomputation (import closure by Lean's importModules restricted to the generated modules, bodies without the leading comment header, stdlib hash)"
  else fail s!"{label}: binding hash recomputation: mismatched {mismatched}, errors {errors.take 3}"

/-- 義務の一覧の共通検査: 先頭の 3 値、ソースの相対パスと hash、正規形。 -/
def checkObligationsFile (label : String) (generated : System.FilePath) (roots : List System.FilePath) : M (Option ParsedObligations) := do
  let path := generated / Naru.Obligations.fileName
  if !(← path.pathExists) then
    fail s!"{label}: {path} not found"
    return none
  let text ← IO.FS.readFile path
  match parseObligations text with
  | .error e =>
    fail s!"{label}: {path} does not parse: {e}"
    return none
  | .ok p =>
    if p.compilerVersion.isEmpty || !(isSha p.compilerHash) || p.stdlibVersion.isEmpty || !(isSha p.stdlibHash) then
      fail s!"{label}: header: naru-compiler `{p.compilerVersion}` sha256 `{p.compilerHash}`, naru-stdlib `{p.stdlibVersion}` sha256 `{p.stdlibHash}`"
    else ok s!"{label}: {Naru.Obligations.fileName} starts with naru-compiler {p.compilerVersion} sha256:{p.compilerHash} and naru-stdlib {p.stdlibVersion} sha256:{p.stdlibHash}"
    let mut files : List String := []
    for r in roots do files := files ++ (← Naru.listFiles r "naru")
    let rootNames := roots.map fun r => ((r.toString.splitOn "/").filter (!·.isEmpty)).getLast!
    let badPrefix := p.sources.filter fun (s, _) => rootNames.any fun n => s.startsWith (n ++ "/")
    let mut badHash : List String := []
    for (s, h) in p.sources do
      let actual ← match ← findInRoots roots s with
        | some f => pure (some (Naru.sha256Hex (← IO.FS.readBinFile f)))
        | none => pure none
      if actual != some h then badHash := badHash ++ [s]
    if p.sources.length == files.length && badPrefix.isEmpty && badHash.isEmpty then
      ok s!"{label}: sources lists {p.sources.length} root-relative paths (none starts with {rootNames}) with their actual sha256"
    else fail s!"{label}: sources: {p.sources.length} listed vs {files.length} files, bad prefix {badPrefix.map (·.1)}, bad hash {badHash}"
    if !text.endsWith "\n" || contains text "\r" then fail s!"{label}: {path} is not LF-terminated canonical JSON"
    return some p

/-! ## 検査 -/

/-- C69(consensus): 決定性・先頭の 3 値・14 件。 -/
def checkConsensus (env : Env) (roots : List System.FilePath) (generated : System.FilePath) : M (Option ParsedObligations) := do
  let r1 ← runProc "lake" #["exe", "naru", "compile"]
  if r1.exitCode != 0 then
    fail s!"C69: lake exe naru compile exit {r1.exitCode}\n{tail (r1.stdout ++ r1.stderr)}"
    return none
  let path := generated / Naru.Obligations.fileName
  if !(← path.pathExists) then
    fail s!"C69: {path} not written by naru compile"
    return none
  let fromConfig ← IO.FS.readFile path
  -- 別々の一時ディレクトリへ 2 回(ソースルートを cwd に、ルート相対パスで `--out`)
  let some root := roots.head? | fail "C69: no source root"; return none
  let rels ← relativeSources root
  let out1 ← freshDir (workDir / "run1")
  let out2 ← freshDir (workDir / "run2")
  let c1 ← runNaru env root (#["compile", "--out", out1.toString] ++ rels.toArray)
  let c2 ← runNaru env root (#["compile", "--out", out2.toString] ++ rels.toArray)
  if c1.exitCode != 0 || c2.exitCode != 0 then
    fail s!"C69: naru compile --out exit {c1.exitCode} / {c2.exitCode}\n{tail (c1.stdout ++ c1.stderr ++ c2.stderr)}"
    return none
  let t1 ← IO.FS.readFile (out1 / Naru.Obligations.fileName)
  let t2 ← IO.FS.readFile (out2 / Naru.Obligations.fileName)
  if t1 == t2 && t1 == fromConfig then
    ok s!"C69: {Naru.Obligations.fileName} is byte-identical across two generations into {out1} and {out2} and equals {path} from naru.toml ({t1.length} characters)"
  else fail s!"C69: {Naru.Obligations.fileName} differs across generations (run1 = run2: {t1 == t2}, run1 = naru.toml: {t1 == fromConfig})"
  let some p ← checkObligationsFile "C69 consensus" generated roots | return none
  let claims := p.obligations.filter (·.kind == "claim")
  let bundles := p.obligations.filter (·.kind == "claim bundle")
  let claimNames := claims.map fun o => (o.name.splitOn ".").getLast!
  let bundleQualified := (bundles.map (·.name)).head?.getD ""
  if p.obligations.length == 14 && claimNames == NaruTest.Statements.claimSurface && bundles.length == 1 &&
      ((bundles.head?.map fun b => (b.name.splitOn ".").getLast!) == some "Consensus") &&
      (p.obligations.getLast?.map (·.kind)) == some "claim bundle" then
    ok s!"C69: consensus has 14 obligations: the 13 claims {claimNames} in the order of the claim surface, then the claim bundle {bundleQualified}"
  else fail s!"C69: consensus obligations: {p.obligations.length} entries, claims {claimNames}, bundles {bundles.map (·.name)}"
  let badBundles := claims.filter fun o => o.bundles != [bundleQualified]
  let bundleBundles := bundles.map (·.bundles)
  if badBundles.isEmpty && bundleBundles == [[]] then ok s!"C69: every claim lists {bundleQualified} as its bundle and the bundle lists none"
  else fail s!"C69: bundles field: claims {badBundles.map fun o => (o.name, o.bundles)}, bundle {bundleBundles}"
  let sameHash := (p.obligations.map (·.hash)).eraseDups.length == 1
  let badTheorem := p.obligations.filter fun o => o.thm != "Proofs." ++ (o.lean.drop "Statements.".length).toString || !(o.lean.startsWith "Statements.")
  let emptyType := p.obligations.filter fun o => o.type.isEmpty || !(contains o.type o.lean)
  if sameHash && badTheorem.isEmpty && emptyType.isEmpty then
    ok s!"C69: all 14 obligations belong to Statements.{(p.obligations.head?.map (·.module)).getD ""} (one binding hash), each `theorem` is `Proofs.` + the Statements name and each type mentions its Statements declaration"
  else fail s!"C69: hashes {(p.obligations.map (·.hash)).eraseDups.length} distinct, theorem names off {badTheorem.map (·.name)}, types off {emptyType.map (·.name)}"
  return some p

/-- C69(検体): 期待 JSON との一致と束縛 hash の変化。返り値は複製のディレクトリと読んだ一覧(C70 が使う)。 -/
def checkSample (env : Env) : M (Option (System.FilePath × ParsedObligations)) := do
  let fixture := fixturesDir / "sample"
  let dir ← freshDir (workDir / "sample")
  if !(← copyFixture fixture dir) then
    fail s!"C69 sample: cannot copy {fixture}"
    return none
  let c ← runNaru env dir #["compile"]
  if c.exitCode != 0 then
    fail s!"C69 sample: naru compile exit {c.exitCode}\n{tail (c.stdout ++ c.stderr)}"
    return none
  let generated := dir / "generated"
  let some p ← checkObligationsFile "C69 sample" generated [dir / "src"] | return none
  let actual ← IO.FS.readFile (generated / Naru.Obligations.fileName)
  let expectedRaw ← IO.FS.readFile (fixture / "expected" / Naru.Obligations.fileName)
  let expected := (expectedRaw.replace "{{compiler-sha256}}" p.compilerHash).replace "{{stdlib-sha256}}" p.stdlibHash
  if actual == expected then ok s!"C69 sample: {fixture}: {Naru.Obligations.fileName} is byte-identical to the hand-written expected/{Naru.Obligations.fileName} (compiler / stdlib sha256 substituted): {p.obligations.length} obligations"
  else
    let al := actual.splitOn "\n"
    let el := expected.splitOn "\n"
    let firstDiff := (List.range (max al.length el.length)).find? fun i => al[i]? != el[i]?
    fail s!"C69 sample: {Naru.Obligations.fileName} differs from the expected at line {firstDiff.map (· + 1)}: actual `{(firstDiff.bind fun i => al[i]?).getD ""}` expected `{(firstDiff.bind fun i => el[i]?).getD ""}`"
  -- 検体の形: 入れ子の bundle、input を使う claim、仮引数の無い claim、bundle に載らない claim、claim の無いモジュール
  let names := p.obligations.map (·.name)
  let outer := p.obligations.find? (·.name == "Sample.Rules.Outer")
  let inner := p.obligations.find? (·.name == "Sample.Rules.Inner")
  let seeded := p.obligations.find? (·.name == "Sample.Rules.seeded")
  let biased := p.obligations.find? (·.name == "Sample.Rules.biased")
  let lonely := p.obligations.find? (·.name == "Sample.Rules.lonely")
  let shape :=
    (outer.map (·.kind)) == some "claim bundle" && (inner.map (·.bundles)) == some ["Sample.Rules.Outer"] &&
    (seeded.map fun o => o.type.startsWith "∀ (seed' : Nat), " && !(contains o.type "«")) == some true &&
    (biased.map fun o => contains o.type "(bias' : (Nat → Nat))") == some true &&
    (lonely.map (·.bundles)) == some [] && !(names.any (·.startsWith "Sample.Far.")) && names.contains "Sample.FarRules.farClaim"
  if shape then ok "C69 sample: the fixture covers a nested bundle (Outer ∋ Inner), claims using a zero-argument input (seeded, no parameters) and an input with an argument (biased), a claim on no bundle (lonely), and a module without claims (Sample.Far has no obligation)"
  else fail s!"C69 sample: fixture shape unexpected: {names}"
  -- 束縛 hash の変化: 宣言コメントだけ / 依存する fn の本体 / 閉包の外のモジュール
  let hashesOf (d : System.FilePath) : IO (Option (List (String × String))) := do
    match parseObligations (← IO.FS.readFile (d / "generated" / Naru.Obligations.fileName)) with
    | .ok q => return some (q.obligations.map fun o => (o.name, o.hash))
    | .error _ => return none
  let base := p.obligations.map fun o => (o.name, o.hash)
  let variant (name : String) (file : String) (old new : String) : M (Option (List (String × String))) := do
    let v ← freshDir (workDir / name)
    if !(← copyFixture fixture v) then fail s!"C69 {name}: cannot copy"; return none
    if !(← replaceInFile (v / "src" / "Sample" / file) old new) then fail s!"C69 {name}: `{old}` not found in {file}"; return none
    let r ← runNaru env v #["compile"]
    if r.exitCode != 0 then fail s!"C69 {name}: naru compile exit {r.exitCode}\n{tail (r.stdout ++ r.stderr)}"; return none
    hashesOf v
  if let some h ← variant "comment" "Rules.naru" "// inc(n) は正(正しい証明: proved)。" "// inc(n) は正(要旨だけを変えた複製)。" then
    if h == base then ok "C69 hash: changing only a declaration comment leaves every binding hash unchanged"
    else fail s!"C69 hash: a comment-only change altered hashes: {(h.zip base).filter (fun (a, b) => a != b) |>.map (·.1.1)}"
  if let some h ← variant "fnbody" "Base.naru" "fn inc(n: Nat) -> Nat { n + 1 }" "fn inc(n: Nat) -> Nat { n + 2 }" then
    let changed := (h.zip base).filter (fun (a, b) => a != b) |>.map (·.1.1)
    let rules := (base.filter fun (n, _) => n.startsWith "Sample.Rules.").map (·.1)
    if changed == rules && !(changed.contains "Sample.FarRules.farClaim") then
      ok s!"C69 hash: changing the body of `inc` changes the hash of the {rules.length} Sample.Rules obligations and not of Sample.FarRules.farClaim"
    else fail s!"C69 hash: changing `inc` altered {changed} (expected exactly {rules})"
  if let some h ← variant "outside" "Far.naru" "fn far(n: Nat) -> Nat { n * 2 }" "fn far(n: Nat) -> Nat { n * 3 }" then
    let changed := (h.zip base).filter (fun (a, b) => a != b) |>.map (·.1.1)
    if changed == ["Sample.FarRules.farClaim"] then ok "C69 hash: changing `far` (outside the import closure of Sample.Rules) changes only Sample.FarRules.farClaim"
    else fail s!"C69 hash: changing `far` altered {changed} (expected only Sample.FarRules.farClaim)"
  return some (dir, p)

/-- C69: claim の無い単位。 -/
def checkNoClaims (env : Env) : M Unit := do
  let fixture := fixturesDir / "noclaims"
  let dir ← freshDir (workDir / "noclaims")
  if !(← copyFixture fixture dir) then fail s!"C69 noclaims: cannot copy {fixture}"; return
  let c ← runNaru env dir #["compile"]
  if c.exitCode != 0 then fail s!"C69 noclaims: naru compile exit {c.exitCode}\n{tail (c.stdout ++ c.stderr)}"; return
  let some p ← checkObligationsFile "C69 noclaims" (dir / "generated") [dir / "src"] | return
  if p.obligations.isEmpty && (contains (← IO.FS.readFile (dir / "generated" / Naru.Obligations.fileName)) "\"obligations\": []") then
    ok "C69 noclaims: a unit without claims gets an obligations.json with 0 obligations (and the 3 header values)"
  else fail s!"C69 noclaims: {p.obligations.length} obligations"

/-- C68(検体): `proofs` を空のディレクトリに向けても `compile --out` の出力は同じ。 -/
def checkCompileIgnoresProofs (env : Env) : M Unit := do
  let fixture := fixturesDir / "sample"
  let withProofs ← freshDir (workDir / "withproofs")
  let noProofs ← freshDir (workDir / "noproofs")
  if !(← copyFixture fixture withProofs) || !(← copyFixture fixture noProofs) then fail "C68: cannot copy the sample"; return
  IO.FS.removeDirAll (noProofs / "proofs")
  IO.FS.createDirAll (noProofs / "empty")
  if !(← replaceInFile (noProofs / "naru.toml") "proofs = \"proofs\"" "proofs = \"empty\"") then fail "C68: naru.toml of the copy has no proofs key"; return
  let rels ← relativeSources (withProofs / "src")
  let files := rels.map fun r => "src/" ++ r
  let a ← runNaru env withProofs (#["compile", "--out", "out"] ++ files.toArray)
  let b ← runNaru env noProofs (#["compile", "--out", "out"] ++ files.toArray)
  if a.exitCode != 0 || b.exitCode != 0 then fail s!"C68: naru compile --out exit {a.exitCode} / {b.exitCode}\n{tail (a.stderr ++ b.stderr)}"; return
  let sa ← snapshotTree [withProofs / "out"]
  let sb ← snapshotTree [noProofs / "out"]
  let rel (base : System.FilePath) (p : String) : String := (p.drop (base.toString.length + 1)).toString
  let aRel := sa.map fun (p, h) => (rel withProofs p, h)
  let bRel := sb.map fun (p, h) => (rel noProofs p, h)
  if aRel == bRel && !aRel.isEmpty then ok s!"C68: naru compile --out writes the same {aRel.length} files (sha256) whether naru.toml points `proofs` at the proofs or at an empty directory (compile does not read proofs/)"
  else fail s!"C68: compile --out output differs with an empty proofs directory: {(aRel.zip bRel).filter (fun (x, y) => x != y) |>.map (·.1.1) |>.take 5}"

/-- `naru proofs` の表示の状況の行 `<name>  <status>  <reason>`。 -/
def statusLines (stdout : String) : List (String × String) :=
  (stdout.splitOn "\n").filterMap fun l =>
    match l.splitOn "  " with
    | name :: status :: _ :: _ => if !(contains name " ") && !(name.startsWith "naru proofs:") then some (name, status) else none
    | _ => none

def countsLine (stdout : String) : Option String := (stdout.splitOn "\n").find? (·.startsWith "proved ")

/-- C70(検体): 証明状況。`dir` は `checkSample` の複製(`naru compile` 済み)。 -/
def checkProofsSample (env : Env) (dir : System.FilePath) (p : ParsedObligations) : M Unit := do
  let fixture := fixturesDir / "sample"
  let before ← snapshotTree [dir / "generated", dir / "proofs"]
  let r ← runNaru env dir #["proofs"]
  let after ← snapshotTree [dir / "generated", dir / "proofs"]
  let expectedText ← IO.FS.readFile (fixture / "expected" / "proofs.txt")
  if r.exitCode == 1 then ok "C70 sample: naru proofs exits 1 (invalid entries present)" else fail s!"C70 sample: naru proofs exit {r.exitCode} (expected 1)\n{tail (r.stdout ++ r.stderr)}"
  if r.stdout == expectedText then ok s!"C70 sample: the display is byte-identical to expected/proofs.txt ({(expectedText.splitOn "\n").length - 1} lines)"
  else
    let al := r.stdout.splitOn "\n"
    let el := expectedText.splitOn "\n"
    let firstDiff := (List.range (max al.length el.length)).find? fun i => al[i]? != el[i]?
    fail s!"C70 sample: the display differs from expected/proofs.txt at line {firstDiff.map (· + 1)}: actual `{(firstDiff.bind fun i => al[i]?).getD ""}` expected `{(firstDiff.bind fun i => el[i]?).getD ""}`"
  -- 明示の期待(状況と件数)
  let got := statusLines r.stdout
  let gotObligations := got.filter fun (n, _) => expectedStatuses.any (·.1 == n)
  if gotObligations == expectedStatuses then ok s!"C70 sample: the {expectedStatuses.length} obligations have the expected statuses {expectedStatuses.map (·.2)} (proved: incPositive / Inner, sorry: seeded, stale: biased (hash changed) / tautology (no binding line), missing: lonely / Outer / farClaim, invalid: other (type of another obligation) / viaAxiom (axiom) / mixed (sorry and axiom: invalid before sorry) / coerced (coercion built from an axiom, caught by the axiom audit of the check theorem))"
  else fail s!"C70 sample: statuses {gotObligations} vs expected {expectedStatuses}"
  if got.any fun (n, s) => n == "Sample.Rules.nonexistent" && s == "invalid" then ok "C70 sample: the binding line naming an obligation that is not in the list is reported as invalid"
  else fail s!"C70 sample: no invalid line for the unknown binding Sample.Rules.nonexistent in {got}"
  if countsLine r.stdout == some expectedCountsLine then ok s!"C70 sample: counts line `{expectedCountsLine}`"
  else fail s!"C70 sample: counts line `{countsLine r.stdout}` (expected `{expectedCountsLine}`)"
  if (r.stdout.splitOn "\n").any (fun l => l.startsWith "layer: " && contains l "separate layer") then ok "C70 sample: the last line states that the compiler's semantics preservation is a separate layer"
  else fail "C70 sample: no `layer:` line"
  if before == after && !before.isEmpty then ok s!"C70 sample: naru proofs wrote nothing under generated/ and proofs/ ({before.length} files, same sha256 before and after)"
  else fail "C70 sample: generated/ or proofs/ changed during naru proofs"
  -- 束縛 hash の独立な再計算(いま生成 Statements の oleans が link 経由でビルド済み)
  checkHashRecomputation "C69 sample" (dir / "generated") p
  -- --json
  let j ← runNaru env dir #["proofs", "--json"]
  let expectedJson ← IO.FS.readFile (fixture / "expected" / "proofs.json")
  if j.exitCode == 1 && j.stdout == expectedJson then ok s!"C70 sample: naru proofs --json exits 1 and is byte-identical to expected/proofs.json ({expectedJson.length} characters)"
  else fail s!"C70 sample: --json exit {j.exitCode}, identical {j.stdout == expectedJson}\n{tail (j.stdout ++ j.stderr) 600}"
  match parseProofsJson j.stdout with
  | .error e => fail s!"C70 sample: --json does not parse: {e}"
  | .ok (counts, results, build) =>
    if counts == expectedCounts && results == expectedStatuses && build == "ok" then ok s!"C70 sample: --json counts {expectedCounts} and per-obligation statuses agree with the display"
    else fail s!"C70 sample: --json counts {counts}, results {results}, build {build}"
  -- 不正の検体を除いた複製: exit 0
  let valid ← freshDir (workDir / "valid")
  if !(← copyFixture dir valid) then fail "C70 valid: cannot copy"; return
  IO.FS.removeFile (valid / "proofs" / "Proofs" / "Invalid.lean")
  let v ← runNaru env valid #["proofs", "--json"]
  match parseProofsJson v.stdout with
  | .error e => fail s!"C70 valid: --json does not parse (exit {v.exitCode}): {e}\n{tail (v.stdout ++ v.stderr) 600}"
  | .ok (counts, results, _) =>
    let wantResults := expectedStatuses.map fun (n, s) => if invalidSample.contains n then (n, "missing") else (n, s)
    if v.exitCode == 0 && counts == expectedCountsValid && results == wantResults then
      ok s!"C70 valid: without Proofs/Invalid.lean naru proofs exits 0 with {expectedCountsValid} ({invalidSample} become missing; unproved and stale obligations do not fail the command)"
    else fail s!"C70 valid: exit {v.exitCode}, counts {counts}, results {results}"
  -- 別名の証明ディレクトリ
  let alias ← freshDir (workDir / "alias")
  if !(← copyFixture dir alias) then fail "C70 alias: cannot copy"; return
  let mv ← runProc "mv" #[(alias / "proofs").toString, (alias / "proofs-alias").toString]
  if mv.exitCode != 0 then fail "C70 alias: mv failed"; return
  if !(← replaceInFile (alias / "naru.toml") "proofs = \"proofs\"" "proofs = \"proofs-alias\"") then fail "C70 alias: naru.toml"; return
  let a ← runNaru env alias #["proofs", "--json"]
  let normalized := a.stdout.replace "proofs-alias" "proofs"
  if a.exitCode == 1 && normalized == expectedJson then ok "C70 alias: with naru.toml pointing `proofs` at a renamed copy of the proofs directory the result is the same (only the directory name differs)"
  else fail s!"C70 alias: exit {a.exitCode}, same {normalized == expectedJson}\n{tail (a.stdout ++ a.stderr) 600}"
  -- 一覧が古い複製(ソースを変えて naru compile していない)とルート Proofs.lean の無い複製: exit 2
  let stale ← freshDir (workDir / "stale")
  if !(← copyFixture dir stale) then fail "C70 stale: cannot copy"; return
  if !(← replaceInFile (stale / "src" / "Sample" / "Base.naru") "// 1 を足す。" "// 1 を足す(編集後に naru compile していない)。") then fail "C70 stale: Base.naru"; return
  let s ← runNaru env stale #["proofs"]
  if s.exitCode == 2 && contains s.stderr "out of date" then ok s!"C70 stale: with a source edited after the last naru compile, naru proofs refuses (exit 2: {(s.stderr.splitOn "\n").head!.take 80}…) instead of judging against an old list"
  else fail s!"C70 stale: exit {s.exitCode}\n{tail (s.stdout ++ s.stderr) 400}"
  let noRoot ← freshDir (workDir / "noroot")
  if !(← copyFixture dir noRoot) then fail "C70 noroot: cannot copy"; return
  IO.FS.removeFile (noRoot / "proofs" / "Proofs.lean")
  let n ← runNaru env noRoot #["proofs"]
  if n.exitCode == 2 && contains n.stderr "Proofs.lean" then ok "C70 noroot: without the root module proofs/Proofs.lean naru proofs exits 2 and names it"
  else fail s!"C70 noroot: exit {n.exitCode}\n{tail (n.stdout ++ n.stderr) 400}"

/-- C68 / C70(ホーム): `naru proofs`、`lake build Proofs`、import 閉包、逆依存、`sorry` / `admit`、束縛 hash の再計算。 -/
def checkHome (proofsDir generated : System.FilePath) (consensus : Option ParsedObligations) : M Unit := do
  let p ← runProc "lake" #["exe", "naru", "proofs", "--json"]
  match parseProofsJson p.stdout with
  | .error e => fail s!"C70 home: lake exe naru proofs --json (exit {p.exitCode}) does not parse: {e}\n{tail (p.stdout ++ p.stderr) 800}"
  | .ok (counts, results, build) =>
    let invalid := (counts.lookup "invalid").getD 99
    if p.exitCode == 0 && invalid == 0 && build == "ok" && results.length == consensusObligations then
      ok s!"C70 home: lake exe naru proofs --json exits 0 for the {consensusObligations} consensus obligations with invalid 0 (counts {counts})"
    else fail s!"C70 home: exit {p.exitCode}, counts {counts}, build {build}, {results.length} results"
    -- C71 の進捗: 証明済みの一覧が proved のまま(退行していない)
    let notProved := consensusProved.filter fun n => results.lookup n != some "proved"
    let proved := (counts.lookup "proved").getD 0
    if notProved.isEmpty && proved == consensusProved.length then
      ok s!"C71 progress: {consensusProved.length} of {consensusObligations} consensus obligations are proved ({consensusProved}); the other {consensusObligations - consensusProved.length} are not yet proved"
    else fail s!"C71 progress: expected exactly {consensusProved} to be proved, but not proved {notProved} and counts.proved = {proved}: {results.filter fun (_, s) => s == "proved"}"
  let b ← runProc "lake" #["build", "Proofs"]
  if b.exitCode == 0 then ok "C68: lake build Proofs exit 0" else fail s!"C68: lake build Proofs exit {b.exitCode}\n{tail b.stderr}"
  if let some c := consensus then checkHashRecomputation "C69 consensus" generated c
  -- import 閉包
  let mut mods : List String := []
  for f in (← Naru.listFiles proofsDir "lean") do
    let rel := (f.drop (proofsDir.toString.length + 1)).toString
    if rel == "Proofs.lean" then mods := mods ++ ["Proofs"]
    else if rel.startsWith "Proofs/" then mods := mods ++ [((rel.dropEnd ".lean".length).toString.replace "/" ".")]
  let rootOf (n : String) : String := (n.splitOn ".").head!
  match ← leanClosure mods with
  | .error e => fail s!"C68: {e}"
  | .ok names =>
    let outside := names.filter fun n => !(allowedRoots.contains (rootOf n))
    let bad := names.filter fun n => forbidden.any fun f => n == f || n.startsWith f || n.startsWith (f ++ ".")
    let hasStatements := names.any (·.startsWith "Statements.")
    let hasMathlib := names.any (·.startsWith "Mathlib.")
    if outside.isEmpty && bad.isEmpty && hasStatements && hasMathlib then
      ok s!"C68: the import closure of {mods} ({names.length} modules) lies within {allowedRoots} (generated Statements and Mathlib present); 0 modules of DecoupledConsensus / NaruSem / Naru / NaruTest"
    else fail s!"C68: closure of Proofs: outside the allowed roots {outside.take 5}, forbidden {bad.take 5}, Statements {hasStatements}, Mathlib {hasMathlib}"
  -- 逆依存: 生成物・stdlib・NaruSem・コンパイラの閉包に Proofs も mathlib も無い
  let sem ← runProc "lake" #["build", "NaruSem", "Naru", "NaruStd", "Model", "Statements"]
  if sem.exitCode != 0 then fail s!"C68: lake build NaruSem Naru NaruStd Model Statements exit {sem.exitCode}\n{tail sem.stderr}"
  else
    match ← leanClosure reverseRoots with
    | .error e => fail s!"C68 reverse: {e}"
    | .ok names =>
      let proofs := names.filter fun n => n == "Proofs" || n.startsWith "Proofs."
      let mathlib := names.filter fun n => mathlibRoots.contains (rootOf n)
      if proofs.isEmpty && mathlib.isEmpty then
        ok s!"C68: the import closure of {reverseRoots} ({names.length} modules) contains no Proofs module and no module of {mathlibRoots} (only Proofs uses mathlib)"
      else fail s!"C68: closure of {reverseRoots}: Proofs {proofs.take 3}, mathlib {mathlib.take 3}"
  let g ← runProc "grep" #["-rnwE", "sorry|admit", "--include=*.lean", proofsDir.toString]
  if g.exitCode == 1 then ok s!"C71: grep -rnwE 'sorry|admit' --include='*.lean' {proofsDir}/ finds nothing"
  else fail s!"C71: sorry / admit under {proofsDir}/ (exit {g.exitCode}):\n{tail g.stdout 600}"

/-- C72: 書き手の案内と文書。 -/
def checkDocs : M Unit := do
  let readme : System.FilePath := "proofs" / "README.md"
  if !(← readme.pathExists) then fail s!"C72: {readme} not found"
  else
    let text ← IO.FS.readFile readme
    let missing := readmeWords.filter fun w => !(contains text w)
    if missing.isEmpty then ok s!"C72: {readme} mentions {readmeWords}"
    else fail s!"C72: {readme} lacks {missing}"
  -- `--untracked`: 新しく書いた文書は次の commit まで追跡対象外なので、追跡対象外のファイルも検索する(commit 後は `git grep -l 'naru proofs' -- …` と同じ結果)
  let g ← runProc "git" (#["grep", "-l", "--untracked", "naru proofs", "--"] ++ docsWithProofs.toArray)
  let hits := ((g.stdout.splitOn "\n").filter (!·.isEmpty)).mergeSort (· ≤ ·)
  if hits == docsWithProofs.mergeSort (· ≤ ·) then ok s!"C72: git grep -l --untracked 'naru proofs' hits all of {docsWithProofs}"
  else fail s!"C72: git grep -l --untracked 'naru proofs' -- {docsWithProofs}: {hits} (exit {g.exitCode})"

def checks : M Unit := do
  let root ← IO.currentDir
  let build ← runProc "lake" #["build", "naru"]
  if build.exitCode != 0 then
    fail s!"lake build naru exit {build.exitCode}: {tail build.stderr}"
    return
  ok "lake build naru exit 0"
  let bin := root / ".lake" / "build" / "bin" / "naru"
  if !(← bin.pathExists) then
    fail s!"{bin} not found"
    return
  let env : Env := { root, bin }
  let cfg ← match ← Naru.readConfig Naru.configFileName with
    | .ok cfg => pure cfg
    | .error e => fail s!"{Naru.configFileName}: {e}"; return
  let roots := cfg.rootPaths
  let generated := cfg.generatedPath
  let some proofsDir := cfg.proofsPath
    | fail s!"C68: {Naru.configFileName} has no `proofs = \"<dir>\"`"; return
  ok s!"{Naru.configFileName}: sources {roots}, generated {generated}, proofs {proofsDir}"
  IO.FS.createDirAll workDir
  let consensus ← checkConsensus env roots generated
  let sample ← checkSample env
  checkNoClaims env
  checkCompileIgnoresProofs env
  if let some (dir, p) := sample then checkProofsSample env dir p
  -- ホーム(`naru proofs` が link をホームに戻す)
  let _ ← runProc "lake" #["exe", "naru", "compile"]
  checkHome proofsDir generated consensus
  checkDocs

def run : IO UInt32 := runGroup "naru_test proofs" checks

end NaruTest.Proofs
