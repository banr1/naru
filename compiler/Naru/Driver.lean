import Naru.Lexer
import Naru.Parser
import Naru.Resolve
import Naru.Typecheck
import Naru.Totality
import Naru.Modules

/-!
# ドライバ

ファイル群 → 字句解析 → 構文解析 → 同名のモジュール(E017)→ 名前解決・phase 検査 → 型・capability 検査(選択 E003・順序 E004 を含む)
と Core IR への elaboration → Core の健全性 → モジュールの循環(E017)→ 計算可能性検査(停止性 E002)。
構文エラーのあるファイルがあれば後段には進まない(1 ファイル 1 エラーで止まる)。
名前解決の誤りがあれば型検査には進まない(未解決名の波及を避ける)。
型検査の誤りがあれば停止性検査には進まない(呼出し先の署名が要る)。
診断が 1 つでもあれば Core は空(backend には届かない)。

モジュール構造(同名のモジュール・生成 Model / Statements の import の循環)は backend ではなくここ(`Modules.lean`)で検査するので、
CLI の `compile`(出力指定あり / なし)と言語サーバーのすべてが同じ E017 を実在する行・列に返す(C18)。

入口は 2 つ: `compileFiles`(パスを読む。CLI の `compile` / `check-reject`)と `compileSources`(パスと内容の組。
言語サーバー `naru lsp` がエディタのバッファを渡す)。検査そのものは純粋で、どちらも同じ `compileSources` を通る。
-/

namespace Naru

/-- ディレクトリ配下の拡張子 `ext` のファイルをパス順に列挙する(決定的な順序)。 -/
def listFiles (dir : System.FilePath) (ext : String) : IO (List String) := do
  if !(← dir.isDir) then return []
  let all ← dir.walkDir
  let hits := all.filter (·.extension == some ext)
  let sorted := hits.qsort (fun a b => a.toString < b.toString)
  return sorted.toList.map (·.toString)

def parseSource (path : String) (src : String) : Except Diagnostic Module := do
  let toks ← lexAll path src
  parseModule path toks

def parseFile (path : String) : IO (Except Diagnostic Module) := do
  return parseSource path (← IO.FS.readFile path)

/-- 検査を通ったコンパイル単位。backend への入力。 -/
structure Checked where
  mods : Array Module
  core : Array Core.Module
  /-- 受理した再帰のサイクルと測度(`Totality`)。 -/
  recursions : Array Totality.Recursion
deriving Inhabited

/-- `(パス, 内容)` の列を 1 つのコンパイル単位として検査する。診断の `file` には与えたパスがそのまま入る。
診断の配列(空なら成功)と、読めたモジュール・Core を返す。 -/
def compileSources (sources : List (String × String)) : Array Diagnostic × Checked := Id.run do
  let mut diags : Array Diagnostic := #[]
  let mut mods : Array Module := #[]
  for (path, src) in sources do
    match parseSource path src with
    | .ok m => mods := mods.push m
    | .error d => diags := diags.push d
  let mut core : Array Core.Module := #[]
  let mut recs : Array Totality.Recursion := #[]
  let mut refs : Array Resolve.Ref := #[]
  if diags.isEmpty then
    -- C18: 同名のモジュール(E017)。名前解決の前に(大域表の鍵がモジュール名で決まるので)
    diags := Modules.duplicates mods
  if diags.isEmpty then
    let (ds, rs) := resolveAll mods
    diags := ds
    refs := rs
  if diags.isEmpty then
    let (ds, cs) := typecheckAll mods
    diags := ds
    core := cs
  if diags.isEmpty then
    -- C35: 診断なしに検査を通った Core に `.error` / 未解決の型が残っていればコンパイラの不変条件の破れ。
    -- 黙って backend に渡さず、宣言の位置に E014 を出す(`Core.Decl.unsound`)
    for cm in core do
      for (key, issues) in cm.unsound do
        let name := (key.splitOn ".").getLast!
        let span := ((mods.find? (·.name == cm.name)).bind fun m => m.decls.find? (·.name == name)).map (·.span) |>.getD {}
        let shown := ", ".intercalate (issues.take 3) ++ (if issues.length > 3 then ", …" else "")
        let msg := s!"internal: the checked Core of `{name}` still contains unresolved types or error nodes ({shown}); this is a compiler bug (no diagnostic was reported for it), so the declaration is rejected instead of being generated"
        diags := diags.push { file := cm.file, span := span, code := Code.typeMismatch, msg := msg }
  if diags.isEmpty then
    -- C18: 生成 Model / Statements の import の循環(E017)。循環に関与する参照の行・列に出す(停止性の前: モジュールを跨ぐ
    -- 相互再帰は E002 ではなく循環として報告する)
    diags := Modules.cycles mods core refs
  if diags.isEmpty then
    let (ds, rs) := totalityAll mods
    diags := ds
    recs := rs
  if !diags.isEmpty then
    core := #[]
  return (diags, { mods, core, recursions := recs })

/-- パス列を読んで 1 つのコンパイル単位として検査する(`compileSources`)。 -/
def compileFiles (paths : List String) : IO (Array Diagnostic × Checked) := do
  let mut sources : List (String × String) := []
  for p in paths do
    sources := sources ++ [(p, ← IO.FS.readFile p)]
  return compileSources sources

end Naru
