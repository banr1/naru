import Naru.Lexer
import Naru.Parser
import Naru.Resolve
import Naru.Typecheck
import Naru.Totality

/-!
# ドライバ

ファイル群 → 字句解析 → 構文解析 → 名前解決・phase 検査 → 型・capability 検査(選択 E003・順序 E004 を含む)
と Core IR への elaboration → 計算可能性検査(停止性 E002)。
構文エラーのあるファイルがあれば後段には進まない(1 ファイル 1 エラーで止まる)。
名前解決の誤りがあれば型検査には進まない(未解決名の波及を避ける)。
型検査の誤りがあれば停止性検査には進まない(呼出し先の署名が要る)。
診断が 1 つでもあれば Core は空(backend には届かない)。

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
  if diags.isEmpty then
    diags := resolveAll mods
  if diags.isEmpty then
    let (ds, cs) := typecheckAll mods
    diags := ds
    core := cs
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
