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
-/

namespace Naru

def parseFile (path : String) : IO (Except Diagnostic Module) := do
  let src ← IO.FS.readFile path
  return (do
    let toks ← lexAll path src
    parseModule path toks)

/-- 検査を通ったコンパイル単位。backend への入力。 -/
structure Checked where
  mods : Array Module
  core : Array Core.Module
  /-- 受理した再帰のサイクルと測度(`Totality`)。 -/
  recursions : Array Totality.Recursion
deriving Inhabited

/-- 診断の配列(空なら成功)と、読めたモジュール・Core を返す。 -/
def compileFiles (paths : List String) : IO (Array Diagnostic × Checked) := do
  let mut diags : Array Diagnostic := #[]
  let mut mods : Array Module := #[]
  for p in paths do
    match ← parseFile p with
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

end Naru
