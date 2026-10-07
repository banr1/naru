import Naru.Lexer
import Naru.Parser
import Naru.Resolve
import Naru.Typecheck
import Naru.Totality

/-!
# ドライバ

ファイル群 → 字句解析 → 構文解析 → 名前解決・phase 検査 → 型・capability 検査(選択 E003・順序 E004 を含む)
→ 計算可能性検査(停止性 E002)。
構文エラーのあるファイルがあれば後段には進まない(1 ファイル 1 エラーで止まる)。
名前解決の誤りがあれば型検査には進まない(未解決名の波及を避ける)。
型検査の誤りがあれば停止性検査には進まない(呼出し先の署名が要る)。
-/

namespace Naru

def parseFile (path : String) : IO (Except Diagnostic Module) := do
  let src ← IO.FS.readFile path
  return (do
    let toks ← lexAll path src
    parseModule path toks)

/-- 診断の配列(空なら成功)と、読めたモジュールを返す。 -/
def compileFiles (paths : List String) : IO (Array Diagnostic × Array Module) := do
  let mut diags : Array Diagnostic := #[]
  let mut mods : Array Module := #[]
  for p in paths do
    match ← parseFile p with
    | .ok m => mods := mods.push m
    | .error d => diags := diags.push d
  if diags.isEmpty then
    diags := resolveAll mods
  if diags.isEmpty then
    diags := typecheckAll mods
  if diags.isEmpty then
    diags := totalityAll mods
  return (diags, mods)

end Naru
