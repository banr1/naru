import Naru.Lexer
import Naru.Parser
import Naru.Resolve

/-!
# ドライバ

ファイル群 → 字句解析 → 構文解析 → 名前解決・phase 検査。
構文エラーのあるファイルがあれば後段には進まない(1 ファイル 1 エラーで止まる)。
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
  return (diags, mods)

end Naru
