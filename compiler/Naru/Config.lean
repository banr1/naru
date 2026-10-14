/-!
# `naru.toml` — コンパイル単位の設定(IDEAL.md C24)

リポジトリのルートの `naru.toml` が、コンパイル単位のソースルートの一覧(`sources`)と生成先(`generated`)を決める。
`naru compile` / `naru simulate` / `naru lsp` と検査ドライバ(`naru_test`)がこれを読む。コンパイラのコードにソースルートの
ディレクトリ名は書かない。

```toml
sources = [<ソースルート>, …]   # 各ルート配下の **/*.naru が 1 つのコンパイル単位。モジュール名はルートからの相対パスに対応する
generated = <生成先>             # `naru compile` が Model / Statements と証明義務の一覧 `obligations.json` を書くディレクトリ
deps = <依存グラフの出力先>       # `naru deps` が `deps.json` と `index.html` を書くディレクトリ(任意。無ければ `naru deps --out <dir>` が要る。C63)
proofs = <証明ディレクトリ>       # `naru proofs` が読む、プロトコル証明(Lake ライブラリ `Proofs`)のディレクトリ(任意。無ければ `naru proofs` は exit 非 0。C70)
```

読むのは最小限の TOML(`key = "string"` / `key = ["a", "b"]`、`#` のコメント、1 行 1 項目)。表(`[table]`)や複数行の配列は
受理しない。`generated` を省くと `generated`。`deps` は省ける(`naru deps` は `--out` が無ければ exit 非 0)。`proofs` も省ける
(`naru proofs` は exit 非 0。`naru compile` / `simulate` / `lsp` / `deps` は読まない)。
-/

namespace Naru

/-- `naru.toml` の内容。パスは `dir`(`naru.toml` のあるディレクトリ)からの相対で書かれたまま持つ。 -/
structure Config where
  /-- `naru.toml` のあるディレクトリ。CLI では `.`、言語サーバーでは文書の祖先の絶対パス。 -/
  dir : System.FilePath
  /-- ソースルート(書かれた順)。 -/
  sources : List String
  /-- 生成先。 -/
  generated : String
  /-- 依存グラフ(`naru deps`)の出力先。書かれていなければ none(`--out` が要る)。 -/
  deps : Option String := none
  /-- プロトコル証明のディレクトリ(`naru proofs` が読む。Lake ライブラリ `Proofs` の実体)。書かれていなければ none。 -/
  proofs : Option String := none
deriving Repr, Inhabited

def configFileName : String := "naru.toml"

/-- `#` から行末までを落とす(文字列の中の `#` は残す。`\"` は文字列を閉じない)。 -/
private def stripComment (line : String) : String := Id.run do
  let mut out := ""
  let mut inStr := false
  let mut escaped := false
  for c in line.toList do
    if inStr then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then inStr := false
    else
      if c == '"' then inStr := true
      else if c == '#' then break
    out := out.push c
  return out

/-- 配列の中身を `,` で分ける(文字列の中の `,` では分けない)。 -/
private def splitItems (inner : String) : List String := Id.run do
  let mut items : List String := []
  let mut cur := ""
  let mut inStr := false
  let mut escaped := false
  for c in inner.toList do
    if inStr then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then inStr := false
      cur := cur.push c
    else if c == '"' then
      inStr := true
      cur := cur.push c
    else if c == ',' then
      items := items ++ [cur]
      cur := ""
    else cur := cur.push c
  return items ++ [cur]

/-- ソースルートの書き方を正規化する: 先頭の `./` と末尾の `/` を落とす(言語サーバーが文書の絶対パスと文字列で比べるため)。 -/
private def normalizeRoot (s : String) : String := Id.run do
  let mut r := s
  while r.startsWith "./" do r := (r.drop 2).toString
  while r.length > 1 && r.endsWith "/" do r := (r.dropEnd 1).toString
  return r

/-- `"…"` を読む(エスケープは `\"` と `\\` だけ)。 -/
private def parseString (s : String) : Except String String := do
  let s := s.trimAscii.toString
  if !(s.startsWith "\"") then throw s!"expected a quoted string, got `{s}`"
  let mut out := ""
  let mut escaped := false
  let mut closed := false
  for c in (s.drop 1).toString.toList do
    if closed then throw s!"unexpected text after the closing quote in `{s}`"
    if escaped then
      out := out.push c
      escaped := false
    else if c == '\\' then escaped := true
    else if c == '"' then closed := true
    else out := out.push c
  if !closed then throw s!"unterminated string `{s}`"
  return out

/-- `[ "a", "b" ]` を読む。 -/
private def parseStringArray (s : String) : Except String (List String) := do
  let s := s.trimAscii.toString
  if !(s.startsWith "[") || !(s.endsWith "]") then throw s!"expected `[\"…\", …]` on one line, got `{s}`"
  let inner := ((s.drop 1).toString.dropEnd 1).toString.trimAscii.toString
  if inner.isEmpty then return []
  let mut out : List String := []
  for item in splitItems inner do
    let t := item.trimAscii.toString
    if t.isEmpty then continue   -- 末尾の `,`
    out := out ++ [← parseString t]
  return out

/-- `naru.toml` の本文を読む。`dir` はそのファイルのあるディレクトリ。 -/
def parseConfig (dir : System.FilePath) (text : String) : Except String Config := do
  let mut sources : Option (List String) := none
  let mut generated : Option String := none
  let mut deps : Option String := none
  let mut proofs : Option String := none
  let mut lineNo := 0
  for raw in text.splitOn "\n" do
    lineNo := lineNo + 1
    let line := (stripComment raw).trimAscii.toString
    if line.isEmpty then continue
    if line.startsWith "[" then throw s!"line {lineNo}: tables (`{line}`) are not supported in {configFileName}"
    match line.splitOn "=" with
    | key :: rest =>
      if rest.isEmpty then throw s!"line {lineNo}: expected `key = value`, got `{line}`"
      let key := key.trimAscii.toString
      let value := "=".intercalate rest
      match key with
      | "sources" =>
        if sources.isSome then throw s!"line {lineNo}: `sources` is given twice"
        match parseStringArray value with
        | .ok xs => sources := some xs
        | .error e => throw s!"line {lineNo}: sources: {e}"
      | "generated" =>
        if generated.isSome then throw s!"line {lineNo}: `generated` is given twice"
        match parseString value with
        | .ok s => generated := some s
        | .error e => throw s!"line {lineNo}: generated: {e}"
      | "deps" =>
        if deps.isSome then throw s!"line {lineNo}: `deps` is given twice"
        match parseString value with
        | .ok s => deps := some s
        | .error e => throw s!"line {lineNo}: deps: {e}"
      | "proofs" =>
        if proofs.isSome then throw s!"line {lineNo}: `proofs` is given twice"
        match parseString value with
        | .ok s => proofs := some s
        | .error e => throw s!"line {lineNo}: proofs: {e}"
      | _ => throw s!"line {lineNo}: unknown key `{key}` (known: sources, generated, deps, proofs)"
    | [] => throw s!"line {lineNo}: expected `key = value`, got `{line}`"
  let some srcs := sources | throw s!"`sources = [\"<dir>\", …]` is missing"
  let srcs := srcs.map normalizeRoot
  if srcs.isEmpty then throw "`sources` is empty; list at least one source root"
  for s in srcs do
    if s.isEmpty || s == "." || s.startsWith "/" then throw s!"source root `{s}` must be a non-empty path relative to {configFileName} (not the root itself)"
  if srcs.eraseDups.length != srcs.length then throw "`sources` lists the same root twice"
  let gen := generated.getD "generated"
  if gen.isEmpty then throw "`generated` must not be empty"
  if deps == some "" then throw "`deps` must not be empty"
  if proofs == some "" then throw "`proofs` must not be empty"
  return { dir, sources := srcs, generated := gen, deps, proofs }

/-- `naru.toml` を読む。 -/
def readConfig (path : System.FilePath) : IO (Except String Config) := do
  let dir := path.parent.getD "."
  return parseConfig dir (← IO.FS.readFile path)

/-- `dir` からの相対パスを実際のパスにする(`dir` が `.` ならそのまま: CLI の相対パスを保つ)。 -/
def Config.resolve (cfg : Config) (rel : String) : System.FilePath :=
  if cfg.dir.toString == "." || cfg.dir.toString.isEmpty then System.FilePath.mk rel else cfg.dir / System.FilePath.mk rel

/-- ソースルートの実際のパス(書かれた順)。 -/
def Config.rootPaths (cfg : Config) : List System.FilePath := cfg.sources.map cfg.resolve

/-- 生成先の実際のパス。 -/
def Config.generatedPath (cfg : Config) : System.FilePath := cfg.resolve cfg.generated

/-- 依存グラフの出力先の実際のパス(`deps` が書かれていれば)。 -/
def Config.depsPath (cfg : Config) : Option System.FilePath := cfg.deps.map cfg.resolve

/-- 証明ディレクトリの実際のパス(`proofs` が書かれていれば)。 -/
def Config.proofsPath (cfg : Config) : Option System.FilePath := cfg.proofs.map cfg.resolve

/-- `path` の祖先(自分自身を含まない)で最も近い `naru.toml`。無ければ none。 -/
partial def findConfigFrom (path : System.FilePath) : IO (Option System.FilePath) := do
  match path.parent with
  | none => return none
  | some dir =>
    let candidate := dir / System.FilePath.mk configFileName
    if ← candidate.pathExists then return some candidate
    findConfigFrom dir

/-- `path` がソースルート `root` の配下なら、ルートからの相対パス。どちらも文字列で比べる(`root` と `path` は同じ基準の
パス: CLI なら cwd 相対、言語サーバーなら絶対)。 -/
def relativeToRoot (root : System.FilePath) (path : String) : Option String :=
  let r := root.toString
  let r := if r.endsWith "/" then r else r ++ "/"
  if path.startsWith r then some (path.drop r.length).toString else none

/-- `path` がどのソースルートの配下か: (ルートの実際のパス, ルートからの相対パス)。最初に合うルート。 -/
def Config.rootOf (cfg : Config) (path : String) : Option (System.FilePath × String) :=
  cfg.rootPaths.findSome? fun root => (relativeToRoot root path).map fun rel => (root, rel)

end Naru
