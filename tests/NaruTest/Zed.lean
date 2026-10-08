import NaruTest.Common

/-!
# `naru_test zed` — Zed 拡張の検査(IDEAL.md C17)

`editors/zed-naru/` の Dev Extension が、`.naru` を言語 `naru` に対応付け、文法をこのリポジトリの `rev` のコミットから取り、
言語サーバー `naru lsp` を起動する形になっていることを確かめる。リポジトリのルートで実行する。

1. 5 ファイル(`extension.toml`・`languages/naru/config.toml`・`languages/naru/highlights.scm`・`Cargo.toml`・`src/lib.rs`)がある。
2. `extension.toml`: `id = "naru"`、`[grammars.naru]` の `repository = "file://<このリポジトリのルート>"`・`rev`(40 桁の SHA)・
   `path = "editors/tree-sitter-naru"`、`[language_servers.naru]` の `name` と `languages = ["naru"]`。鍵の重複は FAIL。
3. `languages/naru/config.toml`: `name = "naru"`、`grammar = "naru"`、`path_suffixes` に `naru`、`language_servers` に `naru`。
4. `rev` がこのリポジトリのコミットで HEAD の祖先、`git diff --exit-code <rev> HEAD -- editors/tree-sitter-naru` が空
   (Zed が使う文法 = HEAD の文法)。
5. `rev` の文法を `git archive` で取り出して `tree-sitter build` が exit 0、作業ツリーの `languages/naru/highlights.scm` を
   その文法で `tree-sitter query` してエラーなくロードできる(捕捉が 1 つ以上出る)。文法を変えた周回では作業ツリーの文法と
   `rev` の文法が違うので、パーサのキャッシュは `TREE_SITTER_LIBDIR` で `naru_test grammar` のものと分ける。
6. `Cargo.toml` が `crate-type = ["cdylib"]` と `zed_extension_api` を持ち、`src/lib.rs` が `lsp.naru.binary.path` の設定 →
   `PATH` 上の `naru` → `.lake/build/bin/naru` の順に探して引数 `lsp` で起動する形(字句の有無と、3 段が現れる順)、
   `cargo build --release --target wasm32-wasip2` が exit 0 で `target/wasm32-wasip2/release/zed_naru.wasm` ができる。

一時ファイルは `.lake/naru/test/zed/` に置く(追跡対象外)。cargo の成果物は `editors/zed-naru/target/`(`.gitignore` で除外)。
-/

namespace NaruTest.Zed

def extDir : System.FilePath := "editors" / "zed-naru"
def grammarRel : String := "editors/tree-sitter-naru"
def extensionToml : System.FilePath := extDir / "extension.toml"
def configToml : System.FilePath := extDir / "languages" / "naru" / "config.toml"
def highlights : System.FilePath := extDir / "languages" / "naru" / "highlights.scm"
def cargoToml : System.FilePath := extDir / "Cargo.toml"
def libRs : System.FilePath := extDir / "src" / "lib.rs"
def wasmOut : System.FilePath := extDir / "target" / "wasm32-wasip2" / "release" / "zed_naru.wasm"
def syntaxExample : System.FilePath := "tests" / "accept" / "editors_syntax.naru"
def scratchDir : System.FilePath := ".lake" / "naru" / "test" / "zed"

/-! ## 最小の TOML 読み(この拡張のファイルに現れる形だけ: 文字列・文字列の配列・テーブル見出し) -/

inductive TomlValue where
  | str (s : String)
  | arr (xs : List String)
  | other (raw : String)
deriving Repr, BEq

/-- `(テーブル名, キー, 値)`。トップレベルのテーブル名は `""`。 -/
abbrev Toml := List (String × String × TomlValue)

def unquote (s : String) : Option String :=
  let s := s.trimAscii.toString
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then
    some ((s.drop 1).toString.dropEnd 1).toString
  else none

def parseValue (v : String) : TomlValue :=
  match unquote v with
  | some s => .str s
  | none =>
    if v.startsWith "[" && v.endsWith "]" then
      let inner := ((v.drop 1).toString.dropEnd 1).toString
      let items := ((inner.splitOn ",").map (·.trimAscii.toString)).filter (!·.isEmpty)
      match items.mapM unquote with
      | some xs => .arr xs
      | none => .other v
    else .other v

/-- 行ごとに読む: `[table]` / `key = value`。値の `[` が同じ行で閉じなければ `]` で終わる行まで繋ぐ。
`#` 始まりの行と空行は飛ばす(行の途中の `#` は見ない)。 -/
def parseToml (src : String) : Toml := Id.run do
  let mut table := ""
  let mut out : Array (String × String × TomlValue) := #[]
  let mut pending : Option (String × String) := none
  for raw in src.splitOn "\n" do
    let l := raw.trimAscii.toString
    match pending with
    | some (k, acc) =>
      let acc := acc ++ " " ++ l
      if l.endsWith "]" then
        out := out.push (table, k, parseValue acc)
        pending := none
      else
        pending := some (k, acc)
    | none =>
      if l.isEmpty || l.startsWith "#" then continue
      if l.startsWith "[" then
        -- 見出し `[table]`(後ろにコメントがあってもよい)
        match (l.drop 1).toString.splitOn "]" with
        | h :: _ => table := h.trimAscii.toString
        | [] => continue
      else
        match l.splitOn "=" with
        | k :: rest@(_ :: _) =>
          let k := k.trimAscii.toString
          let v := ("=".intercalate rest).trimAscii.toString
          if v.startsWith "[" && !v.endsWith "]" then pending := some (k, v)
          else out := out.push (table, k, parseValue v)
        | _ => continue
  return out.toList

def lookup (t : Toml) (table key : String) : Option TomlValue :=
  (t.find? fun (tb, k, _) => tb == table && k == key).map (·.2.2)

def where' (file : System.FilePath) (table key : String) : String :=
  if table.isEmpty then s!"{file}: {key}" else s!"{file}: [{table}] {key}"

/-- 同じテーブルに同じ鍵が 2 度現れたもの(TOML として不正。Zed は拒否するので、`lookup` が最初の 1 つで ok を出す前に止める)。 -/
def duplicateKeys (t : Toml) : List String := Id.run do
  let mut seen : List (String × String) := []
  let mut dup : List String := []
  for (tb, k, _) in t do
    if seen.contains (tb, k) then dup := dup ++ [if tb.isEmpty then k else s!"[{tb}] {k}"]
    else seen := (tb, k) :: seen
  return dup

def checkNoDuplicates (file : System.FilePath) (t : Toml) : M Unit := do
  match duplicateKeys t with
  | [] => pure ()
  | dup => fail s!"{file}: duplicate keys {dup} (invalid TOML)"

def expectStr (file : System.FilePath) (t : Toml) (table key want : String) : M Unit := do
  match lookup t table key with
  | some (.str s) =>
    if s == want then ok s!"{where' file table key} = \"{want}\""
    else fail s!"{where' file table key} = \"{s}\" (expected \"{want}\")"
  | some v => fail s!"{where' file table key} is not a string: {repr v}"
  | none => fail s!"{where' file table key} is missing"

def expectNonEmptyStr (file : System.FilePath) (t : Toml) (table key : String) : M Unit := do
  match lookup t table key with
  | some (.str s) =>
    if s.isEmpty then fail s!"{where' file table key} is empty" else ok s!"{where' file table key} = \"{s}\""
  | some v => fail s!"{where' file table key} is not a string: {repr v}"
  | none => fail s!"{where' file table key} is missing"

def expectArrContains (file : System.FilePath) (t : Toml) (table key want : String) : M Unit := do
  match lookup t table key with
  | some (.arr xs) =>
    if xs.contains want then ok s!"{where' file table key} contains \"{want}\" ({xs})"
    else fail s!"{where' file table key} = {xs} does not contain \"{want}\""
  | some v => fail s!"{where' file table key} is not an array of strings: {repr v}"
  | none => fail s!"{where' file table key} is missing"

def isHex40 (s : String) : Bool :=
  s.length == 40 && s.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-! ## 1. ファイルの存在 -/

def checkFiles : M Bool := do
  let mut missing : Array String := #[]
  for f in [extensionToml, configToml, highlights, cargoToml, libRs] do
    if !(← f.pathExists) then missing := missing.push f.toString
  if missing.isEmpty then
    ok s!"{extDir}: extension.toml, languages/naru/config.toml, languages/naru/highlights.scm, Cargo.toml, src/lib.rs present"
    return true
  else
    fail s!"{extDir}: missing {missing}"
    return false

/-! ## 2. extension.toml -/

/-- `git rev-parse --show-toplevel`(拡張の `repository` はこのリポジトリの `file://` URL でなければならない)。 -/
def repoRoot : IO (Option String) := do
  let out ← runProc "git" #["rev-parse", "--show-toplevel"]
  if out.exitCode == 0 then return some out.stdout.trimAscii.toString else return none

def checkManifest : M (Option String) := do
  let t := parseToml (← IO.FS.readFile extensionToml)
  checkNoDuplicates extensionToml t
  expectStr extensionToml t "" "id" "naru"
  match ← repoRoot with
  | some root => expectStr extensionToml t "grammars.naru" "repository" s!"file://{root}"
  | none => fail "git rev-parse --show-toplevel failed (run from inside the repository)"
  expectStr extensionToml t "grammars.naru" "path" grammarRel
  expectNonEmptyStr extensionToml t "language_servers.naru" "name"
  expectArrContains extensionToml t "language_servers.naru" "languages" "naru"
  match lookup t "grammars.naru" "rev" with
  | some (.str rev) =>
    if isHex40 rev then
      ok s!"{where' extensionToml "grammars.naru" "rev"} = {rev} (40 hex digits)"
      return some rev
    else
      fail s!"{where' extensionToml "grammars.naru" "rev"} = \"{rev}\" is not a 40-digit commit SHA (branch names do not update: pin a commit)"
      return none
  | some v =>
    fail s!"{where' extensionToml "grammars.naru" "rev"} is not a string: {repr v}"
    return none
  | none =>
    fail s!"{where' extensionToml "grammars.naru" "rev"} is missing"
    return none

/-! ## 3. languages/naru/config.toml -/

def checkLanguageConfig : M Unit := do
  let t := parseToml (← IO.FS.readFile configToml)
  checkNoDuplicates configToml t
  expectStr configToml t "" "name" "naru"
  expectStr configToml t "" "grammar" "naru"
  expectArrContains configToml t "" "path_suffixes" "naru"
  expectArrContains configToml t "" "language_servers" "naru"

/-! ## 4. rev がこのリポジトリのコミットで、文法が HEAD と一致 -/

def checkRev (rev : String) : M Bool := do
  let ty ← runProc "git" #["cat-file", "-t", rev]
  if ty.exitCode != 0 || ty.stdout.trimAscii.toString != "commit" then
    fail s!"rev {rev} is not a commit of this repository (git cat-file -t exit {ty.exitCode}: {tail ty.stderr 300})"
    return false
  -- 到達できない(dangling な)コミットは gc で消えうるので、HEAD の祖先であることも求める
  let anc ← runProc "git" #["merge-base", "--is-ancestor", rev, "HEAD"]
  if anc.exitCode != 0 then
    fail s!"rev {rev} is a commit but not an ancestor of HEAD (git merge-base --is-ancestor exit {anc.exitCode}): pin a commit on this branch"
    return false
  ok s!"rev {rev} is a commit of this repository and an ancestor of HEAD"
  let d ← runProc "git" #["diff", "--exit-code", rev, "HEAD", "--", grammarRel]
  if d.exitCode == 0 then
    ok s!"git diff --exit-code {rev} HEAD -- {grammarRel} is empty (Zed compiles the same grammar as HEAD)"
    return true
  else
    fail s!"git diff {rev} HEAD -- {grammarRel} is not empty (exit {d.exitCode}): move rev to the last commit that changed the grammar (`git log -1 --format=%H -- {grammarRel}`)\n{tail d.stdout 800}"
    return false

/-! ## 5. rev の文法でビルドし、作業ツリーの highlights.scm をロード -/

def checkGrammarAtRev (rev : String) : M Unit := do
  let cwd ← IO.currentDir
  let scratch := cwd / scratchDir / "rev"
  if ← scratch.isDir then IO.FS.removeDirAll scratch
  IO.FS.createDirAll scratch
  let tar := scratch / "grammar.tar"
  let ar ← runProc "git" #["archive", "--format=tar", "-o", tar.toString, rev, grammarRel]
  if ar.exitCode != 0 then
    fail s!"git archive {rev} {grammarRel} exit {ar.exitCode}: {tail ar.stderr 500}"
    return
  let ex ← runProc "tar" #["-xf", tar.toString, "-C", scratch.toString]
  if ex.exitCode != 0 then
    fail s!"tar -xf {tar} exit {ex.exitCode}: {tail ex.stderr 500}"
    return
  let gdir := scratch / System.FilePath.mk grammarRel
  if !(← (gdir / "src" / "parser.c").pathExists) then
    fail s!"{gdir / "src" / "parser.c"} is missing in rev {rev} (the grammar's generated src/ must be tracked)"
    return
  let lib := scratch / "naru.dylib"
  let b ← runProc "tree-sitter" #["build", "-o", lib.toString] (some gdir)
  if b.exitCode != 0 then
    fail s!"tree-sitter build of the grammar at {rev} exit {b.exitCode}: {tail b.stderr}"
    return
  ok s!"tree-sitter build of the grammar at {rev} exit 0 ({lib})"
  -- 作業ツリーの Zed 側 highlights.scm を rev の文法でロードする。パーサのキャッシュは専用の場所に(grammar 群と混ぜない)
  let libdir := scratch / "lib"
  IO.FS.createDirAll libdir
  let q ← runProc "tree-sitter"
    #["query", (cwd / highlights).toString, (cwd / syntaxExample).toString] (some gdir)
    #[("TREE_SITTER_LIBDIR", some libdir.toString)]
  let captures := ((q.stdout.splitOn "\n").filter fun l => (l.splitOn "capture:").length > 1).length
  if q.exitCode == 0 && captures > 0 then
    ok s!"{highlights} loads with the grammar at {rev} ({captures} captures on {syntaxExample})"
  else
    fail s!"{highlights} does not load with the grammar at {rev} (tree-sitter query exit {q.exitCode}, {captures} captures): keep highlights.scm loadable by rev's grammar until rev is moved\n{tail q.stderr 800}"

/-! ## 6. Rust の glue と wasm ビルド -/

def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- `needle` が最初に現れる位置(文字数)。無ければ none。 -/
def indexOf (hay needle : String) : Option Nat :=
  match hay.splitOn needle with
  | first :: _ :: _ => some first.length
  | _ => none

def checkRust : M Unit := do
  let cargo ← IO.FS.readFile cargoToml
  let mut bad : Array String := #[]
  if !has cargo "crate-type = [\"cdylib\"]" then bad := bad.push "crate-type = [\"cdylib\"]"
  if !has cargo "zed_extension_api" then bad := bad.push "zed_extension_api dependency"
  if bad.isEmpty then ok s!"{cargoToml}: cdylib with zed_extension_api"
  else fail s!"{cargoToml}: missing {bad}"
  let rs ← IO.FS.readFile libRs
  let needles := [("\"naru\"", "server id / binary name `naru`"),
                  ("LspSettings::for_worktree", "Zed setting lsp.naru.binary.path (LspSettings::for_worktree)"),
                  (".which(", "`naru` on PATH (worktree.which)"),
                  (".lake/build/bin/naru", "worktree's .lake/build/bin/naru"),
                  ("\"lsp\"", "argument `lsp`"),
                  ("register_extension!", "zed::register_extension!")]
  let missing := needles.filter fun (n, _) => !has rs n
  if !missing.isEmpty then
    fail s!"{libRs}: missing {missing.map (·.2)}"
    return
  -- 探索の順: 設定 → PATH → ワークツリー(コメント行を除いたコードで、最初に現れる位置の順で見る)
  let code := "\n".intercalate ((rs.splitOn "\n").filter fun l => !(l.trimAscii.toString.startsWith "//"))
  match indexOf code "LspSettings::for_worktree", indexOf code ".which(", indexOf code ".lake/build/bin/naru" with
  | some a, some b, some c =>
    if a < b && b < c then
      ok s!"{libRs}: lsp.naru.binary.path → PATH naru → .lake/build/bin/naru, args [lsp]"
    else
      fail s!"{libRs}: the lookup order must be the setting (LspSettings::for_worktree), then PATH (which), then .lake/build/bin/naru (found at {a} / {b} / {c})"
  | _, _, _ => fail s!"{libRs}: lookup steps not found"

def cargoCmd : IO String := do
  let probe ← runProc "cargo" #["--version"]
  if probe.exitCode != 127 then return "cargo"
  let home := (← IO.getEnv "HOME").getD ""
  return s!"{home}/.cargo/bin/cargo"

def checkCargoBuild : M Unit := do
  let cargo ← cargoCmd
  let out ← runProc cargo #["build", "--release", "--target", "wasm32-wasip2"] (some extDir)
  if out.exitCode != 0 then
    fail s!"{cargo} build --release --target wasm32-wasip2 (in {extDir}) exit {out.exitCode}:\n{tail out.stderr}"
    return
  if ← wasmOut.pathExists then
    ok s!"cargo build --release --target wasm32-wasip2 exit 0 ({wasmOut})"
  else
    fail s!"cargo build exit 0 but {wasmOut} is missing (package name / crate-type?)"

def run : IO UInt32 := do
  if !(← extDir.isDir) then
    IO.eprintln s!"naru_test zed: {extDir} not found (run from the repository root)"
    return 2
  IO.FS.createDirAll scratchDir
  runGroup "naru_test zed" do
    if !(← checkFiles) then return
    let rev ← checkManifest
    checkLanguageConfig
    match rev with
    | some rev =>
      if ← checkRev rev then checkGrammarAtRev rev
    | none => pure ()
    checkRust
    checkCargoBuild

end NaruTest.Zed
