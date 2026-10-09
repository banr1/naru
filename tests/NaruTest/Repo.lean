import Naru
import NaruTest.Common

/-!
# `naru_test repo` — リポジトリの構成と文書の検査(IDEAL.md C21 / C23 / C25)

リポジトリのルートで `lake exe naru_test repo [--base-commit <sha>]` と実行する。

- C21(README): ルートに `README.md` がある。ルート直下の追跡対象のディレクトリ(`git ls-files` の第 1 要素。作業木で消した
  ファイルだけのディレクトリ(`git ls-files --deleted`)は数えない)がすべて README の構成表(最初の列)に現れる。README と
  `docs/*.md` の相対リンクがすべて実在するファイルまたは見出しを指す。README の「クイックスタート」の節のコマンド(`sh` の
  コードブロック。取得(`git clone` / `git submodule`)を除く)を順に実行して exit 0。`naru simulate` の出力が README に引いた
  抜粋(同じ節の `text` のコードブロック)の各行を含む。
- C23(verified-consensus の submodule): ルート直下に `verified-consensus/` が無い。`.gitmodules` の `third_party/verified-consensus`
  の `url` が上流。`git ls-tree HEAD third_party/verified-consensus` が mode 160000 で、その SHA が `git -C third_party/verified-consensus
  rev-parse HEAD`・`third_party/README.md` に書かれた SHA・基準コミット(`--base-commit`、無ければ IDEAL.md の前提「基準コミット」の行)の
  すべてと一致する。`git -C third_party/verified-consensus status --porcelain` が空。
- C25(文書): `docs/` の 7 ファイルがあり、旧文書(`compiler/` 直下の構文リファレンス)が無い。`docs/diagnostics.md` が
  `compiler/Naru/Diag.lean` に定義された E 番号をすべて載せ、それ以外の E 番号を載せない。旧文書の名前への参照が追跡対象のファイルに
  無い(`git grep -l`。`.idd/cycles/` と `.idd/journal.jsonl`(履歴)、IDEAL.md(条件の文面そのものが旧文書を名指しする)を除く)。
-/

namespace NaruTest.Repo

def readmePath : System.FilePath := "README.md"
def docsDir : System.FilePath := "docs"
def docFiles : List String :=
  ["language.md", "diagnostics.md", "cli.md", "architecture.md", "testing.md", "editors.md", "roadmap.md"]
/-- 旧文書の名前。この検査自身が `git grep` に引っ掛からないよう、連結で作る。 -/
def oldDocName : String := "SYNTAX" ++ ".md"
def oldDocPath : System.FilePath := "compiler" / System.FilePath.mk oldDocName
def diagSource : System.FilePath := "compiler" / "Naru" / "Diag.lean"
def vcPath : String := "third_party/verified-consensus"
def vcUpstream : String := "https://github.com/fradamt/verified-consensus"
def thirdPartyReadme : System.FilePath := "third_party" / "README.md"
def idealPath : System.FilePath := "IDEAL.md"

/-! ## 小さな補助 -/

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- 文字列中の 40 桁の 16 進(SHA)をすべて取る。 -/
def shasIn (s : String) : List String := Id.run do
  let cs := s.toList.toArray
  let mut out : List String := []
  let mut i := 0
  while i < cs.size do
    if isHex cs[i]! && (i == 0 || !(cs[i - 1]!.isAlphanum)) then
      let mut j := i
      while j < cs.size && isHex cs[j]! do j := j + 1
      if j - i == 40 && (j == cs.size || !(cs[j]!.isAlphanum)) then
        out := out ++ [String.ofList (cs.extract i j).toList]
      i := j
    else
      i := i + 1
  return out

/-- `E` + 3 桁の番号をすべて取る(重複なし、順序は出現順)。 -/
def codesIn (s : String) : List String := Id.run do
  let cs := s.toList.toArray
  let mut out : List String := []
  let mut i := 0
  while i + 3 < cs.size + 0 do
    if cs[i]! == 'E' && cs[i + 1]!.isDigit && cs[i + 2]!.isDigit && cs[i + 3]!.isDigit &&
        (i == 0 || !(cs[i - 1]!.isAlphanum)) && (i + 4 ≥ cs.size || !(cs[i + 4]!.isAlphanum)) then
      let code := String.ofList (cs.extract i (i + 4)).toList
      if !out.contains code then out := out ++ [code]
      i := i + 4
    else
      i := i + 1
  return out

/-- markdown の見出し(`#` 始まり)の GitHub 風のアンカー: 小文字にし、英数字・`-`・`_`・空白・非 ASCII 以外を落とし、空白を `-` に。 -/
def slugOf (heading : String) : String :=
  let text := (heading.dropWhile (· == '#')).trimAscii.toString
  let kept := text.toList.filter fun c => c.isAlphanum || c == '-' || c == '_' || c == ' ' || c.toNat > 127
  String.ofList (kept.map fun c => if c == ' ' then '-' else c.toLower)

/-- markdown の `[text](target)` の target をすべて取る(画像 `![…](…)` も含む)。 -/
def linkTargets (src : String) : List String := Id.run do
  let mut out : List String := []
  for part in (src.splitOn "](").drop 1 do
    match (part.splitOn ")")[0]? with
    | some t => if !t.isEmpty then out := out ++ [t.trimAscii.toString]
    | none => pure ()
  return out

def isExternal (t : String) : Bool :=
  t.startsWith "http://" || t.startsWith "https://" || t.startsWith "mailto:" || t.startsWith "file://"

/-- 節(見出しで区切る)の中のコードブロック: (info 文字列, 行)。 -/
def codeBlocks (lines : List String) : List (String × List String) := Id.run do
  let mut out : List (String × List String) := []
  let mut cur : Option (String × List String) := none
  for l in lines do
    match cur with
    | none => if l.startsWith "```" then cur := some ((l.drop 3).toString.trimAscii.toString, [])
    | some (info, body) =>
      if l.startsWith "```" then
        out := out ++ [(info, body)]
        cur := none
      else cur := some (info, body ++ [l])
  return out

def headingLevel (l : String) : Nat := (l.takeWhile (· == '#')).toString.length

/-- 見出し行の本文に `key` を含む最初の節(見出しの次の行から、同じかそれより浅い見出しの前まで)。 -/
def sectionContaining (lines : List String) (key : String) : Option (List String) := Id.run do
  let arr := lines.toArray
  let mut i := 0
  while i < arr.size do
    let l := arr[i]!
    let lvl := headingLevel l
    if lvl > 0 && (l.splitOn key).length > 1 then
      let mut j := i + 1
      let mut body : List String := []
      while j < arr.size do
        let m := arr[j]!
        let ml := headingLevel m
        if ml > 0 && ml ≤ lvl then break
        body := body ++ [m]
        j := j + 1
      return some body
    i := i + 1
  return none

/-! ## C21: README -/

/-- `git ls-files` の第 1 要素(ディレクトリだけ)。作業木で消したファイルだけから成るディレクトリは数えない。 -/
def trackedRootDirs : IO (Except String (List String)) := do
  let all ← runProc "git" #["ls-files"]
  if all.exitCode != 0 then return .error s!"git ls-files: exit {all.exitCode}\n{tail all.stderr}"
  let deleted ← runProc "git" #["ls-files", "--deleted"]
  if deleted.exitCode != 0 then return .error s!"git ls-files --deleted: exit {deleted.exitCode}\n{tail deleted.stderr}"
  let gone := (deleted.stdout.splitOn "\n").filter (!·.isEmpty)
  let mut dirs : List String := []
  for p in all.stdout.splitOn "\n" do
    if p.isEmpty || gone.contains p then continue
    match p.splitOn "/" with
    | d :: _ :: _ => if !dirs.contains d then dirs := dirs ++ [d]
    | _ => pure ()
  return .ok dirs

/-- README の表の最初の列(`|` で始まる行)。バッククォートと末尾の `/` を落とす。 -/
def tableFirstColumn (src : String) : List String := Id.run do
  let mut out : List String := []
  for l in src.splitOn "\n" do
    let t := l.trimAscii.toString
    if !t.startsWith "|" then continue
    match (t.splitOn "|")[1]? with
    | some cell =>
      let c := (cell.replace "`" "").trimAscii.toString
      let c := if c.endsWith "/" then (c.dropEnd 1).toString else c
      if !c.isEmpty then out := out ++ [c]
    | none => pure ()
  return out

def checkReadmeTable : M Unit := do
  if !(← readmePath.pathExists) then
    fail s!"{readmePath} not found at the repository root"
    return
  ok s!"{readmePath} exists"
  let src ← IO.FS.readFile readmePath
  match ← trackedRootDirs with
  | .error e => fail e
  | .ok dirs =>
    let cells := tableFirstColumn src
    let missing := dirs.filter fun d => !cells.contains d
    if missing.isEmpty then ok s!"README の構成表に追跡対象のルート直下のディレクトリ {dirs.length} 件がすべてある: {", ".intercalate dirs}"
    else fail s!"README の構成表に無いルート直下のディレクトリ: {missing}(表の最初の列: {cells})"

/-- `file` の中の相対リンクを検査する。 -/
def checkLinksOf (file : System.FilePath) : M Nat := do
  let src ← IO.FS.readFile file
  let dir := file.parent.getD "."
  let headingsOf (p : System.FilePath) : IO (List String) := do
    return ((← IO.FS.readFile p).splitOn "\n").filter (headingLevel · > 0) |>.map slugOf
  let mut n := 0
  for t in linkTargets src do
    if isExternal t then continue
    n := n + 1
    let (path, frag) := match t.splitOn "#" with
      | [p] => (p, "")
      | p :: f :: _ => (p, f)
      | [] => ("", "")
    let target : System.FilePath := if path.isEmpty then file else dir / System.FilePath.mk path
    if !(← target.pathExists) then
      fail s!"{file}: link `{t}` → {target} does not exist"
      continue
    if !frag.isEmpty then
      if ← target.isDir then
        fail s!"{file}: link `{t}` has an anchor but points at a directory"
      else
        let hs ← headingsOf target
        if !hs.contains frag.toLower then fail s!"{file}: link `{t}` → no heading `#{frag}` in {target} (headings: {hs})"
  return n

def checkLinks : M Unit := do
  let mut files : List System.FilePath := [readmePath]
  for d in docFiles do files := files ++ [docsDir / System.FilePath.mk d]
  let before := (← get).failures.size
  let mut n := 0
  for f in files do
    if ← f.pathExists then n := n + (← checkLinksOf f)
  if (← get).failures.size == before then ok s!"README と docs/*.md の相対リンク {n} 件がすべて実在するファイル / 見出しを指す"

/-- クイックスタートのコマンドを順に実行する。`naru simulate` の出力を返す。 -/
def checkQuickstart : M Unit := do
  let src ← IO.FS.readFile readmePath
  let some sec := sectionContaining (src.splitOn "\n") "クイックスタート"
    | fail "README に「クイックスタート」の見出しが無い"; return
  let blocks := codeBlocks sec
  let commands := blocks.filter fun (info, _) => ["sh", "bash", "shell", "console"].contains info
  let excerpts := blocks.filter fun (info, _) => info == "text"
  if commands.isEmpty then
    fail "README のクイックスタートに `sh` のコードブロックが無い"
    return
  let mut simulateOut : Option String := none
  let mut nRun := 0
  for (_, body) in commands do
    for raw in body do
      let line := raw.trimAscii.toString
      let line := if line.startsWith "$ " then (line.drop 2).toString else line
      if line.isEmpty || line.startsWith "#" then continue
      if (line.splitOn "git clone").length > 1 || (line.splitOn "git submodule").length > 1 then continue
      let r ← runProc "sh" #["-c", line]
      nRun := nRun + 1
      if r.exitCode == 0 then ok s!"quickstart: `{line}` exit 0"
      else fail s!"quickstart: `{line}` exit {r.exitCode}\n{tail (r.stdout ++ r.stderr)}"
      if (line.splitOn "naru simulate").length > 1 then simulateOut := some r.stdout
  if nRun == 0 then fail "README のクイックスタートに実行するコマンドが無い(取得のコマンドを除く)"
  match simulateOut, excerpts with
  | none, _ => fail "README のクイックスタートに `naru simulate` のコマンドが無い"
  | _, [] => fail "README のクイックスタートに期待される出力の抜粋(`text` のコードブロック)が無い"
  | some out, _ =>
    let outLines := (out.splitOn "\n").map (·.trimAscii.toString)
    let mut want : List String := []
    for (_, body) in excerpts do
      for l in body do
        let t := l.trimAscii.toString
        if !t.isEmpty && !t.startsWith "…" && !t.startsWith "..." then want := want ++ [t]
    let missing := want.filter fun w => !outLines.contains w
    if want.isEmpty then fail "README の抜粋が空"
    else if missing.isEmpty then ok s!"quickstart: simulate の出力が README の抜粋 {want.length} 行をすべて含む"
    else fail s!"quickstart: README の抜粋のうち simulate の出力に無い行: {missing}"

/-! ## C23: verified-consensus の submodule -/

/-- `.gitmodules` の `[submodule "<path>"]` の節の `path` と `url`。 -/
def gitmodulesEntry (src : String) (name : String) : Option (String × String) := Id.run do
  let mut inSection := false
  let mut path : Option String := none
  let mut url : Option String := none
  for raw in src.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.startsWith "[" then
      inSection := l == s!"[submodule \"{name}\"]"
      continue
    if !inSection then continue
    match l.splitOn "=" with
    | k :: v :: _ =>
      let k := k.trimAscii.toString
      let v := v.trimAscii.toString
      if k == "path" then path := some v
      if k == "url" then url := some v
    | _ => pure ()
  match path, url with
  | some p, some u => some (p, u)
  | _, _ => none

/-- 基準コミット: 引数、無ければ IDEAL.md の前提「基準コミット」の行の最初の 40 桁。 -/
def baseCommit (arg : Option String) : IO (Except String String) := do
  match arg with
  | some s =>
    if s.length == 40 && s.toList.all isHex then return .ok s.toLower
    return .error s!"--base-commit `{s}` is not a 40-digit SHA"
  | none =>
    if !(← idealPath.pathExists) then return .error s!"{idealPath} not found and no --base-commit given"
    let src ← IO.FS.readFile idealPath
    for l in src.splitOn "\n" do
      if l.trimAscii.toString.startsWith "- 基準コミット" then
        match shasIn l with
        | sha :: _ => return .ok sha.toLower
        | [] => return .error s!"{idealPath}: the line `- 基準コミット` has no 40-digit SHA"
    return .error s!"{idealPath}: no line starting with `- 基準コミット` (pass --base-commit <sha>)"

def checkSubmodule (base : Option String) : M Unit := do
  -- ルート直下に verified-consensus/ が無い
  let old : System.FilePath := "verified-consensus"
  if ← old.pathExists then fail s!"{old} still exists at the repository root (it must live at {vcPath})"
  else ok s!"no `verified-consensus/` at the repository root"
  -- .gitmodules
  let gm : System.FilePath := ".gitmodules"
  if !(← gm.pathExists) then fail s!"{gm} not found"
  else
    match gitmodulesEntry (← IO.FS.readFile gm) vcPath with
    | none => fail s!"{gm} has no `[submodule \"{vcPath}\"]` with path and url"
    | some (p, u) =>
      if p == vcPath && u == vcUpstream then ok s!"{gm}: submodule `{vcPath}` has path = {p}, url = {u}"
      else fail s!"{gm}: submodule `{vcPath}` has path = {p}, url = {u} (expected path {vcPath}, url {vcUpstream})"
  -- git ls-tree HEAD
  let lt ← runProc "git" #["ls-tree", "HEAD", vcPath]
  let ltLine := lt.stdout.trimAscii.toString
  let gitlink : Option String :=
    match ltLine.splitOn " " with
    | ["160000", "commit", rest] => (rest.splitOn "\t")[0]?.map (·.trimAscii.toString)
    | _ => none
  match gitlink with
  | some sha => ok s!"git ls-tree HEAD {vcPath}: mode 160000 (gitlink) {sha}"
  | none => fail s!"git ls-tree HEAD {vcPath} is not a gitlink (mode 160000): `{ltLine}` (exit {lt.exitCode}; the submodule is not committed yet)"
  -- submodule の HEAD
  let rp ← runProc "git" #["-C", vcPath, "rev-parse", "HEAD"]
  let subHead := rp.stdout.trimAscii.toString
  -- 親のリポジトリに解決されてしまった場合(submodule の .git が無い)を退ける
  let parentHead ← runProc "git" #["rev-parse", "HEAD"]
  let subOk := rp.exitCode == 0 && subHead.length == 40 && subHead != parentHead.stdout.trimAscii.toString &&
    (← (System.FilePath.mk vcPath / ".git").pathExists)
  if subOk then ok s!"git -C {vcPath} rev-parse HEAD: {subHead}"
  else fail s!"git -C {vcPath} rev-parse HEAD: not a repository of its own (exit {rp.exitCode}, `{subHead}`; {vcPath}/.git missing?)"
  -- third_party/README.md の SHA
  let readmeSha ← do
    if ← thirdPartyReadme.pathExists then
      let src ← IO.FS.readFile thirdPartyReadme
      let found := shasIn src
      if found.isEmpty then
        fail s!"{thirdPartyReadme} has no 40-digit SHA"
        pure none
      else pure (some found)
    else
      fail s!"{thirdPartyReadme} not found"
      pure none
  -- 基準コミット
  let baseSha ← match ← baseCommit base with
    | .ok s => pure (some s)
    | .error e => fail e; pure none
  match gitlink, baseSha, readmeSha with
  | some g, some b, some rs =>
    let gl := g.toLower
    let subL := subHead.toLower
    if subOk && gl == b && subL == b && rs.any (·.toLower == b) then
      ok s!"gitlink = submodule HEAD = {thirdPartyReadme} = base commit = {b}"
    else
      fail s!"SHA mismatch: gitlink {gl}, submodule HEAD {subL}, {thirdPartyReadme} {rs}, base commit {b}"
  | _, _, _ => fail "cannot compare the SHAs (see the failures above)"
  -- status
  let st ← runProc "git" #["-C", vcPath, "status", "--porcelain"]
  if st.exitCode == 0 && st.stdout.trimAscii.toString.isEmpty && subOk then ok s!"git -C {vcPath} status --porcelain is empty"
  else if !subOk then fail s!"git -C {vcPath} status --porcelain: skipped (not a repository of its own)"
  else fail s!"git -C {vcPath} status --porcelain is not empty (exit {st.exitCode}):\n{tail st.stdout 800}"

/-! ## C25: 文書 -/

def checkDocs : M Unit := do
  let mut missing : List String := []
  for d in docFiles do
    if !(← (docsDir / System.FilePath.mk d).pathExists) then missing := missing ++ [d]
  if missing.isEmpty then ok s!"docs/: {docFiles.length} files present ({", ".intercalate docFiles})"
  else fail s!"docs/: missing {missing}"
  if ← oldDocPath.pathExists then fail s!"{oldDocPath} still exists" else ok s!"{oldDocPath} is gone"
  -- E 番号
  if !(← diagSource.pathExists) then fail s!"{diagSource} not found"
  else
    let defined := (codesIn (← IO.FS.readFile diagSource)).mergeSort (· ≤ ·)
    let docPath := docsDir / "diagnostics.md"
    if ← docPath.pathExists then
      let listed := (codesIn (← IO.FS.readFile docPath)).mergeSort (· ≤ ·)
      let notListed := defined.filter fun c => !listed.contains c
      let extra := listed.filter fun c => !defined.contains c
      if notListed.isEmpty && extra.isEmpty then
        ok s!"{docPath} lists exactly the {defined.length} codes defined in {diagSource}: {", ".intercalate defined}"
      else
        fail s!"{docPath} vs {diagSource}: not listed {notListed}, not defined {extra}"
  -- 旧文書への参照
  let g ← runProc "git" #["grep", "-l", oldDocName]
  let hits := ((g.stdout.splitOn "\n").filter (!·.isEmpty)).filter fun f =>
    !(f.startsWith ".idd/cycles/") && f != ".idd/journal.jsonl" && f != idealPath.toString
  if g.exitCode > 1 then fail s!"git grep -l {oldDocName}: exit {g.exitCode}\n{tail g.stderr}"
  else if hits.isEmpty then ok s!"git grep -l {oldDocName}: no tracked file refers to the old document (excluding .idd/cycles/, .idd/journal.jsonl, IDEAL.md)"
  else fail s!"tracked files still refer to {oldDocName}: {hits}"

def run (base : Option String) : IO UInt32 := runGroup "naru_test repo" do
  checkReadmeTable
  checkLinks
  checkDocs
  checkSubmodule base
  checkQuickstart

end NaruTest.Repo
