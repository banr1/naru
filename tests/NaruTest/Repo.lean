import Std.Data.HashSet
import Naru
import NaruTest.Common

/-!
# `naru_test repo` — リポジトリの構成と文書の検査(IDEAL.md C21 / C23 / C25 / C37 / C60 / C61)

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
- C37(移植ソースの改名): 移植ソースの改名前のモジュール名・ディレクトリ名(`Consensus/Spec/` の前の名前)への参照が、追跡対象と
  追跡対象外(ignore されていない)のファイルに無い(`git grep -l --untracked -E`。README・docs・tests・compiler・specs・生成先・
  `.idd/progress.md`・`.idd/knowledge.md` を含む)。除くのは `.idd/cycles/` と `.idd/journal.jsonl`(履歴)、IDEAL.md(旧名を禁止する
  要件の本文)、`third_party/`(外部基準)、そして一般規則が旧名の形の利用者モジュールにも適用されることを示す意図的な検体
  `tests/accept/legacy_module_name.naru` だけ。
- C60(宣言コメントの形): `naru.toml` のソースルート(`specs/consensus/`。`scenarios/` を含む)配下の全 `.naru` を構文解析して
  宣言(type / record / state / enum / input / fn / protocol / observer / scenario / predicate / condition / regime / property /
  claim / claim bundle。protocol の中の宣言も含む。module / import / derive と scenario の中の `input` 文は宣言でない)を列挙し、
  各宣言の直上に空行を挟まず `//` の連続ブロックがあり、1 行目(要旨)が空でなく日本語(ひらがな・カタカナ・漢字)を含み、
  2 行目以降の説明(空でない行)が fn は 2 行以上・それ以外は 5 行以上で日本語を含むことを確かめ、宣言の総数と種類別の件数を出力する。
  欠落・不足が 1 件でもあれば FAIL。
- C61(手書きの対応名の実在): 宣言コメントが「手書き `名前`」(「手書きの `名前`」も同じ。`/`・`・`・`,`・`、` で続く `名前` も)の形で
  挙げる定義名を抜き出し、`third_party/verified-consensus/`(`.lake/` を除く)の Lean ソースの宣言名の索引(def / theorem / lemma /
  structure / inductive / abbrev / instance / class / opaque / axiom の名前に `namespace` の接頭辞を付けた完全名と、structure の欄・
  inductive の構築子の `型名.名前`。完全名はどの後置列(`A.B.c` / `B.c` / `c`)でも引ける)に実在することを確かめる。無い名前が
  1 件でもあれば FAIL。言及が 1 件も無いのも FAIL(移植ソースは手書きへの対応を書く約束)。
- C60 / C61 の負の検体: 形の不備(説明不足・コメント無し・空行を挟む・要旨に日本語が無い・要旨が空・record の行数不足)と無い手書き名を
  含む小さなモジュールを `.lake/naru/test/repo/declcomments/sample.naru` に書き、同じ走査がちょうどそれらを検出し、実在する名前は
  通すことを確かめる(検査自身の成功例・失敗例)。
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
/-- 移植ソースの改名前の名前の検索パターン(`git grep -E`。IDEAL.md C37)。この検査自身が掛からないよう連結で作る。 -/
def oldSpecPattern : String := "Consensus[./]" ++ "Statements"
/-- 旧名を意図的に使う検体(生成モジュール名の一般規則が旧名の形を特別扱いしないことの受理例。`naru_test regression` が照合する)。 -/
def oldSpecSamples : List String := ["tests/accept/legacy_module_name.naru"]

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

/-! ## C37: 移植ソースの改名前の名前への参照 -/

def checkOldSpecNames : M Unit := do
  let g ← runProc "git" #["grep", "-l", "--untracked", "-E", oldSpecPattern]
  let hits := ((g.stdout.splitOn "\n").filter (!·.isEmpty)).filter fun f =>
    !(f.startsWith ".idd/cycles/") && f != ".idd/journal.jsonl" && f != idealPath.toString &&
    !(f.startsWith "third_party/") && !(oldSpecSamples.contains f)
  if g.exitCode > 1 then fail s!"git grep -l --untracked -E {oldSpecPattern}: exit {g.exitCode}\n{tail g.stderr}"
  else if hits.isEmpty then
    ok s!"C37: git grep -l --untracked -E {oldSpecPattern}: no current file refers to the old module path or name (excluding .idd/cycles/, .idd/journal.jsonl, IDEAL.md, third_party/ and the intentional sample(s) {oldSpecSamples})"
  else fail s!"C37: files still refer to the old module path or name ({oldSpecPattern}): {hits}"

/-! ## C60 / C61: 宣言コメント -/

/-- 日本語の文字(ひらがな・カタカナ・漢字)を含むか。 -/
def hasJapanese (s : String) : Bool :=
  s.any fun c =>
    let n := c.toNat
    (0x3040 ≤ n && n ≤ 0x309F) || (0x30A0 ≤ n && n ≤ 0x30FF) || (0x4E00 ≤ n && n ≤ 0x9FFF)

/-- 説明(要旨の次の行から)の下限行数(IDEAL.md C60: fn は 2、spec 宣言と type / record / state / enum / input / protocol /
observer / scenario は 5)。 -/
def minExplanation : Naru.DeclKind → Nat
  | .fn => 2
  | _ => 5

/-- 宣言の種類(IDEAL.md 用語「宣言コメント」の列挙の順)。 -/
def declKinds : List Naru.DeclKind :=
  [.typeAlias, .record, .state, .enum, .input, .fn, .protocol, .observer, .scenario,
   .predicate, .condition, .regime, .property, .claim, .claimBundle]

/-- 行が `//` のコメントなら、`//` と前後の空白を落とした本文。 -/
def commentBody (l : String) : Option String :=
  let t := l.trimAscii.toString
  if t.startsWith "//" then some ((t.drop 2).toString.trimAscii.toString) else none

/-- 宣言の行か: 字下げを除いて種類のキーワードで始まる(`claim` は `claim bundle` と区別する)。 -/
def startsDecl (kind : Naru.DeclKind) (l : String) : Bool :=
  let t := l.trimAscii.toString
  match kind with
  | .claim => t.startsWith "claim " && !(t.startsWith "claim bundle ")
  | k => t.startsWith (k.describe ++ " ")

structure DeclCommentIssue where
  file : String
  line : Nat
  kind : Naru.DeclKind
  name : String
  reason : String

/-- 1 ファイルの宣言コメントの走査結果。 -/
structure DeclCommentScan where
  /-- (種類, 名前, コメントの各行(`//` を除いた本文)) -/
  decls : Array (Naru.DeclKind × String × List String) := #[]
  issues : Array DeclCommentIssue := #[]
  /-- 宣言コメントが「手書き `名前`」で挙げた名前と、その宣言(ファイル・行) -/
  mentions : Array (String × String × Nat) := #[]

/-- 「手書き `名前`」(「手書きの `名前`」も同じ)が挙げる名前。直後に空白・`/`・`・`・`,`・`、` を挟んで続く `名前` も取る
(例: 手書き `A` / `B`)。バッククォートの中は 1 つの定義名でなければならない(空白などを含めば不正。後で検出する)。 -/
def handwrittenNames (text : String) : List String := Id.run do
  let cs := text.toList.toArray
  let key := "手書き".toList.toArray
  let isSep (c : Char) : Bool := c == ' ' || c == '/' || c == '・' || c == ',' || c == '、'
  let mut out : List String := []
  let mut i := 0
  while i < cs.size do
    if i + key.size ≤ cs.size && cs.extract i (i + key.size) == key then
      let mut j := i + key.size
      if j < cs.size && cs[j]! == 'の' then j := j + 1
      while j < cs.size && cs[j]! == ' ' do j := j + 1
      let mut go := j < cs.size && cs[j]! == '`'
      while go do
        let k := j + 1
        let mut e := k
        while e < cs.size && cs[e]! != '`' do e := e + 1
        if e ≥ cs.size then
          go := false
          j := e
        else
          out := out ++ [String.ofList (cs.extract k e).toList]
          j := e + 1
          let mut s := j
          while s < cs.size && isSep cs[s]! do s := s + 1
          if s < cs.size && cs[s]! == '`' then j := s else go := false
      i := j
    else
      i := i + 1
  return out

/-- 1 ファイルの宣言コメントを走査する(C60 の形と、C61 の「手書き `名前`」の抜き出し)。構文解析に失敗したら `.error`。 -/
def scanDeclComments (path : String) : IO (Except String DeclCommentScan) := do
  match ← Naru.parseFile path with
  | .error d => return .error d.render
  | .ok m =>
    let lines := ((← IO.FS.readFile path).splitOn "\n").toArray
    let mut r : DeclCommentScan := {}
    for d in m.decls do
      let issue (reason : String) : DeclCommentIssue :=
        { file := path, line := d.span.line, kind := d.kind, name := d.name, reason }
      -- 宣言の行: 名前のトークンの行から、種類のキーワードで始まる行まで(最大 3 行)遡る
      let mut l := d.span.line
      let mut found := false
      let mut tries := 0
      while l ≥ 1 && tries < 4 do
        if l ≤ lines.size && startsDecl d.kind lines[l - 1]! then
          found := true
          break
        l := l - 1
        tries := tries + 1
      if !found then
        r := { r with issues := r.issues.push (issue s!"宣言の行を特定できない(名前の行の近くに `{d.kind.describe}` で始まる行が無い)") }
        continue
      -- 直上のコメントブロック(空行を挟まない `//` の連続)
      let mut i := l - 1
      let mut block : List String := []
      while i ≥ 1 do
        match commentBody lines[i - 1]! with
        | some b =>
          block := b :: block
          i := i - 1
        | none => break
      r := { r with decls := r.decls.push (d.kind, d.name, block) }
      match block with
      | [] =>
        r := { r with issues := r.issues.push (issue "直上に宣言コメントが無い(直上が空行かコード)") }
      | head :: rest =>
        if head.isEmpty then
          r := { r with issues := r.issues.push (issue "宣言コメントの 1 行目(要旨)が空") }
        else if !(hasJapanese head) then
          r := { r with issues := r.issues.push (issue s!"宣言コメントの 1 行目(要旨)に日本語が無い: {head}") }
        let expl := rest.filter (!·.isEmpty)
        let need := minExplanation d.kind
        if expl.length < need then
          r := { r with issues := r.issues.push (issue s!"説明が {expl.length} 行(`{d.kind.describe}` は要旨の下に {need} 行以上)") }
        else if !(hasJapanese (" ".intercalate expl)) then
          r := { r with issues := r.issues.push (issue "説明に日本語が無い") }
        for n in handwrittenNames ("\n".intercalate block) do
          r := { r with mentions := r.mentions.push (n, path, l) }
    return .ok r

/-! 手書き Lean の宣言名の索引(C61)。 -/

def leanDeclKeywords : List String :=
  ["def", "theorem", "lemma", "structure", "inductive", "abbrev", "instance", "class", "opaque", "axiom"]
def leanModifiers : List String :=
  ["private", "protected", "noncomputable", "partial", "unsafe", "scoped", "local", "nonrec"]

def identEnd (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '(' || c == ':' || c == '{' || c == '[' || c == '<' || c == '|' || c == '=' ||
  c == '⟨' || c == '}' || c == ')' || c == ','

def takeIdent (s : String) : String := String.ofList (s.toList.takeWhile (!identEnd ·))

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '?' || c == '!' || c == '\'' || c == '.' || c.toNat > 127

/-- 完全名 `A.B.c` のすべての後置列(`A.B.c` / `B.c` / `c`)を索引に入れる。 -/
def insertSuffixes (set : Std.HashSet String) (full : String) : Std.HashSet String := Id.run do
  let parts := full.splitOn "."
  let mut s := set
  for i in [0:parts.length] do
    s := s.insert (".".intercalate (parts.drop i))
  return s

/-- 行頭の属性 `@[…]` と修飾語(`private` / `noncomputable` …)を落とす。 -/
def stripLeanPrefix (s : String) : String := Id.run do
  let mut s := s
  if s.startsWith "@[" then
    match s.splitOn "]" with
    | _ :: rest => s := ("]".intercalate rest).trimAscii.toString
    | [] => pure ()
  let mut changed := true
  while changed do
    changed := false
    for m in leanModifiers do
      if s.startsWith (m ++ " ") then
        s := (s.drop (m.length + 1)).toString.trimAscii.toString
        changed := true
  return s

/-- 1 つの Lean ソースの宣言名を索引に足す: 宣言の頭(`def` / `theorem` / `structure` / …)の名前に `namespace` の接頭辞を付けた
完全名、structure / class の欄と inductive の構築子の `型名.名前`。 -/
def leanDeclaredNames (lines : List String) (acc : Std.HashSet String) : Std.HashSet String := Id.run do
  let mut set := acc
  let mut ns : List String := []
  let mut curType : Option String := none
  for raw in lines do
    let t := raw.trimAscii.toString
    if t.isEmpty then continue
    if raw.startsWith " " || raw.startsWith "\t" then
      -- 字下げ行: 直前の structure / inductive / class の欄・構築子
      match curType with
      | some ty =>
        if t.startsWith "| " then
          let c := takeIdent (t.drop 2).toString.trimAscii.toString
          if !c.isEmpty && c.all isIdentChar then set := insertSuffixes set (ty ++ "." ++ c)
        else
          let c := takeIdent t
          let rest := (t.drop c.length).toString.trimAscii.toString
          if !c.isEmpty && c.all isIdentChar && rest.startsWith ":" then set := insertSuffixes set (ty ++ "." ++ c)
      | none => pure ()
      continue
    let s := stripLeanPrefix t
    if s.startsWith "namespace " then
      let n := takeIdent (s.drop 10).toString.trimAscii.toString
      if !n.isEmpty then ns := n :: ns
      continue
    if s.startsWith "end " then
      let n := takeIdent (s.drop 4).toString.trimAscii.toString
      match ns with
      | top :: below => if top == n then ns := below
      | [] => pure ()
      continue
    let mut matched := false
    for kw in leanDeclKeywords do
      if !matched && s.startsWith (kw ++ " ") then
        matched := true
        let name := takeIdent (s.drop (kw.length + 1)).toString.trimAscii.toString
        if !name.isEmpty && name.all isIdentChar then
          let nsName := ".".intercalate ns.reverse
          let full := if nsName.isEmpty then name else nsName ++ "." ++ name
          set := insertSuffixes set full
          curType := if kw == "structure" || kw == "inductive" || kw == "class" then some full else none
        else
          curType := none
    if !matched && !(s.startsWith "/-") && !(s.startsWith "--") then curType := none
  return set

/-- `root` 配下(`.lake/` を除く)の全 `.lean` から宣言名の索引を作る。(ファイル数, 索引)。 -/
def handwrittenIndex (root : System.FilePath) : IO (Nat × Std.HashSet String) := do
  let all ← root.walkDir (fun d => pure (d.fileName != some ".lake"))
  let files := (all.filter (·.extension == some "lean")).qsort (fun a b => a.toString < b.toString)
  let mut set : Std.HashSet String := {}
  let mut n := 0
  for p in files do
    if ← p.isDir then continue
    n := n + 1
    set := leanDeclaredNames ((← IO.FS.readFile p).splitOn "\n") set
  return (n, set)

/-- 名前として不正(空白・括弧などを含む = 式や文)。 -/
def badHandwrittenName (n : String) : Bool := n.isEmpty || !(n.all isIdentChar)

def checkDeclComments : M Unit := do
  match ← sourceRoots with
  | .error e => fail s!"C60: {e}"
  | .ok roots =>
    let mut files : List String := []
    for r in roots do files := files ++ (← Naru.listFiles r "naru")
    let mut decls : Array (Naru.DeclKind × String × List String) := #[]
    let mut issues : Array DeclCommentIssue := #[]
    let mut mentions : Array (String × String × Nat) := #[]
    for f in files do
      match ← scanDeclComments f with
      | .error e => fail s!"C60: {e}"
      | .ok r =>
        decls := decls ++ r.decls
        issues := issues ++ r.issues
        mentions := mentions ++ r.mentions
    let counts := declKinds.filterMap fun k =>
      let n := (decls.filter (·.1 == k)).size
      if n == 0 then none else some s!"{k.describe} {n}"
    if decls.isEmpty then fail s!"C60: ソースルート {roots} に宣言が 1 つも無い"
    for i in issues do
      fail s!"C60: {i.file}:{i.line} {i.kind.describe} {i.name}: {i.reason}"
    if issues.isEmpty && !decls.isEmpty then
      ok s!"C60: {files.length} ファイル、宣言 {decls.size} 件({", ".intercalate counts})の直上に宣言コメント(空行なしの `//` ブロック。要旨 1 行 + 説明 fn ≥ 2 行 / 他 ≥ 5 行、日本語)"
    -- C61: 「手書き `名前`」の実在
    let (nLean, index) ← handwrittenIndex vcPath
    let bad := mentions.filter fun (n, _, _) => badHandwrittenName n
    for (n, f, l) in bad do
      fail s!"C61: {f}:{l}: 「手書き `{n}`」のバッククォートの中は 1 つの定義名でない"
    let names := (mentions.toList.map (·.1)).eraseDups
    let missing := names.filter fun n => !(badHandwrittenName n) && !(index.contains n)
    for n in missing do
      let at_ := (mentions.filter (·.1 == n)).toList.map fun (_, f, l) => s!"{f}:{l}"
      fail s!"C61: 手書き `{n}` は {vcPath} の Lean ソースに無い({", ".intercalate at_})"
    if mentions.isEmpty then
      fail s!"C61: 宣言コメントに「手書き `名前`」の言及が 1 件も無い"
    else if bad.isEmpty && missing.isEmpty then
      ok s!"C61: 宣言コメントが「手書き `名前`」で挙げる定義名 {mentions.size} 件(異なり {names.length})はすべて {vcPath} の Lean ソース({nLean} ファイル、索引 {index.size} 名)に実在する"

/-- C60 / C61 の検査自身の成功例・失敗例: 形の不備と無い手書き名を含む小さなモジュール。 -/
def declCommentSample : String := "\n".intercalate
  [ "module Sample.Comments", ""
  , "// 要旨。", "// 説明一。", "// 説明二。", "fn good() -> Nat { 1 }", ""
  , "// 要旨。", "// 説明一。", "fn short() -> Nat { 1 }", ""
  , "fn missing() -> Nat { 1 }", ""
  , "// 要旨。", "// 説明一。", "// 説明二。", "", "fn gap() -> Nat { 1 }", ""
  , "// summary without Japanese.", "// 説明一。", "// 説明二。", "fn english() -> Nat { 1 }", ""
  , "//", "// 説明一。", "// 説明二。", "fn emptyHead() -> Nat { 1 }", ""
  , "// 要旨。手書き `slotStart` / `Block.genesis` に対応し、手書き `NoSuchDefinition_xyz` は無い名前。"
  , "// 説明一。", "// 説明二。", "fn mentions() -> Nat { 1 }", ""
  , "// 要旨。", "// 説明一。", "// 説明二。", "// 説明三。", "// 説明四。", "// 説明五。", "record Full { x: Nat }", ""
  , "// 要旨。", "// 説明一。", "// 説明二。", "// 説明三。", "// 説明四。", "record Short { x: Nat }", "" ]

def declCommentSampleDir : System.FilePath := ".lake" / "naru" / "test" / "repo" / "declcomments"

def checkDeclCommentSamples : M Unit := do
  IO.FS.createDirAll declCommentSampleDir
  let path := declCommentSampleDir / "sample.naru"
  IO.FS.writeFile path declCommentSample
  match ← scanDeclComments path.toString with
  | .error e => fail s!"C60 sample: {e}"
  | .ok r =>
    let expected := ["Short", "emptyHead", "english", "gap", "missing", "short"]
    let got := (r.issues.toList.map (·.name)).eraseDups.mergeSort (· ≤ ·)
    if got == expected && r.decls.size == 9 then
      ok s!"C60 sample: {path} の 9 宣言のうち、形の不備のある {expected.length} 件({", ".intercalate expected})だけを検出し、他は通る"
    else
      fail s!"C60 sample: 検出した宣言 {got}(期待 {expected})、宣言数 {r.decls.size}(期待 9): {r.issues.toList.map fun i => s!"{i.name}: {i.reason}"}"
    let names := (r.mentions.toList.map (·.1)).eraseDups
    let (_, index) ← handwrittenIndex vcPath
    let present := names.filter index.contains
    let absent := names.filter fun n => !(index.contains n)
    if present == ["slotStart", "Block.genesis"] && absent == ["NoSuchDefinition_xyz"] then
      ok s!"C61 sample: 実在する手書き名 {present} は索引に見つかり、無い名前 {absent} だけが検出される"
    else
      fail s!"C61 sample: 見つかった {present}、無い {absent}(期待: slotStart / Block.genesis が見つかり NoSuchDefinition_xyz だけ無い)"

def run (base : Option String) : IO UInt32 := runGroup "naru_test repo" do
  checkReadmeTable
  checkLinks
  checkDocs
  checkOldSpecNames
  checkSubmodule base
  checkQuickstart
  checkDeclCommentSamples
  checkDeclComments

end NaruTest.Repo
