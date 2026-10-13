import Lean.Data.Json
import Naru.Driver
import Naru.Describe
import Naru.Config

/-!
# 言語サーバー(`naru lsp`、IDEAL.md C18 / C29 / C30 / C31 / C32)

標準入出力で LSP(JSON-RPC 2.0、`Content-Length` 枠)を話し、コンパイラの診断(E001〜E019)と、コンパイラの索引から取る
ホバー(`textDocument/hover`)・定義ジャンプ(`textDocument/definition`)・補完(`textDocument/completion`)・リネーム
(`textDocument/prepareRename` / `rename`)を返す。エディタ(Zed 拡張 `editors/zed-naru/`)は `naru lsp` を起動し、開いた文書を送ってくる。

- 応じるもの: `initialize` / `initialized` / `shutdown` / `exit`、`textDocument/didOpen` / `didChange`(全文同期)/
  `didSave` / `didClose`、`textDocument/hover`(C29)、`textDocument/definition`(C30)、`textDocument/completion`(C31)、
  `textDocument/prepareRename` / `textDocument/rename`(C32)。それ以外のリクエスト(整形の C33 は未対応)には `MethodNotFound`(-32601)を
  返し、それ以外の通知は無視する。
- リネーム(C32): 位置にあるもの(`locate`)が宣言名(宣言そのもの、または参照の経路の宣言名の区切り)か欄名(record / state の宣言の中・
  式の中の読み `r.f`・record literal の初期化 `R { f: … }`)なら、`prepareRename` はその名前のトークンの範囲と現在の名前を返し、`rename` は
  同じコンパイル単位の全ファイル(開いていないファイルも)のその名前の箇所 — 宣言なら名前解決の索引 `Checked.refs` の全参照の宣言名の区切り、
  欄なら型検査の索引 `Checked.members` の全参照 — を `newName` に置き換える `WorkspaceEdit`(`changes`)を返す。コメントの中は変えない。
  variant・stdlib のメソッド・局所名・モジュール名の区切りの上では null。新しい名前は識別子で、予約語・組み込みの名前でなく、元の名前と
  同じ大文字 / 小文字の区分で、宣言なら同じ単位の他の宣言名と、欄なら同じ record の他の欄名と重ならないこと(違えば `RequestFailed` -32803)。
- 補完(C31): `.` の直後(途中まで書いた名前の中を含む)なら受け手の型から — record / state の欄、stdlib の型のメソッド(受け手の型で
  実体化した署名)、その型を最初の仮引数に取る fn 等(UFCS)。受け手の型は型検査の索引 `Checked.accesses`(欄 / メソッドのアクセスの
  受け手の型。名前が解決できなくても残る)から取り、索引に無ければ(文書が構文エラーの途中、`x.` まで書いた)位置の名前を仮の識別子に
  置き換えた本文で単位を検査し直して取る(探り。診断は送らず索引も変えない)。型が決まらなければ `.` の前の経路から: enum なら variant、
  モジュール名ならその宣言 / 次の区切り、組み込みの型なら静的関数。それ以外の位置なら、位置を含む宣言の仮引数と位置より前の局所名、
  単位の全宣言(署名と宣言コメントの要旨つき)、予約語、組み込みの型と構築子。コメント(行コメントと同じ行のブロックコメント)・文字列の中は空。
- 位置にあるもの(`locate`。C29 / C30 の共通): 文書の位置にある参照(名前解決の索引 `Checked.refs`: 値の位置・型の位置・scenario の input の
  束縛に書かれた経路。経路 `A.B.c` の上ならその最長の接頭辞で解決した宣言と、カーソルのある区切り)、宣言名そのもの、型検査の索引
  `Checked.members` の欄名 / stdlib のメソッド名の順に探す。索引は単位ごとに直前の検査(全ファイルが構文解析できたもの)のものを持つ。
- 定義ジャンプ(C30): 参照・宣言名からは同じコンパイル単位の宣言(別ファイルを含む)の URI と宣言の名前のトークンの範囲(`Location`)、
  欄名(式の中・宣言の中)からはその record の欄の名前のトークン、宣言の中の variant 名からはその variant。どれも無い位置(stdlib のメソッドを
  含む)では null。
- ホバー(C29): Markdown(`MarkupContent`)で、宣言の署名のコードブロック(`Decl.signature`: fn なら仮引数と戻り型、record / enum なら
  欄 / variant と derive …)、種類・名前・モジュール、その宣言の宣言コメント(C60。`Naru.declComment`: 宣言の直上の `//` ブロック。
  1 行目を段落、以降を行ごとの改行で)。経路の残りが enum の variant(と宣言の中の variant 名)ならその variant(1 行の説明があればそれも)、
  欄(式の中・宣言の中)なら `Record.field: T`(宣言に書かれた型)と欄の 1 行の説明と record の宣言コメント、stdlib のメソッドなら受け手の型で
  実体化した署名。範囲(`range`)は参照の経路 / トークン。識別子でない位置(空白・コメント・予約語・局所変数)では null。
- 検査の単位: 開いた文書のパスの祖先で最も近い `naru.toml`(`Naru/Config.lean`)を読み、その `sources` のソースルート配下
  なら、そのルートの `**/*.naru` 全体を 1 つのコンパイル単位にし、開いている文書はディスクではなくバッファの内容で検査する。
  それ以外の文書(`naru.toml` が無い・どのルートの配下でもない)は単独で検査する。どちらも `Driver.compileSources`
  (CLI の `compile` と同じ検査)。cwd には依らない(C24)。
- 診断: `textDocument/publishDiagnostics`。コンパイラの `Diagnostic`(1 始まりの行・列)を 0 始まりの位置に直し、範囲は
  その位置から始まるトークン 1 つ分(識別子・数・文字列・記号)、severity はエラー、`code` は `E0xx`、`source` は `naru`。
  他のファイルに出た診断はそのファイルの URI へ送り、前回その単位で診断を送った URI のうち今回空になったものには空を送って消す。
  閉じた文書には空を送る(同じ単位に開いた文書が残っていれば、ディスクの内容で検査し直す。その検査では閉じた文書へは送らず
  空のままにし、次の検査からは開いていないファイルとして扱う。残っていなければその単位の診断をすべて消す)。
- 列は LSP 既定の UTF-16 単位(コンパイラの列は文字数なので、BMP 外の文字がある行だけ値が変わる)。
- この層は診断の運搬だけで、検査の意味は持たない(IDEAL.md「不変条件」: 診断はすべてコンパイラが出す)。
-/

namespace Naru.Lsp

open Lean (Json)

/-! ## 枠(`Content-Length: n\r\n\r\n<本文>`)の読み書き。検査ドライバ(`naru_test lsp`)も同じ関数で子プロセスと話す。 -/

/-- ちょうど `n` バイト読む。途中で EOF なら none。 -/
def readExact (s : IO.FS.Stream) (n : Nat) : IO (Option ByteArray) := do
  let mut buf := ByteArray.empty
  while buf.size < n do
    let chunk ← s.read (USize.ofNat (n - buf.size))
    if chunk.isEmpty then return none
    buf := buf ++ chunk
  return some buf

/-- メッセージを 1 つ読む。EOF なら none、ヘッダや JSON が壊れていれば `some (.error …)`。 -/
def readMessage (s : IO.FS.Stream) : IO (Option (Except String Json)) := do
  let mut len : Option Nat := none
  repeat
    let line ← s.getLine
    if line.isEmpty then return none
    let l := line.trimAscii.toString
    if l.isEmpty then break
    match l.dropPrefix? "Content-Length:" with
    | some v => len := v.toString.trimAscii.toString.toNat?
    | none => pure ()
  match len with
  | none => return some (.error "missing Content-Length header")
  | some n =>
    match ← readExact s n with
    | none => return none
    | some bytes =>
      match String.fromUTF8? bytes with
      | none => return some (.error "message body is not UTF-8")
      | some body => return some (Json.parse body)

def writeMessage (s : IO.FS.Stream) (j : Json) : IO Unit := do
  let body := j.compress
  s.putStr s!"Content-Length: {body.utf8ByteSize}\r\n\r\n{body}"
  s.flush

/-! ## JSON の小さな読み -/

def getField (j : Json) (key : String) : Option Json := (j.getObjVal? key).toOption

def getStr (j : Json) (key : String) : Option String := (j.getObjVal? key >>= Json.getStr?).toOption

/-! ## 位置と範囲 -/

/-- `i` 番目の文字(0 始まり)の、その行の先頭からの UTF-16 単位の位置。 -/
def utf16Col (line : Array Char) (i : Nat) : Nat := Id.run do
  let mut n := 0
  for c in line.toList.take i do
    n := n + (if c.toNat ≥ 0x10000 then 2 else 1)
  return n

/-- `start`(文字の添字)から始まるトークンの終わり(排他的)。字句解析と同じ切り方: 識別子(末尾 `?` 付き)/ 数 /
文字列リテラル / 2 文字記号 / 1 文字。行末を越えていれば幅 0。 -/
def tokenEnd (line : Array Char) (start : Nat) : Nat := Id.run do
  match line[start]? with
  | none => return start
  | some c =>
    if c.isAlpha || c == '_' then
      let mut e := start + 1
      while (line[e]?.map fun d => d.isAlphanum || d == '_').getD false do e := e + 1
      if line[e]? == some '?' then e := e + 1
      return e
    else if c.isDigit then
      let mut e := start + 1
      while (line[e]?.map Char.isDigit).getD false do e := e + 1
      return e
    else if c == '"' then
      let mut e := start + 1
      let mut escaped := false
      while true do
        match line[e]? with
        | none => break
        | some d =>
          e := e + 1
          if escaped then escaped := false
          else if d == '\\' then escaped := true
          else if d == '"' then break
      return e
    else
      let two := String.ofList [c, (line[start + 1]?).getD ' ']
      return if symbols2.contains two then start + 2 else start + 1

/-- UTF-16 単位の列 `u` にある文字の添字(`utf16Col` の逆。行末を越えていれば行の長さ)。 -/
def charIndex (line : Array Char) (u : Nat) : Nat := Id.run do
  let mut n := 0
  let mut i := 0
  while i < line.size do
    if n ≥ u then break
    n := n + (if line[i]!.toNat ≥ 0x10000 then 2 else 1)
    i := i + 1
  return i

/-- `start`(文字の添字)に書かれた経路 `path` の終わり(排他的): ソースがそこに `A.B.c` と空白なしで書いていればその長さ、
そうでなければトークン 1 つ分(`tokenEnd`)。 -/
def pathEnd (line : Array Char) (start : Nat) (path : List String) : Nat :=
  let cs := (renderPath path).toList
  if !cs.isEmpty && ((line.toList.drop start).take cs.length) == cs then start + cs.length
  else tokenEnd line start

def position (line character : Nat) : Json :=
  Json.mkObj [("line", line), ("character", character)]

def rangeJson (line0 startCh endCh : Nat) : Json :=
  Json.mkObj [("start", position line0 startCh), ("end", position line0 endCh)]

/-- 宣言の名前のトークンの `Location`(`sp` は名前の位置、`lines` はその文書の行)。 -/
def locationJson (uri : String) (lines : List String) (sp : Span) (name : String) : Json :=
  let line0 := sp.line - 1
  let chars := (lines.getD line0 "").toList.toArray
  Json.mkObj [("uri", uri), ("range", rangeJson line0 (utf16Col chars (sp.col - 1)) (utf16Col chars (sp.col - 1 + name.length)))]

/-- コンパイラの診断を LSP の診断にする。`lines` はその文書の行(`splitOn "\n"`)。 -/
def diagnosticJson (lines : List String) (d : Diagnostic) : Json :=
  let line0 := d.span.line - 1
  let col0 := d.span.col - 1
  let chars := (lines.getD line0 "").toList.toArray
  let startCh := utf16Col chars col0
  let endCh := utf16Col chars (tokenEnd chars col0)
  Json.mkObj [
    ("range", rangeJson line0 startCh endCh),
    ("severity", 1),
    ("code", d.code),
    ("source", "naru"),
    ("message", d.msg)]

/-! ## 文書と検査の単位 -/

structure Doc where
  uri : String
  /-- URI から取ったファイルパス(`file://` でなければ URI そのまま)。診断の `file` と突き合わせる。 -/
  path : String
  text : String
  /-- 文書が属するソースルート(`naru.toml` の `sources`。開いたときに決める)。無ければ単独の文書。 -/
  root : Option String := none

def pathOfUri (uri : String) : String :=
  match System.Uri.fileUriToPath? uri with
  | some p => p.toString
  | none => uri

/-- 文書のパスの祖先で最も近い `naru.toml` を読み、その `sources` のルート配下ならそのルート(絶対パス)。
`naru.toml` が無い・読めない・どのルートの配下でもなければ none(単独の文書)。 -/
def unitRoot (path : String) : IO (Option String) := do
  let some cfgPath ← findConfigFrom path | return none
  match ← readConfig cfgPath with
  | .error e =>
    IO.eprintln s!"naru lsp: {cfgPath}: {e} (checking {path} on its own)"
    return none
  | .ok cfg => return (cfg.rootOf path).map fun (root, _) => root.toString

/-- 検査の単位の鍵: ソースルート、または単独の文書のパス。 -/
def unitKey (doc : Doc) : String := doc.root.getD doc.path

/-- 検査の単位ごとの索引(C30): 直前に全ファイルが構文解析できた検査のソース列と結果(名前解決の参照 `Checked.refs` と宣言 `Checked.mods`)。
定義ジャンプはこれを引くだけで、検査し直さない。 -/
structure UnitIndex where
  key : String
  sources : List (String × String)
  checked : Checked
  /-- その検査の診断(空なら単位は健全で索引は完全。リネーム(C32)は空のときだけ応じる)。 -/
  diags : Array Diagnostic := #[]

structure State where
  out : IO.FS.Stream
  version : String
  docs : Array Doc := #[]
  /-- 単位の鍵 → 直前の検査で空でない診断を送った URI。次の検査で空になったものを消すため。 -/
  published : Array (String × Array String) := #[]
  /-- 単位の鍵 → 索引(`UnitIndex`)。 -/
  index : Array UnitIndex := #[]
  shutdownRequested : Bool := false
  exitCode : Option UInt32 := none

abbrev M := StateT State IO

def send (j : Json) : M Unit := do writeMessage (← get).out j

def respond (id : Json) (result : Json) : M Unit :=
  send (Json.mkObj [("jsonrpc", "2.0"), ("id", id), ("result", result)])

def respondError (id : Json) (code : Int) (message : String) : M Unit :=
  send (Json.mkObj [("jsonrpc", "2.0"), ("id", id),
    ("error", Json.mkObj [("code", code), ("message", message)])])

def publish (uri : String) (diags : Array Json) : M Unit :=
  send (Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/publishDiagnostics"),
    ("params", Json.mkObj [("uri", uri), ("diagnostics", Json.arr diags)])])

def log (msg : String) : M Unit := IO.eprintln s!"naru lsp: {msg}"

/-- 文書の単位のソース列。ソースルート配下ならディスクのそのルートの `**/*.naru` 全体(開いている文書はバッファの内容、
ディスクに無い開いた文書も含める)、それ以外はその文書だけ。 -/
def unitSources (st : State) (doc : Doc) : IO (List (String × String)) := do
  match doc.root with
  | none => return [(doc.path, doc.text)]
  | some root =>
    let files ← listFiles root "naru"
    let mut out : List (String × String) := []
    for f in files do
      match st.docs.find? (fun (d : Doc) => d.path == f) with
      | some d => out := out ++ [(f, d.text)]
      | none => out := out ++ [(f, ← IO.FS.readFile f)]
    for d in st.docs do
      if d.root == some root && !files.contains d.path then
        out := out ++ [(d.path, d.text)]
    return out

def uriOfFile (st : State) (file : String) : String :=
  match st.docs.find? (fun (d : Doc) => d.path == file) with
  | some d => d.uri
  | none => System.Uri.pathToUri file

/-- 文書の単位を検査し、診断をファイルごとの URI に送る。文書自身には必ず(空でも)送り、前回この単位で送った URI の
うち今回空になったものにも空を送る。`closed` は直前に閉じた文書の URI: 閉じた文書の診断は空のままにする(条文)ので、
この検査ではそこへ送らない(次の検査からは開いていないファイルとして扱い、診断があれば送る)。 -/
def check (doc : Doc) (closed : Option String := none) : M Unit := do
  let st ← get
  let sources ← unitSources st doc
  let (diags, checked) := compileSources sources
  let key := unitKey doc
  -- 索引(C30): 全ファイルが構文解析できた検査の結果を単位ごとに持つ(構文エラーの途中は前の索引のまま)
  if checked.mods.size == sources.length then
    modify fun s => { s with index := (s.index.filter (·.key != key)).push { key, sources, checked, diags } }
  let mut groups : Array (String × Array Json) := #[]
  for d in diags do
    let lines := ((sources.lookup d.file).getD "").splitOn "\n"
    let j := diagnosticJson lines d
    match groups.findIdx? (·.1 == d.file) with
    | some i => groups := groups.modify i fun (f, a) => (f, a.push j)
    | none => groups := groups.push (d.file, #[j])
  let prev := ((st.published.find? (·.1 == key)).map (·.2)).getD #[]
  let mut sent : Array String := #[]
  let mut nonEmpty : Array String := #[]
  for (f, js) in groups do
    let uri := uriOfFile st f
    if closed == some uri then continue
    publish uri js
    sent := sent.push uri
    nonEmpty := nonEmpty.push uri
  if !sent.contains doc.uri then
    publish doc.uri #[]
    sent := sent.push doc.uri
  for uri in prev do
    if !sent.contains uri && closed != some uri then publish uri #[]
  modify fun s => { s with published := (s.published.filter (·.1 != key)).push (key, nonEmpty) }

def openDoc (uri text : String) : M Unit := do
  let path := pathOfUri uri
  let doc : Doc := { uri, path, text, root := ← unitRoot path }
  modify fun s => { s with docs := (s.docs.filter (fun (d : Doc) => d.uri != uri)).push doc }
  check doc

def changeDoc (uri text : String) : M Unit := do
  let st ← get
  match st.docs.find? (fun (d : Doc) => d.uri == uri) with
  | some d =>
    let doc := { d with text }
    set { st with docs := (st.docs.filter (fun (d : Doc) => d.uri != uri)).push doc }
    check doc
  | none =>
    -- 開いていない文書の変更: 開いたものとして扱う
    openDoc uri text

def saveDoc (uri : String) (text : Option String) : M Unit := do
  let st ← get
  match st.docs.find? (fun (d : Doc) => d.uri == uri) with
  | some d =>
    let doc := { d with text := text.getD d.text }
    set { st with docs := (st.docs.filter (fun (d : Doc) => d.uri != uri)).push doc }
    check doc
  | none => pure ()

def closeDoc (uri : String) : M Unit := do
  let st ← get
  match st.docs.find? (fun (d : Doc) => d.uri == uri) with
  | none => publish uri #[]
  | some doc =>
    set { st with docs := st.docs.filter (fun (d : Doc) => d.uri != uri) }
    publish uri #[]
    let key := unitKey doc
    let st ← get
    match st.docs.find? (fun d => unitKey d == key) with
    | some other => check other (closed := some uri)
    | none =>
      let prev := ((st.published.find? (·.1 == key)).map (·.2)).getD #[]
      for u in prev do
        if u != uri then publish u #[]
      set { st with published := st.published.filter (·.1 != key), index := st.index.filter (·.key != key) }

/-! ## 位置にあるもの(定義ジャンプ C30 とホバー C29 の共通) -/

/-- 文書の位置にあるもの。 -/
inductive Target where
  /-- 名前解決の参照。`segIdx` はカーソルのある区切り(0 始まり)、`prefixLen` は参照先の宣言に解決した接頭辞の区切りの数。 -/
  | ref (r : Resolve.Ref) (segIdx prefixLen : Nat)
  /-- 宣言名そのもの。 -/
  | decl (file : String) (d : Decl)
  /-- record / state の宣言の中の欄名。 -/
  | field (m : Module) (d : Decl) (f : Field)
  /-- enum の宣言の中の variant 名。 -/
  | variant (m : Module) (d : Decl) (v : Variant)
  /-- 型検査が解決した欄 / stdlib のメソッド(式の中)。 -/
  | member (m : Typecheck.MemberRef)

structure Found where
  what : Target
  /-- 文書の行の中の範囲(文字の添字、終わりは排他的)。参照なら書かれた経路の全体、宣言名・欄名・メソッド名ならそのトークン。 -/
  startIdx : Nat
  endIdx : Nat

/-- 経路 `path` が `start` から空白なしで書かれているとき、文字の添字 `i` がどの区切りの上か(0 始まり)。書かれていなければ 0。 -/
def segmentAt (line : Array Char) (start : Nat) (path : List String) (i : Nat) : Nat := Id.run do
  let cs := (renderPath path).toList
  if cs.isEmpty || (line.toList.drop start).take cs.length != cs then return 0
  let mut off := 0
  let mut k := 0
  let mut idx := 0
  for seg in path do
    if start + off ≤ i then idx := k
    off := off + seg.length + 1
    k := k + 1
  return idx

/-- 参照の経路のうち、参照先の宣言に解決した接頭辞の区切りの数(名前解決は最長の接頭辞から試し、単純名か修飾名に一致したもの)。 -/
def prefixLen (r : Resolve.Ref) : Nat := Id.run do
  let mut k := r.path.length
  while k > 1 do
    let p := renderPath (r.path.take k)
    if p == r.target.name || p == r.target.qualified then return k
    k := k - 1
  return k

/-- 文書 `doc`(行 `line0` の文字 `chars`、文字の添字 `i`)の位置にあるもの。参照 → 宣言名 → 宣言の中の欄名 / variant 名 →
式の中の欄 / メソッドの順に探す。位置はトークン(経路)の先頭から終わり(終わりの直後の列を含む: カーソルが識別子の末尾にあるときも
引ける)まで。 -/
def locate (doc : Doc) (idx : UnitIndex) (chars : Array Char) (line0 i : Nat) : Option Found :=
  let hit (sp : Span) (endIdx : Nat) : Bool := sp.line == line0 + 1 && sp.col - 1 ≤ i && i ≤ endIdx
  let token (sp : Span) (name : String) (what : Target) : Found :=
    { what, startIdx := sp.col - 1, endIdx := sp.col - 1 + name.length }
  match idx.checked.refs.find? fun r => r.file == doc.path && hit r.span (pathEnd chars (r.span.col - 1) r.path) with
  | some r =>
    let start := r.span.col - 1
    some { what := .ref r (segmentAt chars start r.path i) (prefixLen r), startIdx := start, endIdx := pathEnd chars start r.path }
  | none =>
    let here := idx.checked.mods.find? (·.file == doc.path)
    match here.bind fun m => m.decls.find? fun d => hit d.span (d.span.col - 1 + d.name.length) with
    | some d => some (token d.span d.name (.decl doc.path d))
    | none =>
      let declared : Option Found := here.bind fun m => m.decls.findSome? fun d =>
        match d.fields.find? fun f => hit f.span (f.span.col - 1 + f.name.length) with
        | some f => some (token f.span f.name (.field m d f))
        | none =>
          (d.variants.find? fun v => hit v.span (v.span.col - 1 + v.name.length)).map fun v => token v.span v.name (.variant m d v)
      match declared with
      | some found => some found
      | none =>
        match idx.checked.members.find? fun m => m.file == doc.path && hit m.span (m.span.col - 1 + m.name.length) with
        | some m => some (token m.span m.name (.member m))
        | none => none

/-- 参照先の宣言(モジュールと宣言)。 -/
def declOf (idx : UnitIndex) (sym : Resolve.Sym) : Option (Module × Decl) :=
  (idx.checked.mods.find? (·.file == sym.file)).bind fun m => (m.decls.find? (·.name == sym.name)).map fun d => (m, d)

/-- 修飾名(`A.B.c`)の宣言(欄の record / state)。 -/
def declByKey (idx : UnitIndex) (key : String) : Option (Module × Decl) := Id.run do
  for m in idx.checked.mods do
    if let some d := m.decls.find? fun d => renderPath (m.name ++ [d.name]) == key then return some (m, d)
  return none

/-- ファイルの本文(開いていればバッファ、なければ索引のソース)。 -/
def textOf (st : State) (idx : UnitIndex) (file : String) : String :=
  match st.docs.find? (fun (d : Doc) => d.path == file) with
  | some d => d.text
  | none => (idx.sources.lookup file).getD ""

/-! ## 定義ジャンプ(`textDocument/definition`、C30) -/

/-- 文書 `uri` の位置(0 始まりの行、UTF-16 の列)にある参照・宣言名・欄名から、宣言(欄ならその record の欄)の `Location`。無ければ null。 -/
def definition (uri : String) (line0 ch : Nat) : M Json := do
  let st ← get
  let some doc := st.docs.find? (fun (d : Doc) => d.uri == uri) | return Json.null
  let some idx := st.index.find? (·.key == unitKey doc) | return Json.null
  let chars := ((doc.text.splitOn "\n").getD line0 "").toList.toArray
  let some found := locate doc idx chars line0 (charIndex chars ch) | return Json.null
  let target : Option (String × Span × String) := match found.what with
    | .ref r .. => some (r.target.file, r.target.span, r.target.name)
    | .decl file d => some (file, d.span, d.name)
    | .field m _ f => some (m.file, f.span, f.name)
    | .variant m _ v => some (m.file, v.span, v.name)
    | .member m =>
      match m.kind with
      | .field => (declByKey idx m.owner).bind fun (md, d) => (d.fields.find? (·.name == m.name)).map fun f => (md.file, f.span, f.name)
      | .method => none
  match target with
  | none => return Json.null
  | some (file, sp, name) => return locationJson (uriOfFile st file) ((textOf st idx file).splitOn "\n") sp name

/-! ## ホバー(`textDocument/hover`、C29) -/

/-- ホバーの本文(Markdown): 署名のコードブロック、種類・名前・モジュール、コメントのブロック(空のものは飛ばす)。 -/
def hoverMarkdown (sig what : String) (comments : List (List String)) : String :=
  "\n\n".intercalate (s!"```naru\n{sig}\n```" :: what :: (comments.filter (!·.isEmpty)).map commentMarkdown)

def describeDecl (m : Module) (d : Decl) : String :=
  s!"{d.kind.describe} `{d.name}` — module `{renderPath m.name}`" ++ (match d.owner with
    | some p => s!" (protocol `{p}`)"
    | none => "")

/-- 欄のホバー: `Record.欄: 型`(宣言に書かれた型)、欄の直上の 1 行の説明、record の宣言コメント。 -/
def fieldHover (lines : Array String) (m : Module) (d : Decl) (f : Field) : String :=
  hoverMarkdown s!"{d.name}.{f.name}: {f.ty.render}" s!"field `{f.name}` of {d.kind.describe} `{d.name}` — module `{renderPath m.name}`"
    [memberComment lines d f.span.line, declComment lines d]

/-- variant のホバー: `Enum.Variant(引数の型)`、variant の直上の 1 行の説明、enum の宣言コメント。 -/
def variantHover (lines : Array String) (m : Module) (d : Decl) (v : Variant) : String :=
  hoverMarkdown s!"{d.name}.{v.render}" s!"variant `{v.name}` of enum `{d.name}` — module `{renderPath m.name}`"
    [memberComment lines d v.span.line, declComment lines d]

/-- 位置にあるもののホバーの本文。宣言が索引に無ければ none。 -/
def hoverOf (st : State) (idx : UnitIndex) : Target → Option String
  | .ref r segIdx prefixLen => do
    let (m, d) ← declOf idx r.target
    let lines := ((textOf st idx m.file).splitOn "\n").toArray
    -- 経路の残り(`Phase.Tick` の `Tick`)の上で、それが enum の variant ならその variant
    if segIdx ≥ prefixLen && d.kind == .enum then
      if let some v := (r.path[segIdx]?).bind fun n => d.variants.find? (·.name == n) then
        return variantHover lines m d v
    return hoverMarkdown d.signature (describeDecl m d) [declComment lines d]
  | .decl file d => do
    let m ← idx.checked.mods.find? (·.file == file)
    let lines := ((textOf st idx file).splitOn "\n").toArray
    return hoverMarkdown d.signature (describeDecl m d) [declComment lines d]
  | .field m d f => some (fieldHover (((textOf st idx m.file).splitOn "\n").toArray) m d f)
  | .variant m d v => some (variantHover (((textOf st idx m.file).splitOn "\n").toArray) m d v)
  | .member mr =>
    match mr.kind with
    | .field => do
      let (m, d) ← declByKey idx mr.owner
      let lines := ((textOf st idx m.file).splitOn "\n").toArray
      match d.fields.find? (·.name == mr.name) with
      | some f => return fieldHover lines m d f
      | none =>
        -- 宣言に無い欄は無い(型検査が解決した欄)が、念のため型検査の型で
        return hoverMarkdown s!"{mr.ownerName}.{mr.name}: {mr.ret.render}"
          s!"field `{mr.name}` of {d.kind.describe} `{d.name}` — module `{renderPath m.name}`" [declComment lines d]
    | .method =>
      let ps := ", ".intercalate (mr.params.map fun (n, t) => match n with
        | some n => s!"{n} = {t.render}"
        | none => t.render)
      some (hoverMarkdown s!"{mr.recv.render}.{mr.name}({ps}) -> {mr.ret.render}" s!"method `{mr.name}` of `{mr.owner}` (stdlib)" [])

/-- 文書 `uri` の位置(0 始まりの行、UTF-16 の列)のホバー(`Hover`: Markdown の `contents` と `range`)。無ければ null。 -/
def hover (uri : String) (line0 ch : Nat) : M Json := do
  let st ← get
  let some doc := st.docs.find? (fun (d : Doc) => d.uri == uri) | return Json.null
  let some idx := st.index.find? (·.key == unitKey doc) | return Json.null
  let chars := ((doc.text.splitOn "\n").getD line0 "").toList.toArray
  let some found := locate doc idx chars line0 (charIndex chars ch) | return Json.null
  let some value := hoverOf st idx found.what | return Json.null
  return Json.mkObj [
    ("contents", Json.mkObj [("kind", "markdown"), ("value", value)]),
    ("range", rangeJson line0 (utf16Col chars found.startIdx) (utf16Col chars found.endIdx))]

/-! ## 補完(`textDocument/completion`、C31) -/

/-- LSP の `CompletionItemKind`(宣言の種類ごと)。 -/
def completionKind : DeclKind → Nat
  | .fn | .observer => 3                                                        -- Function
  | .input => 6                                                                 -- Variable
  | .record | .state => 22                                                      -- Struct
  | .enum => 13                                                                 -- Enum
  | .typeAlias => 7                                                             -- Class
  | .predicate | .condition | .regime | .property | .claim | .claimBundle => 8  -- Interface
  | .protocol => 9                                                              -- Module
  | .scenario => 23                                                             -- Event

/-- 宣言以外の `CompletionItemKind`: メソッド 2・欄 5・変数(局所名)6・モジュール 9・予約語 14・enum の variant 20。 -/
def kindMethod : Nat := 2
def kindField : Nat := 5
def kindVariable : Nat := 6
def kindModule : Nat := 9
def kindKeyword : Nat := 14
def kindEnumMember : Nat := 20

/-- `CompletionItem`: `label`・`kind`・`detail`(署名など)・`documentation`(Markdown: 宣言コメントの要旨など)。 -/
def completionItem (label : String) (kind : Nat) (detail : Option String := none) (doc : Option String := none) : Json :=
  Json.mkObj ([("label", Json.str label), ("kind", kind)]
    ++ detail.toList.map (fun (d : String) => ("detail", Json.str d))
    ++ doc.toList.map (fun (d : String) => ("documentation", Json.mkObj [("kind", Json.str "markdown"), ("value", Json.str d)])))

/-- `CompletionList`(候補は揃っている: `isIncomplete = false`。クライアントが入力中の語で絞る)。 -/
def completionList (items : Array Json) : Json :=
  Json.mkObj [("isIncomplete", false), ("items", Json.arr items)]

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- 添字 `i` を含む識別子の始まり(左へ識別子の文字を遡る。直前が末尾の `?` ならそれも識別子の一部)。 -/
def wordStartAt (chars : Array Char) (i : Nat) : Nat := Id.run do
  let mut s := if i > 0 && chars[i - 1]! == '?' then i - 1 else i
  while s > 0 && isIdentChar chars[s - 1]! do s := s - 1
  return s

/-- 添字 `i` から右へ続く識別子の終わり(排他的。末尾の `?` を含む)。 -/
def wordEndAt (chars : Array Char) (i : Nat) : Nat := Id.run do
  let mut e := i
  while (chars[e]?.map isIdentChar).getD false do e := e + 1
  if chars[e]? == some '?' then e := e + 1
  return e

/-- 添字 `i` がコメント(`//` の後、または同じ行で開いて閉じていない `/* … */`)か文字列リテラルの中か(その行の先頭から見る。
行をまたぐブロックコメントは見ない)。 -/
def inCommentOrString (chars : Array Char) (i : Nat) : Bool := Id.run do
  let mut j := 0
  let mut inStr := false
  let mut escaped := false
  let mut block := 0
  while j < i && j < chars.size do
    let c := chars[j]!
    if block > 0 then
      if c == '*' && chars[j + 1]? == some '/' then
        block := block - 1
        j := j + 1
      else if c == '/' && chars[j + 1]? == some '*' then
        block := block + 1
        j := j + 1
    else if inStr then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then inStr := false
    else if c == '"' then inStr := true
    else if c == '/' && chars[j + 1]? == some '/' then return true
    else if c == '/' && chars[j + 1]? == some '*' then
      block := 1
      j := j + 1
    j := j + 1
  return inStr || block > 0

/-- `.` の位置 `dotIdx` の直前に空白なしで書かれた経路(`A.B`)の区切り。経路でなければ空。 -/
def pathBeforeDot (chars : Array Char) (dotIdx : Nat) : List String := Id.run do
  let mut s := dotIdx
  while s > 0 && (isIdentChar chars[s - 1]! || chars[s - 1]! == '.') do s := s - 1
  let text := String.ofList ((chars.toList.drop s).take (dotIdx - s))
  if text.isEmpty then return []
  let segs := text.splitOn "."
  if segs.any (·.isEmpty) then return []
  return segs

/-- 経路の最長の接頭辞で解決する宣言(単純名か修飾名。名前解決と同じ規則)と、残りの区切り。 -/
def lookupDeclPath (idx : UnitIndex) (path : List String) : Option (Module × Decl × List String) := Id.run do
  let mut k := path.length
  while k > 0 do
    let p := renderPath (path.take k)
    for m in idx.checked.mods do
      for d in m.decls do
        if d.name == p || renderPath (m.name ++ [d.name]) == p then return some (m, d, path.drop k)
    k := k - 1
  return none

/-- Surface の型をソースの表記で正規化する: 型別名を展開し、record / state / enum の経路を表示名にする(`TyV.render` と比べられる形)。 -/
partial def normTy (idx : UnitIndex) (t : Ty) (depth : Nat := 0) : String :=
  match t with
  | .named _ path args =>
    let argsS := if args.isEmpty then "" else "<" ++ ", ".intercalate (args.toList.map (normTy idx · (depth + 1))) ++ ">"
    match lookupDeclPath idx path with
    | some (_, d, []) =>
      match d.kind, d.aliasOf with
      | .typeAlias, some t' => if depth < 16 then normTy idx t' (depth + 1) else renderPath path ++ argsS
      | _, _ => d.name ++ argsS
    | _ => renderPath path ++ argsS
  | .tuple _ elems => "(" ++ ", ".intercalate (elems.toList.map (normTy idx · (depth + 1))) ++ ")"
  | .fn _ ps r => "(" ++ ", ".intercalate (ps.toList.map (normTy idx · (depth + 1))) ++ ") -> " ++ normTy idx r (depth + 1)

/-- 宣言の補完項目: 名前、種類、署名(`detail`)、宣言コメントの要旨と種類・名前・モジュール(`documentation`)。 -/
def declItem (lines : Array String) (m : Module) (d : Decl) (note : Option String := none) : Json :=
  let head := match (declComment lines d).head? with
    | some s => [escapeMarkdown s]
    | none => []
  completionItem d.name (completionKind d.kind) (some d.signature)
    (some ("\n\n".intercalate (head ++ [describeDecl m d] ++ note.toList)))

/-- 単位の全宣言の補完項目(識別子の位置で見える名前: 名前解決はコンパイル単位の 1 つの大域表なので、import の有無に関わらず全宣言)。 -/
def declItems (st : State) (idx : UnitIndex) : Array Json := Id.run do
  let mut out : Array Json := #[]
  for m in idx.checked.mods do
    let lines := ((textOf st idx m.file).splitOn "\n").toArray
    for d in m.decls do
      out := out.push (declItem lines m d)
  return out

def keywordItems : Array Json :=
  (keywords.map fun k => completionItem k kindKeyword (some "keyword")).toArray

/-- 組み込みの型と構築子(`Resolve.builtinTypes` / `Some` / `None` / `Ok` / `Err`、`sort(xs, by = …)`)。常に E003 の `choose` / `pick` は出さない。 -/
def builtinItems : Array Json :=
  (Resolve.builtinTypes.map fun t => completionItem t 7 (some s!"built-in type `{t}`")).toArray
    ++ #[completionItem "Some" 3 (some "Some(x)"), completionItem "None" 6 (some "None"),
         completionItem "Ok" 3 (some "Ok(x)"), completionItem "Err" 3 (some "Err(e)"),
         completionItem "sort" 3 (some "sort(xs, by = |x| …)")]

/-- パターンが束ねる名前。 -/
partial def patBinders : Pattern → List (String × Span)
  | .bind sp n => [(n, sp)]
  | .ctor _ _ args => args.toList.flatMap patBinders
  | .tuple _ elems => elems.toList.flatMap patBinders
  | _ => []

/-- 式の中で束ねられる局所名(`let` / lambda / 量化 / パターン / scenario の `input` の仮引数)とその位置・注釈の型。 -/
partial def exprBinders : Expr → List (String × Span × Option Ty)
  | .lit .. | .var .. => []
  | .call _ f args => exprBinders f ++ args.toList.flatMap argBinders
  | .field _ r _ => exprBinders r
  | .method _ r _ args => exprBinders r ++ args.toList.flatMap argBinders
  | .binop _ _ l r => exprBinders l ++ exprBinders r
  | .unop _ _ a => exprBinders a
  | .ite _ c t e => exprBinders c ++ exprBinders t ++ exprBinders e
  | .matchE _ s arms => exprBinders s ++ arms.toList.flatMap fun arm => match arm with
      | .mk p g b => (patBinders p).map (fun (n, sp) => (n, sp, none)) ++ g.toList.flatMap exprBinders ++ exprBinders b
  | .block _ stmts tail => stmts.toList.flatMap stmtBinders ++ tail.toList.flatMap exprBinders
  | .recordLit _ _ fields base => fields.toList.flatMap (fun (_, _, e) => exprBinders e) ++ base.toList.flatMap exprBinders
  | .listLit _ es | .tupleLit _ es => es.toList.flatMap exprBinders
  | .lambda _ ps body | .quant _ _ ps body => ps.toList.map (fun b => (b.name, b.span, b.ty)) ++ exprBinders body
where
  argBinders : Arg → List (String × Span × Option Ty)
    | .pos e | .named _ e => exprBinders e
  stmtBinders : Stmt → List (String × Span × Option Ty)
    | .letS sp n ty v => (n, sp, ty) :: exprBinders v
    | .exprS e => exprBinders e
    | .inputS _ _ ps v => ps.toList.map (fun (p, sp) => (p, sp, none)) ++ exprBinders v
    | .observeS _ e => exprBinders e

/-- 文書の行 `line1`(1 始まり)を含む宣言: その行以前に始まる最後の宣言(protocol の中の宣言はそれ自身)。 -/
def enclosingDecl (lines : Array String) (m : Module) (line1 : Nat) : Option Decl := Id.run do
  let start (d : Decl) : Nat := (declLine? lines d).getD d.span.line
  let mut best : Option Decl := none
  for d in m.decls do
    if start d ≤ line1 then
      match best with
      | some b => if start d ≥ start b then best := some d
      | none => best := some d
  return best

/-- 位置(1 始まりの行、文字の添字)を含む宣言の仮引数と、その位置より前に束ねられた局所名の補完項目(有効範囲は位置の前後で近似する)。 -/
def localItems (lines : Array String) (m : Module) (line1 i : Nat) : Array Json := Id.run do
  let some d := enclosingDecl lines m line1 | return #[]
  let before (sp : Span) : Bool := sp.line < line1 || (sp.line == line1 && sp.col - 1 < i)
  let mut out : Array Json := #[]
  let mut seen : List String := []
  for p in d.params do
    if !seen.contains p.name then
      seen := p.name :: seen
      out := out.push (completionItem p.name kindVariable (some (Param.render p)) (some s!"parameter of {d.kind.describe} `{d.name}`"))
  for (n, sp, ty) in d.body.toList.flatMap exprBinders do
    if before sp && !seen.contains n then
      seen := n :: seen
      out := out.push (completionItem n kindVariable (ty.map fun t => s!"{n}: {t.render}") (some s!"local name in {d.kind.describe} `{d.name}`"))
  return out

/-- 受け手の型 `recv` の `.` の後の候補: record / state なら欄(宣言に書かれた型と 1 行の説明)、stdlib の型ならメソッド表
(受け手の型で実体化した署名)、どの型でもその型を最初の仮引数に取る fn 等(UFCS `x.f(…)`。仮引数の型は Surface の表記を `normTy` で
正規化して `TyV.render` と文字列で比べる近似: 別モジュールの同じ表示名の record は区別しない)。 -/
def memberItems (st : State) (idx : UnitIndex) (recv : TyV) : Array Json := Id.run do
  let mut out : Array Json := #[]
  if let .named key _ := recv then
    if let some (m, d) := declByKey idx key then
      let lines := ((textOf st idx m.file).splitOn "\n").toArray
      for f in d.fields do
        let doc := (memberComment lines d f.span.line).head?.map escapeMarkdown
        out := out.push (completionItem f.name kindField (some s!"{d.name}.{f.name}: {f.ty.render}") doc)
  if let some (tyName, bound, sigs) := Typecheck.sigsFor recv then
    for (name, sig) in sigs do
      let ps := ", ".intercalate (sig.params.map fun (n, t) =>
        let shown := (Typecheck.substVars bound t).render
        match n with
        | some n => s!"{n} = {shown}"
        | none => shown)
      let ret := (Typecheck.substVars bound sig.ret).render
      out := out.push (completionItem name kindMethod (some s!"{recv.render}.{name}({ps}) -> {ret}") (some s!"method of `{tyName}` (stdlib)"))
  let want := recv.render
  for m in idx.checked.mods do
    let lines := ((textOf st idx m.file).splitOn "\n").toArray
    for d in m.decls do
      if Typecheck.isFnLike d.kind then
        if let some p := d.params[0]? then
          if normTy idx p.ty == want then
            out := out.push (declItem lines m d (some s!"UFCS: `x.{d.name}(…)` = `{d.name}(x, …)`"))
  return out

/-- `.` の前に書かれた経路から作る候補(受け手の型が決まらないとき): enum なら variant、モジュール名(とその接頭辞)ならその宣言 / 次の区切り、
組み込みの型なら静的関数(`Set.empty` …)。 -/
def pathItems (st : State) (idx : UnitIndex) (path : List String) : Array Json := Id.run do
  let mut out : Array Json := #[]
  let statics : List String := match path with
    | ["Set"] => ["empty", "singleton", "of"]
    | ["List"] => ["empty", "range"]
    | ["Table"] => ["empty"]
    | _ => []
  for n in statics do
    out := out.push (completionItem n 3 (some s!"{renderPath path}.{n}(…)") (some "built-in"))
  if let some (m, d, []) := lookupDeclPath idx path then
    if d.kind == .enum then
      let lines := ((textOf st idx m.file).splitOn "\n").toArray
      for v in d.variants do
        out := out.push (completionItem v.name kindEnumMember (some s!"{d.name}.{v.render}") ((memberComment lines d v.span.line).head?.map escapeMarkdown))
  let mut nexts : List String := []
  for m in idx.checked.mods do
    if !path.isEmpty && m.name.take path.length == path then
      if m.name.length == path.length then
        let lines := ((textOf st idx m.file).splitOn "\n").toArray
        for d in m.decls do out := out.push (declItem lines m d)
      else if let some seg := m.name[path.length]? then
        if !nexts.contains seg then
          nexts := seg :: nexts
          out := out.push (completionItem seg kindModule (some s!"module {renderPath (path ++ [seg])}"))
  return out

/-- 索引から、`.` の直後(文字の添字 `nameStart`)に書かれた欄 / メソッド名の受け手の型(決まっていなければ none)。 -/
def accessRecv (checked : Checked) (file : String) (line1 nameStart : Nat) : Option TyV :=
  (checked.accesses.find? fun a => a.file == file && a.span.line == line1 && a.span.col - 1 == nameStart).bind fun a =>
    match a.recv with
    | .mvar _ | .unknown => none
    | t => some t

/-- 補完の探りに使う仮の識別子。 -/
def probeName : String := "naruCompletionProbe"

/-- `.` の後の受け手の型を探る: 位置の名前(途中まで書いたもの。無ければ空)を仮の識別子に置き換えた本文で単位を検査し直し
(診断は送らず索引も変えない)、その位置のアクセスの受け手の型を取る。文書が構文エラーの途中(`x.` まで書いた)でも引ける。 -/
def probeRecv (st : State) (doc : Doc) (lines : List String) (line0 nameStart nameEnd : Nat) : IO (Option TyV) := do
  let chars := (lines.getD line0 "").toList
  let line' := String.ofList (chars.take nameStart ++ probeName.toList ++ chars.drop nameEnd)
  let text' := "\n".intercalate (lines.set line0 line')
  let sources ← unitSources st doc
  let (_, checked) := compileSources (sources.map fun (f, t) => if f == doc.path then (f, text') else (f, t))
  return accessRecv checked doc.path (line0 + 1) nameStart

/-- 文書 `uri` の位置(0 始まりの行、UTF-16 の列)の補完(`CompletionList`)。`.` の直後(途中まで書いた名前の中を含む)なら受け手の型
(索引、無ければ探り)の欄 / メソッド / UFCS、型が決まらなければ `.` の前の経路(enum の variant・モジュールの宣言・組み込みの静的関数)。
それ以外の位置なら、位置を含む宣言の仮引数と位置より前の局所名、単位の全宣言、予約語、組み込み。コメント(行コメントと同じ行のブロックコメント)・文字列の中は空。 -/
def completion (uri : String) (line0 ch : Nat) : M Json := do
  let st ← get
  let some doc := st.docs.find? (fun (d : Doc) => d.uri == uri) | return completionList #[]
  let lines := doc.text.splitOn "\n"
  let chars := (lines.getD line0 "").toList.toArray
  let i := charIndex chars ch
  if inCommentOrString chars i then return completionList #[]
  let some idx := st.index.find? (·.key == unitKey doc) | return completionList (keywordItems ++ builtinItems)
  let wordStart := wordStartAt chars i
  let wordEnd := wordEndAt chars i
  let line1 := line0 + 1
  if wordStart > 0 && chars[wordStart - 1]! == '.' && !(wordStart > 1 && chars[wordStart - 2]! == '.') then
    let current := idx.sources.lookup doc.path == some doc.text
    let fromIndex := if current then accessRecv idx.checked doc.path line1 wordStart else none
    let recv? ← match fromIndex with
      | some t => pure (some t)
      | none => probeRecv st doc lines line0 wordStart wordEnd
    let items := match recv? with
      | some t => memberItems st idx t
      | none => #[]
    if !items.isEmpty then return completionList items
    return completionList (pathItems st idx (pathBeforeDot chars (wordStart - 1)))
  else
    let locals := match idx.checked.mods.find? (·.file == doc.path) with
      | some m => localItems (((textOf st idx m.file).splitOn "\n").toArray) m line1 i
      | none => #[]
    return completionList (locals ++ declItems st idx ++ keywordItems ++ builtinItems)

/-! ## リネーム(`textDocument/prepareRename` / `textDocument/rename`、C32) -/

/-- リネームの対象: 宣言(大域名)か record / state の欄。 -/
inductive RenameTarget where
  /-- 宣言。`file` / `span` はその名前のトークン、`qualified` は修飾名(参照の `target.qualified` と照合する)。 -/
  | decl (file : String) (span : Span) (name qualified : String)
  /-- record / state `key`(修飾名)の欄 `f`(宣言はモジュール `m` の `d`)。 -/
  | field (key : String) (m : Module) (d : Decl) (f : Field)

def RenameTarget.name : RenameTarget → String
  | .decl _ _ n _ => n
  | .field _ _ _ f => f.name

def RenameTarget.describe : RenameTarget → String
  | .decl _ _ n _ => s!"declaration `{n}`"
  | .field _ _ d f => s!"field `{f.name}` of {d.kind.describe} `{d.name}`"

/-- 行 `chars` の `start` から書かれた経路 `path` の各区切りの範囲(文字の添字、終わりは排他的)。区切りの間の `.` の前後の空白は許す。
そこにその経路が書かれていなければ none。 -/
def segmentRanges (chars : Array Char) (start : Nat) (path : List String) : Option (List (Nat × Nat)) := Id.run do
  let mut pos := start
  let mut out : List (Nat × Nat) := []
  let mut first := true
  for seg in path do
    if !first then
      while (chars[pos]?.map Char.isWhitespace).getD false do pos := pos + 1
      if chars[pos]? != some '.' then return none
      pos := pos + 1
      while (chars[pos]?.map Char.isWhitespace).getD false do pos := pos + 1
    first := false
    let cs := seg.toList
    if cs.isEmpty || (chars.toList.drop pos).take cs.length != cs then return none
    out := out ++ [(pos, pos + cs.length)]
    pos := pos + cs.length
  return some out

/-- 位置にあるもの(`locate`)のうちリネームできるものと、その名前のトークンの範囲(文字の添字)。参照は、書かれた経路のうち宣言名の区切り
(解決した接頭辞の最後)の上だけ(モジュール名の区切り・enum の variant の区切りは対象外。カーソルの区切り `i` は `segmentRanges` の範囲から
求める: `.` の前後に空白のある経路でも正しい区切りを見る)。宣言名・欄名(宣言の中・式の中・record literal の初期化)はそのトークン。
variant・stdlib のメソッド・局所名は none。 -/
def renameTargetAt (idx : UnitIndex) (chars : Array Char) (i : Nat) (found : Found) : Option (RenameTarget × Nat × Nat) :=
  match found.what with
  | .ref r _ prefixLen =>
    (segmentRanges chars found.startIdx r.path).bind fun rs =>
      match rs.findIdx? (fun (s, e) => s ≤ i && i ≤ e) with
      | none => none
      | some segIdx =>
        if prefixLen == 0 || segIdx + 1 != prefixLen then none
        else (rs[segIdx]?).map fun (s, e) => (.decl r.target.file r.target.span r.target.name r.target.qualified, s, e)
  | .decl file d =>
    (idx.checked.mods.find? (·.file == file)).map fun m =>
      (.decl file d.span d.name (renderPath (m.name ++ [d.name])), found.startIdx, found.endIdx)
  | .field m d f => some (.field (renderPath (m.name ++ [d.name])) m d f, found.startIdx, found.endIdx)
  | .variant .. => none
  | .member mr =>
    match mr.kind with
    | .field => (declByKey idx mr.owner).bind fun (m, d) => (d.fields.find? (·.name == mr.name)).map fun f =>
        (.field mr.owner m d f, found.startIdx, found.endIdx)
    | .method => none

/-- 書き換える箇所 1 つ: ファイル、1 始まりの行、文字の添字の範囲(終わりは排他的)、置き換える文字列(略記の展開なら `old: new` / `new: old`)。 -/
structure RenameEdit where
  file : String
  line : Nat
  startIdx : Nat
  endIdx : Nat
  newText : String
deriving BEq, Inhabited

/-- 行 `chars` の `[s, e)` がちょうど `name` か。 -/
def tokenIs (chars : Array Char) (s e : Nat) (name : String) : Bool :=
  e - s == name.length && (chars.toList.drop s).take (e - s) == name.toList

/-- `s` の前(空白を飛ばして)が `:` か(明示の `name: value` の値の位置)。 -/
def precededByColon (chars : Array Char) (s : Nat) : Bool := Id.run do
  let mut j := s
  while j > 0 && chars[j - 1]!.isWhitespace do j := j - 1
  return j > 0 && chars[j - 1]! == ':'

/-- 対象の名前が書かれたすべての箇所(同じコンパイル単位の全ファイル)と、各箇所の置き換え。宣言なら、その名前のトークンと、名前解決の索引
`Checked.refs` のその宣言への参照(値の位置・型の位置・record literal の型名・パターンの構築子・UFCS のメソッド名・scenario の input の束縛)の
宣言名の区切り。欄なら、record / state の宣言の中の欄名と、型検査の索引 `Checked.members` のその欄の参照(式の中の読み `r.f` と record literal の
初期化 `R { f: … }`)。略記(欄名 / claim bundle の項目名と値が同じトークン: `R { f }`、`bundle { c }`)は名前と値を分けて、宣言の改名なら
`old: new`(欄名 / 項目名を保つ。claim surface を変えない)、欄の改名なら `new: old`(値の局所名を保つ)に展開する。各箇所の本文が元の名前で
なければ(索引と本文の不一致)失敗にする(不完全・不正確な編集を返さない)。 -/
def renameEdits (st : State) (idx : UnitIndex) (target : RenameTarget) (newName : String) : Except String (List RenameEdit) := do
  let lineOf (file : String) (line : Nat) : Array Char := (((textOf st idx file).splitOn "\n").getD (line - 1) "").toList.toArray
  let edit (file : String) (line s e : Nat) (old newText : String) : Except String RenameEdit := do
    if !tokenIs (lineOf file line) s e old then
      throw s!"the text at {file}:{line}:{s + 1} is not `{old}` (the index does not match the current text)"
    return { file, line, startIdx := s, endIdx := e, newText }
  match target with
  | .decl file span name qualified => do
    let mut out : List RenameEdit := [← edit file span.line (span.col - 1) (span.col - 1 + name.length) name newName]
    for r in idx.checked.refs do
      if r.target.file == file && r.target.qualified == qualified then
        let chars := lineOf r.file r.span.line
        let k := prefixLen r
        match (segmentRanges chars (r.span.col - 1) r.path).bind (·[k - 1]?) with
        | none => throw s!"cannot locate the reference `{renderPath r.path}` at {r.file}:{r.span.line}:{r.span.col} in the current text"
        | some (s, e) =>
          let fieldShorthand := idx.checked.members.any fun mr =>
            mr.init && mr.shorthand && mr.file == r.file && mr.span.line == r.span.line && mr.span.col - 1 == s
          let itemShorthand := r.declKind == .claimBundle && r.path.length == 1 && !precededByColon chars s &&
            (((idx.checked.mods.find? (·.file == r.file)).bind fun m => m.decls.find? fun d => d.kind == .claimBundle && d.name == r.declName).any
              fun d => d.items.any fun (item, e) => item == name && e.span == r.span)
          let newText := if fieldShorthand || itemShorthand then s!"{name}: {newName}" else newName
          out := out ++ [← edit r.file r.span.line s e name newText]
    return out.eraseDups
  | .field key m _ f => do
    let mut out : List RenameEdit := [← edit m.file f.span.line (f.span.col - 1) (f.span.col - 1 + f.name.length) f.name newName]
    for mr in idx.checked.members do
      if mr.kind == .field && mr.owner == key && mr.name == f.name then
        let newText := if mr.init && mr.shorthand then s!"{newName}: {f.name}" else newName
        out := out ++ [← edit mr.file mr.span.line (mr.span.col - 1) (mr.span.col - 1 + f.name.length) f.name newText]
    return out.eraseDups

/-- 新しい名前の検査: 識別子(`[A-Za-z_][A-Za-z0-9_]*` + 末尾の `?`)で、予約語・組み込みの名前でなく、元の名前と同じ大文字 / 小文字の区分
(大文字始まりは型・モジュール・enum・構築子の経路として読まれるので、区分を変えると参照の読みが変わる)。宣言なら同じ単位の他の宣言名と
重ならず(E012)、その宣言を参照する宣言の局所名(仮引数・let・lambda・量化・パターン・scenario の input の仮引数)に捕まらない。欄なら同じ
record / state の他の欄名と重ならず、Lean が生成する予約名(`mk` / `rec` …)でない。問題があればその説明。 -/
def renameNameError (idx : UnitIndex) (target : RenameTarget) (newName : String) : Option String := Id.run do
  let old := target.name
  let body := if newName.endsWith "?" then (newName.dropEnd 1).toString else newName
  let cs := body.toList
  let identOk := match cs with
    | [] => false
    | c :: rest => isIdentStart c && rest.all isIdentChar
  if !identOk then return some s!"`{newName}` is not an identifier (`[A-Za-z_][A-Za-z0-9_]*`, optionally ending in `?`)"
  if keywords.contains newName then return some s!"`{newName}` is a keyword"
  if Resolve.isBuiltinHead newName then return some s!"`{newName}` is a built-in name"
  if old.front.isUpper != newName.front.isUpper then
    return some s!"`{newName}` must start with {if old.front.isUpper then "an uppercase" else "a lowercase"} letter like `{old}` (uppercase names are read as type / module / enum / constructor paths)"
  if newName == old then return some s!"`{newName}` is the current name"
  match target with
  | .decl file _ _ qualified =>
    for m in idx.checked.mods do
      if let some d := m.decls.find? (·.name == newName) then
        return some s!"`{newName}` is already declared ({d.kind.describe} at {m.file}:{d.span.line}:{d.span.col})"
    for r in idx.checked.refs do
      if r.target.file == file && r.target.qualified == qualified then
        if let some d := (idx.checked.mods.find? (·.file == r.file)).bind fun m => m.decls.find? fun d => d.name == r.declName && d.kind == r.declKind then
          if d.params.any (·.name == newName) || (d.body.toList.flatMap exprBinders).any (·.1 == newName) then
            return some s!"`{newName}` would be captured by a local name of {d.kind.describe} `{d.name}` ({r.file}:{d.span.line}), which refers to `{old}`"
    return none
  | .field _ _ d _ =>
    if d.fields.any (·.name == newName) then return some s!"{d.kind.describe} `{d.name}` already has a field `{newName}`"
    if Typecheck.leanGenerated.contains newName then
      return some s!"`{newName}` is reserved (Lean generates a declaration of that name for every record / enum)"
    return none

/-- 文書 `uri` の位置(0 始まりの行、UTF-16 の列)でリネームできるものと、その名前のトークンの範囲。無ければ none。 -/
def renameAt (uri : String) (line0 ch : Nat) : M (Option (UnitIndex × RenameTarget × Nat × Nat × Array Char)) := do
  let st ← get
  let some doc := st.docs.find? (fun (d : Doc) => d.uri == uri) | return none
  let some idx := st.index.find? (·.key == unitKey doc) | return none
  let chars := ((doc.text.splitOn "\n").getD line0 "").toList.toArray
  let i := charIndex chars ch
  let some found := locate doc idx chars line0 i | return none
  return (renameTargetAt idx chars i found).map fun (t, s, e) => (idx, t, s, e, chars)

/-- `textDocument/prepareRename`: リネームできる位置ならその名前の範囲と `placeholder`(現在の名前)、できなければ null。 -/
def prepareRename (uri : String) (line0 ch : Nat) : M Json := do
  let some (_, target, s, e, chars) ← renameAt uri line0 ch | return Json.null
  return Json.mkObj [("range", rangeJson line0 (utf16Col chars s) (utf16Col chars e)), ("placeholder", Json.str target.name)]

/-- `TextEdit`(1 行の中の範囲を `newText` に置き換える)。 -/
def textEditJson (lines : List String) (ed : RenameEdit) : Json :=
  let chars := (lines.getD (ed.line - 1) "").toList.toArray
  Json.mkObj [("range", rangeJson (ed.line - 1) (utf16Col chars ed.startIdx) (utf16Col chars ed.endIdx)), ("newText", Json.str ed.newText)]

/-- `textDocument/rename`: 位置の宣言名 / 欄名を `newName` に変える `WorkspaceEdit`(`changes`: URI → `TextEdit` の列。同じコンパイル単位の
全ファイル、開いていないファイルも URI で)。リネームできない位置なら null。単位に診断がある(索引が不完全)、開いている文書が直前の検査の
本文と違う(索引が古い)、開いていないファイルがディスクで変わった、新しい名前が不適切(`renameNameError`)、参照の位置が本文と合わない
(`renameEdits`)なら `.error`(不完全・不正確な編集を返さない)。 -/
def rename (uri : String) (line0 ch : Nat) (newName : String) : M (Except String Json) := do
  let some (idx, target, _, _, _) ← renameAt uri line0 ch | return .ok Json.null
  let st ← get
  if let some d := idx.diags[0]? then
    return .error s!"cannot rename {target.describe}: the unit has diagnostics ({d.code} at {d.file}:{d.span.line}:{d.span.col}); fix them first"
  for d in st.docs do
    if unitKey d == idx.key && idx.sources.lookup d.path != some d.text then
      return .error s!"cannot rename {target.describe}: {d.path} changed since the last successful check (fix the syntax error first)"
  -- 開いていないファイルがディスクで変わっていれば(索引の本文と違う)断る: 編集の位置は索引の本文のもの
  for (f, t) in idx.sources do
    if (st.docs.find? fun (d : Doc) => d.path == f).isNone then
      let onDisk ← try IO.FS.readFile f catch _ => pure ""
      if onDisk != t then
        return .error s!"cannot rename {target.describe}: {f} changed on disk since the last successful check (edit or save a document of the unit to re-check)"
  if let some why := renameNameError idx target newName then return .error s!"cannot rename {target.describe} to `{newName}`: {why}"
  match renameEdits st idx target newName with
  | .error e => return .error s!"cannot rename {target.describe}: {e}"
  | .ok edits =>
    let files := (edits.map (·.file)).eraseDups
    let changes := files.map fun f =>
      let lines := (textOf st idx f).splitOn "\n"
      let here := (edits.filter (·.file == f)).mergeSort fun a b => a.line < b.line || (a.line == b.line && a.startIdx ≤ b.startIdx)
      (uriOfFile st f, Json.arr (here.map fun ed => textEditJson lines ed).toArray)
    return .ok (Json.mkObj [("changes", Json.mkObj changes)])

/-! ## メッセージの処理 -/

def initializeResult (version : String) : Json :=
  Json.mkObj [
    ("capabilities", Json.mkObj [
      ("textDocumentSync", Json.mkObj [("openClose", true), ("change", 1), ("save", true)]),
      ("hoverProvider", true),
      ("definitionProvider", true),
      ("completionProvider", Json.mkObj [("triggerCharacters", Json.arr #[Json.str "."]), ("resolveProvider", false)]),
      ("renameProvider", Json.mkObj [("prepareProvider", true)])]),
    ("serverInfo", Json.mkObj [("name", "naru"), ("version", version)])]

/-- `params.position` の (0 始まりの行, UTF-16 の列)。 -/
def positionOf (params : Json) : Option (Nat × Nat) := do
  let pos ← getField params "position"
  let line ← (pos.getObjVal? "line" >>= Json.getNat?).toOption
  let ch ← (pos.getObjVal? "character" >>= Json.getNat?).toOption
  return (line, ch)

/-- `params.textDocument.uri`。 -/
def docUri (params : Json) : Option String := getField params "textDocument" >>= (getStr · "uri")

/-- `didChange` の `contentChanges` から全文を取る(最後の全文。`range` 付きの差分は全文同期では来ないので捨てる)。 -/
def fullText (params : Json) : Option String := Id.run do
  let some changes := (getField params "contentChanges" >>= fun j => j.getArr?.toOption) | return none
  let mut text : Option String := none
  for c in changes do
    if (getField c "range").isNone then
      if let some t := getStr c "text" then text := some t
  return text

def handle (msg : Json) : M Unit := do
  let some method := getStr msg "method" | return   -- 応答(こちらからのリクエストは無い)は無視
  let id? := getField msg "id"
  let params := (getField msg "params").getD Json.null
  match method, id? with
  | "initialize", some id => respond id (initializeResult (← get).version)
  | "initialized", _ => pure ()
  | "shutdown", some id =>
    modify fun s => { s with shutdownRequested := true }
    respond id Json.null
  | "exit", _ =>
    modify fun s => { s with exitCode := some (if s.shutdownRequested then 0 else 1) }
  | "textDocument/didOpen", _ =>
    match docUri params, getField params "textDocument" >>= (getStr · "text") with
    | some uri, some text => openDoc uri text
    | _, _ => log "didOpen: textDocument.uri / text missing"
  | "textDocument/didChange", _ =>
    match docUri params, fullText params with
    | some uri, some text => changeDoc uri text
    | some _, none => log "didChange: no full-text contentChanges (server uses full sync)"
    | none, _ => log "didChange: textDocument.uri missing"
  | "textDocument/didSave", _ =>
    match docUri params with
    | some uri => saveDoc uri (getStr params "text")
    | none => log "didSave: textDocument.uri missing"
  | "textDocument/didClose", _ =>
    match docUri params with
    | some uri => closeDoc uri
    | none => log "didClose: textDocument.uri missing"
  | "textDocument/definition", some id =>
    match docUri params, positionOf params with
    | some uri, some (line, ch) => respond id (← definition uri line ch)
    | _, _ => respondError id (-32602) "definition: textDocument.uri / position missing"
  | "textDocument/hover", some id =>
    match docUri params, positionOf params with
    | some uri, some (line, ch) => respond id (← hover uri line ch)
    | _, _ => respondError id (-32602) "hover: textDocument.uri / position missing"
  | "textDocument/completion", some id =>
    match docUri params, positionOf params with
    | some uri, some (line, ch) => respond id (← completion uri line ch)
    | _, _ => respondError id (-32602) "completion: textDocument.uri / position missing"
  | "textDocument/prepareRename", some id =>
    match docUri params, positionOf params with
    | some uri, some (line, ch) => respond id (← prepareRename uri line ch)
    | _, _ => respondError id (-32602) "prepareRename: textDocument.uri / position missing"
  | "textDocument/rename", some id =>
    match docUri params, positionOf params, getStr params "newName" with
    | some uri, some (line, ch), some newName =>
      match ← rename uri line ch newName with
      | .ok result => respond id result
      | .error e => respondError id (-32803) e   -- RequestFailed: 新しい名前が不適切、または参照の位置が本文に見つからない
    | _, _, _ => respondError id (-32602) "rename: textDocument.uri / position / newName missing"
  | _, some id => respondError id (-32601) s!"method not found: {method}"
  | _, none => pure ()

partial def loop (stdin : IO.FS.Stream) : M UInt32 := do
  match ← readMessage stdin with
  | none => return (if (← get).shutdownRequested then 0 else 1)
  | some (.error e) =>
    log s!"cannot read message: {e}"
    loop stdin
  | some (.ok msg) =>
    try handle msg
    catch e => log s!"{(getStr msg "method").getD "?"}: {e}"
    match (← get).exitCode with
    | some c => return c
    | none => loop stdin

/-- `naru lsp`: 標準入出力で LSP を話す。`exit` で終わる(`shutdown` の後なら 0、そうでなければ 1。入力が閉じても同じ)。 -/
def serve (version : String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let out ← IO.getStdout
  let (code, _) ← (loop stdin).run { out, version }
  return code

end Naru.Lsp
