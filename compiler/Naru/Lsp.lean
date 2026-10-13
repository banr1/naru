import Lean.Data.Json
import Naru.Driver
import Naru.Describe
import Naru.Config

/-!
# 言語サーバー(`naru lsp`、IDEAL.md C18 / C29 / C30)

標準入出力で LSP(JSON-RPC 2.0、`Content-Length` 枠)を話し、コンパイラの診断(E001〜E019)と、コンパイラの索引から取る
ホバー(`textDocument/hover`)・定義ジャンプ(`textDocument/definition`)を返す。エディタ(Zed 拡張 `editors/zed-naru/`)は `naru lsp` を
起動し、開いた文書を送ってくる。

- 応じるもの: `initialize` / `initialized` / `shutdown` / `exit`、`textDocument/didOpen` / `didChange`(全文同期)/
  `didSave` / `didClose`、`textDocument/hover`(C29)、`textDocument/definition`(C30)。それ以外のリクエスト(補完・リネーム・整形の
  C31〜C33 は未対応)には `MethodNotFound`(-32601)を返し、それ以外の通知は無視する。
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
    modify fun s => { s with index := (s.index.filter (·.key != key)).push { key, sources, checked } }
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

/-! ## メッセージの処理 -/

def initializeResult (version : String) : Json :=
  Json.mkObj [
    ("capabilities", Json.mkObj [
      ("textDocumentSync", Json.mkObj [("openClose", true), ("change", 1), ("save", true)]),
      ("hoverProvider", true),
      ("definitionProvider", true)]),
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
