import Naru
import NaruTest.Common

/-!
# `naru_test lsp` — 言語サーバー `naru lsp` の検査(IDEAL.md C18 / C29 / C30 / C31 / C32 / C33)

リポジトリのルートで実行する。`lake build naru` の後、子プロセスの `.lake/build/bin/naru lsp` と標準入出力で LSP を話し、
次を確かめる(`ok:` / `FAIL:`)。期待値はコンパイラ(`Naru.compileSources`、CLI の `compile` と同じ検査)から取る。

1. `initialize` の応答に全文同期(`textDocumentSync.change = 1`、`openClose`)と `hoverProvider = true`(C29)・`definitionProvider = true`(C30)・
   `completionProvider`(`triggerCharacters` に `.`。C31)・`renameProvider`(`prepareProvider = true`。C32)・`documentFormattingProvider = true`(C33)
   がある。`initialized` を送る。
   整形(C33、`textDocument/formatting`): `tests/accept/` の全受理例(3b)と `specs/consensus/` の移植ソースの全ファイル(5a)への `formatting` が
   空の配列(整形済み)。各ファイルの崩した複製(`mangle`: 字下げ・行の中の空白・行末の空白・空行・先頭の空行・末尾の改行を崩し、文字列と
   コメントの中とブロックコメントの中の行は変えない)を単独の文書(`.lake/naru/test/lsp/format/` 配下のディスクに無いパス)として開くと、
   `formatting` の編集を適用した本文が元と同一で、字句列(`Naru.lexAll`)が同じで、その本文への `formatting` は空(冪等)。元のソースと
   崩した複製を `.lake/naru/test/lsp/format/{accept/<名前>,unitgen}/{orig,mangled}/` に書いて CLI の `naru compile --out out <同じ相対パス>` を
   走らせ、生成 Lean の全ファイルの本文が C1 のヘッダ(`-- naru-…`)を除いて同一。`Naru.Format.format` の検体(3b'): 空行の規則(先頭・連続・
   開き括弧の直後・閉じ括弧の直前・末尾)と宣言コメントの隣接、ブロックコメント・文字列の中の不変、型引数 / lambda / 単項 `-` の空白、
   続きの行・`forall` の本体・揃えた引数・`if` の条件の続き・`else` の字下げが期待の文面と一致し冪等、未終了の文字列は E010 で整形されず
   LSP では null。
   リネーム(C32、`textDocument/prepareRename` / `rename`): 単独の受理例の参照の先頭で `prepareRename` が名前の範囲と placeholder を返し、`rename` の
   WorkspaceEdit がその文書の全出現を書き換える(3d)。移植ソース(5e): 別ファイルの fn 8 の参照の先頭で `prepareRename` が経路の宣言名の区切りの範囲と
   placeholder を返し、`rename` の WorkspaceEdit(`changes`: URI → `TextEdit`)が単位の全ファイルのその名前 — 編集の総数がコメントを除いた `grep -w` の
   出現数と一致し、宣言の名前のトークンと参照を含む — を一時名に書き換え、編集を適用した複製が `compileSources` で診断 0、ディスクに書いた複製
   (`.lake/naru/test/lsp/rename/<名前>/`)への CLI の `naru compile <files>` が exit 0。宣言名の上からも同じ編集。予約語・大文字始まり・既存の宣言名・
   識別子でない新しい名前は -32803 で拒否。欄名(5e'): 他の宣言・仮引数・他の record の欄と名前が重ならない欄の読みと record の宣言の欄名から、
   宣言の欄名・式の中の全読み・record literal の全初期化を書き換える(同じ検査)。コメント行・予約語・仮引数(局所名)・enum の宣言の中の variant 名・
   stdlib のメソッド名では `prepareRename` / `rename` とも null(5e'')。検体 `tests/units/accept/rename_cases/`(5e'''): 編集の位置と文面がちょうど期待と
   一致する — 欄 `x`(宣言・`x: 0`・略記 `{ x, ..p }` → `xRenamed: x`・読み `p.x`。仮引数 `x` は触らない)、claim `nonNegative`(宣言と略記の bundle の項目
   → `nonNegative: nonNegativeRenamed`。項目名が保たれる)、claim `doubled`(明示の項目 `second: doubled` は値だけ)、fn `twice`(宣言と runtime / spec の
   呼出し)、`Color . Red` の空白入りの経路(`Red` は null、`Color` は宣言・仮引数の型・経路) —、`twice` → `v`(呼出し側の局所名に捕まる)・欄 → `mk`
   (予約名)・欄 → `y`(既存の欄)は -32803、E011 のある単位と構文エラーで索引が古い文書では -32803 で、戻すと通る。検体の複製
   (`.lake/naru/test/lsp/stale/`)で閉じているファイルをディスクで書き換えると -32803 で、開いている文書を送り直す(検査し直す)と通る。
   補完(C31、`textDocument/completion`): 単独の受理例の参照の途中で参照先の宣言が候補にある(3d)。移植ソース(5b''): 別ファイルの fn の参照の
   途中(先頭の 2 文字目)で、単位の全 fn 名(参照先は kind Function と `Decl.signature` の detail)・全予約語(kind Keyword)・位置を含む宣言の
   仮引数(kind Variable、`名前: 型`)が候補にある。コメント行では候補なし(5c)。`Enum.Variant` の `.` の直後では、その enum の全 variant
   (kind EnumMember、detail `Enum.Variant(型)`)だけ(5c'')。式の中の欄名の位置(`.` の直後)では record の全欄(kind Field、detail
   `Record.欄: 型`)が候補にあり予約語は無い。Set の式の `.` の直後では stdlib の Set の全メソッド(kind Method、detail `Set<T>.m(…) -> 戻り型`)が
   候補にあり、常に拒否されるメソッド(E003 / E004)と予約語は無い。メソッド名を消して文書を壊しても(E010)同じ候補が返る(サーバーが仮の名前で
   単位を探る)(5d)。
2. 未対応のリクエスト(`textDocument/signatureHelp`: C29〜C33 に挙げた以外のリクエスト)には `MethodNotFound`(-32601)が返る。この応答は以後、
   通知の処理の終わりを待つ barrier にも使う(サーバーはメッセージを順に処理するので、応答が返れば直前の通知の診断は送り終わっている)。
   定義ジャンプ(C30、`textDocument/definition`): 受理例 1 つ(単独の単位)を開き、同じファイルの参照の位置から、その宣言の名前の範囲が返る(3d)。
   移植ソース(5b): 別ファイルの fn / type への参照(先頭と、先頭の区切りの最後の文字)から、宣言ファイルの URI と宣言の名前のトークンの範囲
   (`compileSources` の参照の索引 `Checked.refs` の `target` から計算した期待)が返り、コメント行・予約語 `fn` の位置では null、
   宣言名の上ではその宣言自身が返る(5c)。欄名の上では record の欄の名前のトークンが返る(5d)。
   ホバー(C29、`textDocument/hover`): 同じ参照の先頭へのホバーが Markdown(`contents.kind = "markdown"`)で、参照先の宣言の署名
   (`Decl.signature`: fn なら各仮引数 `名前: 型` と `-> 戻り型`)・種類と名前・モジュール名と、その宣言の宣言コメント(C60)の 1 行目
   (`Naru.declComment`)を含み、範囲が参照の経路を覆う(3d は単独の受理例なのでコメントは要求しない。5b の別ファイルの fn 8 / type 8)。
   空白(空行・字下げ)・コメント行・予約語 `fn` の位置では null、宣言名の上ではその宣言の署名(5c。`fn genesisStamp() -> Stamp` と
   `type Time = Int` は固定の期待で、表示関数の誤りも検出する)。record / enum の宣言の中の欄名 / variant 名の上では `Record.欄: 型` /
   `Enum.Variant(型)` で定義ジャンプは自身(5c')。式の中の欄名の上では `Record.欄: 型` と欄の record の宣言コメント、Set の stdlib メソッド名の
   上では受け手の型で実体化した署名 `Set<T>.m(…) -> 戻り型`(5d。型検査の索引 `Checked.members` から)。
3. `tests/reject/` の各反例を `didOpen` すると、`naru compile` と同じ E 番号・同じ行(・列)の診断がその URI に返り、
   反例の先頭コメントが名指しする E 番号(`期待: … E001`)がその中にある。`didClose` で空になる。
   `tests/accept/` の各受理例(単独の単位)を `didOpen` すると診断 0 件(C35 の正常例 `prop_bool.naru` を含む)、`didClose` で空。
   複数ファイルのコンパイル単位 `tests/units/`(各検体の `naru.toml` のルート `src/` 配下。C18): 反例(モジュール重複・runtime 循環・spec 循環)は
   全ファイルを `didOpen` すると、各ファイルの行末の `// E017` の印の行に、`naru compile`(`compileSources`)と同じ行・列(UTF-16)で
   トークン 1 つ分の幅の E017 が返る(関与する全ファイルの URI に)。`fix/` の内容に `didChange` して循環・重複を解消すると、関係する
   URI すべての診断が消え、戻すと戻る。受理例(正常な依存関係)は全ファイルの `didOpen` で 0 件。`didClose` で空。
   言語サーバーの検査はファイルを生成しない: 生成先と `tests/units/` の全ファイルの sha256 がセッションの前後で同じ。
4. BMP 外の文字(絵文字)を含む単独の文書(ディスクに無い)で、診断の列が UTF-16 単位で、範囲がトークン 1 つ分の幅になる。
5. `naru.toml` のソースルート(`specs/consensus/`)の移植ソースをすべて `didOpen` しても診断は 0 件(他の URI にも非空の診断は来ない)。
6. `<ルート>/Consensus/Objects/Time.naru` を `didChange` で壊す: 末尾に未解決名を使う fn を足すとその行に E011 が出る。
   `slotStart` を改名すると、それを使う他のファイル(Parameters / Grades)の URI に E011 が出る(開いている文書のバッファで
   単位全体を検査している)。その状態で Parameters を `didClose` すると空になり、同じ単位の再検査でも非空が送り直されない。
   Parameters を `didOpen` し直すと E011 が戻る。Time を元に戻すとそれらが空になって消える。`didSave` でも空のまま。
7. `didClose` を全ファイルに送ると、それぞれ空になる。
8. `shutdown` の応答が `null`、`exit` で子プロセスが exit 0。
-/

namespace NaruTest.Lsp

open Lean (Json)
open Naru.Lsp (readMessage writeMessage getField getStr)

/-- 診断の要約: `(E 番号, 0 始まりの行, 0 始まりの UTF-16 の列)`。 -/
abbrev Diag := String × Nat × Nat

/-- 受け取った publishDiagnostics: URI、診断の要約、各診断の範囲の終わりの列(要約と同じ順)。 -/
structure Pub where
  uri : String
  diags : Array Diag
  ends : Array Nat

structure Client where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }
  stdin : IO.FS.Stream
  stdout : IO.FS.Stream

def send (c : Client) (j : Json) : IO Unit := writeMessage c.stdin j

def notify (c : Client) (method : String) (params : Json) : IO Unit :=
  send c (Json.mkObj [("jsonrpc", "2.0"), ("method", method), ("params", params)])

def request (c : Client) (id : Nat) (method : String) (params : Json) : IO Unit :=
  send c (Json.mkObj [("jsonrpc", "2.0"), ("id", id), ("method", method), ("params", params)])

/-- publishDiagnostics の読み。壊れていれば `.error`。 -/
def parsePublish (params : Json) : Except String Pub := do
  let some uri := getStr params "uri" | throw "publishDiagnostics without uri"
  let arr ← (params.getObjVal? "diagnostics" >>= Json.getArr?)
  let mut diags : Array Diag := #[]
  let mut ends : Array Nat := #[]
  for d in arr do
    let some code := getStr d "code" | throw s!"{uri}: diagnostic without code"
    let some msg := getStr d "message" | throw s!"{uri}: diagnostic without message"
    if msg.isEmpty then throw s!"{uri}: empty message"
    let sev ← (d.getObjVal? "severity" >>= Json.getNat?)
    if sev != 1 then throw s!"{uri}: severity {sev} (expected 1 = Error)"
    if getStr d "source" != some "naru" then throw s!"{uri}: source is not \"naru\""
    let range ← d.getObjVal? "range"
    let st ← range.getObjVal? "start"
    let en ← range.getObjVal? "end"
    let sl ← (st.getObjVal? "line" >>= Json.getNat?)
    let sc ← (st.getObjVal? "character" >>= Json.getNat?)
    let el ← (en.getObjVal? "line" >>= Json.getNat?)
    let ec ← (en.getObjVal? "character" >>= Json.getNat?)
    if el != sl || ec < sc then throw s!"{uri}: range end {el}:{ec} before start {sl}:{sc}"
    diags := diags.push (code, sl, sc)
    ends := ends.push ec
  return { uri, diags, ends }

/-- id の応答が来るまで読み、その間の publishDiagnostics を(順に)集める。EOF なら none。 -/
partial def collectUntil (c : Client) (id : Nat) (acc : Array Pub := #[]) : IO (Option (Json × Array Pub)) := do
  match ← readMessage c.stdout with
  | none => return none
  | some (.error e) =>
    IO.eprintln s!"naru_test lsp: unreadable message from server: {e}"
    return none
  | some (.ok msg) =>
    if (getField msg "id" >>= fun j => j.getNat?.toOption) == some id then
      return some (msg, acc)
    match getStr msg "method" with
    | some "textDocument/publishDiagnostics" =>
      match parsePublish ((getField msg "params").getD Json.null) with
      | .ok p => collectUntil c id (acc.push p)
      | .error e =>
        IO.eprintln s!"naru_test lsp: {e}"
        collectUntil c id (acc.push { uri := "<malformed>", diags := #[], ends := #[] })
    | _ => collectUntil c id acc

/-- 同じ URI への publish は最後のものが有効。 -/
def latest (pubs : Array Pub) : Array Pub := Id.run do
  let mut out : Array Pub := #[]
  for p in pubs do
    match out.findIdx? (·.uri == p.uri) with
    | some i => out := out.set! i p
    | none => out := out.push p
  return out

def sortDiags (ds : Array Diag) : Array Diag :=
  ds.qsort fun (c1, l1, k1) (c2, l2, k2) => l1 < l2 || (l1 == l2 && (k1 < k2 || (k1 == k2 && c1 < c2)))

def showDiags (ds : Array Diag) : String :=
  ", ".intercalate ((sortDiags ds).toList.map fun (c, l, k) => s!"{c}@{l + 1}:{k + 1}")

/-! ## 期待値(コンパイラから) -/

/-- 1 始まりの文字の列 → 0 始まりの UTF-16 の列(サーバーとは別に書いた変換。ASCII の行では `col - 1`)。 -/
def utf16Of (text : String) (line1 col1 : Nat) : Nat :=
  let line := ((text.splitOn "\n").getD (line1 - 1) "").toList
  (line.take (col1 - 1)).foldl (fun n c => n + (if c.toNat ≥ 0x10000 then 2 else 1)) 0

/-- `sources` を 1 単位として検査したときの、ファイルの URI ごとの期待診断。 -/
def expectedOf (sources : List (String × String)) : Array (String × Array Diag) := Id.run do
  let (diags, _) := Naru.compileSources sources
  let mut out : Array (String × Array Diag) := #[]
  for d in diags do
    let uri := System.Uri.pathToUri d.file
    let text := (sources.lookup d.file).getD ""
    let e : Diag := (d.code, d.span.line - 1, utf16Of text d.span.line d.span.col)
    match out.findIdx? (·.1 == uri) with
    | some i => out := out.modify i fun (u, a) => (u, a.push e)
    | none => out := out.push (uri, #[e])
  return out

/-- (URI, 0 始まりの行, E 番号) の列を並べる(印との照合用。列は印に無い)。 -/
def sortLines (xs : List (String × Nat × String)) : List (String × Nat × String) :=
  xs.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 ≤ b.2.2)))

/-! ## 検査の本体 -/

structure Env where
  client : Client
  root : System.FilePath
  nextId : IO.Ref Nat
  /-- `exit` の後に子プロセスを回収したら true(回収済みのプロセスに `tryWait` / `kill` は使えない)。 -/
  exited : IO.Ref Bool

def barrierParams : Json :=
  Json.mkObj [("textDocument", Json.mkObj [("uri", "file:///nonexistent.naru")]),
    ("position", Json.mkObj [("line", 0), ("character", 0)])]

/-- barrier に使う未対応のリクエスト(C29〜C33 に挙げた以外のもの。実装される予定の hover / completion 等は使わない)。 -/
def barrierMethod : String := "textDocument/signatureHelp"

/-- 通知の処理の終わりを待つ: 未対応のリクエストを送り、その `MethodNotFound` が返るまでの publish を集める。 -/
def barrier (env : Env) : M (Option (Array Pub)) := do
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  request env.client id barrierMethod barrierParams
  match ← collectUntil env.client id with
  | none =>
    fail "server closed its output (or sent an unreadable message) before answering the barrier request"
    return none
  | some (resp, pubs) =>
    let code := getField resp "error" >>= fun e => (e.getObjVal? "code" >>= Json.getInt?).toOption
    if code != some (-32601) then
      fail s!"unknown request {barrierMethod}: expected error code -32601, got {resp.compress}"
    return some (latest pubs)

def textDocument (uri : String) (extra : List (String × Json) := []) : Json :=
  Json.mkObj (("uri", uri) :: extra)

def didOpen (env : Env) (uri text : String) : IO Unit :=
  notify env.client "textDocument/didOpen"
    (Json.mkObj [("textDocument", textDocument uri [("languageId", "naru"), ("version", 1), ("text", text)])])

def didChange (env : Env) (uri : String) (version : Nat) (text : String) : IO Unit :=
  notify env.client "textDocument/didChange"
    (Json.mkObj [("textDocument", textDocument uri [("version", version)]),
      ("contentChanges", Json.arr #[Json.mkObj [("text", text)]])])

def didSave (env : Env) (uri : String) : IO Unit :=
  notify env.client "textDocument/didSave" (Json.mkObj [("textDocument", textDocument uri)])

def didClose (env : Env) (uri : String) : IO Unit :=
  notify env.client "textDocument/didClose" (Json.mkObj [("textDocument", textDocument uri)])

/-- 受け取った publish(URI → 最後の診断)が期待と一致するか: 期待のある URI はその診断と一致(順不同)、期待に無い URI への
publish は空、`mustPublish` の URI には(空でも)publish がある。 -/
def agrees (what : String) (received : Array Pub) (expected : Array (String × Array Diag)) (mustPublish : List String) :
    M Bool := do
  let mut good := true
  for (uri, want) in expected do
    match received.find? (·.uri == uri) with
    | none =>
      fail s!"{what}: no publishDiagnostics for {uri} (expected {showDiags want})"
      good := false
    | some p =>
      if sortDiags p.diags != sortDiags want then
        fail s!"{what}: {uri}: got [{showDiags p.diags}], expected [{showDiags want}]"
        good := false
  for p in received do
    if (expected.find? (·.1 == p.uri)).isNone && !p.diags.isEmpty then
      fail s!"{what}: unexpected diagnostics for {p.uri}: [{showDiags p.diags}]"
      good := false
  for uri in mustPublish do
    if (received.find? (·.uri == uri)).isNone then
      fail s!"{what}: no publishDiagnostics for {uri} (expected an empty one)"
      good := false
  return good

def rel (env : Env) (abs : String) : String :=
  let pre := env.root.toString ++ "/"
  if abs.startsWith pre then (abs.drop pre.length).toString else abs

def relOfUri (env : Env) (uri : String) : String :=
  rel env (((System.Uri.fileUriToPath? uri).map (·.toString)).getD uri)

/-! ## 定義ジャンプ(C30) -/

/-- `Location` の要約: (URI, 0 始まりの行, 開始の UTF-16 の列, 終わりの列)。 -/
abbrev Loc := String × Nat × Nat × Nat

def parseLocation (j : Json) : Except String Loc := do
  let some uri := getStr j "uri" | throw s!"Location without uri: {j.compress}"
  let range ← j.getObjVal? "range"
  let st ← range.getObjVal? "start"
  let en ← range.getObjVal? "end"
  let sl ← (st.getObjVal? "line" >>= Json.getNat?)
  let sc ← (st.getObjVal? "character" >>= Json.getNat?)
  let el ← (en.getObjVal? "line" >>= Json.getNat?)
  let ec ← (en.getObjVal? "character" >>= Json.getNat?)
  if el != sl || ec ≤ sc then throw s!"Location range {sl}:{sc}-{el}:{ec} is not one token on one line"
  return (uri, sl, sc, ec)

/-- `textDocument/definition` を送り、`result` を読む: null → none、`Location` か 1 要素の配列 → その Location。 -/
def definitionAt (env : Env) (uri : String) (line ch : Nat) : IO (Except String (Option Loc)) := do
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  request env.client id "textDocument/definition"
    (Json.mkObj [("textDocument", Json.mkObj [("uri", uri)]), ("position", Json.mkObj [("line", line), ("character", ch)])])
  match ← collectUntil env.client id with
  | none => return .error "server closed its output before answering textDocument/definition"
  | some (resp, _) =>
    if let some e := getField resp "error" then return .error s!"textDocument/definition → error {e.compress}"
    match getField resp "result" with
    | none => return .error s!"textDocument/definition: response without result: {resp.compress}"
    | some Json.null => return .ok none
    | some (Json.arr ls) =>
      match ls.toList with
      | [l] => return (parseLocation l).map some
      | _ => return .error s!"textDocument/definition: expected one Location, got {ls.size}"
    | some l => return (parseLocation l).map some

/-- 宣言 `s` の期待(名前のトークンの Location。列は UTF-16)。 -/
def wantLoc (sources : List (String × String)) (s : Naru.Resolve.Sym) : Loc :=
  let text := (sources.lookup s.file).getD ""
  let sc := utf16Of text s.span.line s.span.col
  (System.Uri.pathToUri s.file, s.span.line - 1, sc, sc + s.name.length)

def showLoc (env : Env) : Loc → String
  | (uri, l, sc, ec) => s!"{relOfUri env uri}:{l + 1}:{sc + 1}-{ec + 1}"

/-- 参照 `r`(ソース `sources` の単位)の位置(先頭と、先頭の区切りの最後の文字)への `definition` が、参照先の宣言の名前の範囲を返す。
参照の位置が書かれた経路の先頭、宣言の位置がその名前であることも確かめる(期待の計算が成り立つ前提)。 -/
def checkDefinitionOf (env : Env) (sources : List (String × String)) (r : Naru.Resolve.Ref) : M Bool := do
  let text := (sources.lookup r.file).getD ""
  let targetText := (sources.lookup r.target.file).getD ""
  let want := wantLoc sources r.target
  let head := r.path.head?.getD ""
  let mut good := true
  if tokenAt targetText r.target.span.line r.target.span.col != r.target.name then
    fail s!"{rel env r.target.file}:{r.target.span.line}:{r.target.span.col}: the declaration's position should be its name `{r.target.name}`, found `{tokenAt targetText r.target.span.line r.target.span.col}`"
    good := false
  if tokenAt text r.span.line r.span.col != head then
    fail s!"{rel env r.file}:{r.span.line}:{r.span.col}: the reference's position should be the head of `{Naru.renderPath r.path}`, found `{tokenAt text r.span.line r.span.col}`"
    good := false
  let ch := utf16Of text r.span.line r.span.col
  for (k, label) in [(0, "head"), (head.length - 1, "last character of the head")] do
    let at_ := s!"{rel env r.file}:{r.span.line}:{r.span.col + k} ({label})"
    match ← definitionAt env (System.Uri.pathToUri r.file) (r.span.line - 1) (ch + k) with
    | .error e => fail s!"{at_}: {e}"; good := false
    | .ok none => fail s!"{at_}: definition → null, expected {showLoc env want}"; good := false
    | .ok (some got) =>
      if got != want then
        fail s!"{at_}: definition → {showLoc env got}, expected {showLoc env want}"
        good := false
  return good

/-- 先頭の参照を、参照先の宣言ごとに 1 つずつ、`n` 個まで。 -/
def distinctTargets (rs : Array Naru.Resolve.Ref) (n : Nat) : List Naru.Resolve.Ref := Id.run do
  let mut out : List Naru.Resolve.Ref := []
  for r in rs do
    if out.length ≥ n then break
    if out.any (·.target.qualified == r.target.qualified) then continue
    out := out ++ [r]
  return out

/-! ## ホバー(C29) -/

/-- 範囲の要約: (0 始まりの行, 開始の UTF-16 の列, 終わりの列)。1 行の中で幅が正のもの。 -/
def parseRange (j : Json) : Except String (Nat × Nat × Nat) := do
  let st ← j.getObjVal? "start"
  let en ← j.getObjVal? "end"
  let sl ← (st.getObjVal? "line" >>= Json.getNat?)
  let sc ← (st.getObjVal? "character" >>= Json.getNat?)
  let el ← (en.getObjVal? "line" >>= Json.getNat?)
  let ec ← (en.getObjVal? "character" >>= Json.getNat?)
  if el != sl || ec ≤ sc then throw s!"range {sl}:{sc}-{el}:{ec} is not a non-empty range on one line"
  return (sl, sc, ec)

/-- `textDocument/hover` を送り、`result` を読む: null → none、`Hover`(`contents` は `MarkupContent` の `markdown`、`range` あり)→ 本文と範囲。 -/
def hoverAt (env : Env) (uri : String) (line ch : Nat) : IO (Except String (Option (String × (Nat × Nat × Nat)))) := do
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  request env.client id "textDocument/hover"
    (Json.mkObj [("textDocument", Json.mkObj [("uri", uri)]), ("position", Json.mkObj [("line", line), ("character", ch)])])
  match ← collectUntil env.client id with
  | none => return .error "server closed its output before answering textDocument/hover"
  | some (resp, _) =>
    if let some e := getField resp "error" then return .error s!"textDocument/hover → error {e.compress}"
    match getField resp "result" with
    | none => return .error s!"textDocument/hover: response without result: {resp.compress}"
    | some Json.null => return .ok none
    | some h =>
      let some contents := getField h "contents" | return .error s!"textDocument/hover: result without contents: {h.compress}"
      if getStr contents "kind" != some "markdown" then
        return .error s!"textDocument/hover: contents.kind is not \"markdown\": {contents.compress}"
      let some value := getStr contents "value" | return .error s!"textDocument/hover: contents without value: {contents.compress}"
      let some range := getField h "range" | return .error s!"textDocument/hover: result without range: {h.compress}"
      match parseRange range with
      | .error e => return .error s!"textDocument/hover: {e}"
      | .ok r => return .ok (some (value, r))

/-- ホバーの本文に `needle` が含まれるか(Markdown の逃がし `\` を除いて比べる。`needle` は空でないこと)。 -/
def hoverHas (value needle : String) : Bool :=
  ((value.replace "\\" "").splitOn (needle.replace "\\" "")).length > 1

/-- ホバーの本文の 1 行目(署名のコードブロックの中身)。 -/
def hoverSignature (value : String) : String := ((value.splitOn "\n").getD 1 "")

/-- 宣言 `d`(モジュール `m`)のホバーに含まれるべき文字列: 署名、種類と名前、モジュール、fn なら各仮引数 `名前: 型` と `-> 戻り型`。 -/
def wantInHover (m : Naru.Module) (d : Naru.Decl) : List String :=
  [d.signature, s!"{d.kind.describe} `{d.name}`", s!"module `{Naru.renderPath m.name}`"]
    ++ (if d.kind == .fn then d.params.toList.map Naru.Param.render ++ (d.ret.toList.map fun t => s!"-> {t.render}") else [])

/-- 位置 `(line1, col1)`(1 始まりの文字の列)へのホバーが、宣言 `d` の署名等と(`needComment` なら)宣言コメントの 1 行目を含み、
範囲が `(line1, col1)` から始まって `minWidth` 以上の幅を持つか。失敗は `fail` に書く。 -/
def checkHover (env : Env) (sources : List (String × String)) (file : String) (line1 col1 minWidth : Nat)
    (m : Naru.Module) (d : Naru.Decl) (needComment : Bool) : M (Option String) := do
  let text := (sources.lookup file).getD ""
  let at_ := s!"{rel env file}:{line1}:{col1}"
  let targetLines := (((sources.lookup m.file).getD "").splitOn "\n").toArray
  let comment := Naru.declComment targetLines d
  let mut want := wantInHover m d
  if needComment then
    match comment.head? with
    | some summary => want := want ++ [summary]
    | none =>
      fail s!"{rel env m.file}:{d.span.line}: `{d.name}` has no declaration comment (C60), nothing to expect in the hover"
      return none
  let ch := utf16Of text line1 col1
  match ← hoverAt env (System.Uri.pathToUri file) (line1 - 1) ch with
  | .error e => fail s!"{at_}: {e}"; return none
  | .ok none => fail s!"{at_}: hover → null, expected the hover of {d.kind.describe} `{d.name}`"; return none
  | .ok (some (value, (l, sc, ec))) =>
    let missing := want.filter fun n => !(hoverHas value n)
    if !missing.isEmpty then
      fail s!"{at_}: hover lacks {missing}; got: {value.take 300}"
      return none
    if l != line1 - 1 || sc != ch || ec < ch + minWidth then
      fail s!"{at_}: hover range {l + 1}:{sc + 1}-{ec + 1} does not cover the token (expected start {ch + 1}, width ≥ {minWidth})"
      return none
    return some (hoverSignature value)

/-- 参照 `r` の先頭へのホバー(参照先の宣言の署名・種類・モジュール・宣言コメントの 1 行目、範囲は経路の先頭から)。 -/
def checkHoverOf (env : Env) (sources : List (String × String)) (checked : Naru.Checked) (r : Naru.Resolve.Ref)
    (needComment : Bool) : M (Option String) := do
  let some (m, d) := (checked.mods.find? (·.file == r.target.file)).bind fun m => (m.decls.find? (·.name == r.target.name)).map fun d => (m, d)
    | fail s!"{rel env r.file}:{r.span.line}:{r.span.col}: the target declaration `{r.target.name}` is not in {rel env r.target.file}"
      return none
  checkHover env sources r.file r.span.line r.span.col (r.path.head?.getD "").length m d needComment

/-- 位置へのホバーが null であること。 -/
def checkHoverNull (env : Env) (file : String) (line0 ch : Nat) (what : String) : M Unit := do
  let at_ := s!"{rel env file}:{line0 + 1}:{ch + 1} ({what})"
  match ← hoverAt env (System.Uri.pathToUri file) line0 ch with
  | .ok none => ok s!"{at_}: textDocument/hover → null (no identifier there)"
  | .ok (some (value, _)) => fail s!"{at_}: hover → {value.take 80}, expected null"
  | .error e => fail s!"{at_}: {e}"

/-! ## 補完(C31) -/

/-- 補完項目の要約: (label, kind, detail)。 -/
abbrev Item := String × Nat × String

/-- `textDocument/completion` を送り、`CompletionList`(`isIncomplete = false`、`items`: 各項目に `label` と `kind`)の項目を読む。 -/
def completionAt (env : Env) (uri : String) (line ch : Nat) : IO (Except String (Array Item)) := do
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  request env.client id "textDocument/completion"
    (Json.mkObj [("textDocument", Json.mkObj [("uri", uri)]), ("position", Json.mkObj [("line", line), ("character", ch)])])
  match ← collectUntil env.client id with
  | none => return .error "server closed its output before answering textDocument/completion"
  | some (resp, _) =>
    if let some e := getField resp "error" then return .error s!"textDocument/completion → error {e.compress}"
    match getField resp "result" with
    | none => return .error s!"textDocument/completion: response without result: {resp.compress}"
    | some res =>
      let some items := (getField res "items" >>= fun j => j.getArr?.toOption)
        | return .error s!"textDocument/completion: result without items: {res.compress.take 200}"
      if (res.getObjVal? "isIncomplete" >>= Json.getBool?).toOption != some false then
        return .error s!"textDocument/completion: isIncomplete should be false: {res.compress.take 200}"
      let mut out : Array Item := #[]
      for it in items do
        let some label := getStr it "label" | return .error s!"completion item without label: {it.compress}"
        let some kind := (it.getObjVal? "kind" >>= Json.getNat?).toOption | return .error s!"completion item `{label}` without kind"
        out := out.push (label, kind, (getStr it "detail").getD "")
      return .ok out

def labelsOf (items : Array Item) : List String := items.toList.map (·.1)

/-- 項目の中に `label` があり、種類が `kind` で、`detail` が `detailOk` を満たすか。 -/
def hasItem (items : Array Item) (label : String) (kind : Nat) (detailOk : String → Bool := fun _ => true) : Bool :=
  items.any fun (l, k, d) => l == label && k == kind && detailOk d

/-- LSP の `CompletionItemKind`(検査が名指しするもの。サーバーの表とは別に書く)。 -/
def kindFunction : Nat := 3
def kindMethod : Nat := 2
def kindField : Nat := 5
def kindVariable : Nat := 6
def kindKeyword : Nat := 14
def kindEnumMember : Nat := 20

/-- 宣言の種類に期待する `CompletionItemKind`(fn / observer は Function 3、input は Variable 6、record / state は Struct 22、enum は Enum 13、
type は Class 7、spec 宣言は Interface 8、protocol は Module 9、scenario は Event 23)。 -/
def kindOfDecl : Naru.DeclKind → Nat
  | .fn | .observer => 3
  | .input => 6
  | .record | .state => 22
  | .enum => 13
  | .typeAlias => 7
  | .predicate | .condition | .regime | .property | .claim | .claimBundle => 8
  | .protocol => 9
  | .scenario => 23

/-! ## リネーム(C32) -/

/-- `TextEdit` の要約: (0 始まりの行, 開始の UTF-16 の列, 終わりの列, newText)。 -/
abbrev TextEdit := Nat × Nat × Nat × String

/-- `textDocument/prepareRename` を送り、`result` を読む: null → none、`{ range, placeholder }` → その範囲と名前。 -/
def prepareRenameAt (env : Env) (uri : String) (line ch : Nat) : IO (Except String (Option ((Nat × Nat × Nat) × String))) := do
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  request env.client id "textDocument/prepareRename"
    (Json.mkObj [("textDocument", Json.mkObj [("uri", uri)]), ("position", Json.mkObj [("line", line), ("character", ch)])])
  match ← collectUntil env.client id with
  | none => return .error "server closed its output before answering textDocument/prepareRename"
  | some (resp, _) =>
    if let some e := getField resp "error" then return .error s!"textDocument/prepareRename → error {e.compress}"
    match getField resp "result" with
    | none => return .error s!"textDocument/prepareRename: response without result: {resp.compress}"
    | some Json.null => return .ok none
    | some r =>
      let some range := getField r "range" | return .error s!"textDocument/prepareRename: result without range: {r.compress}"
      let some placeholder := getStr r "placeholder" | return .error s!"textDocument/prepareRename: result without placeholder: {r.compress}"
      match parseRange range with
      | .error e => return .error s!"textDocument/prepareRename: {e}"
      | .ok rg => return .ok (some (rg, placeholder))

/-- `textDocument/rename` の結果: null(リネームできない位置)/ 拒否(新しい名前が不適切: エラーの `code` と `message`)/
`WorkspaceEdit` の `changes`(URI → 編集の列)。 -/
inductive RenameResult where
  | null
  | refused (code : Int) (message : String)
  | edits (changes : List (String × List TextEdit))

def parseTextEdit (j : Json) : Except String TextEdit := do
  let some newText := getStr j "newText" | throw s!"TextEdit without newText: {j.compress}"
  let range ← j.getObjVal? "range"
  let (l, sc, ec) ← parseRange range
  return (l, sc, ec, newText)

def renameAt (env : Env) (uri : String) (line ch : Nat) (newName : String) : IO (Except String RenameResult) := do
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  request env.client id "textDocument/rename"
    (Json.mkObj [("textDocument", Json.mkObj [("uri", uri)]), ("position", Json.mkObj [("line", line), ("character", ch)]),
      ("newName", newName)])
  match ← collectUntil env.client id with
  | none => return .error "server closed its output before answering textDocument/rename"
  | some (resp, _) =>
    if let some e := getField resp "error" then
      let code := ((e.getObjVal? "code" >>= Json.getInt?).toOption).getD 0
      return .ok (.refused code ((getStr e "message").getD ""))
    match getField resp "result" with
    | none => return .error s!"textDocument/rename: response without result: {resp.compress}"
    | some Json.null => return .ok .null
    | some r =>
      let some changes := getField r "changes" | return .error s!"textDocument/rename: WorkspaceEdit without changes: {r.compress.take 200}"
      let some obj := changes.getObj?.toOption | return .error "textDocument/rename: changes is not an object"
      let mut out : List (String × List TextEdit) := []
      for (u, arr) in obj.toList do
        let some items := arr.getArr?.toOption | return .error s!"textDocument/rename: changes[{u}] is not an array"
        let mut eds : List TextEdit := []
        for it in items do
          match parseTextEdit it with
          | .ok e => eds := eds ++ [e]
          | .error e => return .error s!"textDocument/rename: {e}"
        out := out ++ [(u, eds)]
      return .ok (.edits out)

def identChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- コメント(`//` から行末まで、`/* … */` の入れ子)を空白に置き換える(改行と文字列リテラルの中は保つ)。「コメントを除いた `grep -w`」の数え方。 -/
def stripComments (text : String) : String := Id.run do
  let cs := text.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  let mut depth := 0
  let mut inStr := false
  while i < cs.size do
    let c := cs[i]!
    let next := cs[i + 1]?
    if depth > 0 then
      if c == '/' && next == some '*' then
        depth := depth + 1
        i := i + 2
      else if c == '*' && next == some '/' then
        depth := depth - 1
        i := i + 2
      else
        out := out.push (if c == '\n' then '\n' else ' ')
        i := i + 1
    else if inStr then
      out := out.push c
      if c == '\\' then
        if let some d := next then out := out.push d
        i := i + 2
      else
        if c == '"' then inStr := false
        i := i + 1
    else if c == '"' then
      inStr := true
      out := out.push c
      i := i + 1
    else if c == '/' && next == some '/' then
      while i < cs.size && cs[i]! != '\n' do i := i + 1
    else if c == '/' && next == some '*' then
      depth := 1
      i := i + 2
    else
      out := out.push c
      i := i + 1
  return String.ofList out.toList

/-- `name` が識別子として現れる回数(`grep -w` 相当: 前後が識別子の文字でなく、直後が末尾の `?` でもない)。 -/
def countWord (text name : String) : Nat := Id.run do
  let cs := text.toList.toArray
  let n := name.toList.toArray
  let mut k := 0
  let mut i := 0
  while i + n.size ≤ cs.size do
    let before := i == 0 || !(identChar cs[i - 1]!)
    let after := !(((cs[i + n.size]?).map fun c => identChar c || c == '?').getD false)
    if cs.extract i (i + n.size) == n && before && after then
      k := k + 1
      i := i + n.size
    else i := i + 1
  return k

/-- UTF-16 の列 → 文字の添字(`utf16Of` の逆)。 -/
def charIdxOf (chars : List Char) (u : Nat) : Nat := Id.run do
  let mut n := 0
  let mut i := 0
  for c in chars do
    if n ≥ u then break
    n := n + (if c.toNat ≥ 0x10000 then 2 else 1)
    i := i + 1
  return i

/-- 編集を本文に適用する(各編集は 1 行の中の範囲。同じ行は後ろから)。 -/
def applyEdits (text : String) (edits : List TextEdit) : String := Id.run do
  let mut lines := (text.splitOn "\n").toArray
  let sorted := edits.mergeSort fun (l1, s1, _, _) (l2, s2, _, _) => l1 > l2 || (l1 == l2 && s1 ≥ s2)
  for (l, s, e, newText) in sorted do
    let chars := (lines.getD l "").toList
    lines := lines.set! l (String.ofList (chars.take (charIdxOf chars s) ++ newText.toList ++ chars.drop (charIdxOf chars e)))
  return "\n".intercalate lines.toList

/-- リネームの `WorkspaceEdit` の検査: 編集はすべて `newName` への置き換えで幅が元の名前の長さ、URI は単位のファイル、`mustInclude` の位置
(URI, 0 始まりの行, UTF-16 の列)を含み、編集の総数が単位の全ソースのコメントを除いた `name` の `grep -w` の出現数と一致し、
編集を適用した複製(メモリ上)を `compileSources` が診断 0 で通し、同じ複製を `dir/<name>/` に書いて CLI の `naru compile <files>` が exit 0。
通れば ok を書いて true。 -/
def checkRenameEdits (env : Env) (sources : List (String × String)) (dir : System.FilePath) (what name newName : String)
    (changes : List (String × List TextEdit)) (mustInclude : List (String × Nat × Nat)) : M Bool := do
  let total := (changes.map fun (_, eds) => eds.length).foldl (· + ·) 0
  let wordCount := (sources.map fun (_, t) => countWord (stripComments t) name).foldl (· + ·) 0
  let fileOf (u : String) : Option String := (sources.find? fun (f, _) => System.Uri.pathToUri f == u).map (·.1)
  for (u, eds) in changes do
    if (fileOf u).isNone then
      fail s!"{what}: rename edits a file outside the unit: {u}"
      return false
    for (l, sc, ec, newText) in eds do
      if newText != newName || ec - sc != name.length then
        fail s!"{what}: edit at {relOfUri env u}:{l + 1}:{sc + 1}-{ec + 1} replaces with `{newText}` (expected `{newName}` over the {name.length} chars of `{name}`)"
        return false
  for (u, l, ch) in mustInclude do
    let found := (changes.lookup u).getD [] |>.any fun (l', sc, _, _) => l' == l && sc == ch
    if !found then
      fail s!"{what}: the edits lack the position {relOfUri env u}:{l + 1}:{ch + 1}"
      return false
  if total != wordCount then
    fail s!"{what}: {total} edit(s), but `{name}` occurs {wordCount} time(s) as a word outside comments in the unit's sources"
    return false
  -- 複製に適用して検査(メモリ上: CLI と同じ `compileSources`)
  let renamedSources := sources.map fun (f, t) => match changes.lookup (System.Uri.pathToUri f) with
    | some eds => (f, applyEdits t eds)
    | none => (f, t)
  let (diags, _) := Naru.compileSources renamedSources
  if !diags.isEmpty then
    fail s!"{what}: after applying the edits, compileSources reports {diags.size} diagnostic(s): {(diags.toList.take 3).map fun d => s!"{d.code}@{rel env d.file}:{d.span.line}:{d.span.col} {d.msg.take 80}"}"
    return false
  -- 複製をディスクに書いて CLI の `naru compile <files>`(検査だけ)
  let copy := dir / name
  if ← copy.pathExists then IO.FS.removeDirAll copy
  let root := env.root.toString ++ "/"
  let mut paths : Array String := #[]
  for (f, t) in renamedSources do
    let relPath := if f.startsWith root then (f.drop root.length).toString else f
    let dst := copy / relPath
    if let some parent := dst.parent then IO.FS.createDirAll parent
    IO.FS.writeFile dst t
    paths := paths.push dst.toString
  let bin := env.root / ".lake" / "build" / "bin" / "naru"
  let out ← runProc bin.toString (#["compile"] ++ paths) (cwd := some copy)
  if out.exitCode != 0 || (out.stderr.splitOn "error[").length > 1 then
    fail s!"{what}: naru compile on the renamed copy {copy} → exit {out.exitCode}: {tail out.stderr 300}"
    return false
  ok s!"{what}: textDocument/rename `{name}` → `{newName}` → WorkspaceEdit with {total} edit(s) in {changes.length} file(s) (= the {wordCount} word occurrence(s) outside comments, incl. the declaration and the reference), applied to a copy: compileSources 0 diagnostics and naru compile exit 0 ({copy})"
  return true

/-- 同じ編集の集合か(URI ごとの編集を位置で並べて比べる)。 -/
def sameEdits (a b : List (String × List TextEdit)) : Bool :=
  let norm (xs : List (String × List TextEdit)) : List (String × List TextEdit) :=
    (xs.map fun (u, eds) => (u, eds.mergeSort fun (l1, s1, _, _) (l2, s2, _, _) => l1 < l2 || (l1 == l2 && s1 ≤ s2))).mergeSort fun x y => x.1 ≤ y.1
  norm a == norm b

/-- 本文の中で `needle` が `occurrence` 回目(0 始まり)に現れる位置 (0 始まりの行, 文字の列)。ASCII の検体で使う(列 = UTF-16 の列)。 -/
def findIn (text needle : String) (occurrence : Nat := 0) : Option (Nat × Nat) := Id.run do
  let mut seen := 0
  let mut line0 := 0
  for l in text.splitOn "\n" do
    let parts := l.splitOn needle
    let mut col := 0
    for k in [0:parts.length - 1] do
      col := col + (parts[k]!).length
      if seen == occurrence then return some (line0, col)
      seen := seen + 1
      col := col + needle.length
    line0 := line0 + 1
  return none

/-- 期待の編集 (URI, 0 始まりの行, 開始の列, 終わりの列, newText) の集合とちょうど一致し、適用した複製を `compileSources` が診断 0 で通すこと。 -/
def checkExactEdits (env : Env) (sources : List (String × String)) (what : String) (changes : List (String × List TextEdit))
    (expected : List (String × TextEdit)) : M Bool := do
  let got := changes.flatMap fun (u, eds) => eds.map fun e => (u, e)
  let show_ (x : String × TextEdit) : String := s!"{relOfUri env x.1}:{x.2.1 + 1}:{x.2.2.1 + 1}-{x.2.2.2.1 + 1} `{x.2.2.2.2}`"
  let missing := expected.filter fun e => !got.contains e
  let extra := got.filter fun e => !expected.contains e
  if !missing.isEmpty || !extra.isEmpty then
    fail s!"{what}: edits differ from the expectation; missing {missing.map show_}, unexpected {extra.map show_}"
    return false
  let renamed := sources.map fun (f, t) => match changes.lookup (System.Uri.pathToUri f) with
    | some eds => (f, applyEdits t eds)
    | none => (f, t)
  let (diags, _) := Naru.compileSources renamed
  if !diags.isEmpty then
    fail s!"{what}: after applying the edits, compileSources reports {diags.size} diagnostic(s): {(diags.toList.take 3).map fun d => s!"{d.code}@{rel env d.file}:{d.span.line}:{d.span.col} {d.msg.take 80}"}"
    return false
  ok s!"{what}: textDocument/rename → exactly the {expected.length} expected edit(s) ({expected.map show_}), compile clean after applying"
  return true

/-- `rename` が -32803 で拒まれ、メッセージに `needle` を含むこと。 -/
def checkRenameRefused (env : Env) (uri : String) (line0 ch : Nat) (newName needle what : String) : M Unit := do
  match ← renameAt env uri line0 ch newName with
  | .ok (.refused code msg) =>
    if code == -32803 && (msg.splitOn needle).length > 1 then ok s!"{what}: textDocument/rename → `{newName}` refused (-32803: {msg.take 160})"
    else fail s!"{what}: rename → `{newName}` refused with code {code} / message `{msg.take 160}`, expected -32803 mentioning `{needle}`"
  | .ok .null => fail s!"{what}: rename → `{newName}` → null, expected an error"
  | .ok (.edits _) => fail s!"{what}: rename → `{newName}` → edits, expected an error"
  | .error e => fail s!"{what}: {e}"

/-- 位置へのリネームが null であること(`prepareRename` と `rename` の両方)。 -/
def checkRenameNull (env : Env) (file : String) (line0 ch : Nat) (what : String) : M Unit := do
  let at_ := s!"{rel env file}:{line0 + 1}:{ch + 1} ({what})"
  let uri := System.Uri.pathToUri file
  match ← prepareRenameAt env uri line0 ch with
  | .error e => fail s!"{at_}: {e}"
  | .ok (some (_, placeholder)) => fail s!"{at_}: prepareRename → `{placeholder}`, expected null"
  | .ok none =>
    match ← renameAt env uri line0 ch "lspRenameProbe" with
    | .error e => fail s!"{at_}: {e}"
    | .ok .null => ok s!"{at_}: textDocument/prepareRename and textDocument/rename → null (nothing to rename there)"
    | .ok (.refused code msg) => fail s!"{at_}: rename → error {code} {msg}, expected null"
    | .ok (.edits changes) => fail s!"{at_}: rename → {changes.length} file(s) of edits, expected null"

/-! ## 整形(C33) -/

/-- 行をまたぐ `TextEdit`: ((開始の行, 列), (終わりの行, 列), newText)。行は 0 始まり、列は UTF-16。 -/
abbrev FullEdit := (Nat × Nat) × (Nat × Nat) × String

def parsePos (j : Json) : Except String (Nat × Nat) := do
  let l ← j.getObjVal? "line" >>= Json.getNat?
  let c ← j.getObjVal? "character" >>= Json.getNat?
  return (l, c)

def parseFullEdit (j : Json) : Except String FullEdit := do
  let some newText := getStr j "newText" | throw s!"TextEdit without newText: {j.compress.take 200}"
  let range ← j.getObjVal? "range"
  let s ← parsePos (← range.getObjVal? "start")
  let e ← parsePos (← range.getObjVal? "end")
  return (s, e, newText)

/-- `textDocument/formatting` を送り、`result` を読む: null → none(整形できない)、`TextEdit[]` → その列(空なら整形済み)。 -/
def formattingAt (env : Env) (uri : String) : IO (Except String (Option (List FullEdit))) := do
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  request env.client id "textDocument/formatting"
    (Json.mkObj [("textDocument", Json.mkObj [("uri", uri)]), ("options", Json.mkObj [("tabSize", 2), ("insertSpaces", true)])])
  match ← collectUntil env.client id with
  | none => return .error "server closed its output before answering textDocument/formatting"
  | some (resp, _) =>
    if let some e := getField resp "error" then return .error s!"textDocument/formatting → error {e.compress}"
    match getField resp "result" with
    | none => return .error s!"textDocument/formatting: response without result: {resp.compress.take 200}"
    | some Json.null => return .ok none
    | some r =>
      let some items := r.getArr?.toOption | return .error s!"textDocument/formatting: result is not an array: {r.compress.take 200}"
      let mut out : List FullEdit := []
      for it in items do
        match parseFullEdit it with
        | .ok e => out := out ++ [e]
        | .error e => return .error s!"textDocument/formatting: {e}"
      return .ok (some out)

/-- 行をまたぐ編集を本文に適用する(後ろから)。 -/
def applyFullEdits (text : String) (edits : List FullEdit) : String := Id.run do
  let lines := (text.splitOn "\n").toArray
  let offsetOf (l ch : Nat) : Nat := Id.run do
    let mut off := 0
    for k in [0:min l lines.size] do off := off + (lines[k]!).length + 1
    return off + charIdxOf (lines.getD l "").toList ch
  let sorted := edits.mergeSort fun (s1, _, _) (s2, _, _) => s1.1 > s2.1 || (s1.1 == s2.1 && s1.2 ≥ s2.2)
  let mut cs := text.toList
  for (s, e, newText) in sorted do
    cs := cs.take (offsetOf s.1 s.2) ++ newText.toList ++ cs.drop (offsetOf e.1 e.2)
  return String.ofList cs

/-- 2 つの本文の最初に違う行(1 始まり)とその両方の内容。 -/
def firstDiff (a b : String) : Option (Nat × String × String) := Id.run do
  let la := (a.splitOn "\n").toArray
  let lb := (b.splitOn "\n").toArray
  for i in [0:max la.size lb.size] do
    if la[i]? != lb[i]? then return some (i + 1, (la[i]?).getD "<eof>", (lb[i]?).getD "<eof>")
  return none

def showDiff (a b : String) : String :=
  match firstDiff a b with
  | some (n, x, y) => s!"first difference at line {n}: got `{x.take 100}`, expected `{y.take 100}`"
  | none => "no line differs"

/-- 整形の検体を作る: 字句と字句の間の改行の有無は保ったまま、字下げ(3 空白ずつずらす・タブ・0)・行の中の空白(`, ` / ` = ` / `) {` /
`(` / `: ` / ` -> ` の周り)・行末の空白・空行(2 つに、開き括弧の直後と閉じ括弧の直前にも)・先頭の空行・末尾の改行を崩す。
文字列リテラルかコメントを含む行は字下げだけ(その中は変えない)、ブロックコメントの中の行は触らない。 -/
def mangle (text : String) : String := Id.run do
  let mut out : Array String := #["", ""]
  let mut depth := 0
  let mut k := 0
  for l in text.splitOn "\n" do
    let cs := l.toList
    let body := String.ofList (cs.dropWhile fun c => c == ' ' || c == '\t')
    let indent := cs.length - body.length
    let opens := (body.splitOn "/*").length - 1
    let closes := (body.splitOn "*/").length - 1
    let hasQuote := body.toList.contains '"'
    let hasComment := (body.splitOn "//").length > 1 || opens > 0 || closes > 0
    if depth > 0 then
      out := out.push l
    else if body.isEmpty then
      out := out.push ""
      out := out.push "  "
    else
      let mangled :=
        if hasQuote || hasComment then body
        else (((((((body.replace ", " ",  ").replace " = " "  =  ").replace ") {" ")  {").replace "(" "( ").replace ": " " :  ").replace " -> " "->").replace " " "  ")
      let newIndent := if k % 2 == 0 then indent + 3 else 0
      let line := String.ofList (List.replicate newIndent ' ') ++ (if k % 4 == 0 then "\t" else "") ++ mangled
      if body.startsWith "}" || body.startsWith ")" || body.startsWith "]" then out := out.push ""
      out := out.push (if hasComment then line else line ++ "   \t")
      if body.endsWith "{" && !hasComment then out := out.push ""
      k := k + 1
    depth := depth + opens - closes
  return "\n".intercalate out.toList ++ "\n\n"

/-- 整形済みであること: 開いている文書への `formatting` が空の配列。 -/
def checkFormatted (env : Env) (uri what text : String) : M Bool := do
  match ← formattingAt env uri with
  | .error e => fail s!"{what}: {e}"; return false
  | .ok none => fail s!"{what}: textDocument/formatting → null (the server could not lex the document)"; return false
  | .ok (some []) => return true
  | .ok (some edits) =>
    fail s!"{what}: textDocument/formatting → {edits.length} edit(s), expected none (the file is not in canonical form; {showDiff text (applyFullEdits text edits)})"
    return false

/-- 崩した複製(`mangle`)を単独の文書(ディスクに無い `fakePath`)として開き、`formatting` の編集を適用すると元と同一になり、字句列が
同じで、その本文への `formatting` は空(冪等)であること。 -/
def checkMangled (env : Env) (what fakePath text : String) : M Bool := do
  let uri := System.Uri.pathToUri fakePath
  let mangled := mangle text
  if mangled == text then
    fail s!"{what}: the mangled copy equals the original"
    return false
  didOpen env uri mangled
  let some _ ← barrier env | return false
  let mut good := true
  match ← formattingAt env uri with
  | .error e => fail s!"{what}: {e}"; good := false
  | .ok none => fail s!"{what}: formatting the mangled copy → null"; good := false
  | .ok (some edits) =>
    let formatted := applyFullEdits mangled edits
    if formatted != text then
      fail s!"{what}: formatting the mangled copy ({edits.length} edit(s)) does not restore the original ({showDiff formatted text})"
      good := false
    else
      match Naru.lexAll fakePath mangled, Naru.lexAll fakePath formatted with
      | .ok a, .ok b =>
        if a.map (·.kind) != b.map (·.kind) then
          fail s!"{what}: the token sequence changed between the mangled copy and its formatting"
          good := false
      | _, _ => fail s!"{what}: the mangled copy or its formatting does not lex"; good := false
      didChange env uri 2 formatted
      let some _ ← barrier env | return false
      match ← formattingAt env uri with
      | .ok (some []) => pure ()
      | .ok (some es) => fail s!"{what}: formatting the formatted copy again → {es.length} edit(s), expected none (not idempotent)"; good := false
      | .ok none => fail s!"{what}: formatting the formatted copy again → null"; good := false
      | .error e => fail s!"{what}: {e}"; good := false
  didClose env uri
  let some _ ← barrier env | return false
  return good

/-- 生成先の全ファイルの本文(C1 のヘッダ `-- naru-…` 行を除く)。鍵は `dir` からの相対パス。 -/
def generatedBodies (dir : System.FilePath) : IO (List (String × String)) := do
  let files ← Naru.listFiles dir "lean"
  let pre := dir.toString ++ "/"
  let mut out : List (String × String) := []
  for f in files do
    let rel := if f.startsWith pre then (f.drop pre.length).toString else f
    let body := "\n".intercalate (((← IO.FS.readFile f).splitOn "\n").filter fun l => !l.startsWith "-- naru-")
    out := out ++ [(rel, body)]
  return out.mergeSort fun a b => a.1 ≤ b.1

/-- 整形の前後で生成 Lean の本文(ヘッダを除く)が同一であること: `files`(相対パス, 本文)を `dir/orig/` と、崩した複製を `dir/mangled/` に
書き、それぞれを cwd にして同じ相対パスで CLI の `naru compile --out out <files>` を走らせ(ヘッダのソースのパスも同じになる)、
`out/` の全ファイルの本文を照合する。 -/
def checkCompileSame (env : Env) (what : String) (dir : System.FilePath) (files : List (String × String)) : M Bool := do
  let bin := env.root / ".lake" / "build" / "bin" / "naru"
  for sub in ["orig", "mangled"] do
    let base := dir / sub
    if ← base.pathExists then IO.FS.removeDirAll base
    for (rel, t) in files do
      let dst := base / rel
      if let some parent := dst.parent then IO.FS.createDirAll parent
      IO.FS.writeFile dst (if sub == "orig" then t else mangle t)
    let out ← runProc bin.toString (#["compile", "--out", "out"] ++ (files.map (·.1)).toArray) (cwd := some base)
    if out.exitCode != 0 then
      fail s!"{what}: naru compile on {base} → exit {out.exitCode}: {tail out.stderr 300}"
      return false
  let a ← generatedBodies (dir / "orig" / "out")
  let b ← generatedBodies (dir / "mangled" / "out")
  if a.isEmpty then
    fail s!"{what}: naru compile --out wrote nothing under {dir / "orig" / "out"}"
    return false
  if a == b then return true
  let differing := (a.filter fun (p, body) => b.lookup p != some body).map (·.1)
  let missing := (b.filter fun (p, _) => (a.lookup p).isNone).map (·.1)
  fail s!"{what}: generated Lean differs between the original and the mangled copy: differing {differing.take 5}, only in the mangled {missing.take 5}"
  return false

/-- `Naru.Format.format` の検体: `input` の正規形が `expected` で、`expected` を整形しても変わらない。 -/
def checkSnippet (what input expected : String) : M Unit := do
  match Naru.Format.format "<snippet>" input with
  | .error d => fail s!"{what}: format → {d.code}: {d.msg}"
  | .ok out =>
    if out != expected then fail s!"{what}: format → {showDiff out expected}\n--- got\n{out}--- expected\n{expected}"
    else
      match Naru.Format.format "<snippet>" out with
      | .ok again =>
        if again == out then ok s!"{what}: Naru.Format.format → the expected canonical form ({(expected.splitOn "\n").length - 1} line(s)), idempotent"
        else fail s!"{what}: formatting the canonical form again changes it ({showDiff again out})"
      | .error d => fail s!"{what}: formatting the canonical form again → {d.code}: {d.msg}"

/-- 3b'. 整形(C33)の受理例の検査: 各受理例を単独の文書として開いて `formatting` が空(整形済み)、閉じてから崩した複製の復元と冪等
(`checkMangled`)、元と崩した複製の `naru compile --out` の生成 Lean の本文の一致(`checkCompileSame`)。 -/
def acceptFormatChecks (env : Env) (accepts : List String) (formatDir : System.FilePath) : M Unit := do
  let mut nFormatted := 0
  let mut nMangled := 0
  let mut nCompileSame := 0
  for p in accepts do
    let abs := (env.root / p).toString
    let uri := System.Uri.pathToUri abs
    let text ← IO.FS.readFile abs
    didOpen env uri text
    let some _ ← barrier env | return
    if ← checkFormatted env uri p text then nFormatted := nFormatted + 1
    didClose env uri
    let some _ ← barrier env | return
    let name := (System.FilePath.mk p).fileName.getD p
    if ← checkMangled env s!"{p} (mangled copy)" (formatDir / "single" / name).toString text then nMangled := nMangled + 1
    if ← checkCompileSame env s!"{p} (naru compile --out of the original and the mangled copy)" (formatDir / "accept" / name) [(name, text)] then
      nCompileSame := nCompileSame + 1
  if nFormatted == accepts.length && nFormatted > 0 then
    ok s!"tests/accept/: {nFormatted} files, textDocument/formatting → [] (every accept example is in canonical form)"
  if nMangled == accepts.length && nMangled > 0 then
    ok s!"tests/accept/: {nMangled} mangled copies (indentation, spaces, blank lines, trailing whitespace, final newline), textDocument/formatting restores the original with the same token sequence, and formatting the result again → []"
  if nCompileSame == accepts.length && nCompileSame > 0 then
    ok s!"tests/accept/: {nCompileSame} files, naru compile --out of the original and of the mangled copy → identical generated Lean apart from the `-- naru-` header lines ({formatDir / "accept"})"

/-- 3b'. `Naru.Format.format` の検体: 空行(先頭・連続・開き括弧の直後・閉じ括弧の直前・末尾)と宣言コメントの隣接、ブロックコメントと文字列の中の
不変、型引数・lambda・単項 `-` の空白、続きの行と `forall` の本体・揃えた引数・`if` の条件の続き・`else` の字下げ、字句解析に失敗する本文
(`format` は E010、LSP は null)。 -/
def snippetChecks (env : Env) (formatDir : System.FilePath) : M Unit := do
  checkSnippet "snippet: blank lines and a declaration comment"
    "\n\nmodule A\n\n\n// c1\n// c2\nfn f(a: Nat) -> Nat {\n\n  a   +  1\n\n}\n\n\n"
    "module A\n\n// c1\n// c2\nfn f(a: Nat) -> Nat {\n  a + 1\n}\n"
  checkSnippet "snippet: block comment and string literal kept verbatim"
    "fn g() -> String {\n    /* a\n       b */  \"x // y\"\n}"
    "fn g() -> String {\n  /* a\n       b */ \"x // y\"\n}\n"
  checkSnippet "snippet: type arguments, lambda bars, unary minus, member access"
    "fn h(xs:List<Nat>,t:Table<Nat,List<Nat>>)->Int{xs.map(|x|-x.toInt()).fold(0,|a,b|a+b)}"
    "fn h(xs: List<Nat>, t: Table<Nat, List<Nat>>) -> Int { xs.map(|x| -x.toInt()).fold(0, |a, b| a + b) }\n"
  checkSnippet "snippet: continuation lines and a quantifier body"
    "fn k(a: Bool, b: Bool) -> Bool {\na\n&& b\n|| (forall n: Nat {\nn >= 0\n})\n}"
    "fn k(a: Bool, b: Bool) -> Bool {\n  a\n    && b\n    || (forall n: Nat {\n         n >= 0\n       })\n}\n"
  checkSnippet "snippet: aligned arguments, if condition continuation, else, record update"
    "fn m(st: S, x: Nat,\n  y: Nat) -> S {\nif x > 0\n&& y > 0 {\nS { x: x, ..st }\n} else {\nst\n}\n}"
    "fn m(st: S, x: Nat,\n     y: Nat) -> S {\n  if x > 0\n      && y > 0 {\n    S { x: x, ..st }\n  } else {\n    st\n  }\n}\n"
  checkSnippet "snippet: adjacent symbols that would merge into one token keep a space (`| |`, `x ?`, `. ..`, `! =`)"
    "fn z() -> Nat { apply( |  |   1) }\nfn w() -> Nat {   x   ?   }\nfn v(s: S) -> S { S {   .   ..s } }\nfn u() -> Bool {  !   =  }"
    "fn z() -> Nat { apply(| | 1) }\nfn w() -> Nat { x ? }\nfn v(s: S) -> S { S { . ..s } }\nfn u() -> Bool { ! = }\n"
  checkSnippet "snippet: CRLF line endings become LF"
    "fn c() -> Nat {\r\n  1\r\n}\r\n"
    "fn c() -> Nat {\n  1\n}\n"
  match Naru.Format.format "<snippet>" "fn f() -> String { \"unterminated }\n" with
  | .error d =>
    if d.code == "E010" then ok s!"snippet: an unterminated string literal → Naru.Format.format fails with {d.code} (not formatted)"
    else fail s!"snippet: unterminated string → {d.code}, expected E010"
  | .ok _ => fail "snippet: an unterminated string literal was formatted, expected a lexer failure"
  let lexUri := System.Uri.pathToUri (formatDir / "single" / "lexerror.naru").toString
  didOpen env lexUri "fn f() -> String { \"unterminated }\n"
  let some _ ← barrier env | return
  match ← formattingAt env lexUri with
  | .ok none => ok "lexerror.naru (unterminated string literal): textDocument/formatting → null"
  | .ok (some es) => fail s!"lexerror.naru: textDocument/formatting → {es.length} edit(s), expected null"
  | .error e => fail s!"lexerror.naru: {e}"
  didClose env lexUri
  let some _ ← barrier env | return

/-- 5a. 整形(C33)の移植ソースの検査: 開いている全ファイルへの `formatting` が空(整形済み)、崩した複製の復元と冪等、単位全体の
`naru compile --out` の生成 Lean の本文が元と崩した複製で一致。 -/
def unitFormatChecks (env : Env) (unitRoot : String) (dslFiles : List String) (formatDir : System.FilePath) : M Unit := do
  let mut nFormatted := 0
  let mut nMangled := 0
  let mut unitFiles : List (String × String) := []
  for p in dslFiles do
    let abs := (env.root / p).toString
    let text ← IO.FS.readFile abs
    if ← checkFormatted env (System.Uri.pathToUri abs) p text then nFormatted := nFormatted + 1
    let rel := if p.startsWith (unitRoot ++ "/") then (p.drop (unitRoot.length + 1)).toString else p
    if ← checkMangled env s!"{p} (mangled copy)" (formatDir / "unit" / rel).toString text then nMangled := nMangled + 1
    unitFiles := unitFiles ++ [(rel, text)]
  if nFormatted == dslFiles.length && nFormatted > 0 then
    ok s!"{unitRoot}/: {nFormatted} files, textDocument/formatting → [] (every file of the unit is in canonical form)"
  if nMangled == dslFiles.length && nMangled > 0 then
    ok s!"{unitRoot}/: {nMangled} mangled copies, textDocument/formatting restores the original with the same token sequence, and formatting the result again → []"
  if ← checkCompileSame env s!"{unitRoot}/ (naru compile --out of the unit and of its mangled copy)" (formatDir / "unitgen") unitFiles then
    ok s!"{unitRoot}/: naru compile --out of the {unitFiles.length} original files and of their mangled copies → identical generated Lean apart from the `-- naru-` header lines ({formatDir / "unitgen"})"

def checks (env : Env) : M Unit := do
  let c := env.client
  -- 1. initialize / initialized
  request c 1 "initialize"
    (Json.mkObj [("processId", Json.null), ("rootUri", System.Uri.pathToUri env.root), ("capabilities", Json.mkObj [])])
  let some (resp, _) ← collectUntil c 1
    | fail "no response to initialize"; return
  let caps := getField resp "result" >>= (getField · "capabilities")
  let sync := caps >>= (getField · "textDocumentSync")
  let change := sync >>= fun s => (s.getObjVal? "change" >>= Json.getNat?).toOption
  let openClose := sync >>= fun s => (s.getObjVal? "openClose" >>= Json.getBool?).toOption
  let definitionProvider := caps >>= fun s => (s.getObjVal? "definitionProvider" >>= Json.getBool?).toOption
  let hoverProvider := caps >>= fun s => (s.getObjVal? "hoverProvider" >>= Json.getBool?).toOption
  let triggers := caps >>= (getField · "completionProvider") >>= (getField · "triggerCharacters") >>= fun j => j.getArr?.toOption
  let dotTrigger := (triggers.map fun a => a.any fun j => j.getStr?.toOption == some ".").getD false
  let prepareProvider := caps >>= (getField · "renameProvider") >>= fun r => (r.getObjVal? "prepareProvider" >>= Json.getBool?).toOption
  let formattingProvider := caps >>= fun s => (s.getObjVal? "documentFormattingProvider" >>= Json.getBool?).toOption
  if change == some 1 && openClose == some true && definitionProvider == some true && hoverProvider == some true && dotTrigger && prepareProvider == some true && formattingProvider == some true then
    ok "initialize: textDocumentSync.change = 1 (full), openClose = true, hoverProvider = true, definitionProvider = true, completionProvider.triggerCharacters has \".\", renameProvider.prepareProvider = true, documentFormattingProvider = true"
  else
    fail s!"initialize: expected textDocumentSync.change = 1, openClose = true, hoverProvider = true, definitionProvider = true, completionProvider with trigger \".\", renameProvider.prepareProvider = true and documentFormattingProvider = true, got {resp.compress}"
  notify c "initialized" (Json.mkObj [])
  -- 2. 未対応のリクエスト
  let some _ ← barrier env | return
  ok s!"unknown request {barrierMethod} → error -32601 (MethodNotFound)"
  -- 3. 反例
  let rejects ← Naru.listFiles "tests/reject" "naru"
  let mut nRejects := 0
  for p in rejects do
    let abs := (env.root / p).toString
    let text ← IO.FS.readFile abs
    let uri := System.Uri.pathToUri abs
    let expected := expectedOf [(abs, text)]
    let want := ((expected.find? (·.1 == uri)).map (·.2)).getD #[]
    if want.isEmpty then
      fail s!"{p}: naru compile reports no diagnostics for this reject example"
      continue
    didOpen env uri text
    let some got ← barrier env | return
    let mut good ← agrees s!"{p}: didOpen" got expected [uri]
    let codes := (got.find? (·.uri == uri)).map (·.diags.map (·.1)) |>.getD #[]
    match namedCode text with
    | none =>
      fail s!"{p}: the header comment names no E number"
      good := false
    | some code =>
      if !codes.contains code then
        fail s!"{p}: the header comment expects {code} but the server returned [{showDiags (sortDiags ((got.find? (·.uri == uri)).map (·.diags) |>.getD #[]))}]"
        good := false
    if good then
      nRejects := nRejects + 1
      ok s!"{p}: didOpen → {want.size} diagnostic(s) at the same lines as naru compile [{showDiags want}], including the header's {(namedCode text).getD "?"}"
    didClose env uri
    let some got ← barrier env | return
    let _ ← agrees s!"{p}: didClose" got #[] [uri]
  if nRejects == rejects.length then
    ok s!"tests/reject/: {nRejects} files, didOpen diagnostics match naru compile and the header's E number, didClose clears them"
  -- 3b. 受理例(単独の単位): `didOpen` で診断 0 件(C35 の正常例 `prop_bool.naru` を含む)、`didClose` で空
  let accepts ← Naru.listFiles "tests/accept" "naru"
  let mut nAccepts := 0
  for p in accepts do
    let abs := (env.root / p).toString
    let uri := System.Uri.pathToUri abs
    didOpen env uri (← IO.FS.readFile abs)
    let some got ← barrier env | return
    let opened ← agrees s!"{p}: didOpen" got #[] [uri]
    didClose env uri
    let some got ← barrier env | return
    let closed ← agrees s!"{p}: didClose" got #[] [uri]
    if opened && closed then nAccepts := nAccepts + 1
  if nAccepts == accepts.length && nAccepts > 0 then
    ok s!"tests/accept/: {nAccepts} files, didOpen → 0 diagnostics (none for other URIs either), didClose → empty"
  -- 3b'. 整形(C33): 受理例が整形済み、崩した複製の復元と冪等、生成 Lean の本文の不変、`Naru.Format.format` の検体
  let formatDir := env.root / ".lake" / "naru" / "test" / "lsp" / "format"
  acceptFormatChecks env accepts formatDir
  snippetChecks env formatDir
  -- 3d. 定義ジャンプ(C30)、単独の文書: 参照のある最初の受理例を開き、その最初の参照の位置から同じファイルの宣言の名前の範囲が返る
  let mut singleDone := false
  for p in accepts do
    if singleDone then break
    let abs := (env.root / p).toString
    let text ← IO.FS.readFile abs
    let (_, checked) := Naru.compileSources [(abs, text)]
    let some r := checked.refs[0]? | continue
    singleDone := true
    let uri := System.Uri.pathToUri abs
    didOpen env uri text
    let some _ ← barrier env | return
    if ← checkDefinitionOf env [(abs, text)] r then
      ok s!"{p}: textDocument/definition on `{Naru.renderPath r.path}` (line {r.span.line}) in a single-document unit → {r.target.kind.describe} `{r.target.name}` at {showLoc env (wantLoc [(abs, text)] r.target)}"
    if let some sig ← checkHoverOf env [(abs, text)] checked r (needComment := false) then
      ok s!"{p}: textDocument/hover on `{Naru.renderPath r.path}` (line {r.span.line}) in a single-document unit → markdown with `{sig}`"
    -- 補完(C31)、単独の文書: 参照の 2 文字目(識別子の途中)で、参照先の宣言(その種類)が候補にある
    match ← completionAt env uri (r.span.line - 1) (utf16Of text r.span.line r.span.col + 1) with
    | .error e => fail s!"{p}:{r.span.line}:{r.span.col + 1}: {e}"
    | .ok items =>
      if hasItem items r.target.name (kindOfDecl r.target.kind) then
        ok s!"{p}: textDocument/completion inside `{Naru.renderPath r.path}` (line {r.span.line}) in a single-document unit → {items.size} item(s) incl. {r.target.kind.describe} `{r.target.name}` (kind {kindOfDecl r.target.kind})"
      else fail s!"{p}:{r.span.line}:{r.span.col + 1}: completion lacks {r.target.kind.describe} `{r.target.name}` (kind {kindOfDecl r.target.kind}); got {(labelsOf items).take 10}"
    -- リネーム(C32)、単独の文書: 参照の先頭で `prepareRename` が名前の範囲と placeholder、`rename` がこの文書の全出現を書き換える
    let ch := utf16Of text r.span.line r.span.col
    let at_ := s!"{p}:{r.span.line}:{r.span.col}"
    match ← prepareRenameAt env uri (r.span.line - 1) ch with
    | .error e => fail s!"{at_}: {e}"
    | .ok none => fail s!"{at_}: prepareRename → null on the reference `{Naru.renderPath r.path}`"
    | .ok (some ((l, sc, ec), placeholder)) =>
      if r.path.length == 1 && placeholder == r.target.name && l == r.span.line - 1 && sc == ch && ec == ch + r.target.name.length then
        ok s!"{at_}: textDocument/prepareRename on `{Naru.renderPath r.path}` in a single-document unit → range {l + 1}:{sc + 1}-{ec + 1}, placeholder `{placeholder}`"
      else fail s!"{at_}: prepareRename → range {l + 1}:{sc + 1}-{ec + 1} placeholder `{placeholder}`, expected the simple name `{r.target.name}` at {r.span.line}:{ch + 1}"
    match ← renameAt env uri (r.span.line - 1) ch (r.target.name ++ "Renamed") with
    | .error e => fail s!"{at_}: {e}"
    | .ok .null => fail s!"{at_}: rename → null on the reference `{Naru.renderPath r.path}`"
    | .ok (.refused code msg) => fail s!"{at_}: rename refused ({code}: {msg})"
    | .ok (.edits changes) =>
      let _ ← checkRenameEdits env [(abs, text)] (env.root / ".lake" / "naru" / "test" / "lsp" / "rename-single") s!"{p} (single-document unit)"
        r.target.name (r.target.name ++ "Renamed") changes
        [(uri, r.span.line - 1, ch), (uri, r.target.span.line - 1, utf16Of text r.target.span.line r.target.span.col)]
    didClose env uri
    let some got ← barrier env | return
    let _ ← agrees s!"{p}: didClose" got #[] [uri]
  if !singleDone then fail "tests/accept/: no accept example with a resolved reference (needed for the single-document definition check)"
  -- 3c. 複数ファイルのコンパイル単位(`tests/units/`。C18): 各検体の `naru.toml` のルート `src/` 配下なので、どのファイルを開いても
  -- 単位全体が検査される。反例は行末の `// E017` の印の行に CLI と同じ行・列・幅の E017、`fix/` の didChange で関係する URI すべてが空、
  -- 戻すと戻る。受理例は 0 件。
  let rejectUnits ← listUnits "reject"
  let acceptUnits ← listUnits "accept"
  let mut nUnits := 0
  for u in rejectUnits ++ acceptUnits do
    let isReject := rejectUnits.any (·.name == u.name)
    let label := s!"{unitsDir}/{if isReject then "reject" else "accept"}/{u.name}"
    if u.files.isEmpty then
      fail s!"{label}: no .naru under src/"
      continue
    let mut sources : List (String × String) := []
    for f in u.files do
      let abs := (env.root / f).toString
      sources := sources ++ [(abs, ← IO.FS.readFile abs)]
    let uris := sources.map fun (f, _) => System.Uri.pathToUri f
    let expected := expectedOf sources
    let mut good := true
    -- 期待(CLI = `compileSources`)と印の照合: 反例は印の (ファイル, 行, E017) と一致、受理例は 0 件
    let mut marks : List (String × Nat × String) := []
    for (f, text) in sources do
      for (l, c) in markedDiagnostics text do marks := marks ++ [(System.Uri.pathToUri f, l - 1, c)]
    let expectedLines := sortLines (expected.toList.flatMap fun (uri, ds) => ds.toList.map fun (c, l, _) => (uri, l, c)).eraseDups
    if isReject then
      if marks.isEmpty then
        fail s!"{label}: a reject unit needs `// E0dd` marks"
        good := false
      else if expectedLines != sortLines marks.eraseDups then
        fail s!"{label}: naru compile reports {expectedLines.map fun (u, l, c) => s!"{c}@{relOfUri env u}:{l + 1}"}, the marks expect {(sortLines marks).map fun (u, l, c) => s!"{c}@{relOfUri env u}:{l + 1}"}"
        good := false
      else if !(marks.all fun (_, _, c) => c == "E017") then
        fail s!"{label}: the marks must all be E017"
        good := false
    else if !expected.isEmpty then
      fail s!"{label}: naru compile reports diagnostics for an accept unit: {expectedLines}"
      good := false
    -- 全ファイルを didOpen(単位全体の検査が毎回走る)。最後の状態が期待と一致し、各診断がトークン 1 つ分の幅を持つ
    let mut all : Array Pub := #[]
    for (f, text) in sources do
      didOpen env (System.Uri.pathToUri f) text
      let some got ← barrier env | return
      all := all ++ got
    let got := latest all
    if !(← agrees s!"{label}: didOpen all {sources.length} files" got expected uris) then good := false
    let mut zeroWidth : List String := []
    for p in got do
      for i in [0:p.diags.size] do
        let (c, l, sc) := p.diags[i]!
        if (p.ends[i]?).getD sc ≤ sc then zeroWidth := zeroWidth ++ [s!"{c}@{relOfUri env p.uri}:{l + 1}:{sc + 1}"]
    if !zeroWidth.isEmpty then
      fail s!"{label}: diagnostics with an empty range (the column must point at a token): {zeroWidth}"
      good := false
    if isReject && good then
      let shown := expectedLines.map fun (u, l, c) => s!"{c}@{relOfUri env u}:{l + 1}"
      ok s!"{label}: didOpen → E017 at the marked lines with naru compile's columns (UTF-16) and token-wide ranges: {shown}"
    if !isReject && good then
      ok s!"{label}: didOpen all {sources.length} files → 0 diagnostics (valid dependencies across modules)"
    -- fix/: 循環・重複を解消する didChange で、関係する URI すべての診断が消える。戻すと戻る
    let fixes := u.fixes.map fun (f, t) => ((env.root / f).toString, t)
    if !fixes.isEmpty then
      let fixed := sources.map fun (f, t) => match fixes.lookup f with
        | some t' => (f, t')
        | none => (f, t)
      let expectedFixed := expectedOf fixed
      if !expectedFixed.isEmpty then
        fail s!"{label}: with fix/ applied, naru compile should report 0 diagnostics, got {expectedFixed.toList.map fun (u, ds) => s!"{relOfUri env u} [{showDiags ds}]"}"
        good := false
      let involved := expected.toList.map (·.1)
      let mut ver := 2
      let mut allFix : Array Pub := #[]
      for (f, t') in fixes do
        didChange env (System.Uri.pathToUri f) ver t'
        ver := ver + 1
        let some got ← barrier env | return
        allFix := allFix ++ got
      if ← agrees s!"{label}: didChange (fix/)" (latest allFix) #[] involved then
        ok s!"{label}: didChange with fix/{", ".intercalate (fixes.map fun (f, _) => ((System.FilePath.mk f).fileName).getD f)} → empty diagnostics for all {involved.length} involved URI(s): {involved.map (relOfUri env)}"
      else good := false
      let mut allBack : Array Pub := #[]
      for (f, _) in fixes do
        didChange env (System.Uri.pathToUri f) ver ((sources.lookup f).getD "")
        ver := ver + 1
        let some got ← barrier env | return
        allBack := allBack ++ got
      if ← agrees s!"{label}: didChange (revert)" (latest allBack) expected (fixes.map fun (f, _) => System.Uri.pathToUri f) then
        ok s!"{label}: didChange back to the original → the E017 diagnostics are back in all {expected.size} file(s)"
      else good := false
    else if isReject then
      fail s!"{label}: a reject unit needs a fix/ file that resolves the error (for the didChange check)"
      good := false
    -- didClose(順に): 閉じた文書は空になる。同じ単位に開いた文書が残っていれば単位の再検査が走り、他のファイル(開いているものと、前に閉じて
    -- 以後は開いていないファイルとして扱うもの)にはその診断が送られる。最後の文書を閉じると単位の診断がすべて消える
    let mut nClosed := 0
    let mut remaining := uris
    for uri in uris do
      didClose env uri
      remaining := remaining.filter (· != uri)
      let some got ← barrier env | return
      let others := if remaining.isEmpty then #[] else expected.filter fun (u, _) => u != uri
      if ← agrees s!"{label}: didClose {relOfUri env uri}" got others [uri] then nClosed := nClosed + 1
    if nClosed == uris.length then ok s!"{label}: didClose on all {nClosed} files → empty for each closed file, and all empty once the last one is closed"
    else good := false
    if good then nUnits := nUnits + 1
  if nUnits == (rejectUnits ++ acceptUnits).length && !rejectUnits.isEmpty && !acceptUnits.isEmpty then
    ok s!"{unitsDir}/: {rejectUnits.length} reject unit(s) ({", ".intercalate (rejectUnits.map (·.name))}) and {acceptUnits.length} accept unit(s) ({", ".intercalate (acceptUnits.map (·.name))}) behave as expected"
  else fail s!"{unitsDir}/: expected every unit to pass, with at least one reject and one accept unit (passed {nUnits} of {(rejectUnits ++ acceptUnits).length})"
  -- 4. BMP 外の文字を含む単独の文書(ディスクに無い: 単独の単位はバッファだけを検査する)
  let emojiPath := "/tmp/naru-lsp-probe/emoji.naru"
  let emojiUri := System.Uri.pathToUri emojiPath
  let emojiText := "module Probe.Emoji\n// 絵文字 😀 の後ろの列が UTF-16 でずれないこと\nfn f(x: Nat) -> Nat { /* 😀😀 */ lspUndefinedName(x) }\n"
  let (emojiDiags, _) := Naru.compileSources [(emojiPath, emojiText)]
  match emojiDiags.toList with
  | [d] =>
    let want : Diag := (d.code, d.span.line - 1, utf16Of emojiText d.span.line d.span.col)
    didOpen env emojiUri emojiText
    let some got ← barrier env | return
    if ← agrees "emoji probe: didOpen" got #[(emojiUri, #[want])] [emojiUri] then
      let utf16 := want.2.2
      let endCh := ((got.find? (·.uri == emojiUri)).bind fun p => p.ends[0]?).getD 0
      if utf16 != d.span.col - 1 + 2 then
        fail s!"emoji probe: expected the UTF-16 column {d.span.col - 1 + 2} (2 astral chars before the token), got {utf16}"
      else if endCh != utf16 + "lspUndefinedName".length then
        fail s!"emoji probe: range end {endCh}, expected {utf16 + "lspUndefinedName".length} (one token `lspUndefinedName`)"
      else
        ok s!"emoji probe: {d.code} at line {d.span.line}, column {d.span.col} (chars) → character {utf16} (UTF-16), range width {endCh - utf16} = `lspUndefinedName`"
    didClose env emojiUri
    let some got ← barrier env | return
    let _ ← agrees "emoji probe: didClose" got #[] [emojiUri]
  | ds => fail s!"emoji probe: naru compile should report exactly 1 diagnostic, got {ds.length}"
  -- 5. ソースルート(naru.toml)の移植ソース
  let unitRoot ← match ← sourceRoots with
    | .ok (r :: _) => pure r.toString
    | .ok [] => fail "naru.toml lists no source root"; return
    | .error e => fail e; return
  let dslFiles ← Naru.listFiles unitRoot "naru"
  let mut nDsl := 0
  for p in dslFiles do
    let abs := (env.root / p).toString
    let uri := System.Uri.pathToUri abs
    didOpen env uri (← IO.FS.readFile abs)
    let some got ← barrier env | return
    if ← agrees s!"{p}: didOpen" got #[] [uri] then nDsl := nDsl + 1
  if nDsl == dslFiles.length then
    ok s!"{unitRoot}/: {nDsl} files didOpen → 0 diagnostics (none for other URIs either)"
  -- 5a. 整形(C33): 移植ソースの全ファイルが整形済み(`formatting` が空)、崩した複製への `formatting` は元と同一になり冪等、
  -- 単位全体の生成 Lean の本文(ヘッダを除く)は整形の前後で同一
  unitFormatChecks env unitRoot dslFiles formatDir
  -- 5b. 定義ジャンプ(C30): 別ファイルの fn / type への参照(参照先の宣言ごとに 1 つ、fn 8 / type 8 まで)→ 宣言ファイルの URI と宣言の名前の範囲
  let mut unitSrc : List (String × String) := []
  for p in dslFiles do
    let abs := (env.root / p).toString
    unitSrc := unitSrc ++ [(abs, ← IO.FS.readFile abs)]
  let (_, unitChecked) := Naru.compileSources unitSrc
  let cross := unitChecked.refs.filter fun r => r.file != r.target.file
  let fnRefs := distinctTargets (cross.filter (·.target.kind == .fn)) 8
  let tyRefs := distinctTargets (cross.filter (·.target.kind.isType)) 8
  if fnRefs.isEmpty || tyRefs.isEmpty then
    fail s!"{unitRoot}/: expected cross-file references to fn and type declarations (found {fnRefs.length} fn / {tyRefs.length} type among {cross.size} cross-file references)"
  let mut nDef := 0
  let mut shown : List String := []
  for r in fnRefs ++ tyRefs do
    if ← checkDefinitionOf env unitSrc r then
      nDef := nDef + 1
      shown := shown ++ [s!"{Naru.renderPath r.path}@{rel env r.file}:{r.span.line} → {r.target.kind.describe} {r.target.name}@{showLoc env (wantLoc unitSrc r.target)}"]
  if nDef == (fnRefs ++ tyRefs).length && nDef > 0 then
    ok s!"{unitRoot}/: textDocument/definition on {fnRefs.length} cross-file fn reference(s) and {tyRefs.length} cross-file type reference(s) (at the head and at its last character) → the declaring file's URI and the declaration name's range: {shown}"
  -- 5b'. ホバー(C29): 同じ参照の先頭へのホバーが、参照先の宣言の署名(fn なら仮引数と戻り型)・種類と名前・モジュール・宣言コメントの 1 行目を含む
  let mut nHover := 0
  let mut shownHover : List String := []
  for r in fnRefs ++ tyRefs do
    if let some sig ← checkHoverOf env unitSrc unitChecked r (needComment := true) then
      nHover := nHover + 1
      shownHover := shownHover ++ [s!"{Naru.renderPath r.path}@{rel env r.file}:{r.span.line} → `{sig}`"]
  if nHover == (fnRefs ++ tyRefs).length && nHover > 0 then
    ok s!"{unitRoot}/: textDocument/hover on the same {fnRefs.length} cross-file fn reference(s) and {tyRefs.length} cross-file type reference(s) → markdown with the declaration's signature (fn: each parameter and the return type), kind and name, module, and the first line of its declaration comment: {shownHover}"
  -- 5b''. 補完(C31): 同じ fn の参照の途中(先頭の 2 文字目)で、単位の全 fn 名(参照先は kind Function と署名の detail)・全予約語(kind Keyword)・
  -- 位置を含む宣言の仮引数(kind Variable、detail `名前: 型`)が候補にある
  let allFnNames := unitChecked.mods.toList.flatMap fun m => (m.decls.toList.filter (·.kind == .fn)).map (·.name)
  let mut nComp := 0
  for r in fnRefs do
    let text := (unitSrc.lookup r.file).getD ""
    let head := r.path.head?.getD ""
    let off := if head.length > 1 then 1 else 0
    let at_ := s!"{rel env r.file}:{r.span.line}:{r.span.col + off}"
    let ch := utf16Of text r.span.line r.span.col + off
    let some td := (unitChecked.mods.find? (·.file == r.target.file)).bind fun m => m.decls.find? (·.name == r.target.name)
      | fail s!"{at_}: the target declaration `{r.target.name}` is not in the unit"; continue
    let enclosing := (unitChecked.mods.find? (·.file == r.file)).bind fun m => m.decls.find? (·.name == r.declName)
    match ← completionAt env (System.Uri.pathToUri r.file) (r.span.line - 1) ch with
    | .error e => fail s!"{at_}: {e}"
    | .ok items =>
      let labels := labelsOf items
      let missingFns := allFnNames.filter fun n => !labels.contains n
      let missingKws := Naru.keywords.filter fun k => !(hasItem items k kindKeyword)
      let missingParams := (enclosing.map fun d => d.params.toList.filter fun p => !(hasItem items p.name kindVariable (· == Naru.Param.render p))).getD []
      if !missingFns.isEmpty then fail s!"{at_}: completion inside `{head}` lacks fn name(s) {missingFns.take 5} (of {allFnNames.length})"
      else if !missingKws.isEmpty then fail s!"{at_}: completion inside `{head}` lacks keyword(s) {missingKws}"
      else if !(hasItem items r.target.name kindFunction (· == td.signature)) then
        fail s!"{at_}: completion inside `{head}` lacks the item `{r.target.name}` with kind Function and detail `{td.signature}`"
      else if !missingParams.isEmpty then
        fail s!"{at_}: completion inside `{head}` lacks parameter(s) {missingParams.map (·.name)} of the enclosing {r.declKind.describe} `{r.declName}`"
      else nComp := nComp + 1
  if nComp == fnRefs.length && nComp > 0 then
    ok s!"{unitRoot}/: textDocument/completion inside the same {fnRefs.length} cross-file fn reference(s) → all {allFnNames.length} fn names of the unit (the target with kind Function and its signature as detail), all {Naru.keywords.length} keywords (kind Keyword) and the parameters of the enclosing declaration (kind Variable, `name: type`)"
  -- 5c. 宣言の無い位置では null、宣言名の上ではその宣言自身(定義ジャンプ)/ その宣言の署名(ホバー)
  let probeRel := unitRoot ++ "/Consensus/Objects/Time.naru"
  let probePath := (env.root / probeRel).toString
  let probeText := (unitSrc.lookup probePath).getD ""
  let probeLines := probeText.splitOn "\n"
  let commentLine := probeLines.findIdx? fun l => l.trimAscii.toString.startsWith "//"
  let fnLine := probeLines.findIdx? fun l => l.startsWith "fn "
  let emptyLine := probeLines.findIdx? fun l => l.isEmpty
  let indentLine := probeLines.findIdx? fun l => l.startsWith "  "
  for (what, pos) in [("a comment line", commentLine.map (·, 2)), ("the keyword `fn`", fnLine.map (·, 0))] do
    match pos with
    | none => fail s!"{probeRel}: no {what} to probe"
    | some (l, ch) =>
      match ← definitionAt env (System.Uri.pathToUri probePath) l ch with
      | .ok none => ok s!"{probeRel}:{l + 1}:{ch + 1} ({what}): textDocument/definition → null (no declaration there)"
      | .ok (some got) => fail s!"{probeRel}:{l + 1}:{ch + 1} ({what}): definition → {showLoc env got}, expected null"
      | .error e => fail s!"{probeRel}:{l + 1}:{ch + 1} ({what}): {e}"
  for (what, pos) in [("a comment line", commentLine.map (·, 2)), ("the keyword `fn`", fnLine.map (·, 0)), ("an empty line", emptyLine.map (·, 0)),
      ("the leading whitespace of an indented line", indentLine.map (·, 0))] do
    match pos with
    | none => fail s!"{probeRel}: no {what} to probe"
    | some (l, ch) => checkHoverNull env probePath l ch what
  -- 補完(C31): コメントの中では候補なし
  if let some l := commentLine then
    match ← completionAt env (System.Uri.pathToUri probePath) l 2 with
    | .ok items =>
      if items.isEmpty then ok s!"{probeRel}:{l + 1}:3 (a comment line): textDocument/completion → no items"
      else fail s!"{probeRel}:{l + 1}:3 (a comment line): completion offers {items.size} item(s) inside a comment: {(labelsOf items).take 5}"
    | .error e => fail s!"{probeRel}:{l + 1}:3 (a comment line): {e}"
  match (unitChecked.mods.find? (·.file == probePath)).bind fun m => (m.decls.find? (·.kind == .fn)).map fun d => (m, d) with
  | none => fail s!"{probeRel}: no fn declaration to probe"
  | some (pm, d) =>
    let self : Naru.Resolve.Sym := { name := d.name, qualified := d.name, kind := d.kind, file := probePath, span := d.span }
    let want := wantLoc unitSrc self
    match ← definitionAt env (System.Uri.pathToUri probePath) (d.span.line - 1) (utf16Of probeText d.span.line d.span.col) with
    | .ok (some got) =>
      if got == want then ok s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name `{d.name}`): textDocument/definition → the declaration itself {showLoc env want}"
      else fail s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name): definition → {showLoc env got}, expected {showLoc env want}"
    | .ok none => fail s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name `{d.name}`): definition → null, expected {showLoc env want}"
    | .error e => fail s!"{probeRel}:{d.span.line}:{d.span.col}: {e}"
    -- 固定の期待(表示関数の誤りも検出する): Time.naru の最初の fn の署名は `fn genesisStamp() -> Stamp`
    if let some sig ← checkHover env unitSrc probePath d.span.line d.span.col d.name.length pm d (needComment := true) then
      if sig == "fn genesisStamp() -> Stamp" then
        ok s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name `{d.name}`): textDocument/hover → markdown with `{sig}` (the fixed expectation) and its declaration comment"
      else fail s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name `{d.name}`): hover signature `{sig}`, expected exactly `fn genesisStamp() -> Stamp`"
  match (unitChecked.mods.find? (·.file == probePath)).bind fun m => (m.decls.find? (·.kind == .typeAlias)).map fun d => (m, d) with
  | none => fail s!"{probeRel}: no type declaration to probe"
  | some (pm, d) =>
    if let some sig ← checkHover env unitSrc probePath d.span.line d.span.col d.name.length pm d (needComment := true) then
      if sig == "type Time = Int" then
        ok s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name `{d.name}`): textDocument/hover → markdown with `{sig}` (the fixed expectation) and its declaration comment"
      else fail s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name `{d.name}`): hover signature `{sig}`, expected exactly `type Time = Int`"
  -- 5c'. 宣言の中の欄名 / variant 名(record の最初の欄、enum の最初の variant): ホバーは `Record.欄: 型` / `Enum.Variant(型)`、定義ジャンプは自身
  let declaredProbes : List (String × Option (Naru.Module × Naru.Decl × String × Naru.Span × String)) :=
    [("field", (unitChecked.mods.toList.findSome? fun m => (m.decls.find? fun d => d.kind == .record && !d.fields.isEmpty).map fun d =>
        let f := d.fields[0]!;
        (m, d, f.name, f.span, s!"{d.name}.{f.name}: {f.ty.render}"))),
     ("variant", (unitChecked.mods.toList.findSome? fun m => (m.decls.find? fun d => d.kind == .enum && !d.variants.isEmpty).map fun d =>
        let v := d.variants[0]!;
        (m, d, v.name, v.span, s!"{d.name}.{v.render}")))]
  for (what, probe) in declaredProbes do
    match probe with
    | none => fail s!"{unitRoot}/: no {what} declaration to probe"
    | some (dm, dd, name, sp, wantSig) =>
      let text := (unitSrc.lookup dm.file).getD ""
      let at_ := s!"{rel env dm.file}:{sp.line}:{sp.col}"
      if tokenAt text sp.line sp.col != name then
        fail s!"{at_}: the {what}'s position should be its name `{name}`, found `{tokenAt text sp.line sp.col}`"
        continue
      let ch := utf16Of text sp.line sp.col
      let uri := System.Uri.pathToUri dm.file
      match ← hoverAt env uri (sp.line - 1) ch with
      | .error e => fail s!"{at_}: {e}"
      | .ok none => fail s!"{at_}: hover on the declared {what} `{name}` → null"
      | .ok (some (value, (l, sc, ec))) =>
        if hoverSignature value != wantSig then
          fail s!"{at_}: hover signature `{hoverSignature value}`, expected `{wantSig}`"
        else if !(hoverHas value s!"{what} `{name}` of {dd.kind.describe} `{dd.name}`") then
          fail s!"{at_}: hover lacks `{what} `{name}` of {dd.kind.describe} `{dd.name}``; got: {value.take 300}"
        else if l != sp.line - 1 || sc != ch || ec != ch + name.length then
          fail s!"{at_}: hover range {l + 1}:{sc + 1}-{ec + 1}, expected the {what} name `{name}`"
        else ok s!"{at_}: textDocument/hover on the declared {what} `{name}` of {dd.kind.describe} `{dd.name}` → markdown with `{wantSig}`"
      let selfSym : Naru.Resolve.Sym := { name, qualified := name, kind := dd.kind, file := dm.file, span := sp }
      let want := wantLoc unitSrc selfSym
      match ← definitionAt env uri (sp.line - 1) ch with
      | .ok (some got) =>
        if got == want then ok s!"{at_}: textDocument/definition on the declared {what} `{name}` → itself {showLoc env want}"
        else fail s!"{at_}: definition on the declared {what} `{name}` → {showLoc env got}, expected {showLoc env want}"
      | .ok none => fail s!"{at_}: definition on the declared {what} `{name}` → null, expected {showLoc env want}"
      | .error e => fail s!"{at_}: {e}"
  -- 5c''. 補完(C31)、enum の経路: `Enum.Variant` と空白なしで書かれた参照の `.` の直後の補完は、その enum の全 variant
  -- (kind EnumMember、detail `Enum.Variant(型)`)で、それ以外の項目は無い(受け手は値ではないので `.` の前の経路から作る)
  let contiguous (r : Naru.Resolve.Ref) : Bool :=
    let line := (((unitSrc.lookup r.file).getD "").splitOn "\n").getD (r.span.line - 1) ""
    let written := (Naru.renderPath r.path).toList
    ((line.toList.drop (r.span.col - 1)).take written.length) == written
  let enumRef := unitChecked.refs.find? fun r => r.target.kind == .enum && r.path.length == 2 && contiguous r
  match enumRef with
  | none => fail s!"{unitRoot}/: no `Enum.Variant` reference (written without spaces) to probe"
  | some r =>
    let head := r.path.head?.getD ""
    let text := (unitSrc.lookup r.file).getD ""
    let ch := utf16Of text r.span.line r.span.col + head.length + 1
    let at_ := s!"{rel env r.file}:{r.span.line}:{r.span.col + head.length + 1}"
    match (unitChecked.mods.find? (·.file == r.target.file)).bind fun m => m.decls.find? (·.name == r.target.name) with
    | none => fail s!"{at_}: the enum `{r.target.name}` is not in the unit"
    | some ed =>
      match ← completionAt env (System.Uri.pathToUri r.file) (r.span.line - 1) ch with
      | .error e => fail s!"{at_}: {e}"
      | .ok items =>
        let missing := ed.variants.toList.filter fun v => !(hasItem items v.name kindEnumMember (· == s!"{ed.name}.{v.render}"))
        let extra := items.filter fun (_, k, _) => k != kindEnumMember
        if !missing.isEmpty then fail s!"{at_}: completion after `{head}.` lacks variant(s) {missing.map (·.name)} of enum `{ed.name}` (kind EnumMember, detail `{ed.name}.<Variant>(…)`)"
        else if !extra.isEmpty then fail s!"{at_}: completion after `{head}.` offers non-variant item(s) {(labelsOf extra).take 5}"
        else ok s!"{at_}: textDocument/completion after `{head}.` → the {ed.variants.size} variant(s) of enum `{ed.name}` (kind EnumMember, detail `{ed.name}.<Variant>(…)`), nothing else"
  -- 5d. 欄名と stdlib のメソッド名(型検査の索引 `Checked.members`): 欄名へのホバーは `Record.欄: 型` と record の宣言コメント、定義ジャンプは
  -- record の欄の名前のトークン。Set のメソッド名へのホバーは受け手の型で実体化した署名
  match unitChecked.members.find? fun m => m.kind == .field && !m.init with
  | none => fail s!"{unitRoot}/: no resolved field reference to probe"
  | some fm =>
    let text := (unitSrc.lookup fm.file).getD ""
    let at_ := s!"{rel env fm.file}:{fm.span.line}:{fm.span.col}"
    let ch := utf16Of text fm.span.line fm.span.col
    match (unitChecked.mods.toList.findSome? fun m => (m.decls.find? fun d => Naru.renderPath (m.name ++ [d.name]) == fm.owner).map fun d => (m, d)) with
    | none => fail s!"{at_}: the record `{fm.owner}` of field `{fm.name}` is not in the unit"
    | some (rm, rd) =>
      let wantSig := s!"{fm.ownerName}.{fm.name}: {fm.ret.render}"
      let summary := (Naru.declComment (((unitSrc.lookup rm.file).getD "").splitOn "\n").toArray rd).head?.getD ""
      match ← hoverAt env (System.Uri.pathToUri fm.file) (fm.span.line - 1) ch with
      | .error e => fail s!"{at_}: {e}"
      | .ok none => fail s!"{at_}: hover on field `{fm.name}` → null"
      | .ok (some (value, (l, sc, ec))) =>
        let want := [wantSig, s!"field `{fm.name}` of {rd.kind.describe} `{rd.name}`", s!"module `{Naru.renderPath rm.name}`"] ++ (if summary.isEmpty then [] else [summary])
        let missing := want.filter fun n => !(hoverHas value n)
        if !missing.isEmpty then fail s!"{at_}: hover on field `{fm.name}` lacks {missing}; got: {value.take 300}"
        else if l != fm.span.line - 1 || sc != ch || ec != ch + fm.name.length then
          fail s!"{at_}: hover range {l + 1}:{sc + 1}-{ec + 1}, expected the field name `{fm.name}`"
        else ok s!"{at_}: textDocument/hover on field `{fm.name}` → markdown with `{wantSig}`, `{rd.kind.describe} {rd.name}` of module {Naru.renderPath rm.name} and the record's declaration comment"
      match rd.fields.find? (·.name == fm.name) with
      | none => fail s!"{at_}: record `{rd.name}` has no field `{fm.name}`"
      | some f =>
        let fieldSym : Naru.Resolve.Sym := { name := f.name, qualified := fm.owner ++ "." ++ f.name, kind := rd.kind, file := rm.file, span := f.span }
        let want := wantLoc unitSrc fieldSym
        match ← definitionAt env (System.Uri.pathToUri fm.file) (fm.span.line - 1) ch with
        | .ok (some got) =>
          if got == want then ok s!"{at_}: textDocument/definition on field `{fm.name}` → the field in {rd.kind.describe} `{rd.name}` at {showLoc env want}"
          else fail s!"{at_}: definition on field `{fm.name}` → {showLoc env got}, expected {showLoc env want}"
        | .ok none => fail s!"{at_}: definition on field `{fm.name}` → null, expected {showLoc env want}"
        | .error e => fail s!"{at_}: {e}"
      -- 補完(C31): 欄名の位置(`.` の直後)の補完は record の全欄(kind Field、detail `Record.欄: 型`)を含み、予約語を含まない
      match ← completionAt env (System.Uri.pathToUri fm.file) (fm.span.line - 1) ch with
      | .error e => fail s!"{at_}: {e}"
      | .ok items =>
        let missing := rd.fields.toList.filter fun f => !(hasItem items f.name kindField (· == s!"{rd.name}.{f.name}: {f.ty.render}"))
        if !missing.isEmpty then
          fail s!"{at_}: completion after `.` lacks field(s) {missing.map (·.name)} of {rd.kind.describe} `{rd.name}` (kind Field, detail `{rd.name}.<field>: <type>`)"
        else if items.any (·.2.1 == kindKeyword) then fail s!"{at_}: completion after `.` offers keywords"
        else ok s!"{at_}: textDocument/completion after `.` → the {rd.fields.size} field(s) of {rd.kind.describe} `{rd.name}` (kind Field, detail `{rd.name}.<field>: <type>`), no keywords ({items.size} item(s))"
  match unitChecked.members.find? fun m => m.kind == .method && (match m.recv with | .set _ => true | _ => false) with
  | none => fail s!"{unitRoot}/: no resolved Set method reference to probe"
  | some mm =>
    let text := (unitSrc.lookup mm.file).getD ""
    let at_ := s!"{rel env mm.file}:{mm.span.line}:{mm.span.col}"
    let ch := utf16Of text mm.span.line mm.span.col
    let wantHead := s!"{mm.recv.render}.{mm.name}("
    let wantRet := s!"-> {mm.ret.render}"
    match ← hoverAt env (System.Uri.pathToUri mm.file) (mm.span.line - 1) ch with
    | .error e => fail s!"{at_}: {e}"
    | .ok none => fail s!"{at_}: hover on method `{mm.name}` → null"
    | .ok (some (value, (l, sc, ec))) =>
      let want := [wantHead, wantRet, s!"method `{mm.name}` of `{mm.owner}`"]
      let missing := want.filter fun n => !(hoverHas value n)
      if !missing.isEmpty then fail s!"{at_}: hover on method `{mm.name}` lacks {missing}; got: {value.take 300}"
      else if l != mm.span.line - 1 || sc != ch || ec != ch + mm.name.length then
        fail s!"{at_}: hover range {l + 1}:{sc + 1}-{ec + 1}, expected the method name `{mm.name}`"
      else ok s!"{at_}: textDocument/hover on stdlib method `{mm.name}` → markdown with `{hoverSignature value}`"
    -- 補完(C31): Set の式の `.` の直後の補完は stdlib の Set の全メソッド(kind Method、detail `Set<T>.m(…) -> 戻り型`)を含み、
    -- 常に拒否されるメソッド(E003 の選択・E004 の順序)と予約語を含まない
    let setNames := Naru.Typecheck.setSigs.map (·.1)
    let checkSetItems (items : Array Item) : Option String :=
      let missing := setNames.filter fun n => !(hasItem items n kindMethod (·.startsWith s!"{mm.recv.render}.{n}("))
      let forbidden := (Naru.Typecheck.setChoiceMethods ++ Naru.Typecheck.setOrderMethods).filter fun n => (labelsOf items).contains n
      -- C31 の検証文が名指しする `contains`(表から消えても検出するよう、固定の名前で)
      if !(hasItem items "contains" kindMethod (· == s!"{mm.recv.render}.contains({(match mm.recv with | .set t => t | t => t).render}) -> Bool")) then
        some s!"lacks `contains` (kind Method, detail `{mm.recv.render}.contains(<element>) -> Bool`)"
      else if !missing.isEmpty then some s!"lacks stdlib method(s) {missing} (kind Method, detail `{mm.recv.render}.<m>(…) -> …`)"
      else if !forbidden.isEmpty then some s!"offers Set methods that are always rejected (E003 / E004): {forbidden}"
      else if items.any (·.2.1 == kindKeyword) then some "offers keywords"
      else none
    match ← completionAt env (System.Uri.pathToUri mm.file) (mm.span.line - 1) ch with
    | .error e => fail s!"{at_}: {e}"
    | .ok items =>
      match checkSetItems items with
      | some why => fail s!"{at_}: completion after `.` on `{mm.recv.render}` {why}"
      | none => ok s!"{at_}: textDocument/completion after `.` on `{mm.recv.render}` → all {setNames.length} stdlib Set methods incl. `contains` (kind Method, detail `{mm.recv.render}.<m>(…) -> …`), none of the E003 / E004 methods, no keywords"
    -- 壊れた文書でも: メソッド名を消して `….(…)` にすると構文エラー(E010)になるが、`.` の直後の補完は(サーバーが仮の名前で単位を探って)同じ候補を返す
    let mmLines := text.splitOn "\n"
    let mmChars := (mmLines.getD (mm.span.line - 1) "").toList
    let brokenLine := String.ofList (mmChars.take (mm.span.col - 1) ++ mmChars.drop (mm.span.col - 1 + mm.name.length))
    let brokenText := "\n".intercalate (mmLines.set (mm.span.line - 1) brokenLine)
    let mmUri := System.Uri.pathToUri mm.file
    let brokenExpected := expectedOf (unitSrc.map fun (f, t) => if f == mm.file then (f, brokenText) else (f, t))
    let brokenHere := ((brokenExpected.find? (·.1 == mmUri)).map (·.2)).getD #[]
    if brokenHere.isEmpty then fail s!"{at_}: deleting `{mm.name}` should make naru compile report a diagnostic in this file"
    didChange env mmUri 2 brokenText
    let some got ← barrier env | return
    if ← agrees s!"{rel env mm.file}: didChange (delete `{mm.name}`)" got brokenExpected [mmUri] then
      match ← completionAt env mmUri (mm.span.line - 1) ch with
      | .error e => fail s!"{at_}: {e}"
      | .ok items =>
        match checkSetItems items with
        | some why => fail s!"{at_}: with `{mm.name}` deleted, completion after `.` {why}"
        | none => ok s!"{at_}: with `{mm.name}` deleted (the document has [{showDiags brokenHere}]), textDocument/completion after `.` still → all {setNames.length} stdlib Set methods of `{mm.recv.render}` (the server probes the unit with a placeholder name)"
    didChange env mmUri 3 text
    let some got ← barrier env | return
    if ← agrees s!"{rel env mm.file}: didChange (restore `{mm.name}`)" got #[] [mmUri] then
      ok s!"{rel env mm.file}: didChange back to the original → 0 diagnostics"
  -- 5e. リネーム(C32)、宣言名: 別ファイルの fn 8 の参照の先頭で `prepareRename` が名前の範囲(経路の宣言名の区切り)と placeholder を返し、
  -- `rename` の WorkspaceEdit が単位の全ファイルのその名前(コメントを除いた `grep -w` の出現数と同数。宣言のトークンと参照を含む)を
  -- 一時名に書き換え、作業ツリーの複製に適用して `compileSources` / CLI の `naru compile` が診断 0。宣言名の上からも同じ編集
  let renameDir := env.root / ".lake" / "naru" / "test" / "lsp" / "rename"
  -- 数え方(コメントを除いた `grep -w`)が成り立つ fn: 名前が欄名・variant 名・仮引数名・局所名と重ならないもの(`gfVotes` は fn と欄の両方にある)
  let allMemberNames := unitChecked.mods.toList.flatMap fun m => m.decls.toList.flatMap fun d => d.fields.toList.map (·.name) ++ d.variants.toList.map (·.name)
  let allLocalNames := unitChecked.mods.toList.flatMap fun m => m.decls.toList.flatMap fun d =>
    d.params.toList.map (·.name) ++ (d.body.toList.flatMap Naru.Lsp.exprBinders).map (·.1)
  let distinctName (n : String) : Bool := !allMemberNames.contains n && !allLocalNames.contains n
  let renameFnRefs := distinctTargets (cross.filter fun r => r.target.kind == .fn && distinctName r.target.name) 8
  if renameFnRefs.isEmpty then
    fail s!"{unitRoot}/: no cross-file fn reference whose name is distinct from all fields, variants, parameters and local names (needed for the rename count check)"
  let mut nRename := 0
  let mut firstFnEdits : Option (Naru.Resolve.Ref × List (String × List TextEdit)) := none
  for r in renameFnRefs do
    let text := (unitSrc.lookup r.file).getD ""
    let name := r.target.name
    let newName := name ++ "Renamed"
    let at_ := s!"{rel env r.file}:{r.span.line}:{r.span.col}"
    let ch := utf16Of text r.span.line r.span.col
    let uri := System.Uri.pathToUri r.file
    -- 宣言名の区切りの期待: 単純名なら先頭、修飾名なら最後の区切り(経路は空白なしで書かれている前提: 5c'' と同じ)
    let nameStart := if r.path.length == 1 then ch else ch + (Naru.renderPath r.path.dropLast).length + 1
    let mut prepared := false
    match ← prepareRenameAt env uri (r.span.line - 1) ch with
    | .error e => fail s!"{at_}: {e}"
    | .ok none => fail s!"{at_}: prepareRename → null on the reference `{Naru.renderPath r.path}` to fn `{name}`"
    | .ok (some ((l, sc, ec), placeholder)) =>
      if placeholder == name && l == r.span.line - 1 && sc == nameStart && ec == nameStart + name.length then prepared := true
      else fail s!"{at_}: prepareRename → range {l + 1}:{sc + 1}-{ec + 1} placeholder `{placeholder}`, expected `{name}` at {r.span.line}:{nameStart + 1}-{nameStart + name.length + 1}"
    if !prepared then continue
    match ← renameAt env uri (r.span.line - 1) ch newName with
    | .error e => fail s!"{at_}: {e}"
    | .ok .null => fail s!"{at_}: rename → null on fn `{name}`"
    | .ok (.refused code msg) => fail s!"{at_}: rename `{name}` → `{newName}` refused ({code}: {msg})"
    | .ok (.edits changes) =>
      let targetText := (unitSrc.lookup r.target.file).getD ""
      let declPos := (System.Uri.pathToUri r.target.file, r.target.span.line - 1, utf16Of targetText r.target.span.line r.target.span.col)
      if ← checkRenameEdits env unitSrc renameDir s!"{at_} (`{Naru.renderPath r.path}` → fn `{name}` in {rel env r.target.file})" name newName changes
          [(uri, r.span.line - 1, nameStart), declPos] then
        nRename := nRename + 1
        if firstFnEdits.isNone then firstFnEdits := some (r, changes)
  if nRename == renameFnRefs.length && nRename > 0 then
    ok s!"{unitRoot}/: textDocument/prepareRename + rename on {renameFnRefs.length} cross-file fn reference(s) ({", ".intercalate (renameFnRefs.map (·.target.name))}) → the name's range, and a WorkspaceEdit over the unit whose edits equal the word occurrences outside comments, compile clean after applying ({renameDir})"
  -- 宣言名の上からのリネームは参照からと同じ編集
  match firstFnEdits with
  | none => pure ()
  | some (r, fromRef) =>
    let targetText := (unitSrc.lookup r.target.file).getD ""
    let at_ := s!"{rel env r.target.file}:{r.target.span.line}:{r.target.span.col}"
    match ← renameAt env (System.Uri.pathToUri r.target.file) (r.target.span.line - 1) (utf16Of targetText r.target.span.line r.target.span.col) (r.target.name ++ "Renamed") with
    | .error e => fail s!"{at_}: {e}"
    | .ok (.edits fromDecl) =>
      if sameEdits fromDecl fromRef then ok s!"{at_}: textDocument/rename on the declaration name `{r.target.name}` → the same edits as from its reference"
      else fail s!"{at_}: rename on the declaration name `{r.target.name}` → different edits than from its reference"
    | .ok .null => fail s!"{at_}: rename on the declaration name `{r.target.name}` → null"
    | .ok (.refused code msg) => fail s!"{at_}: rename on the declaration name `{r.target.name}` refused ({code}: {msg})"
    -- 不適切な新しい名前は拒否(-32803): 予約語、大文字始まり(大文字 / 小文字の区分を変える)、既存の宣言名、識別子でない
    let uri := System.Uri.pathToUri r.file
    let text := (unitSrc.lookup r.file).getD ""
    let ch := utf16Of text r.span.line r.span.col
    let other := ((renameFnRefs.find? fun r' => r'.target.name != r.target.name).map (·.target.name)).getD "slotStart"
    let mut nRefused := 0
    let bad : List (String × String) := [("match", "a keyword"), (r.target.name.capitalize, "an uppercase name"), (other, "an existing declaration"), ("1abc", "not an identifier")]
    for (newName, why) in bad do
      match ← renameAt env uri (r.span.line - 1) ch newName with
      | .ok (.refused code _) =>
        if code == -32803 then nRefused := nRefused + 1
        else fail s!"{rel env r.file}:{r.span.line}:{r.span.col}: rename `{r.target.name}` → `{newName}` ({why}) refused with code {code}, expected -32803 (RequestFailed)"
      | .ok .null => fail s!"{rel env r.file}:{r.span.line}:{r.span.col}: rename `{r.target.name}` → `{newName}` ({why}) → null, expected an error"
      | .ok (.edits _) => fail s!"{rel env r.file}:{r.span.line}:{r.span.col}: rename `{r.target.name}` → `{newName}` ({why}) → edits, expected an error"
      | .error e => fail s!"{rel env r.file}:{r.span.line}:{r.span.col}: {e}"
    if nRefused == bad.length then
      ok s!"{rel env r.file}:{r.span.line}:{r.span.col}: rename `{r.target.name}` to {bad.map (·.1)} (a keyword / an uppercase name / an existing declaration / not an identifier) → error -32803 for each"
  -- 5e'. リネーム(C32)、欄名: 単位の中で名前が他の宣言・他の record の欄・仮引数と重ならない欄(型検査の索引 `Checked.members` の最初のそのような読み)で、
  -- 読みの位置と record の宣言の欄名の位置からの `rename` が、宣言の欄名・式の中の全読み・record literal の全初期化(コメントを除いた `grep -w` と同数)を書き換える
  let allDeclNames := unitChecked.mods.toList.flatMap fun m => m.decls.toList.map (·.name)
  let allParamNames := unitChecked.mods.toList.flatMap fun m => m.decls.toList.flatMap fun d => d.params.toList.map (·.name)
  let fieldOwners (name : String) : List String := unitChecked.mods.toList.flatMap fun m => (m.decls.toList.filter fun d => d.fields.any (·.name == name)).map fun d => Naru.renderPath (m.name ++ [d.name])
  let distinctField := unitChecked.members.find? fun m => m.kind == .field && !m.init && !allDeclNames.contains m.name && !allParamNames.contains m.name && fieldOwners m.name == [m.owner]
  match distinctField with
  | none => fail s!"{unitRoot}/: no field read whose name is distinct from all declarations, parameters and other records' fields (needed for the field rename check)"
  | some fm =>
    let text := (unitSrc.lookup fm.file).getD ""
    let at_ := s!"{rel env fm.file}:{fm.span.line}:{fm.span.col}"
    let ch := utf16Of text fm.span.line fm.span.col
    let uri := System.Uri.pathToUri fm.file
    let newName := fm.name ++ "Renamed"
    match (unitChecked.mods.toList.findSome? fun m => (m.decls.find? fun d => Naru.renderPath (m.name ++ [d.name]) == fm.owner).map fun d => (m, d)) with
    | none => fail s!"{at_}: the record `{fm.owner}` of field `{fm.name}` is not in the unit"
    | some (rm, rd) =>
      match rd.fields.find? (·.name == fm.name) with
      | none => fail s!"{at_}: record `{rd.name}` has no field `{fm.name}`"
      | some f =>
        let rmText := (unitSrc.lookup rm.file).getD ""
        let declPos := (System.Uri.pathToUri rm.file, f.span.line - 1, utf16Of rmText f.span.line f.span.col)
        let inits := unitChecked.members.toList.filter fun m => m.kind == .field && m.init && m.owner == fm.owner && m.name == fm.name
        let initPos := inits.map fun m => (System.Uri.pathToUri m.file, m.span.line - 1, utf16Of ((unitSrc.lookup m.file).getD "") m.span.line m.span.col)
        match ← prepareRenameAt env uri (fm.span.line - 1) ch with
        | .error e => fail s!"{at_}: {e}"
        | .ok none => fail s!"{at_}: prepareRename → null on field `{fm.name}`"
        | .ok (some ((l, sc, ec), placeholder)) =>
          if placeholder == fm.name && l == fm.span.line - 1 && sc == ch && ec == ch + fm.name.length then
            ok s!"{at_}: textDocument/prepareRename on field `{fm.name}` of {rd.kind.describe} `{rd.name}` → its range, placeholder `{fm.name}`"
          else fail s!"{at_}: prepareRename → range {l + 1}:{sc + 1}-{ec + 1} placeholder `{placeholder}`, expected `{fm.name}` at {fm.span.line}:{ch + 1}"
        match ← renameAt env uri (fm.span.line - 1) ch newName with
        | .error e => fail s!"{at_}: {e}"
        | .ok .null => fail s!"{at_}: rename → null on field `{fm.name}`"
        | .ok (.refused code msg) => fail s!"{at_}: rename field `{fm.name}` refused ({code}: {msg})"
        | .ok (.edits fromRead) =>
          if ← checkRenameEdits env unitSrc renameDir s!"{at_} (field `{fm.name}` of {rd.kind.describe} `{rd.name}`, {inits.length} record literal initialization(s))" fm.name newName fromRead
              ([(uri, fm.span.line - 1, ch), declPos] ++ initPos) then
            if inits.isEmpty then fail s!"{at_}: field `{fm.name}` has no record literal initialization in the unit (the check wants to cover `R \{ {fm.name}: … }`)"
            match ← renameAt env (System.Uri.pathToUri rm.file) (f.span.line - 1) (utf16Of rmText f.span.line f.span.col) newName with
            | .ok (.edits fromDecl) =>
              if sameEdits fromDecl fromRead then ok s!"{rel env rm.file}:{f.span.line}:{f.span.col}: textDocument/rename on the declared field `{fm.name}` → the same edits as from its read"
              else fail s!"{rel env rm.file}:{f.span.line}:{f.span.col}: rename on the declared field `{fm.name}` → different edits than from its read"
            | .ok .null => fail s!"{rel env rm.file}:{f.span.line}:{f.span.col}: rename on the declared field `{fm.name}` → null"
            | .ok (.refused code msg) => fail s!"{rel env rm.file}:{f.span.line}:{f.span.col}: rename on the declared field `{fm.name}` refused ({code}: {msg})"
            | .error e => fail s!"{rel env rm.file}:{f.span.line}:{f.span.col}: {e}"
  -- 5e''. リネームできない位置では null: コメント行、予約語 `fn`、仮引数(局所名)、enum の宣言の中の variant 名、stdlib のメソッド名
  for (what, pos) in [("a comment line", commentLine.map (·, 2)), ("the keyword `fn`", fnLine.map (·, 0))] do
    match pos with
    | none => fail s!"{probeRel}: no {what} to probe"
    | some (l, ch) => checkRenameNull env probePath l ch what
  match (unitChecked.mods.find? (·.file == probePath)).bind fun m => m.decls.find? fun d => d.kind == .fn && !d.params.isEmpty with
  | none => fail s!"{probeRel}: no fn with a parameter to probe"
  | some d =>
    let p := d.params[0]!
    checkRenameNull env probePath (p.span.line - 1) (utf16Of probeText p.span.line p.span.col) s!"the parameter `{p.name}` of fn `{d.name}` (a local name)"
  match unitChecked.mods.toList.findSome? fun m => (m.decls.find? fun d => d.kind == .enum && !d.variants.isEmpty).map fun d => (m, d) with
  | none => fail s!"{unitRoot}/: no enum with a variant to probe"
  | some (vm, vd) =>
    let v := vd.variants[0]!
    checkRenameNull env vm.file (v.span.line - 1) (utf16Of ((unitSrc.lookup vm.file).getD "") v.span.line v.span.col) s!"the declared variant `{v.name}` of enum `{vd.name}`"
  match unitChecked.members.find? (·.kind == .method) with
  | none => fail s!"{unitRoot}/: no stdlib method reference to probe"
  | some mr =>
    checkRenameNull env mr.file (mr.span.line - 1) (utf16Of ((unitSrc.lookup mr.file).getD "") mr.span.line mr.span.col) s!"the stdlib method `{mr.name}`"
  -- 5e'''. リネームの検体 `tests/units/accept/rename_cases/`: 略記の欄 `Point { x, ..p }`(欄の改名は `xRenamed: x`、宣言の改名は値だけ)、
  -- claim bundle の略記の項目 `nonNegative,`(claim の改名は `nonNegative: nonNegativeRenamed` で項目名を保つ)と明示の項目 `second: doubled`、
  -- 局所名に捕まる改名(`twice` → `v`)の拒否、予約名 / 既存の欄名の拒否、`.` の前後に空白のある経路(`Color . Red`)、診断のある単位と古い索引での拒否
  match (← listUnits "accept").find? (·.name == "rename_cases") with
  | none => fail s!"{unitsDir}/accept/rename_cases is missing"
  | some u =>
    let mut rcSrc : List (String × String) := []
    for f in u.files do
      let abs := (env.root / f).toString
      rcSrc := rcSrc ++ [(abs, ← IO.FS.readFile abs)]
    let rcUris := rcSrc.map fun (f, _) => System.Uri.pathToUri f
    let shapes := (rcSrc.find? fun (f, _) => f.endsWith "Shapes.naru").map (·.1) |>.getD ""
    let rules := (rcSrc.find? fun (f, _) => f.endsWith "Rules.naru").map (·.1) |>.getD ""
    let shapesText := (rcSrc.lookup shapes).getD ""
    let rulesText := (rcSrc.lookup rules).getD ""
    let shapesUri := System.Uri.pathToUri shapes
    let rulesUri := System.Uri.pathToUri rules
    let (rcDiags, _) := Naru.compileSources rcSrc
    if !rcDiags.isEmpty then fail s!"rename_cases: naru compile reports {rcDiags.size} diagnostic(s) for the fixture"
    for (f, t) in rcSrc do didOpen env (System.Uri.pathToUri f) t
    let some got ← barrier env | return
    let _ ← agrees "rename_cases: didOpen" got #[] rcUris
    let at_ (needle : String) (text : String) (off : Nat := 0) (occurrence : Nat := 0) : Nat × Nat :=
      match findIn text needle occurrence with
      | some (l, c) => (l, c + off)
      | none => (0, 0)
    let ed (uri : String) (pos : Nat × Nat) (width : Nat) (newText : String) : String × TextEdit := (uri, (pos.1, pos.2, pos.2 + width, newText))
    -- 欄 `x`(宣言 → 初期化 `x: 0`、略記 `{ x, ..p }` → `xRenamed: x`、読み `p.x`。仮引数 `x` は触らない)
    let fieldDecl := at_ "x: Nat" shapesText
    match ← renameAt env shapesUri fieldDecl.1 fieldDecl.2 "xRenamed" with
    | .ok (.edits changes) =>
      let _ ← checkExactEdits env rcSrc "rename_cases: field `x` of `Point` from its declaration" changes
        [ed shapesUri fieldDecl 1 "xRenamed", ed shapesUri (at_ "x: 0" shapesText) 1 "xRenamed",
         ed shapesUri (at_ "x, ..p" shapesText) 1 "xRenamed: x", ed shapesUri (at_ "p.x" shapesText 2) 1 "xRenamed"]
    | .ok .null => fail "rename_cases: rename on field `x` → null"
    | .ok (.refused code msg) => fail s!"rename_cases: rename on field `x` refused ({code}: {msg})"
    | .error e => fail s!"rename_cases: {e}"
    checkRenameRefused env shapesUri fieldDecl.1 fieldDecl.2 "mk" "reserved" "rename_cases: field `x` → `mk`"
    checkRenameRefused env shapesUri fieldDecl.1 fieldDecl.2 "y" "already has a field" "rename_cases: field `x` → `y`"
    -- claim `nonNegative`(宣言と略記の項目: 項目名を保って値だけ変える)
    let claimPos := at_ "claim nonNegative" rulesText 6
    match ← renameAt env rulesUri claimPos.1 claimPos.2 "nonNegativeRenamed" with
    | .ok (.edits changes) =>
      if ← checkExactEdits env rcSrc "rename_cases: claim `nonNegative` (shorthand bundle item)" changes
          [ed rulesUri claimPos "nonNegative".length "nonNegativeRenamed", ed rulesUri (at_ "  nonNegative," rulesText 2) "nonNegative".length "nonNegative: nonNegativeRenamed"] then
        let renamedRules := applyEdits rulesText ((changes.lookup rulesUri).getD [])
        match Naru.parseSource rules renamedRules with
        | .ok m =>
          let items := ((m.decls.find? (·.kind == .claimBundle)).map fun d => d.items.toList.map (·.1)).getD []
          if items == ["nonNegative", "second"] then ok s!"rename_cases: after renaming the claim, the bundle's item names are unchanged {items} (claim surface preserved)"
          else fail s!"rename_cases: after renaming the claim, the bundle's item names are {items}, expected [nonNegative, second]"
        | .error d => fail s!"rename_cases: the renamed Rules.naru does not parse: {d.msg}"
    | .ok .null => fail "rename_cases: rename on claim `nonNegative` → null"
    | .ok (.refused code msg) => fail s!"rename_cases: rename on claim `nonNegative` refused ({code}: {msg})"
    | .error e => fail s!"rename_cases: {e}"
    -- claim `doubled`(明示の項目 `second: doubled`: 値だけ変わる)
    let doubledPos := at_ "claim doubled" rulesText 6
    match ← renameAt env rulesUri doubledPos.1 doubledPos.2 "doubledRenamed" with
    | .ok (.edits changes) =>
      let _ ← checkExactEdits env rcSrc "rename_cases: claim `doubled` (explicit bundle item `second: doubled`)" changes
        [ed rulesUri doubledPos "doubled".length "doubledRenamed", ed rulesUri (at_ "second: doubled" rulesText 8) "doubled".length "doubledRenamed"]
    | .ok .null => fail "rename_cases: rename on claim `doubled` → null"
    | .ok (.refused code msg) => fail s!"rename_cases: rename on claim `doubled` refused ({code}: {msg})"
    | .error e => fail s!"rename_cases: {e}"
    -- fn `twice`: 局所名 `v` に捕まる改名は拒否、`twiceRenamed` は宣言 + 呼出し 2 つ(runtime の `scale`、spec の `doubled`)
    let twicePos := at_ "fn twice" shapesText 3
    checkRenameRefused env shapesUri twicePos.1 twicePos.2 "v" "captured" "rename_cases: fn `twice` → `v` (a local name of `scale` which calls it)"
    let twiceExpected := [ed shapesUri twicePos 5 "twiceRenamed", ed shapesUri (at_ "{ twice(v) }" shapesText 2) 5 "twiceRenamed", ed rulesUri (at_ "{ twice(n)" rulesText 2) 5 "twiceRenamed"]
    match ← renameAt env shapesUri twicePos.1 twicePos.2 "twiceRenamed" with
    | .ok (.edits changes) => let _ ← checkExactEdits env rcSrc "rename_cases: fn `twice`" changes twiceExpected
    | .ok .null => fail "rename_cases: rename on fn `twice` → null"
    | .ok (.refused code msg) => fail s!"rename_cases: rename on fn `twice` refused ({code}: {msg})"
    | .error e => fail s!"rename_cases: {e}"
    -- `Color . Red`(空白入りの経路): `Red` の上は null(variant)、`Color` の上は enum の名前の範囲、改名は宣言・仮引数の型・経路の 3 箇所
    let spaced := at_ "Color . Red" shapesText
    checkRenameNull env shapes spaced.1 (spaced.2 + 8) "the variant `Red` of the spaced path `Color . Red`"
    match ← prepareRenameAt env shapesUri spaced.1 spaced.2 with
    | .ok (some ((l, sc, ec), placeholder)) =>
      if placeholder == "Color" && l == spaced.1 && sc == spaced.2 && ec == spaced.2 + 5 then
        ok s!"rename_cases: textDocument/prepareRename on `Color` of the spaced path `Color . Red` → the `Color` token, placeholder `Color`"
      else fail s!"rename_cases: prepareRename on `Color . Red` → range {l + 1}:{sc + 1}-{ec + 1} placeholder `{placeholder}`, expected `Color` at {spaced.1 + 1}:{spaced.2 + 1}"
    | .ok none => fail "rename_cases: prepareRename on `Color` of `Color . Red` → null"
    | .error e => fail s!"rename_cases: {e}"
    match ← renameAt env shapesUri spaced.1 spaced.2 "ColorRenamed" with
    | .ok (.edits changes) =>
      let _ ← checkExactEdits env rcSrc "rename_cases: enum `Color` from the spaced path" changes
        [ed shapesUri (at_ "enum Color" shapesText 5) 5 "ColorRenamed", ed shapesUri (at_ "c: Color" shapesText 3) 5 "ColorRenamed", ed shapesUri spaced 5 "ColorRenamed"]
    | .ok .null => fail "rename_cases: rename on enum `Color` → null"
    | .ok (.refused code msg) => fail s!"rename_cases: rename on enum `Color` refused ({code}: {msg})"
    | .error e => fail s!"rename_cases: {e}"
    -- 診断のある単位(E011)では拒否、戻すと通る。構文エラーで索引が古いままの文書でも拒否、戻すと通る
    let brokenE011 := shapesText ++ "\nfn broken() -> Nat { lspUndefinedName(1) }\n"
    didChange env shapesUri 2 brokenE011
    let some got ← barrier env | return
    let brokenExpected := expectedOf (rcSrc.map fun (f, t) => if f == shapes then (f, brokenE011) else (f, t))
    if ← agrees "rename_cases: didChange (E011)" got brokenExpected [shapesUri] then
      checkRenameRefused env shapesUri twicePos.1 twicePos.2 "twiceRenamed" "diagnostics" "rename_cases: with E011 in the unit, rename `twice`"
    didChange env shapesUri 3 shapesText
    let some got ← barrier env | return
    if ← agrees "rename_cases: didChange (restore)" got #[] [shapesUri] then
      match ← renameAt env shapesUri twicePos.1 twicePos.2 "twiceRenamed" with
      | .ok (.edits changes) => let _ ← checkExactEdits env rcSrc "rename_cases: fn `twice` after restoring the text" changes twiceExpected
      | .ok .null => fail "rename_cases: rename on fn `twice` after restoring → null"
      | .ok (.refused code msg) => fail s!"rename_cases: rename on fn `twice` after restoring refused ({code}: {msg})"
      | .error e => fail s!"rename_cases: {e}"
    let brokenSyntax := shapesText ++ "\nfn broken( {\n"
    didChange env shapesUri 4 brokenSyntax
    let some got ← barrier env | return
    let syntaxExpected := expectedOf (rcSrc.map fun (f, t) => if f == shapes then (f, brokenSyntax) else (f, t))
    if ← agrees "rename_cases: didChange (syntax error)" got syntaxExpected [shapesUri] then
      checkRenameRefused env shapesUri twicePos.1 twicePos.2 "twiceRenamed" "changed since" "rename_cases: with a syntax error (stale index), rename `twice`"
    didChange env shapesUri 5 shapesText
    let some got ← barrier env | return
    if ← agrees "rename_cases: didChange (restore again)" got #[] [shapesUri] then
      match ← renameAt env shapesUri twicePos.1 twicePos.2 "twiceRenamed" with
      | .ok (.edits changes) => let _ ← checkExactEdits env rcSrc "rename_cases: fn `twice` after restoring the text again" changes twiceExpected
      | .ok .null => fail "rename_cases: rename on fn `twice` after restoring again → null"
      | .ok (.refused code msg) => fail s!"rename_cases: rename on fn `twice` after restoring again refused ({code}: {msg})"
      | .error e => fail s!"rename_cases: {e}"
    for uri in rcUris do
      didClose env uri
      let some got ← barrier env | return
      let _ ← agrees s!"rename_cases: didClose {relOfUri env uri}" got #[] [uri]
    -- 開いていないファイルがディスクで変わったとき(索引が古い): 検体の複製(`.lake/naru/test/lsp/stale/`)を単位として Shapes だけ開き、
    -- 閉じている Rules をディスクで書き換えると断る。開いている文書を送り直して検査し直すと通る
    let staleDir := env.root / ".lake" / "naru" / "test" / "lsp" / "stale"
    if ← staleDir.pathExists then IO.FS.removeDirAll staleDir
    IO.FS.createDirAll (staleDir / "src")
    IO.FS.writeFile (staleDir / "naru.toml") (← IO.FS.readFile (env.root / unitsDir / "accept" / u.name / "naru.toml"))
    let stalePath (f : String) : System.FilePath := staleDir / "src" / ((System.FilePath.mk f).fileName.getD f)
    for (f, t) in rcSrc do IO.FS.writeFile (stalePath f) t
    let sShapes := (stalePath shapes).toString
    let sRules := (stalePath rules).toString
    let sShapesUri := System.Uri.pathToUri sShapes
    let sRulesUri := System.Uri.pathToUri sRules
    let staleExpected := [ed sShapesUri twicePos 5 "twiceRenamed", ed sShapesUri (at_ "{ twice(v) }" shapesText 2) 5 "twiceRenamed", ed sRulesUri (at_ "{ twice(n)" rulesText 2) 5 "twiceRenamed"]
    didOpen env sShapesUri shapesText
    let some got ← barrier env | return
    if ← agrees "stale copy: didOpen Shapes.naru (Rules.naru stays closed)" got #[] [sShapesUri] then
      match ← renameAt env sShapesUri twicePos.1 twicePos.2 "twiceRenamed" with
      | .ok (.edits changes) => let _ ← checkExactEdits env [(sShapes, shapesText), (sRules, rulesText)] "stale copy: fn `twice` with Rules.naru closed (read from disk)" changes staleExpected
      | .ok .null => fail "stale copy: rename on fn `twice` → null"
      | .ok (.refused code msg) => fail s!"stale copy: rename on fn `twice` refused ({code}: {msg})"
      | .error e => fail s!"stale copy: {e}"
      let rulesChanged := rulesText ++ "// changed on disk after the last check\n"
      IO.FS.writeFile (stalePath rules) rulesChanged
      checkRenameRefused env sShapesUri twicePos.1 twicePos.2 "twiceRenamed" "changed on disk" "stale copy: with the closed Rules.naru changed on disk, rename `twice`"
      didChange env sShapesUri 2 shapesText
      let some got ← barrier env | return
      if ← agrees "stale copy: didChange (re-check reads the disk)" got #[] [sShapesUri] then
        match ← renameAt env sShapesUri twicePos.1 twicePos.2 "twiceRenamed" with
        | .ok (.edits changes) => let _ ← checkExactEdits env [(sShapes, shapesText), (sRules, rulesChanged)] "stale copy: fn `twice` after re-checking" changes staleExpected
        | .ok .null => fail "stale copy: rename on fn `twice` after re-checking → null"
        | .ok (.refused code msg) => fail s!"stale copy: rename on fn `twice` after re-checking refused ({code}: {msg})"
        | .error e => fail s!"stale copy: {e}"
      didClose env sShapesUri
      let some got ← barrier env | return
      let _ ← agrees "stale copy: didClose" got #[] [sShapesUri]
  -- 6. didChange(ソースルートの単位: 開いた文書のバッファで検査する)
  let targetRel := unitRoot ++ "/Consensus/Objects/Time.naru"
  let target := (env.root / targetRel).toString
  let targetUri := System.Uri.pathToUri target
  let orig ← IO.FS.readFile target
  let mut sources : List (String × String) := []
  for p in dslFiles do
    let abs := (env.root / p).toString
    sources := sources ++ [(abs, ← IO.FS.readFile abs)]
  let withTarget (t : String) : List (String × String) := sources.map fun (f, s) => if f == target then (f, t) else (f, s)
  -- 6a. 同じファイルに出る診断
  let probe := orig ++ (if orig.endsWith "\n" then "" else "\n") ++ "fn lspProbe(x: Nat) -> Nat { lspUndefinedName(x) }\n"
  let expected := expectedOf (withTarget probe)
  let wantHere := ((expected.find? (·.1 == targetUri)).map (·.2)).getD #[]
  if !(wantHere.any fun (code, _, _) => code == "E011") then
    fail s!"{targetRel}: the probe should make naru compile report E011 in this file (got [{showDiags wantHere}])"
  didChange env targetUri 2 probe
  let some got ← barrier env | return
  if ← agrees s!"{targetRel}: didChange (probe)" got expected [targetUri] then
    ok s!"{targetRel}: didChange with an unresolved name → [{showDiags wantHere}] in this file"
  -- 6b. 他のファイルに出る診断(slotStart の改名)
  let renamed := (orig.splitOn "fn slotStart(").foldl (init := "") fun acc part =>
    if acc.isEmpty then part else acc ++ "fn slotStartRenamed(" ++ part
  let expected := expectedOf (withTarget renamed)
  let others := expected.filter (·.1 != targetUri)
  if others.isEmpty then
    fail s!"{targetRel}: renaming slotStart should make naru compile report diagnostics in other files of {unitRoot}/"
  didChange env targetUri 3 renamed
  let some got ← barrier env | return
  if ← agrees s!"{targetRel}: didChange (rename slotStart)" got expected [targetUri] then
    let names := others.toList.map fun (u, ds) => s!"{relOfUri env u} [{showDiags ds}]"
    ok s!"{targetRel}: didChange renaming slotStart → diagnostics published to {others.size} other file(s): {", ".intercalate names}"
  -- 6c. 壊れたまま、診断の出ている他の文書を閉じる: 閉じた文書は空になり、同じ単位の再検査でも非空が送り直されない
  match others.toList with
  | (closedUri, closedWant) :: _ =>
    let closedRel := relOfUri env closedUri
    didClose env closedUri
    let some got ← barrier env | return
    let stillOpen := others.filter (·.1 != closedUri)
    if ← agrees s!"{closedRel}: didClose while broken" got stillOpen [closedUri] then
      ok s!"{closedRel}: didClose while its diagnostics are non-empty → empty for it (the unit's re-check keeps the other {stillOpen.size} file(s))"
    -- 開き直すと(ディスクの内容のまま壊れているので)診断が戻る
    didOpen env closedUri (← IO.FS.readFile (((System.Uri.fileUriToPath? closedUri).map (·.toString)).getD closedUri))
    let some got ← barrier env | return
    if ← agrees s!"{closedRel}: didOpen again" got others [closedUri] then
      ok s!"{closedRel}: didOpen again → [{showDiags closedWant}] is back"
  | [] => pure ()
  -- 6d. 元に戻すと消える
  didChange env targetUri 4 orig
  let some got ← barrier env | return
  if ← agrees s!"{targetRel}: didChange (revert)" got #[] (targetUri :: others.toList.map (·.1)) then
    ok s!"{targetRel}: didChange back to the original → empty diagnostics for this file and the {others.size} other(s)"
  -- 6e. didSave
  didSave env targetUri
  let some got ← barrier env | return
  if ← agrees s!"{targetRel}: didSave" got #[] [targetUri] then
    ok s!"{targetRel}: didSave → still 0 diagnostics"
  -- 7. didClose
  let mut nClosed := 0
  for p in dslFiles do
    let uri := System.Uri.pathToUri (env.root / p).toString
    didClose env uri
    let some got ← barrier env | return
    if ← agrees s!"{p}: didClose" got #[] [uri] then nClosed := nClosed + 1
  if nClosed == dslFiles.length then
    ok s!"{unitRoot}/: didClose on all {nClosed} files → empty diagnostics for each"
  -- 8. shutdown / exit
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  request c id "shutdown" Json.null
  let some (resp, _) ← collectUntil c id
    | fail "no response to shutdown"; return
  if (getField resp "result") == some Json.null then
    ok "shutdown → result null"
  else
    fail s!"shutdown: expected result null, got {resp.compress}"
  notify c "exit" Json.null
  let code ← c.child.wait
  env.exited.set true
  if code == 0 then ok "exit → naru lsp exited with 0"
  else fail s!"exit: naru lsp exited with {code}"

def run : IO UInt32 := runGroup "naru_test lsp" do
  let root ← IO.currentDir
  let build ← runProc "lake" #["build", "naru"]
  if build.exitCode != 0 then
    fail s!"lake build naru exit {build.exitCode}: {tail build.stderr}"
    return
  ok "lake build naru exit 0"
  let bin := root / ".lake" / "build" / "bin" / "naru"
  if !(← bin.pathExists) then
    fail s!"{bin} not found"
    return
  -- 言語サーバーの検査はファイルを生成しない(C18): 生成先と `tests/units/` の全ファイルをセッションの前後で照合する
  let generated ← match ← Naru.readConfig Naru.configFileName with
    | .ok cfg => pure cfg.generatedPath
    | .error e => fail s!"{Naru.configFileName}: {e}"; return
  let before ← snapshotTree [generated, unitsDir]
  let child ← IO.Process.spawn
    { cmd := bin.toString, args := #["lsp"], cwd := some root, stdin := .piped, stdout := .piped, stderr := .inherit }
  let client : Client := { child, stdin := IO.FS.Stream.ofHandle child.stdin, stdout := IO.FS.Stream.ofHandle child.stdout }
  let nextId ← IO.mkRef 2
  let exited ← IO.mkRef false
  let env : Env := { client, root, nextId, exited }
  checks env
  -- 途中で止まった(サーバーが応答しなかった・検査が途中で返った)場合は子プロセスを止める
  if !(← exited.get) then
    child.kill
    let _ ← child.wait
  let after ← snapshotTree [generated, unitsDir]
  if before == after && !before.isEmpty then
    ok s!"the LSP session generated nothing: {before.length} files under {generated}/ and {unitsDir}/ have the same paths and sha256 before and after"
  else
    let onlyAfter := after.filter fun (p, _) => (before.lookup p).isNone
    let changed := after.filter fun (p, h) => (before.lookup p).isSome && before.lookup p != some h
    let gone := before.filter fun (p, _) => (after.lookup p).isNone
    fail s!"generated files changed during the LSP session: new {onlyAfter.map (·.1) |>.take 5}, changed {changed.map (·.1) |>.take 5}, removed {gone.map (·.1) |>.take 5}"

end NaruTest.Lsp
