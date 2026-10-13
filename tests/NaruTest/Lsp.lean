import Naru
import NaruTest.Common

/-!
# `naru_test lsp` — 言語サーバー `naru lsp` の検査(IDEAL.md C18 / C30)

リポジトリのルートで実行する。`lake build naru` の後、子プロセスの `.lake/build/bin/naru lsp` と標準入出力で LSP を話し、
次を確かめる(`ok:` / `FAIL:`)。期待値はコンパイラ(`Naru.compileSources`、CLI の `compile` と同じ検査)から取る。

1. `initialize` の応答に全文同期(`textDocumentSync.change = 1`、`openClose`)と `definitionProvider = true`(C30)がある。`initialized` を送る。
2. 未対応のリクエスト(`textDocument/signatureHelp`: C29〜C33 に挙げた以外のリクエスト)には `MethodNotFound`(-32601)が返る。この応答は以後、
   通知の処理の終わりを待つ barrier にも使う(サーバーはメッセージを順に処理するので、応答が返れば直前の通知の診断は送り終わっている)。
   定義ジャンプ(C30、`textDocument/definition`): 受理例 1 つ(単独の単位)を開き、同じファイルの参照の位置から、その宣言の名前の範囲が返る(3d)。
   移植ソース(5b): 別ファイルの fn / type への参照(先頭と、先頭の区切りの最後の文字)から、宣言ファイルの URI と宣言の名前のトークンの範囲
   (`compileSources` の参照の索引 `Checked.refs` の `target` から計算した期待)が返り、コメント行・予約語 `fn` の位置では null、
   宣言名の上ではその宣言自身が返る(5c)。
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
  if change == some 1 && openClose == some true && definitionProvider == some true then
    ok "initialize: textDocumentSync.change = 1 (full), openClose = true, definitionProvider = true"
  else
    fail s!"initialize: expected textDocumentSync.change = 1, openClose = true and definitionProvider = true, got {resp.compress}"
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
  -- 5c. 宣言の無い位置では null、宣言名の上ではその宣言自身
  let probeRel := unitRoot ++ "/Consensus/Objects/Time.naru"
  let probePath := (env.root / probeRel).toString
  let probeText := (unitSrc.lookup probePath).getD ""
  let probeLines := probeText.splitOn "\n"
  let commentLine := probeLines.findIdx? fun l => l.trimAscii.toString.startsWith "//"
  let fnLine := probeLines.findIdx? fun l => l.startsWith "fn "
  for (what, pos) in [("a comment line", commentLine.map (·, 2)), ("the keyword `fn`", fnLine.map (·, 0))] do
    match pos with
    | none => fail s!"{probeRel}: no {what} to probe"
    | some (l, ch) =>
      match ← definitionAt env (System.Uri.pathToUri probePath) l ch with
      | .ok none => ok s!"{probeRel}:{l + 1}:{ch + 1} ({what}): textDocument/definition → null (no declaration there)"
      | .ok (some got) => fail s!"{probeRel}:{l + 1}:{ch + 1} ({what}): definition → {showLoc env got}, expected null"
      | .error e => fail s!"{probeRel}:{l + 1}:{ch + 1} ({what}): {e}"
  match (unitChecked.mods.find? (·.file == probePath)).bind fun m => m.decls.find? (·.kind == .fn) with
  | none => fail s!"{probeRel}: no fn declaration to probe"
  | some d =>
    let self : Naru.Resolve.Sym := { name := d.name, qualified := d.name, kind := d.kind, file := probePath, span := d.span }
    let want := wantLoc unitSrc self
    match ← definitionAt env (System.Uri.pathToUri probePath) (d.span.line - 1) (utf16Of probeText d.span.line d.span.col) with
    | .ok (some got) =>
      if got == want then ok s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name `{d.name}`): textDocument/definition → the declaration itself {showLoc env want}"
      else fail s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name): definition → {showLoc env got}, expected {showLoc env want}"
    | .ok none => fail s!"{probeRel}:{d.span.line}:{d.span.col} (declaration name `{d.name}`): definition → null, expected {showLoc env want}"
    | .error e => fail s!"{probeRel}:{d.span.line}:{d.span.col}: {e}"
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
