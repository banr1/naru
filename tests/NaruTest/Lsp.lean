import Naru
import NaruTest.Common

/-!
# `naru_test lsp` — 言語サーバー `naru lsp` の検査(IDEAL.md C18)

リポジトリのルートで実行する。`lake build naru` の後、子プロセスの `.lake/build/bin/naru lsp` と標準入出力で LSP を話し、
次を確かめる(`ok:` / `FAIL:`)。期待値はコンパイラ(`Naru.compileSources`、CLI の `compile` と同じ検査)から取る。

1. `initialize` の応答に全文同期(`textDocumentSync.change = 1`、`openClose`)がある。`initialized` を送る。
2. 未対応のリクエスト(`textDocument/hover`)には `MethodNotFound`(-32601)が返る。この応答は以後、通知の処理の終わりを
   待つ barrier にも使う(サーバーはメッセージを順に処理するので、応答が返れば直前の通知の診断は送り終わっている)。
3. `tests/reject/` の各反例を `didOpen` すると、`naru compile` と同じ E 番号・同じ行(・列)の診断がその URI に返り、
   反例の先頭コメントが名指しする E 番号(`期待: … E001`)がその中にある。`didClose` で空になる。
   `tests/accept/` の各受理例(単独の単位)を `didOpen` すると診断 0 件(C35 の正常例 `prop_bool.naru` を含む)、`didClose` で空。
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

/-- 文字列の中で最初に現れる `E0dd`。 -/
def firstCode (s : String) : Option String := Id.run do
  let cs := s.toList.toArray
  for i in [0:cs.size] do
    if cs[i]? == some 'E' && cs[i + 1]? == some '0' && (cs[i + 2]?.map Char.isDigit).getD false
        && (cs[i + 3]?.map Char.isDigit).getD false then
      return some (String.ofList [cs[i]!, cs[i + 1]!, cs[i + 2]!, cs[i + 3]!])
  return none

/-- 反例の本文(先頭のコメント)が名指しする E 番号: `期待:` の行の `E0dd`、その行が無ければ本文で最初の `E0dd`
(`type_path_escape.naru` のように、説明の中で別の番号に先に触れる反例がある)。 -/
def namedCode (text : String) : Option String :=
  match (text.splitOn "\n").find? (fun l => (l.splitOn "期待").length > 1 && (firstCode l).isSome) with
  | some l => firstCode l
  | none => firstCode text

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

/-- 通知の処理の終わりを待つ: 未対応のリクエストを送り、その `MethodNotFound` が返るまでの publish を集める。 -/
def barrier (env : Env) : M (Option (Array Pub)) := do
  let id ← env.nextId.modifyGet fun n => (n, n + 1)
  request env.client id "textDocument/hover" barrierParams
  match ← collectUntil env.client id with
  | none =>
    fail "server closed its output (or sent an unreadable message) before answering the barrier request"
    return none
  | some (resp, pubs) =>
    let code := getField resp "error" >>= fun e => (e.getObjVal? "code" >>= Json.getInt?).toOption
    if code != some (-32601) then
      fail s!"unknown request textDocument/hover: expected error code -32601, got {resp.compress}"
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

def checks (env : Env) : M Unit := do
  let c := env.client
  -- 1. initialize / initialized
  request c 1 "initialize"
    (Json.mkObj [("processId", Json.null), ("rootUri", System.Uri.pathToUri env.root), ("capabilities", Json.mkObj [])])
  let some (resp, _) ← collectUntil c 1
    | fail "no response to initialize"; return
  let sync := getField resp "result" >>= (getField · "capabilities") >>= (getField · "textDocumentSync")
  let change := sync >>= fun s => (s.getObjVal? "change" >>= Json.getNat?).toOption
  let openClose := sync >>= fun s => (s.getObjVal? "openClose" >>= Json.getBool?).toOption
  if change == some 1 && openClose == some true then
    ok "initialize: textDocumentSync.change = 1 (full), openClose = true"
  else
    fail s!"initialize: expected textDocumentSync.change = 1 and openClose = true, got {resp.compress}"
  notify c "initialized" (Json.mkObj [])
  -- 2. 未対応のリクエスト
  let some _ ← barrier env | return
  ok "unknown request textDocument/hover → error -32601 (MethodNotFound)"
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

end NaruTest.Lsp
