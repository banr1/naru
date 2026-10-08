import NaruTest.Common
import NaruTest.Zed

/-!
# `naru_test zed-install` — 人間の Zed に Dev Extension を入れる(IDEAL.md C19)

起動中の Zed(人間のインスタンス)に `editors/zed-naru/` を Dev Extension として入れ(無ければ `zed: install dev extension`、
あれば `zed: rebuild dev extension`)、Zed が文法と拡張をビルドして読み込んだことを `~/Library/Logs/Zed/Zed.log` と
ファイルで確かめる。リポジトリのルートで実行する。操作は `osascript`(System Events。前提「画面観測」の手順)で行う:
コマンドパレット(⌘⇧P)にコマンド名をクリップボード経由で貼って Enter、install ならフォルダ選択ダイアログで ⌘⇧G →
拡張ディレクトリの絶対パスを貼って Enter → Enter、rebuild で Dev Extension が 2 つ以上あれば picker に `naru` を貼って Enter。

1. 前提: Zed が起動している(`pgrep -x zed`)、`Zed.log` がある、`lake build naru` が exit 0(拡張は `.lake/build/bin/naru lsp` を起動する)。
2. `~/Library/Application Support/Zed/extensions/installed/naru` が無ければ install、`editors/zed-naru` への symlink なら rebuild、
   それ以外(他の `naru` 拡張)なら触らずに FAIL。
3. 操作の開始を目印ファイルの mtime と `Zed.log` のサイズ(以後に足された行だけを読む)で控え、`grammars/naru.wasm` があれば消して
   文法を必ずコンパイルし直させる(Zed は `parser.c` より新しい wasm があると文法のコンパイルを飛ばすので、`rev` を変えない
   rebuild では wasm の時刻が動かない)。
4. `osascript` で操作し、`Zed.log` に `extensions updated.` の行(または失敗の行)が足されるまで待つ(最長 5 分)。
5. 足された行に `compiled grammar naru`、`finished compiling extension <installed/naru>`(install では Zed は symlink を作る前に
   拡張のソースのパス `editors/zed-naru` でコンパイルして記録するのでそれも受理し、どちらだったかを出す。パスの引用符の
   有無は問わない: Zed 1.23 は引用符付き)、`extensions updated.` の `loading 1` または `reloading 1` があり、
   `failed to compile` / `Failed to install dev extension` が 0 件。
6. `installed/naru` が `editors/zed-naru` への symlink(`realpath` 同士で比較)。
7. `editors/zed-naru/extension.wasm` と `grammars/naru.wasm` の mtime が操作の開始以後。`grammars/naru/` の checkout が
   `extension.toml` の `rev`。

人間の Zed を操作するときの安全策(AppleScript): 前面が Zed であることをキーを送る直前ごとに確かめる、文字列はクリップボード
経由で入れて終わりに戻す(エラーでも戻す)、⌘⇧P の前に Escape を 1 回送って開いたままの palette / modal を閉じる(⌘⇧P は
トグル)、install のフォルダ選択ダイアログは AX に `title = "Open"` の窓(かシート)として現れるのでそれを待ってから ⌘⇧G を
送り、最後の Enter の後にその窓が消えたことも確かめる(消えなければ Escape で閉じて失敗にする)、rebuild の picker は
有効な Dev Extension(`installed/` の symlink で `extension.toml` を持つもの)が 2 つ以上のときだけ `naru` を貼る。
Zed 自身の palette / picker は AX に現れないので、その部分はスクリーンショット(最後の Enter の直前)を残す。
人間の Zed の設定・窓・他の拡張には触れない(触るのは `extensions/installed/naru` の symlink を作る Zed 自身だけ)。

スクリーンショットと目印・AppleScript は `.lake/naru/test/zed-install/` に置く(追跡対象外)。
-/

namespace NaruTest.ZedInstall

open NaruTest.Zed (extDir extensionToml parseToml lookup has)

def extensionId : String := "naru"
def scratchDir : System.FilePath := ".lake" / "naru" / "test" / "zed-install"
def extensionWasm : System.FilePath := extDir / "extension.wasm"
def grammarWasm : System.FilePath := extDir / "grammars" / "naru.wasm"
def grammarCheckout : System.FilePath := extDir / "grammars" / "naru"

structure Env where
  home : String
  root : System.FilePath
  extAbs : System.FilePath
  installedDir : System.FilePath
  installedLink : System.FilePath
  zedLog : System.FilePath
  scratch : System.FilePath

def mkEnv : IO Env := do
  let home := (← IO.getEnv "HOME").getD ""
  let root ← IO.currentDir
  let support := System.FilePath.mk home / "Library" / "Application Support" / "Zed"
  let installedDir := support / "extensions" / "installed"
  return { home, root, extAbs := root / extDir, installedDir, installedLink := installedDir / extensionId,
           zedLog := System.FilePath.mk home / "Library" / "Logs" / "Zed" / "Zed.log", scratch := root / scratchDir }

/-! ## 操作の AppleScript(実行時に書き出して `osascript <file> <mode> <arg> <picker|nopicker> <png>` で走らせる) -/

def appleScript : String := r#"-- naru_test zed-install が書き出して osascript で実行する(IDEAL.md C19)。
-- usage: osascript zed-dev-extension.applescript install <extension dir> nopicker <png>
--        osascript zed-dev-extension.applescript rebuild <extension id> <picker|nopicker> <png>
-- 文字列はクリップボード経由で入れる(入力ソースが日本語だと keystroke の文字列は IME で化ける)。
-- キーを送る直前ごとに前面が Zed であることを確かめる(人間が同じ機械を使っていると前面がすぐ戻る)。

on frontName()
	tell application "System Events" to return name of first application process whose frontmost is true
end frontName

on ensureZedFront()
	set n to my frontName()
	if n is not "zed" then error "the front application is " & n & ", not Zed"
end ensureZedFront

on bringZedFront()
	tell application "System Events" to set frontmost of process "Zed" to true
	delay 0.4
	my ensureZedFront()
end bringZedFront

on pasteText(t)
	my ensureZedFront()
	set the clipboard to t
	delay 0.15
	tell application "System Events" to keystroke "v" using command down
end pasteText

on pressKey(kc)
	my ensureZedFront()
	tell application "System Events" to key code kc
end pressKey

-- フォルダ選択ダイアログ(AppKit の open panel)は AX に title "Open" の窓(前面 = window 1)かシートとして現れる。
-- Zed 自身の窓も AX の窓に数えられるので、窓の数では判定しない。
on dialogShown()
	tell application "System Events" to tell process "Zed"
		try
			if (count of windows) > 0 and (title of window 1 is "Open") then return true
		end try
		try
			if exists sheet 1 of window 1 then return true
		end try
	end tell
	return false
end dialogShown

on waitDialog(shown)
	repeat 20 times
		delay 0.5
		if (my dialogShown()) is shown then return true
	end repeat
	return false
end waitDialog

on operate(mode, arg, picker, shot)
	my bringZedFront()
	-- ⌘⇧P はトグル: 開いたままの palette / modal があれば先に閉じる
	my pressKey(53)
	delay 0.4
	my ensureZedFront()
	tell application "System Events" to keystroke "p" using {command down, shift down}
	delay 0.8
	if mode is "install" then
		my pasteText("zed: install dev extension")
	else
		my pasteText("zed: rebuild dev extension")
	end if
	delay 0.8
	my pressKey(36)
	if mode is "install" then
		if not (my waitDialog(true)) then error "the folder dialog (window titled Open) of zed: install dev extension did not appear"
		delay 0.5
		my ensureZedFront()
		tell application "System Events" to keystroke "g" using {command down, shift down}
		delay 0.8
		my pasteText(arg)
		delay 0.8
		my pressKey(36)
		delay 1.2
		do shell script "screencapture -x -D 1 " & quoted form of shot
		my pressKey(36)
		if not (my waitDialog(false)) then
			my pressKey(53)
			error "the folder dialog did not close after Enter → Enter (cancelled with Escape)"
		end if
	else if picker is "picker" then
		delay 1.0
		my pasteText(arg)
		delay 0.8
		do shell script "screencapture -x -D 1 " & quoted form of shot
		my pressKey(36)
	else
		delay 1.0
		do shell script "screencapture -x -D 1 " & quoted form of shot
	end if
	delay 0.5
end operate

on run argv
	set mode to item 1 of argv
	set arg to item 2 of argv
	set picker to item 3 of argv
	set shot to item 4 of argv
	set prevApp to my frontName()
	set saved to ""
	try
		set saved to (the clipboard as text)
	end try
	set failure to ""
	try
		my operate(mode, arg, picker, shot)
	on error msg
		set failure to msg
	end try
	-- クリップボードと前面を戻す(失敗したときも)
	if saved is not "" then set the clipboard to saved
	try
		tell application "System Events" to set frontmost of process prevApp to true
	end try
	if failure is not "" then error failure
	return "ok"
end run
"#

/-! ## 補助 -/

def isSymlink (p : System.FilePath) : IO Bool := do
  try
    let m ← p.symlinkMetadata
    return m.type == .symlink
  catch _ => return false

def realpath (p : String) : IO (Option String) := do
  let out ← runProc "realpath" #[p]
  if out.exitCode == 0 then return some out.stdout.trimAscii.toString else return none

def readlink (p : System.FilePath) : IO (Option String) := do
  let out ← runProc "readlink" #[p.toString]
  if out.exitCode == 0 then return some out.stdout.trimAscii.toString else return none

def fileSize (p : System.FilePath) : IO Nat := do
  if ← p.pathExists then return (← p.metadata).byteSize.toNat else return 0

/-- `Zed.log` の `offset` バイト以後(操作の開始以後に足された行)。Zed は行ごとに書き足すので境界は改行。
ファイルが `offset` より短くなっていたら(Zed の再起動でローテーションされた)先頭から読む。 -/
def logSince (p : System.FilePath) (offset : Nat) : IO String := do
  if !(← p.pathExists) then return ""
  let bytes ← IO.FS.readBinFile p
  let start := if bytes.size < offset then 0 else offset
  if bytes.size ≤ start then return ""
  return (String.fromUTF8? (bytes.extract start bytes.size)).getD ""

def lines (s : String) : List String := (s.splitOn "\n").filter (!·.isEmpty)

def countLines (s needle : String) : Nat := ((lines s).filter (has · needle)).length

def mtime (p : System.FilePath) : IO (Option IO.FS.SystemTime) := do
  if ← p.pathExists then return some (← p.metadata).modified else return none

def showTime (t : IO.FS.SystemTime) : String := s!"{t.sec}.{t.nsec}"

/-! ## 検査 -/

inductive Mode where
  | install
  | rebuild
deriving BEq, Repr

def modeName : Mode → String
  | .install => "install"
  | .rebuild => "rebuild"

def checkPreconditions (e : Env) : M Bool := do
  if !(← extensionToml.pathExists) then
    fail s!"{extensionToml} not found (run from the repository root)"
    return false
  let z ← runProc "pgrep" #["-x", "zed"]
  if z.exitCode != 0 then
    fail "Zed is not running (pgrep -x zed found nothing): C19 installs into the human's running Zed"
    return false
  ok s!"Zed is running (pid {(z.stdout.trimAscii.toString.splitOn "\n").headD "?"})"
  if !(← e.zedLog.pathExists) then
    fail s!"{e.zedLog} not found"
    return false
  let build ← runProc "lake" #["build", "naru"]
  if build.exitCode != 0 then
    fail s!"lake build naru exit {build.exitCode}: {tail build.stderr}"
    return false
  ok "lake build naru exit 0 (the extension starts .lake/build/bin/naru lsp)"
  return true

/-- `installed/naru` がこの拡張への symlink か(`realpath` 同士で比較)。`(symlink の先, 一致)`。 -/
def linkStatus (e : Env) : IO (String × Bool) := do
  let target := (← readlink e.installedLink).getD ""
  match ← realpath e.installedLink.toString, ← realpath e.extAbs.toString with
  | some a, some b => return (target, a == b)
  | _, _ => return (target, false)

/-- install か rebuild か。`installed/naru` が他の場所への symlink や実体なら触らない。 -/
def decideMode (e : Env) : M (Option Mode) := do
  if !(← e.installedLink.pathExists) && !(← isSymlink e.installedLink) then
    ok s!"{e.installedLink} is absent → zed: install dev extension"
    return some .install
  if !(← isSymlink e.installedLink) then
    fail s!"{e.installedLink} exists but is not a symlink: another `naru` extension is installed; not touching it"
    return none
  let (target, same) ← linkStatus e
  if same then
    ok s!"{e.installedLink} → {target} (this extension) → zed: rebuild dev extension"
    return some .rebuild
  else
    fail s!"{e.installedLink} → {target} is not {e.extAbs}: another `naru` dev extension is installed; not touching it"
    return none

/-- 有効な Dev Extension(`installed/` の symlink で、先に `extension.toml` があるもの)の数。
2 つ以上なら `zed: rebuild dev extension` は picker を出す(Zed は読み込めた dev extension だけを数える)。 -/
def devExtensionCount (e : Env) : IO (Nat × List String) := do
  if !(← e.installedDir.isDir) then return (0, [])
  let mut names : List String := []
  for entry in ← e.installedDir.readDir do
    if (← isSymlink entry.path) && (← (entry.path / "extension.toml").pathExists) then
      names := names ++ [entry.fileName]
  return (names.length, names)

def runAppleScript (e : Env) (mode : Mode) (picker : Bool) (shot : System.FilePath) : M Bool := do
  let script := e.scratch / "zed-dev-extension.applescript"
  IO.FS.writeFile script appleScript
  let arg := match mode with
    | .install => e.extAbs.toString
    | .rebuild => extensionId
  let args := #[script.toString, modeName mode, arg, if picker then "picker" else "nopicker", shot.toString]
  let out ← runProc "osascript" args
  if out.exitCode == 0 && out.stdout.trimAscii.toString == "ok" then
    let how := match mode, picker with
      | .install, _ => "Escape → ⌘⇧P → zed: install dev extension → Enter → folder dialog (window Open) → ⌘⇧G → path → Enter → Enter → dialog closed"
      | .rebuild, true => "Escape → ⌘⇧P → zed: rebuild dev extension → Enter → picker → naru → Enter"
      | .rebuild, false => "Escape → ⌘⇧P → zed: rebuild dev extension → Enter"
    ok s!"osascript: {how} (screenshot {shot})"
    return true
  else
    fail s!"osascript exit {out.exitCode}: {tail out.stderr 500}{tail out.stdout 200}"
    return false

/-- `extensions updated.` か失敗の行が足されるまで待つ(1 秒ごと、最長 `maxSec` 秒)。足された部分を返す。 -/
partial def waitForZed (e : Env) (offset : Nat) (maxSec : Nat) (n : Nat := 0) : IO (String × Nat) := do
  let added ← logSince e.zedLog offset
  if has added "extensions updated." || has added "failed to compile" || has added "Failed to install dev extension" then
    return (added, n)
  if n ≥ maxSec then return (added, n)
  IO.sleep 1000
  waitForZed e offset maxSec (n + 1)

def checkLog (e : Env) (mode : Mode) (added : String) (waited : Nat) : M Unit := do
  if !(has added "extensions updated.") then
    fail s!"Zed.log: no `extensions updated.` line within {waited}s after the operation (last lines:\n{tail added 1200})"
  let failures := countLines added "failed to compile" + countLines added "Failed to install dev extension"
  if failures == 0 then ok s!"Zed.log: 0 `failed to compile` / `Failed to install dev extension` lines ({(lines added).length} lines added in {waited}s)"
  else fail s!"Zed.log: {failures} failure line(s):\n{"\n".intercalate ((lines added).filter fun l => has l "failed to compile" || has l "Failed to install dev extension")}"
  let installedPath := e.installedLink.toString
  let sourcePath := e.extAbs.toString
  -- Zed はパスを引用符なし(〜1.22 頃)でも引用符付き(1.23: Debug 表示)でも記録するので、どちらでも受理する。
  -- 他の拡張(esl 等)の行を拾わないよう、この拡張のパスを含む行だけを見る
  let mentions (l prefix' path : String) : Bool :=
    has l s!"{prefix'} {path}" || has l s!"{prefix'} \"{path}\""
  let findLine (prefix' : String) : Option (String × Bool) :=
    match (lines added).find? (fun l => mentions l prefix' installedPath) with
    | some l => some (l, true)
    | none =>
      match (lines added).find? (fun l => mentions l prefix' sourcePath) with
      | some l => some (l, false)
      | none => none
  match findLine "compiled grammar naru for extension" with
  | some (l, _) => ok s!"Zed.log: `compiled grammar naru` — {l}"
  | none => fail s!"Zed.log: no `compiled grammar naru for extension <{installedPath} | {sourcePath}>` line"
  match findLine "finished compiling extension" with
  | some (l, true) => ok s!"Zed.log: `finished compiling extension {installedPath}` — {l}"
  | some (l, false) =>
    if mode == .install then
      ok s!"Zed.log: `finished compiling extension {sourcePath}` (install compiles at the source path before creating the symlink; rebuild logs {installedPath}) — {l}"
    else
      fail s!"Zed.log: rebuild should log `finished compiling extension {installedPath}`, got the source path: {l}"
  | none => fail s!"Zed.log: no `finished compiling extension <{installedPath} | {sourcePath}>` line"
  match (lines added).find? (has · "extensions updated.") with
  | some l =>
    if has l "extensions updated. loading 1," || has l "reloading 1," then
      ok s!"Zed.log: `extensions updated.` with loading 1 / reloading 1 — {l}"
    else
      fail s!"Zed.log: `extensions updated.` without loading 1 / reloading 1: {l}"
  | none => pure ()

def checkSymlink (e : Env) : M Unit := do
  if !(← isSymlink e.installedLink) then
    fail s!"{e.installedLink} is not a symlink"
    return
  let (target, same) ← linkStatus e
  if same then ok s!"{e.installedLink} is a symlink to {target} (= {extDir})"
  else fail s!"{e.installedLink} → {target} does not resolve to {e.extAbs}"

def checkFresh (p : System.FilePath) (since : IO.FS.SystemTime) : M Unit := do
  match ← mtime p with
  | some t =>
    if compare since t != .gt then ok s!"{p} updated after the operation started (mtime {showTime t} ≥ {showTime since})"
    else fail s!"{p} is older than the operation (mtime {showTime t} < {showTime since})"
  | none => fail s!"{p} is missing"

def checkGrammarRev : M Unit := do
  let t := parseToml (← IO.FS.readFile extensionToml)
  let rev := match lookup t "grammars.naru" "rev" with
    | some (.str r) => r
    | _ => ""
  let out ← runProc "git" #["-C", grammarCheckout.toString, "rev-parse", "HEAD"]
  let head := out.stdout.trimAscii.toString
  if out.exitCode == 0 && head == rev then ok s!"{grammarCheckout} is checked out at rev {rev}"
  else fail s!"{grammarCheckout}: HEAD is `{head}` (git rev-parse exit {out.exitCode}), extension.toml rev is `{rev}`"

def checks (e : Env) : M Unit := do
  if !(← checkPreconditions e) then return
  let some mode ← decideMode e | return
  let (devCount, devNames) ← devExtensionCount e
  let picker := mode == .rebuild && devCount ≥ 2
  if mode == .rebuild then
    ok s!"{devCount} dev extension(s) installed {devNames} → {if picker then "picker expected: choose naru" else "no picker"}"
  IO.FS.createDirAll e.scratch
  -- 文法を必ずコンパイルし直させる(wasm が parser.c より新しいと Zed は飛ばす)
  if ← grammarWasm.pathExists then
    IO.FS.removeFile grammarWasm
    ok s!"removed {grammarWasm} so that Zed recompiles the grammar"
  -- 操作の開始: 目印の mtime と Zed.log のサイズ
  let marker := e.scratch / "started"
  IO.FS.writeFile marker ""
  let since := (← marker.metadata).modified
  let offset ← fileSize e.zedLog
  let shot1 := e.scratch / System.FilePath.mk s!"{modeName mode}-before-enter.png"
  if !(← runAppleScript e mode picker shot1) then return
  let (added, waited) ← waitForZed e offset 300
  checkLog e mode added waited
  checkSymlink e
  checkFresh extensionWasm since
  checkFresh grammarWasm since
  checkGrammarRev
  let shot2 := e.scratch / System.FilePath.mk s!"{modeName mode}-after.png"
  let sc ← runProc "screencapture" #["-x", "-D", "1", shot2.toString]
  if sc.exitCode == 0 then ok s!"screenshot after the operation: {shot2}"
  else fail s!"screencapture exit {sc.exitCode}: {tail sc.stderr 300}"

def run : IO UInt32 := do
  if !(← extDir.isDir) then
    IO.eprintln s!"naru_test zed-install: {extDir} not found (run from the repository root)"
    return 2
  let e ← mkEnv
  runGroup "naru_test zed-install" (checks e)

end NaruTest.ZedInstall
