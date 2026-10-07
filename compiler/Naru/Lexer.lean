import Naru.Diag

/-!
# 字句解析

`.naru` ソースをトークン列にする。空白と改行は意味を持たない。
コメントは `// …`(行末まで)と `/* … */`(入れ子可)。
識別子は `[A-Za-z_][A-Za-z0-9_]*` に末尾の `?` を許す(`find?` / `minBy?` 等)。
-/

namespace Naru

inductive TokenKind where
  | ident (s : String)
  | kw (s : String)
  | nat (n : Nat)
  | str (s : String)
  | sym (s : String)
  | eof
deriving Repr, Inhabited, BEq

structure Token where
  kind : TokenKind
  span : Span
deriving Repr, Inhabited

def TokenKind.describe : TokenKind → String
  | .ident s => s!"identifier `{s}`"
  | .kw s => s!"keyword `{s}`"
  | .nat n => s!"number `{n}`"
  | .str _ => "string literal"
  | .sym s => s!"`{s}`"
  | .eof => "end of file"

/-- 予約語。IDEAL.md の MVP 構文 + 式の予約語。 -/
def keywords : List String :=
  ["module", "import", "type", "record", "enum", "derive", "input", "fn", "state",
   "protocol", "predicate", "condition", "regime", "property", "claim", "bundle",
   "scenario", "observer", "let", "if", "else", "match", "forall", "exists", "in",
   "implies", "true", "false"]

/-- 2 文字記号(1 文字記号より先に照合する)。`>>` は含めない(`Table<K, List<V>>` のため)。 -/
def symbols2 : List String := ["=>", "->", "==", "!=", "<=", ">=", "&&", "||", ".."]

def symbols1 : String := "(){}[]<>,:;.=+-*/%!&|?"

structure LexState where
  src : Array Char
  i : Nat
  line : Nat
  col : Nat

namespace LexState

def peek (s : LexState) (k : Nat := 0) : Option Char := s.src[s.i + k]?

def span (s : LexState) : Span := { line := s.line, col := s.col }

def adv (s : LexState) : LexState :=
  match s.peek with
  | some '\n' => { s with i := s.i + 1, line := s.line + 1, col := 1 }
  | some _ => { s with i := s.i + 1, col := s.col + 1 }
  | none => s

def advN (s : LexState) : Nat → LexState
  | 0 => s
  | n + 1 => s.adv.advN n

end LexState

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

namespace Lexer

partial def skipLine (s : LexState) : LexState :=
  match s.peek with
  | none | some '\n' => s
  | some _ => skipLine s.adv

/-- `/*` の直後から呼ぶ。入れ子を数え、閉じ `*/` の直後の状態を返す。閉じなければ `none`。 -/
partial def skipBlock (s : LexState) (depth : Nat) : Option LexState :=
  match s.peek with
  | none => none
  | some '*' =>
    if s.peek 1 == some '/' then
      if depth == 1 then some (s.advN 2) else skipBlock (s.advN 2) (depth - 1)
    else skipBlock s.adv depth
  | some '/' =>
    if s.peek 1 == some '*' then skipBlock (s.advN 2) (depth + 1) else skipBlock s.adv depth
  | some _ => skipBlock s.adv depth

partial def takeWhile (s : LexState) (p : Char → Bool) (acc : String) : LexState × String :=
  match s.peek with
  | some c => if p c then takeWhile s.adv p (acc.push c) else (s, acc)
  | none => (s, acc)

/-- 開き `"` の直後から呼ぶ。 -/
partial def lexString (s : LexState) (acc : String) : Except String (LexState × String) :=
  match s.peek with
  | none => .error "unterminated string literal"
  | some '"' => .ok (s.adv, acc)
  | some '\n' => .error "unterminated string literal"
  | some '\\' =>
    match s.peek 1 with
    | some 'n' => lexString (s.advN 2) (acc.push '\n')
    | some 't' => lexString (s.advN 2) (acc.push '\t')
    | some '"' => lexString (s.advN 2) (acc.push '"')
    | some '\\' => lexString (s.advN 2) (acc.push '\\')
    | _ => .error "invalid escape sequence in string literal"
  | some c => lexString s.adv (acc.push c)

partial def go (file : String) (s : LexState) (acc : Array Token) :
    Except Diagnostic (Array Token) :=
  let err (msg : String) : Except Diagnostic (Array Token) :=
    .error { file, span := s.span, code := Code.syntaxError, msg }
  match s.peek with
  | none => .ok (acc.push { kind := .eof, span := s.span })
  | some c =>
    if c.isWhitespace then go file s.adv acc
    else if c == '/' && s.peek 1 == some '/' then go file (skipLine s) acc
    else if c == '/' && s.peek 1 == some '*' then
      match skipBlock (s.advN 2) 1 with
      | some s' => go file s' acc
      | none => err "unterminated block comment"
    else if isIdentStart c then
      let (s', word) := takeWhile s isIdentChar ""
      let (s', word) :=
        if s'.peek == some '?' then (s'.adv, word.push '?') else (s', word)
      let kind := if keywords.contains word then TokenKind.kw word else TokenKind.ident word
      go file s' (acc.push { kind, span := s.span })
    else if c.isDigit then
      let (s', digits) := takeWhile s Char.isDigit ""
      go file s' (acc.push { kind := .nat digits.toNat!, span := s.span })
    else if c == '"' then
      match lexString s.adv "" with
      | .ok (s', str) => go file s' (acc.push { kind := .str str, span := s.span })
      | .error msg => err msg
    else
      let two := String.ofList [c, (s.peek 1).getD ' ']
      if symbols2.contains two then
        go file (s.advN 2) (acc.push { kind := .sym two, span := s.span })
      else if symbols1.contains c then
        go file s.adv (acc.push { kind := .sym (String.singleton c), span := s.span })
      else err s!"unexpected character `{c}`"

end Lexer

/-- ソース全体をトークン列にする。末尾に必ず `eof` が付く。 -/
def lexAll (file : String) (src : String) : Except Diagnostic (Array Token) :=
  Lexer.go file { src := src.toList.toArray, i := 0, line := 1, col := 1 } #[]

end Naru
