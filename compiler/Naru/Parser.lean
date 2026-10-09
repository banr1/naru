import Naru.Lexer
import Naru.Ast

/-!
# 構文解析(再帰下降)

文法の全体は `docs/language.md`。バックトラックせず、先読み(高々 2 トークン)だけで決める。
`if` / `match` の頭部では record literal を許さない(`if x { … }` との衝突を避ける。Rust と同じ)。
-/

namespace Naru.Parser

structure PState where
  file : String
  toks : Array Token
  pos : Nat := 0
  /-- true の間は `Name { … }` を record literal と読まない。 -/
  noRecordLit : Bool := false

abbrev P := EStateM Diagnostic PState

def peekTok (k : Nat := 0) : P Token := do
  let s ← get
  match s.toks[s.pos + k]? with
  | some t => return t
  | none => return s.toks.back!

def curSpan : P Span := do return (← peekTok).span

def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

def failAt (span : Span) (msg : String) : P α := do
  let s ← get
  throw { file := s.file, span, code := Code.syntaxError, msg }

def fail (msg : String) : P α := do
  let t ← peekTok
  failAt t.span msg

def isSym (s : String) : P Bool := do return (← peekTok).kind == .sym s
def isKw (s : String) : P Bool := do return (← peekTok).kind == .kw s

def expectSym (s : String) : P Span := do
  let t ← peekTok
  if t.kind == .sym s then
    advance
    return t.span
  else fail s!"expected `{s}`, found {t.kind.describe}"

def expectKw (s : String) : P Span := do
  let t ← peekTok
  if t.kind == .kw s then
    advance
    return t.span
  else fail s!"expected `{s}`, found {t.kind.describe}"

def acceptSym (s : String) : P Bool := do
  if (← isSym s) then
    advance
    return true
  else return false

def expectIdent : P (String × Span) := do
  let t ← peekTok
  match t.kind with
  | .ident s =>
    advance
    return (s, t.span)
  | k => fail s!"expected identifier, found {k.describe}"

/-- 局所名(引数・let・lambda・量化の束縛)。小文字か `_` で始まらなければ E010。
大文字始まりは型・モジュール・enum・構築子の経路として読むので、局所名に許すと経路の読みが曖昧になる。 -/
def expectLocalIdent : P (String × Span) := do
  let (n, sp) ← expectIdent
  if n.front.isUpper then
    failAt sp s!"local name `{n}` must start with a lowercase letter or `_` (uppercase names are reserved for types, modules, enums and constructors)"
  return (n, sp)

/-- `a.b.c` を区切りごとの位置付きで読む。`.` の後が識別子のときだけ続ける。 -/
def parsePathSpans : P (Array (String × Span)) := do
  let first ← expectIdent
  let mut segs := #[first]
  repeat
    if !(← isSym ".") then break
    let t ← peekTok 1
    match t.kind with
    | .ident s =>
      advance
      advance
      segs := segs.push (s, t.span)
    | _ => break
  return segs

/-- `a.b.c`。位置は先頭の区切りのもの。 -/
def parsePath : P (List String × Span) := do
  let segs ← parsePathSpans
  return (segs.toList.map (·.1), segs[0]!.2)

def withRecordLit (allowed : Bool) (p : P α) : P α := do
  let old := (← get).noRecordLit
  modify fun s => { s with noRecordLit := !allowed }
  let r ← p
  modify fun s => { s with noRecordLit := old }
  return r

/-- `close` が来るまで `item` を `,` 区切りで読む。末尾の `,` を許す。`close` を消費する。 -/
partial def parseCommaList (close : String) (item : P α) : P (Array α) := do
  let mut xs := #[]
  repeat
    if (← acceptSym close) then break
    xs := xs.push (← item)
    if (← acceptSym ",") then continue
    let _ ← expectSym close
    break
  return xs

/-! ## 型 -/

partial def parseTy : P Ty := do
  let t ← peekTok
  match t.kind with
  | .sym "(" =>
    advance
    let elems ← parseCommaList ")" parseTy
    -- `(T1, T2) -> U` は関数型(仮引数の型にだけ書ける。検査は型検査の段)
    if (← acceptSym "->") then
      let ret ← parseTy
      return .fn t.span elems ret
    if elems.size == 0 then return .named t.span ["Unit"] #[]
    else if elems.size == 1 then return elems[0]!
    else return .tuple t.span elems
  | .ident _ =>
    let (segs, sp) ← parsePath
    let args ← if (← acceptSym "<") then parseCommaList ">" parseTy else pure #[]
    return .named sp segs args
  | k => fail s!"expected type, found {k.describe}"

/-! ## 式 -/

/-- 二項演算子の優先順位(大きいほど強い)。`implies` は右結合。 -/
def binPrec : String → Option Nat
  | "implies" => some 1
  | "||" => some 2
  | "&&" => some 3
  | "==" | "!=" => some 4
  | "<" | "<=" | ">" | ">=" => some 5
  | "+" | "-" => some 6
  | "*" | "/" | "%" => some 7
  | _ => none

def peekBinOp : P (Option (String × Nat)) := do
  let t ← peekTok
  match t.kind with
  | .sym s => return (binPrec s).map (s, ·)
  | .kw "implies" => return some ("implies", 1)
  | _ => return none

mutual

partial def parseExpr : P Expr := parseBin 1

partial def parseBin (minPrec : Nat) : P Expr := do
  let mut lhs ← parseUnary
  repeat
    match ← peekBinOp with
    | some (op, prec) =>
      if prec < minPrec then break
      let sp ← curSpan
      advance
      let nextMin := if op == "implies" then prec else prec + 1
      let rhs ← parseBin nextMin
      lhs := .binop sp op lhs rhs
    | none => break
  return lhs

partial def parseUnary : P Expr := do
  let t ← peekTok
  match t.kind with
  | .sym "!" =>
    advance
    let e ← parseUnary
    return .unop t.span "!" e
  | .sym "-" =>
    advance
    let e ← parseUnary
    return .unop t.span "-" e
  | _ => parsePostfix

partial def parsePostfix : P Expr := do
  let mut e ← parsePrimary
  repeat
    let t ← peekTok
    match t.kind with
    | .sym "(" =>
      advance
      let args ← withRecordLit true parseArgs
      e := match e with
        | .field sp r m => .method sp r m args
        | _ => .call t.span e args
    | .sym "." =>
      let t2 ← peekTok 1
      match t2.kind with
      | .ident name =>
        advance
        advance
        e := .field t2.span e name
      | _ => break
    | _ => break
  return e

/-- `(` の直後から `)` まで。`name = e` は名前付き引数。 -/
partial def parseArgs : P (Array Arg) := do
  let mut args := #[]
  repeat
    if (← acceptSym ")") then break
    let t ← peekTok
    let t2 ← peekTok 1
    match t.kind, t2.kind with
    | .ident n, .sym "=" =>
      advance
      advance
      let e ← parseExpr
      args := args.push (.named n e)
    | _, _ =>
      let e ← parseExpr
      args := args.push (.pos e)
    if (← acceptSym ",") then continue
    let _ ← expectSym ")"
    break
  return args

partial def parsePrimary : P Expr := do
  let t ← peekTok
  match t.kind with
  | .nat n =>
    advance
    return .lit t.span (.nat n)
  | .str s =>
    advance
    return .lit t.span (.str s)
  | .kw "true" =>
    advance
    return .lit t.span (.bool true)
  | .kw "false" =>
    advance
    return .lit t.span (.bool false)
  | .sym "(" =>
    advance
    if (← acceptSym ")") then return .lit t.span .unit
    let first ← withRecordLit true parseExpr
    if (← acceptSym ",") then
      let mut elems := #[first]
      repeat
        if (← isSym ")") then break
        elems := elems.push (← withRecordLit true parseExpr)
        if !(← acceptSym ",") then break
      let _ ← expectSym ")"
      return .tupleLit t.span elems
    else
      let _ ← expectSym ")"
      return first
  | .sym "[" =>
    advance
    let elems ← withRecordLit true (parseCommaList "]" parseExpr)
    return .listLit t.span elems
  | .sym "{" => parseBlock
  | .kw "if" => parseIf
  | .kw "match" => parseMatch
  | .kw "forall" => parseQuant .forall_
  | .kw "exists" => parseQuant .exists_
  | .sym "|" => parseLambda
  | .sym "||" =>
    advance
    let body ← parseExpr
    return .lambda t.span #[] body
  | .ident _ => parseIdentExpr
  | k => fail s!"expected expression, found {k.describe}"

partial def parseBlock : P Expr := do
  let sp ← expectSym "{"
  withRecordLit true (parseBlockBody sp)

partial def parseBlockBody (sp : Span) : P Expr := do
  let mut stmts := #[]
  let mut tail : Option Expr := none
  repeat
    if (← acceptSym "}") then break
    if (← isKw "let") then
      let lsp ← curSpan
      advance
      let (name, _) ← expectLocalIdent
      let ty ← if (← acceptSym ":") then some <$> parseTy else pure none
      let _ ← expectSym "="
      let val ← parseExpr
      let _ ← expectSym ";"
      stmts := stmts.push (.letS lsp name ty val)
    else
      let e ← parseExpr
      if (← acceptSym ";") then
        stmts := stmts.push (.exprS e)
      else
        let _ ← expectSym "}"
        tail := some e
        break
  return .block sp stmts tail

partial def parseIf : P Expr := do
  let sp ← expectKw "if"
  let cond ← withRecordLit false parseExpr
  let thn ← parseBlock
  let _ ← expectKw "else"
  let els ← if (← isKw "if") then parseIf else parseBlock
  return .ite sp cond thn els

partial def parseMatch : P Expr := do
  let sp ← expectKw "match"
  let scrut ← withRecordLit false parseExpr
  let _ ← expectSym "{"
  let arms ← withRecordLit true parseArms
  return .matchE sp scrut arms

/-- `{` の直後から `}` まで。本体がブロックの arm の後は `,` を省略できる(Rust と同じ)。 -/
partial def parseArms : P (Array Arm) := do
  let mut arms := #[]
  repeat
    if (← acceptSym "}") then break
    let arm ← parseArm
    arms := arms.push arm
    if (← acceptSym ",") then continue
    match arm with
    | .mk _ _ (.block ..) => continue
    | _ =>
      let _ ← expectSym "}"
      break
  return arms

partial def parseArm : P Arm := do
  let pat ← parsePattern
  let guard ← if (← isKw "if") then (do advance; some <$> parseExpr) else pure none
  let _ ← expectSym "=>"
  let body ← parseExpr
  return .mk pat guard body

partial def parseQuant (q : Quant) : P Expr := do
  let sp ← curSpan
  advance
  let mut binders := #[]
  repeat
    let (n, bsp) ← expectLocalIdent
    let ty ← if (← acceptSym ":") then some <$> parseTy else pure none
    binders := binders.push { name := n, ty, span := bsp : Binder }
    if !(← acceptSym ",") then break
  let body ← parseBlock
  return .quant sp q binders body

partial def parseLambda : P Expr := do
  let sp ← expectSym "|"
  let mut params := #[]
  repeat
    if (← acceptSym "|") then break
    let (n, bsp) ← expectLocalIdent
    let ty ← if (← acceptSym ":") then some <$> parseTy else pure none
    params := params.push { name := n, ty, span := bsp : Binder }
    if (← acceptSym ",") then continue
    let _ ← expectSym "|"
    break
  let body ← parseExpr
  return .lambda sp params body

/-- 識別子で始まる式。大文字始まりは大域経路(record literal の可能性あり)、小文字始まりは値と欄の連鎖。 -/
partial def parseIdentExpr : P Expr := do
  let segsWithSpans ← parsePathSpans
  let segs := segsWithSpans.toList.map (·.1)
  let (head, sp) := segsWithSpans[0]!
  if head.front.isUpper then
    if (← isSym "{") && !(← get).noRecordLit then
      advance
      let (fields, base) ← parseRecordFields
      return .recordLit sp segs fields base
    else
      return .var sp segs
  else
    let mut e := Expr.var sp [head]
    for (seg, segSp) in segsWithSpans.toList.tail do
      e := .field segSp e seg
    return e

/-- `{` の直後から `}` まで。`f: e` / `f`(短縮)/ 末尾の `..base`。 -/
partial def parseRecordFields : P (Array (String × Expr) × Option Expr) := do
  let mut fields := #[]
  let mut base : Option Expr := none
  repeat
    if (← acceptSym "}") then break
    if (← acceptSym "..") then
      base := some (← parseExpr)
      let _ ← acceptSym ","
      let _ ← expectSym "}"
      break
    let (n, nsp) ← expectIdent
    let v ← if (← acceptSym ":") then parseExpr else pure (Expr.var nsp [n])
    fields := fields.push (n, v)
    if (← acceptSym ",") then continue
    let _ ← expectSym "}"
    break
  return (fields, base)

partial def parsePattern : P Pattern := do
  let t ← peekTok
  match t.kind with
  | .ident "_" =>
    advance
    return .wild t.span
  | .nat n =>
    advance
    return .lit t.span (.nat n)
  | .str s =>
    advance
    return .lit t.span (.str s)
  | .kw "true" =>
    advance
    return .lit t.span (.bool true)
  | .kw "false" =>
    advance
    return .lit t.span (.bool false)
  | .sym "(" =>
    advance
    let elems ← parseCommaList ")" parsePattern
    if elems.size == 1 then return elems[0]! else return .tuple t.span elems
  | .ident _ =>
    let (segs, sp) ← parsePath
    if segs.length == 1 && !segs.head!.front.isUpper then
      return .bind sp segs.head!
    else
      let args ← if (← acceptSym "(") then parseCommaList ")" parsePattern else pure #[]
      return .ctor sp segs args
  | k => fail s!"expected pattern, found {k.describe}"

end

/-! ## 宣言 -/

def parseParams : P (Array Param) := do
  let _ ← expectSym "("
  parseCommaList ")" (do
    let (n, sp) ← expectLocalIdent
    let _ ← expectSym ":"
    let ty ← parseTy
    return { name := n, ty, span := sp : Param })

def capabilities : List String := ["eq", "order", "finite", "repr"]

def parseDerive : P (Array String) := do
  if !(← isKw "derive") then return #[]
  advance
  let mut caps := #[]
  repeat
    let (n, sp) ← expectIdent
    unless capabilities.contains n do
      failAt sp s!"unknown capability `{n}` (expected one of eq, order, finite, repr)"
    caps := caps.push n
    if !(← acceptSym ",") then break
  return caps

def parseRecordLike (kind : DeclKind) : P Decl := do
  advance
  let (n, sp) ← expectIdent
  let _ ← expectSym "{"
  let fields ← parseCommaList "}" (do
    let (f, fsp) ← expectIdent
    let _ ← expectSym ":"
    let ty ← parseTy
    return { name := f, ty, span := fsp : Field })
  let derives ← parseDerive
  return { kind, name := n, span := sp, fields, derives }

def parseEnum : P Decl := do
  advance
  let (n, sp) ← expectIdent
  let _ ← expectSym "{"
  let variants ← parseCommaList "}" (do
    let (v, vsp) ← expectIdent
    let args ← if (← acceptSym "(") then parseCommaList ")" parseTy else pure #[]
    return { name := v, args, span := vsp : Variant })
  let derives ← parseDerive
  return { kind := .enum, name := n, span := sp, variants, derives }

def parseFnLike (kind : DeclKind) : P Decl := do
  advance
  let (n, sp) ← expectIdent
  let params ← parseParams
  let _ ← expectSym "->"
  let ret ← parseTy
  let body ← parseBlock
  return { kind, name := n, span := sp, params, ret := some ret, body := some body }

def parseInput : P Decl := do
  advance
  let (n, sp) ← expectIdent
  let params ← parseParams
  let _ ← expectSym "->"
  let ret ← parseTy
  let _ ← acceptSym ";"
  return { kind := .input, name := n, span := sp, params, ret := some ret }

def parseSpecLike (kind : DeclKind) : P Decl := do
  advance
  let (n, sp) ← expectIdent
  let params ← if (← isSym "(") then parseParams else pure #[]
  let body ← parseBlock
  return { kind, name := n, span := sp, params, body := some body }

def parseClaim : P Decl := do
  advance
  if (← isKw "bundle") then
    advance
    let (n, sp) ← expectIdent
    let _ ← expectSym "{"
    let items ← parseCommaList "}" (do
      let (i, isp) ← expectIdent
      let e ← if (← acceptSym ":") then parseExpr else pure (Expr.var isp [i])
      return (i, e))
    return { kind := .claimBundle, name := n, span := sp, items }
  else
    let (n, sp) ← expectIdent
    let params ← if (← isSym "(") then parseParams else pure #[]
    let body ← parseBlock
    return { kind := .claim, name := n, span := sp, params, body := some body }

/-- scenario の本体: `{ (input f(x, y) = e;)* (let … ; | observe e;)* }`。
input の束縛は先頭にまとめて書く(後ろに書くと E010)。末尾の式は無く、出力は `observe` だけ。 -/
def parseScenarioBody (scenarioName : String) : P Expr := do
  let sp ← expectSym "{"
  withRecordLit true do
    let mut stmts : Array Stmt := #[]
    let mut afterHead := false
    repeat
      if (← acceptSym "}") then break
      let t ← peekTok
      match t.kind with
      | .kw "input" =>
        if afterHead then
          failAt t.span s!"input bindings come first in scenario `{scenarioName}` (before any `let` / `observe`)"
        advance
        let (name, _) ← expectIdent
        let _ ← expectSym "("
        let params ← parseCommaList ")" expectLocalIdent
        let _ ← expectSym "="
        let val ← parseExpr
        let _ ← expectSym ";"
        stmts := stmts.push (.inputS t.span name params val)
      | .kw "let" =>
        afterHead := true
        advance
        let (name, _) ← expectLocalIdent
        let ty ← if (← acceptSym ":") then some <$> parseTy else pure none
        let _ ← expectSym "="
        let val ← parseExpr
        let _ ← expectSym ";"
        stmts := stmts.push (.letS t.span name ty val)
      | .kw "observe" =>
        afterHead := true
        advance
        let e ← parseExpr
        let _ ← expectSym ";"
        stmts := stmts.push (.observeS t.span e)
      | k =>
        fail s!"expected `input`, `let`, `observe` or `}` in scenario `{scenarioName}`, found {k.describe} (a scenario has no result value: its output is `observe <observer>(…);`)"
    return .block sp stmts none

/-- 1 つの宣言。`protocol` は本体の宣言を平坦化して複数返す。 -/
partial def parseDecl : P (Array Decl) := do
  let t ← peekTok
  match t.kind with
  | .kw "type" =>
    advance
    let (n, sp) ← expectIdent
    let _ ← expectSym "="
    let ty ← parseTy
    let _ ← acceptSym ";"
    return #[{ kind := .typeAlias, name := n, span := sp, aliasOf := some ty }]
  | .kw "record" => return #[← parseRecordLike .record]
  | .kw "state" => return #[← parseRecordLike .state]
  | .kw "enum" => return #[← parseEnum]
  | .kw "input" => return #[← parseInput]
  | .kw "fn" => return #[← parseFnLike .fn]
  | .kw "observer" => return #[← parseFnLike .observer]
  | .kw "predicate" => return #[← parseSpecLike .predicate]
  | .kw "condition" => return #[← parseSpecLike .condition]
  | .kw "regime" => return #[← parseSpecLike .regime]
  | .kw "property" => return #[← parseSpecLike .property]
  | .kw "claim" => return #[← parseClaim]
  | .kw "scenario" =>
    advance
    let (n, sp) ← expectIdent
    let body ← parseScenarioBody n
    return #[{ kind := .scenario, name := n, span := sp, body := some body }]
  | .kw "protocol" =>
    advance
    let (n, sp) ← expectIdent
    let _ ← expectSym "{"
    let mut members : Array Decl := #[]
    repeat
      if (← acceptSym "}") then break
      let ds ← parseDecl
      members := members ++ ds.map (fun d => { d with owner := some n })
    return #[{ kind := .protocol, name := n, span := sp }] ++ members
  | k => fail s!"expected a declaration, found {k.describe}"

def parseModuleP : P Module := do
  let _ ← expectKw "module"
  let (name, nsp) ← parsePath
  let _ ← acceptSym ";"
  let mut imports := #[]
  let mut decls := #[]
  repeat
    let t ← peekTok
    match t.kind with
    | .eof => break
    | .kw "import" =>
      advance
      let (p, _) ← parsePath
      let _ ← acceptSym ";"
      imports := imports.push p
    | _ => decls := decls ++ (← parseDecl)
  let s ← get
  return { file := s.file, name, nameSpan := nsp, imports, decls }

end Parser

/-- トークン列を 1 モジュールに読む。最初の構文エラーで止まる。 -/
def parseModule (file : String) (toks : Array Token) : Except Diagnostic Module :=
  match Parser.parseModuleP.run { file, toks } with
  | .ok m _ => .ok m
  | .error e _ => .error e

end Naru
