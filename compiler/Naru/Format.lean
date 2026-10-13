import Naru.Lexer

/-!
# 整形(`naru lsp` の `textDocument/formatting`、IDEAL.md C33)

字句列から正規形を印字し直す。字句(識別子・予約語・数・文字列・記号)とコメントの内容、字句の間の改行の有無(書き手の行分け)は
変えず、字下げ・行の中の空白・空行の数・ファイル末尾の改行だけを正規形にする。空白と改行は意味を持たない(`docs/language.md`
「字句」)ので、整形は字句列(したがって意味)を変えない。整形は冪等(整形済みの本文を整形しても変わらない)。

正規形:
- 字下げは 2 空白(タブは使わない)。行の字下げはその行の先頭の字句で決まる:
  - 閉じ括弧 `}` / `)` / `]` で始まる行は、対応する開き括弧の anchor(下)。
  - 二項演算子(`&&` `||` `implies` `==` `!=` `<` … `+` `-` `*` `/` `%`、`=`、`=>`、`.`)で始まる行(式の続き)は、同じ深さの直前の
    行が自分より弱い演算子で始まる行(`implies …` の次の `|| …`: その演算子の右の被演算子の続き)ならその行の字下げ + 2、そうで
    なければ同じ深さで直前の「式の頭」の行(演算子でも閉じ括弧でも始まらない行)の字下げ + 2(頭が `if` で始まる行なら + 4: 条件の
    続きを本体と区別する)。頭が無ければ(括弧の内容の最初の行)その括弧の anchor + 2。`->` で始まる行(署名の戻り型の続き)は + 4。
  - `else` で始まる行は直前の行と同じ。
  - 直前の行が二項演算子(または lambda の閉じ `|`)で終わる行(その続き)は、直前の行の字下げ + 2。
  - それ以外は、いちばん内側の開き括弧の「内容の列」: 行末の開き括弧(ぶら下がり)なら anchor + 2、行の途中の開き括弧なら
    その括弧の次の列(引数の並びを揃える)。深さ 0 は 0。
  - 開き括弧の anchor: 行の途中の開き括弧ならその括弧の列。ぶら下がりなら、それを開いた式の行の anchor(行の字下げ。行が演算子で
    始まり、その次の字句が `forall` / `exists` / `match` / `if` / `(` ならその字句の列: `&& forall v: T {` の本体はそこから + 2)。
    行が `->` で始まる(署名の戻り型の続き)、演算子で始まるがその次の字句が上のどれでもない(`if` の条件の続き `&& c {`)、閉じ括弧で
    始まる(`} else {`)、その開き括弧より前に別の行で開いた括弧がこの行で閉じている(`fn f(a: T,\n    b: T) {`)なら、同じ深さの
    直前の式の頭の行(`fn` / `if` の行)の anchor。
  - コメントだけの行は、いちばん内側の開き括弧の内容の列。
- 行の中の空白: 二項演算子・`=`・`=>`・`->` の前後に 1 つ、`,` `;` `:` の後に 1 つ(前は無し)、`(` `[` の内側と `.` の前後、
  `!` と単項 `-` の後、lambda の `|…|` の内側、呼出しの名前と `(` の間は無し、`{` `}` の内側は 1 つ(`{}` は無し)、型引数の
  `<` `>`(`List<…>` / `Set<…>` / `Option<…>` / `Result<…>` / `Table<…>`)の内側と前後は無し、行末コメントの前に 1 つ。
  文字列リテラルとコメントの中はそのまま。
- 改行: 字句の間の改行の有無は変えない(行を分ける・つなぐことはしない)。連続する空行は 1 つに、開き括弧の直後と閉じ括弧の
  直前の空行は無し、先頭の空行は無し、末尾は改行 1 つ。行末の空白は無し。複数行のブロックコメントの 2 行目以降はそのまま。
  宣言コメント(C60: 宣言の直上の `//` ブロック)と宣言の間に空行は入れない(空行の挿入はしない)。

字句解析に失敗する本文(未終了の文字列・ブロックコメント、未知の文字: E010)は整形しない(`format` はその診断を返す)。
-/

namespace Naru.Format

inductive Kind where
  | ident | kw | nat | str | sym | lineComment | blockComment
deriving Repr, BEq, Inhabited

/-- 整形の単位: 字句かコメント。`text` は元の本文(行コメントは行末の空白を除く)。 -/
structure Piece where
  kind : Kind
  text : String
  /-- 直前の piece との間の改行の数(0 なら同じ行)。 -/
  nlBefore : Nat
deriving Repr, Inhabited

def Piece.isSym (p : Piece) (s : String) : Bool := p.kind == .sym && p.text == s
def Piece.isKw (p : Piece) (s : String) : Bool := p.kind == .kw && p.text == s
def Piece.isComment (p : Piece) : Bool := p.kind == .lineComment || p.kind == .blockComment
def Piece.isOpener (p : Piece) : Bool := p.kind == .sym && (p.text == "(" || p.text == "[" || p.text == "{")
def Piece.isCloser (p : Piece) : Bool := p.kind == .sym && (p.text == ")" || p.text == "]" || p.text == "}")

/-- 行の先頭 / 末尾にあれば「式の続き」とみなす二項演算子(`implies` を含む)。 -/
def binaryOps : List String := ["+", "-", "*", "/", "%", "==", "!=", "<", ">", "<=", ">=", "&&", "||", "=", "=>", "->", "."]

def Piece.isBinaryOp (p : Piece) : Bool := (p.kind == .sym && binaryOps.contains p.text) || p.isKw "implies"

/-- 二項演算子の強さ(大きいほど強く結びつく。`docs/language.md`「式」の順)。 -/
def prec : String → Nat
  | "implies" => 1
  | "||" => 2
  | "&&" => 3
  | "==" | "!=" | "<" | ">" | "<=" | ">=" => 4
  | "+" | "-" => 5
  | "*" | "/" | "%" => 6
  | "." => 7
  | _ => 0

/-- 型引数を取る組み込みの型(この名前の直後の `<` は比較でなく型引数の括弧)。 -/
def genericHeads : List String := ["List", "Set", "Option", "Result", "Table"]

/-! ## 字句とコメントの列 -/

def slice (src : Array Char) (i j : Nat) : String := String.ofList (src.extract i j).toList

def lineStarts (src : Array Char) : Array Nat := Id.run do
  let mut out := #[0]
  for i in [0:src.size] do
    if src[i]! == '\n' then out := out.push (i + 1)
  return out

/-- `start` から始まる字句の終わり(排他的)。字句解析と同じ切り方。 -/
def tokenEnd (src : Array Char) (start : Nat) : TokenKind → Nat
  | .ident s | .kw s | .sym s => start + s.length
  | .nat _ => Id.run do
    let mut i := start
    while i < src.size && (src[i]!).isDigit do i := i + 1
    return i
  | .str _ => Id.run do
    let mut i := start + 1
    while i < src.size && src[i]! != '"' do
      i := i + (if src[i]! == '\\' then 2 else 1)
    return min (i + 1) src.size
  | .eof => start

/-- `/*` の直後 `i` から、入れ子を数えて閉じ `*/` の直後を返す(字句解析が閉じを確かめている)。 -/
partial def blockEnd (src : Array Char) (i depth : Nat) : Nat :=
  if i ≥ src.size then src.size
  else if src[i]! == '*' && src[i + 1]? == some '/' then
    if depth == 1 then i + 2 else blockEnd src (i + 2) (depth - 1)
  else if src[i]! == '/' && src[i + 1]? == some '*' then blockEnd src (i + 2) (depth + 1)
  else blockEnd src (i + 1) depth

/-- `i` から `stop`(次の字句の先頭)までの空白とコメントを読む。コメントは piece にし、返すのは次の字句の前の改行の数。 -/
partial def scanTrivia (src : Array Char) (i stop nl : Nat) (acc : Array Piece) : Nat × Array Piece :=
  if i ≥ stop then (nl, acc)
  else
    let c := src[i]!
    if c == '\n' then scanTrivia src (i + 1) stop (nl + 1) acc
    else if c.isWhitespace then scanTrivia src (i + 1) stop nl acc
    else if c == '/' && src[i + 1]? == some '/' then
      let j := Id.run do
        let mut j := i
        while j < stop && src[j]! != '\n' do j := j + 1
        return j
      let k := Id.run do
        let mut k := j
        while k > i && (src[k - 1]!).isWhitespace do k := k - 1
        return k
      scanTrivia src j stop 0 (acc.push { kind := .lineComment, text := slice src i k, nlBefore := nl })
    else if c == '/' && src[i + 1]? == some '*' then
      let j := blockEnd src (i + 2) 1
      scanTrivia src j stop 0 (acc.push { kind := .blockComment, text := slice src i j, nlBefore := nl })
    else scanTrivia src (i + 1) stop nl acc

/-- 字句解析の結果から、字句とコメントの列(ソースの順)を作る。 -/
def pieces (src : Array Char) (toks : Array Token) : Array Piece := Id.run do
  let starts := lineStarts src
  let mut acc : Array Piece := #[]
  let mut pos := 0
  for t in toks do
    let start := (starts[t.span.line - 1]?).getD 0 + (t.span.col - 1)
    let (nl, acc') := scanTrivia src pos start 0 acc
    acc := acc'
    match t.kind with
    | .eof => pure ()
    | k =>
      let e := tokenEnd src start k
      let kind : Kind := match k with
        | .ident _ => .ident
        | .kw _ => .kw
        | .nat _ => .nat
        | .str _ => .str
        | _ => .sym
      acc := acc.push { kind, text := slice src start e, nlBefore := nl }
      pos := e
  return acc

/-! ## 印字 -/

/-- 行の中での字句の役割(空白の規則が見る)。 -/
inductive Role where
  | plain | genericOpen | genericClose | lambdaOpen | lambdaClose | unaryMinus | prefixNot
deriving BEq, Repr, Inhabited

/-- 開いている括弧。`anchor` は閉じ括弧で始まる行の字下げ、`contentCol` は内容の行の字下げ。 -/
structure Frame where
  anchor : Nat
  contentCol : Nat
deriving Repr, Inhabited

/-- 印字した行の情報(後の行の字下げが見る)。 -/
structure LineInfo where
  /-- 行の先頭での括弧の深さ。 -/
  startDepth : Nat := 0
  indent : Nat := 0
  /-- 行の anchor: 字下げ、または行が演算子で始まるならその次の字句の列。 -/
  anchor : Nat := 0
  /-- 先頭の字句の本文。 -/
  firstText : String := ""
  firstIsOp : Bool := false
  firstIsArrow : Bool := false
  firstIsCloser : Bool := false
  /-- 演算子で始まる行の、演算子の次の字句が `forall` / `exists` / `match` / `if` / `(`(その字句がぶら下がりの括弧を持つ)。 -/
  operandBlock : Bool := false
  /-- コメントだけの行でない。 -/
  isCode : Bool := false
  /-- 最後の字句(コメントを除く)が二項演算子か lambda の閉じ `|`。 -/
  endsWithOp : Bool := false
deriving Repr, Inhabited

/-- 被演算子の終わりになれる字句(この直後の `-` は二項、`|` は lambda の開きでない)。 -/
def operandEnd (p : Piece) (r : Role) : Bool :=
  match p.kind with
  | .ident | .nat | .str => true
  | .kw => p.text == "true" || p.text == "false"
  | .sym => p.text == ")" || p.text == "]" || p.text == "}" || p.text == "?" || r == .genericClose
  | _ => false

/-- 空白を挟まないと 1 つの字句に読まれてしまう組: 記号の末尾と次の記号の先頭が 2 文字記号(`-` と `>` → `->`、`!` と `=` → `!=`、`|` と `|`、
`.` と `..` …)、識別子・予約語と `?`(`find?`)。整形は字句列を変えないので、これらには必ず空白を置く。 -/
def mergesInto (prev next : Piece) : Bool :=
  (prev.kind == .sym && next.kind == .sym &&
    (match prev.text.toList.getLast?, next.text.toList.head? with
     | some a, some b => symbols2.contains (String.ofList [a, b])
     | _, _ => false))
  || ((prev.kind == .ident || prev.kind == .kw) && next.isSym "?")

/-- 同じ行の直前の字句 `prev`(役割 `pr`)と次の字句 `next`(役割 `nr`)の間に空白を置くか。 -/
def spaceBetween (prev : Piece) (pr : Role) (next : Piece) (nr : Role) : Bool :=
  if next.isComment then true
  else if prev.kind == .blockComment then true
  else if mergesInto prev next then true
  else if prev.isSym "(" || prev.isSym "[" then false
  else if pr == .genericOpen || pr == .lambdaOpen || pr == .prefixNot || pr == .unaryMinus then false
  else if prev.isSym "." || prev.isSym ".." then false
  else if prev.isSym "{" then !next.isSym "}"
  else if next.isSym ")" || next.isSym "]" || next.isSym "," || next.isSym ";" || next.isSym "." || next.isSym "?" || next.isSym ":" then false
  else if nr == .genericOpen || nr == .genericClose || nr == .lambdaClose then false
  else if next.isSym "(" then
    !(prev.kind == .ident || prev.isSym ")" || prev.isSym "]" || prev.isSym "?" || pr == .genericClose)
  else true

/-- 字句の役割。`prev` は同じ行の直前の字句(行頭なら none)。 -/
def roleOf (prev : Option (Piece × Role)) (genDepth : Nat) (lambdaOpen : Bool) (p : Piece) : Role :=
  if p.isSym "<" then
    match prev with
    | some (q, _) => if q.kind == .ident && genericHeads.contains q.text then .genericOpen else .plain
    | none => .plain
  else if p.isSym ">" then (if genDepth > 0 then .genericClose else .plain)
  else if p.isSym "|" then
    if lambdaOpen then .lambdaClose
    else match prev with
      | some (q, r) => if operandEnd q r then .plain else .lambdaOpen
      | none => .lambdaOpen
  else if p.isSym "-" then
    match prev with
    | some (q, r) => if operandEnd q r then .plain else .unaryMinus
    | none => .plain
  else if p.isSym "!" then .prefixNot
  else .plain

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- 深さ `d` の式の頭の行(同じ深さで、演算子でも閉じ括弧でも始まらない直近の行)。深さがそれより浅い行に当たったら無し。 -/
def headLine (lines : Array LineInfo) (d : Nat) : Option LineInfo := Id.run do
  let mut i := lines.size
  while i > 0 do
    i := i - 1
    let l := lines[i]!
    if l.startDepth < d then return none
    if l.startDepth == d && l.isCode && !l.firstIsOp && !l.firstIsCloser then return some l
  return none

/-- 深さ `d` で始まる直近の行(深い行は飛ばす。浅い行に当たったら無し)。 -/
def prevSameDepth (lines : Array LineInfo) (d : Nat) : Option LineInfo := Id.run do
  let mut i := lines.size
  while i > 0 do
    i := i - 1
    let l := lines[i]!
    if l.startDepth < d then return none
    if l.startDepth == d then return some l
  return none

/-- 深さ `s` で開いたぶら下がりの括弧の anchor になる行(現在の行より前。同じ深さで始まる直近の式の頭の行: 演算子でも閉じ括弧でも
始まらない行。`if c\n    && d {` の `{` と `} else {` の `{` はどちらも `if` の行)。 -/
def ownerLine (lines : Array LineInfo) (s : Nat) : Option LineInfo := Id.run do
  let mut i := lines.size
  while i > 0 do
    i := i - 1
    let l := lines[i]!
    if l.startDepth < s then return none
    if l.startDepth == s && l.isCode && !l.firstIsOp && !l.firstIsCloser then return some l
  return none

/-- 字句とコメントの列を正規形に印字する。 -/
def layout (ps : Array Piece) : String := Id.run do
  let n := ps.size
  -- 各 piece が、その行の最後の字句(コメントを除く)か(開き括弧のぶら下がりの判定)
  let mut lastCode : Array Bool := Array.replicate n false
  let mut lastIdx : Option Nat := none
  for i in [0:n] do
    if i > 0 && ps[i]!.nlBefore > 0 then
      if let some j := lastIdx then lastCode := lastCode.set! j true
      lastIdx := none
    if !ps[i]!.isComment then lastIdx := some i
  if let some j := lastIdx then lastCode := lastCode.set! j true
  let mut out := ""
  let mut lines : Array LineInfo := #[]
  let mut stack : Array Frame := #[]
  let mut cur : LineInfo := {}
  let mut pieceIdx := 0          -- 行の中の何番目の piece か
  let mut col := 0
  let mut prev : Option (Piece × Role) := none
  let mut prevPiece : Option Piece := none
  let mut genDepth := 0
  let mut lambdaOpen := false
  for i in [0:n] do
    let p := ps[i]!
    if i == 0 || p.nlBefore > 0 then
      -- 行の終わりと空行
      if i > 0 then
        lines := lines.push cur
        let afterOpener := (prevPiece.map (·.isOpener)).getD false
        let k := if afterOpener || p.isCloser then 1 else min p.nlBefore 2
        out := out ++ String.ofList (List.replicate k '\n')
      -- 新しい行の字下げ
      let d := stack.size
      let top := stack.back?
      let contentCol := (top.map (·.contentCol)).getD 0
      let prevCode := lines.findRev? (·.isCode)
      let indent :=
        if p.isCloser then (top.map (·.anchor)).getD 0
        else if p.isComment then contentCol
        else if p.isKw "else" then (prevCode.map (·.indent)).getD contentCol
        else if (prevCode.map (·.endsWithOp)).getD false then (prevCode.map (·.indent)).getD 0 + 2
        else if p.isBinaryOp then
          -- 直前の同じ深さの行が自分より弱い演算子で始まる(`implies …` の次の `|| …`)なら、その右の被演算子の続き
          let weaker := match prevSameDepth lines d with
            | some l => l.isCode && l.firstIsOp && !l.firstIsArrow && prec l.firstText < prec p.text
            | none => false
          if weaker then ((prevSameDepth lines d).map (·.indent)).getD 0 + 2
          else
            let (base, plus) := match headLine lines d with
              | some h => (h.indent, if h.firstText == "if" then 4 else 2)
              | none => ((top.map (·.anchor)).getD 0, 2)
            base + (if p.isSym "->" then 4 else plus)
        else contentCol
      let firstIsOp := p.isBinaryOp
      cur := { startDepth := d, indent, anchor := if firstIsOp then indent + p.text.length + 1 else indent,
               firstText := p.text, firstIsOp, firstIsArrow := p.isSym "->", firstIsCloser := p.isCloser }
      pieceIdx := 0
      out := out ++ spaces indent
      col := indent
      prev := none
      lambdaOpen := false
    else
      let r := roleOf prev genDepth lambdaOpen p
      let sp := match prev with
        | some (q, qr) => spaceBetween q qr p r
        | none => false
      if sp then
        out := out ++ " "
        col := col + 1
    let r := roleOf prev genDepth lambdaOpen p
    out := out ++ p.text
    if p.kind == .blockComment && (p.text.splitOn "\n").length > 1 then
      col := ((p.text.splitOn "\n").getLast? |>.getD "").length
    else
      col := col + p.text.length
    if !p.isComment then
      cur := { cur with isCode := true, endsWithOp := (p.isBinaryOp && r == .plain) || r == .lambdaClose }
      if pieceIdx == 1 && cur.firstIsOp then
        cur := { cur with operandBlock := p.isKw "forall" || p.isKw "exists" || p.isKw "match" || p.isKw "if" || p.isSym "(" }
      if p.isOpener then
        let s := stack.size
        let openerCol := col - p.text.length
        let hanging := lastCode[i]!
        let anchor :=
          if !hanging then openerCol
          else if cur.startDepth < s then cur.anchor
          else if cur.startDepth == s && (!cur.firstIsOp || (cur.operandBlock && !cur.firstIsArrow)) then cur.anchor
          else ((ownerLine lines s).map (·.anchor)).getD cur.anchor
        stack := stack.push { anchor, contentCol := if hanging then anchor + 2 else openerCol + 1 }
      else if p.isCloser then
        stack := stack.pop
      if r == .genericOpen then genDepth := genDepth + 1
      if r == .genericClose then genDepth := genDepth - 1
      if r == .lambdaOpen then lambdaOpen := true
      if r == .lambdaClose then lambdaOpen := false
    prev := some (p, r)
    prevPiece := some p
    pieceIdx := pieceIdx + 1
  if n > 0 then out := out ++ "\n"
  return out

/-- 本文 `src` の正規形。字句解析に失敗したら(E010)その診断。整形後の本文を字句解析し直して字句の列が元と違えば(`mergesInto` の守りが
あるので起きない想定の安全網)整形せず診断を返す。 -/
def format (file src : String) : Except Diagnostic String := do
  let toks ← lexAll file src
  let out := layout (pieces src.toList.toArray toks)
  match lexAll file out with
  | .ok toks' =>
    if toks.map (·.kind) == toks'.map (·.kind) then return out
    else throw { file, span := { line := 1, col := 1 }, code := Code.syntaxError,
                 msg := "internal: formatting would change the token sequence; the document was not formatted" }
  | .error d => throw { d with msg := s!"internal: the formatted text does not lex ({d.msg}); the document was not formatted" }

end Naru.Format
