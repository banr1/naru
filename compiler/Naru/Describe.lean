import Naru.Ast

/-!
# 宣言の表示と宣言コメントの読み(IDEAL.md C29 / C60)

- `Decl.signature`: 宣言を naru の文法で 1 行に戻す(fn / input / observer / spec 宣言なら仮引数と戻り型、record / state なら欄と `derive`、
  enum なら variant と `derive`、type なら右辺、claim bundle なら項目名)。言語サーバーのホバー(C29)が「宣言の種類と型」として見せる。
- 宣言コメント(IDEAL.md 用語「宣言コメント」): 宣言の直上に空行を挟まず続く `//` の連続ブロック。`declLine?` が名前のトークンの行から
  種類のキーワードで始まる行まで遡って宣言の行を決め、`commentAbove` がその直上のブロックを本文(`//` と前後の空白を除く)として読む。
  `naru_test repo` の C60 / C61 の検査と `naru lsp` のホバー(C29)が同じ読み方を使う。
- `escapeMarkdown`: コメントの行を Markdown の本文にするとき、バッククォートの外の `\ * _ [ ] < > #` を逃がす(比較の `<` / `>` や添字の
  `_` が HTML や強調に読まれないように)。
-/

namespace Naru

def Param.render (p : Param) : String := s!"{p.name}: {p.ty.render}"

/-- `{ a, b }`(空なら `{ }`)。 -/
def braces (xs : List String) : String :=
  if xs.isEmpty then "{ }" else "{ " ++ ", ".intercalate xs ++ " }"

/-- enum の variant をソースの表記に(`At(Time)`)。 -/
def Variant.render (v : Variant) : String :=
  v.name ++ (if v.args.isEmpty then "" else "(" ++ ", ".intercalate (v.args.toList.map Ty.render) ++ ")")

/-- 宣言を naru の文法で 1 行に戻す(本体は含めない)。 -/
def Decl.signature (d : Decl) : String :=
  let params := "(" ++ ", ".intercalate (d.params.toList.map Param.render) ++ ")"
  let ret := match d.ret with
    | some t => s!" -> {t.render}"
    | none => ""
  let derives := if d.derives.isEmpty then "" else " derive " ++ ", ".intercalate d.derives.toList
  match d.kind with
  | .typeAlias =>
    s!"type {d.name}" ++ (match d.aliasOf with
      | some t => s!" = {t.render}"
      | none => "")
  | .record | .state =>
    s!"{d.kind.describe} {d.name} " ++ braces (d.fields.toList.map fun f => s!"{f.name}: {f.ty.render}") ++ derives
  | .enum =>
    s!"enum {d.name} " ++ braces (d.variants.toList.map Variant.render) ++ derives
  | .claimBundle => s!"claim bundle {d.name} " ++ braces (d.items.toList.map (·.1))
  | .protocol | .scenario => s!"{d.kind.describe} {d.name}"
  | _ => s!"{d.kind.describe} {d.name}{params}{ret}"

/-! ## 宣言コメント -/

/-- 行が `//` のコメントなら、`//` と前後の空白を落とした本文。 -/
def commentBody (l : String) : Option String :=
  let t := l.trimAscii.toString
  if t.startsWith "//" then some ((t.drop 2).toString.trimAscii.toString) else none

/-- 宣言の行か: 字下げを除いて種類のキーワードで始まる(`claim` は `claim bundle` と区別する)。 -/
def startsDecl (kind : DeclKind) (l : String) : Bool :=
  let t := l.trimAscii.toString
  match kind with
  | .claim => t.startsWith "claim " && !(t.startsWith "claim bundle ")
  | k => t.startsWith (k.describe ++ " ")

/-- 宣言の行(1 始まり): 名前のトークンの行(`Decl.span`)から、種類のキーワードで始まる行まで(最大 3 行)遡る。無ければ none。 -/
def declLine? (lines : Array String) (d : Decl) : Option Nat := Id.run do
  let mut l := d.span.line
  let mut tries := 0
  while l ≥ 1 && tries < 4 do
    if l ≤ lines.size && startsDecl d.kind lines[l - 1]! then return some l
    l := l - 1
    tries := tries + 1
  return none

/-- 行 `l`(1 始まり)の直上に空行を挟まず続く `//` の連続ブロックの本文(上から順)。 -/
def commentAbove (lines : Array String) (l : Nat) : List String := Id.run do
  let mut i := l - 1
  let mut block : List String := []
  while i ≥ 1 && i ≤ lines.size do
    match commentBody lines[i - 1]! with
    | some b =>
      block := b :: block
      i := i - 1
    | none => break
  return block

/-- 宣言コメント: 宣言の行の直上のブロック。宣言の行が決まらなければ空。 -/
def declComment (lines : Array String) (d : Decl) : List String :=
  match declLine? lines d with
  | some l => commentAbove lines l
  | none => []

/-- record の欄・enum の variant の 1 行の説明(その行の直上のブロック)。宣言の行と同じ行にある欄 / variant には無い
(直上は宣言コメントになるので取らない)。 -/
def memberComment (lines : Array String) (d : Decl) (memberLine : Nat) : List String :=
  if declLine? lines d == some memberLine then [] else commentAbove lines memberLine

/-- コメントの行を Markdown の本文にする: バッククォートの外の `\ * _ [ ] < > #` をバックスラッシュで逃がす。 -/
def escapeMarkdown (s : String) : String := Id.run do
  let mut out := ""
  let mut inCode := false
  for c in s.toList do
    if c == '`' then
      inCode := !inCode
      out := out.push c
    else if !inCode && "\\*_[]<>#".contains c then
      out := (out.push '\\').push c
    else
      out := out.push c
  return out

/-- 宣言コメントの Markdown: 1 行目(要旨)を 1 つの段落、2 行目以降を行ごとに改行(行末の 2 空白)でつないだ段落
(空のコメント行は段落の区切り)。 -/
def commentMarkdown (block : List String) : String :=
  match block with
  | [] => ""
  | head :: rest =>
    let paragraphs := (rest.splitBy fun a b => !a.isEmpty && !b.isEmpty).filter (fun p => !(p.all (·.isEmpty)))
    let body := paragraphs.map fun p => "  \n".intercalate ((p.filter (!·.isEmpty)).map escapeMarkdown)
    "\n\n".intercalate (escapeMarkdown head :: body)

end Naru
