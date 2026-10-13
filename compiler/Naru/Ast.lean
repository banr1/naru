import Naru.Diag

/-!
# Surface AST

構文解析の出力。構文糖を含んだままの木で、Lean には直接落とさない
(型・phase・計算可能性の検査を経て Core IR に下ろす)。
-/

namespace Naru

/-- `A.B.c` のような区切り名。 -/
def renderPath (q : List String) : String := ".".intercalate q

inductive Ty where
  /-- `Name<T1, T2>`。引数なしは `#[]`。 -/
  | named (span : Span) (name : List String) (args : Array Ty)
  /-- `(T1, T2)`。 -/
  | tuple (span : Span) (elems : Array Ty)
  /-- `(T1, T2) -> U`: first-order の関数値の型。fn / observer / predicate … の仮引数と closure の引数にだけ書ける。 -/
  | fn (span : Span) (params : Array Ty) (ret : Ty)

instance : Inhabited Ty := ⟨.tuple default #[]⟩

/-- 型をソースの表記に戻す(`Name<T1, T2>` / `(T1, T2)` / `(T1) -> U`)。言語サーバーのホバー(C29)が署名を見せるのに使う。 -/
partial def Ty.render : Ty → String
  | .named _ name args =>
    renderPath name ++ (if args.isEmpty then "" else "<" ++ ", ".intercalate (args.toList.map Ty.render) ++ ">")
  | .tuple _ elems => "(" ++ ", ".intercalate (elems.toList.map Ty.render) ++ ")"
  | .fn _ params ret => "(" ++ ", ".intercalate (params.toList.map Ty.render) ++ ") -> " ++ ret.render

inductive Lit where
  | nat (n : Nat)
  | str (s : String)
  | bool (b : Bool)
  | unit
deriving Inhabited, Repr, BEq

inductive Quant where
  | forall_
  | exists_
deriving Inhabited, Repr, BEq

/-- lambda / forall / exists の束縛変数。 -/
structure Binder where
  name : String
  ty : Option Ty
  span : Span
deriving Inhabited

mutual
inductive Pattern where
  | wild (span : Span)
  | bind (span : Span) (name : String)
  | lit (span : Span) (l : Lit)
  /-- `Enum.Variant(p1, p2)` / `Some(x)`。 -/
  | ctor (span : Span) (name : List String) (args : Array Pattern)
  | tuple (span : Span) (elems : Array Pattern)

inductive Expr where
  | lit (span : Span) (l : Lit)
  /-- 変数・大域名。大文字で始まる経路(`Phase.Tick`, `Set.empty`)は経路のまま保持する。 -/
  | var (span : Span) (name : List String)
  | call (span : Span) (callee : Expr) (args : Array Arg)
  | field (span : Span) (recv : Expr) (name : String)
  | method (span : Span) (recv : Expr) (name : String) (args : Array Arg)
  | binop (span : Span) (op : String) (lhs rhs : Expr)
  | unop (span : Span) (op : String) (arg : Expr)
  | ite (span : Span) (cond thn els : Expr)
  | matchE (span : Span) (scrut : Expr) (arms : Array Arm)
  | block (span : Span) (stmts : Array Stmt) (tail : Option Expr)
  /-- `Name { f: e, ..base }`。欄は(名前, 名前のトークンの位置, 値)。位置は言語サーバーの欄名のリネーム(C32)が使う。 -/
  | recordLit (span : Span) (name : List String) (fields : Array (String × Span × Expr)) (base : Option Expr)
  | listLit (span : Span) (elems : Array Expr)
  | tupleLit (span : Span) (elems : Array Expr)
  /-- `|x, y| body`。 -/
  | lambda (span : Span) (params : Array Binder) (body : Expr)
  /-- `forall x: T { body }` / `exists x: T { body }`(spec 専用)。 -/
  | quant (span : Span) (q : Quant) (binders : Array Binder) (body : Expr)

inductive Arg where
  | pos (e : Expr)
  /-- `name = e`(`sort(xs, by = …)` 等)。 -/
  | named (name : String) (e : Expr)

inductive Arm where
  | mk (pat : Pattern) (guard : Option Expr) (body : Expr)

inductive Stmt where
  | letS (span : Span) (name : String) (ty : Option Ty) (val : Expr)
  | exprS (e : Expr)
  /-- `input f(x, y) = e;`(scenario の先頭にだけ書ける): 環境の入力 `f` にこの fixture での値を与える。
  仮引数は名前だけ(型は `input` 宣言から取る)。`span` は名前 `f` のトークンの位置(束縛する input への参照の位置でもある)。 -/
  | inputS (span : Span) (name : String) (params : Array (String × Span)) (val : Expr)
  /-- `observe e;`(scenario にだけ書ける): observer の呼出し `e` の値を simulation の出力にする。 -/
  | observeS (span : Span) (e : Expr)
end

instance : Inhabited Pattern := ⟨.wild default⟩
instance : Inhabited Expr := ⟨.lit default .unit⟩
instance : Inhabited Arg := ⟨.pos default⟩
instance : Inhabited Arm := ⟨.mk default none default⟩
instance : Inhabited Stmt := ⟨.exprS default⟩

def Expr.span : Expr → Span
  | .lit s _ | .var s _ | .call s .. | .field s .. | .method s .. | .binop s .. | .unop s ..
  | .ite s .. | .matchE s .. | .block s .. | .recordLit s .. | .listLit s _ | .tupleLit s _
  | .lambda s .. | .quant s .. => s

/-- 式をソースに近い 1 行の文字列にする(`observe` の表示用ラベル)。値・リテラル・呼出し・欄・メソッド・演算・
record / list / tuple literal はそのまま、分岐・ブロック・lambda・量化は `…` に畳む。 -/
partial def renderExpr : Expr → String
  | .lit _ (.nat n) => toString n
  | .lit _ (.str s) =>
    -- 字句の逆(`\n` `\t` `\"` `\\`)で、ソースに書かれた形に戻す
    "\"" ++ (s.foldl (init := "") fun acc ch =>
      acc ++ match ch with
        | '"' => "\\\""
        | '\\' => "\\\\"
        | '\n' => "\\n"
        | '\t' => "\\t"
        | ch => ch.toString) ++ "\""
  | .lit _ (.bool b) => if b then "true" else "false"
  | .lit _ .unit => "()"
  | .var _ segs => renderPath segs
  | .call _ f args => renderExpr f ++ "(" ++ ", ".intercalate (args.toList.map renderArg) ++ ")"
  | .field _ r n => renderExpr r ++ "." ++ n
  | .method _ r n args => renderExpr r ++ "." ++ n ++ "(" ++ ", ".intercalate (args.toList.map renderArg) ++ ")"
  | .binop _ op l r => renderExpr l ++ " " ++ op ++ " " ++ renderExpr r
  | .unop _ op a => op ++ renderExpr a
  | .recordLit _ name fields base =>
    let fs := fields.toList.map fun (f, _, e) => f ++ ": " ++ renderExpr e
    let bs := match base with
      | some b => [".." ++ renderExpr b]
      | none => []
    renderPath name ++ " { " ++ ", ".intercalate (fs ++ bs) ++ " }"
  | .listLit _ es => "[" ++ ", ".intercalate (es.toList.map renderExpr) ++ "]"
  | .tupleLit _ es => "(" ++ ", ".intercalate (es.toList.map renderExpr) ++ ")"
  | .ite .. | .matchE .. | .block .. | .lambda .. | .quant .. => "…"
where
  renderArg : Arg → String
    | .pos e => renderExpr e
    | .named n e => n ++ " = " ++ renderExpr e

structure Param where
  name : String
  ty : Ty
  span : Span
deriving Inhabited

structure Field where
  name : String
  ty : Ty
  span : Span
deriving Inhabited

structure Variant where
  name : String
  args : Array Ty
  span : Span
deriving Inhabited

inductive DeclKind where
  | typeAlias | record | enum | input | fn | state | protocol
  | predicate | condition | regime | property | claim | claimBundle
  | scenario | observer
deriving Inhabited, Repr, BEq, DecidableEq

/-- 宣言の phase。runtime は実行に参加し、spec は検証にだけ参加する。 -/
inductive Phase where
  | runtime
  | spec
deriving Inhabited, Repr, BEq, DecidableEq

def Phase.describe : Phase → String
  | .runtime => "runtime"
  | .spec => "spec"

def DeclKind.phase : DeclKind → Phase
  | .predicate | .condition | .regime | .property | .claim | .claimBundle => .spec
  | _ => .runtime

def DeclKind.isType : DeclKind → Bool
  | .typeAlias | .record | .enum | .state => true
  | _ => false

def DeclKind.describe : DeclKind → String
  | .typeAlias => "type"
  | .record => "record"
  | .enum => "enum"
  | .input => "input"
  | .fn => "fn"
  | .state => "state"
  | .protocol => "protocol"
  | .predicate => "predicate"
  | .condition => "condition"
  | .regime => "regime"
  | .property => "property"
  | .claim => "claim"
  | .claimBundle => "claim bundle"
  | .scenario => "scenario"
  | .observer => "observer"

/-- トップレベル宣言。種類ごとに使う欄が違う(使わない欄は既定値)。 -/
structure Decl where
  kind : DeclKind
  name : String
  span : Span
  /-- fn / input / observer / predicate / … の引数。 -/
  params : Array Param := #[]
  /-- fn / input / observer の戻り型。 -/
  ret : Option Ty := none
  /-- fn / observer / predicate / … / scenario の本体。 -/
  body : Option Expr := none
  /-- `type Name = T` の右辺。 -/
  aliasOf : Option Ty := none
  /-- record / state の欄。 -/
  fields : Array Field := #[]
  /-- enum の variant。 -/
  variants : Array Variant := #[]
  /-- `derive eq, order, …`。 -/
  derives : Array String := #[]
  /-- claim bundle の項目(名前 → claim への参照)。 -/
  items : Array (String × Expr) := #[]
  /-- `protocol P { … }` の中で宣言されたなら `some "P"`。 -/
  owner : Option String := none
deriving Inhabited

structure Module where
  file : String
  name : List String
  nameSpan : Span
  imports : Array (List String)
  decls : Array Decl
deriving Inhabited

end Naru
