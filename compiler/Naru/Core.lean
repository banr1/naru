import Naru.Ast

/-!
# Typed Core IR

型・capability 検査(`Typecheck.lean`)が Surface AST を elaborate して作る、小さな中間表現。
backend(Model / Statements)はこの IR だけを読み、Surface syntax を直接 Lean に落とさない
(IDEAL.md「コンパイラの構造」)。

Surface との違い:
- 名前は解決済み。局所名(`var`)と大域の修飾名(`call` / `global` / `named` / `record` / `variant`)を区別する。
- UFCS(`x.f()`)は `call` に、stdlib メソッドは `method`(受け手の型名 + メソッド名)に、
  組み込みの構築子・静的関数(`Some` / `Set.empty` …)は `builtin` に展開済み。
- 名前付き引数は仮引数の順に並べ替え済み。
- ブロックは `let_` の入れ子(`e;` 文は名前 `_` の `let_`)。
- 型が要る位置(`let` / lambda の引数 / リテラル / 空のコレクション)には解決済みの型を持つ。
  elaboration の終わりにメタ変数が残っていればその宣言は E014(backend には届かない)。
-/

namespace Naru

/-- 内部の型表現。Surface の `Ty` を解決・展開したもの(型別名は展開済み)。 -/
inductive TyV where
  | bool | nat | int | string | unit
  | option (t : TyV)
  | result (t e : TyV)
  | list (t : TyV)
  | set (t : TyV)
  | table (k v : TyV)
  | tuple (ts : List TyV)
  /-- record / state / enum。`key` は大域表の鍵(修飾名)、`display` は表示名。
  `$T` のように `$` で始まる key はメソッド表の型変数。 -/
  | named (key display : String)
  | fn (params : List TyV) (ret : TyV)
  /-- 推論用のメタ変数(Core には残らない)。 -/
  | mvar (n : Nat)
  /-- 既に報告した誤りの波及を抑えるための「不明」。何とでも単一化する(Core には残らない)。 -/
  | unknown
deriving Inhabited

partial def TyV.render : TyV → String
  | .bool => "Bool"
  | .nat => "Nat"
  | .int => "Int"
  | .string => "String"
  | .unit => "Unit"
  | .option t => s!"Option<{t.render}>"
  | .result t e => s!"Result<{t.render}, {e.render}>"
  | .list t => s!"List<{t.render}>"
  | .set t => s!"Set<{t.render}>"
  | .table k v => s!"Table<{k.render}, {v.render}>"
  | .tuple ts => "(" ++ ", ".intercalate (ts.map TyV.render) ++ ")"
  | .named _ d => d
  | .fn ps r => "(" ++ ", ".intercalate (ps.map TyV.render) ++ ") -> " ++ r.render
  | .mvar n => s!"?{n}"
  | .unknown => "_"

/-- 型に現れる大域名(record / state / enum の修飾名)。 -/
partial def TyV.namedKeys : TyV → List String
  | .named k _ => if k.startsWith "$" then [] else [k]
  | .option a | .list a | .set a => a.namedKeys
  | .result a b | .table a b => a.namedKeys ++ b.namedKeys
  | .tuple ts => ts.flatMap TyV.namedKeys
  | .fn ps r => ps.flatMap TyV.namedKeys ++ r.namedKeys
  | _ => []

namespace Core

inductive Pat where
  | wild
  | bind (name : String)
  | lit (l : Lit)
  | tuple (ps : List Pat)
  /-- `Some(p)` / `None` / `Ok(p)` / `Err(p)`。 -/
  | builtin (name : String) (args : List Pat)
  /-- `Enum.Variant(p1, p2)`。`enumKey` は enum の修飾名。 -/
  | variant (enumKey variant : String) (args : List Pat)
deriving Inhabited

mutual
inductive Expr where
  /-- リテラル。数値リテラルは `ty` が `Nat` か `Int`。 -/
  | lit (l : Lit) (ty : TyV)
  /-- 局所名(引数・`let`・lambda・パターン・量化の束縛)。 -/
  | var (name : String)
  /-- fn / input / observer / predicate … の値としての参照(修飾名)。 -/
  | global (key : String)
  /-- fn 等の呼出し。実引数は仮引数の順。 -/
  | call (key : String) (args : List Expr)
  /-- 局所の関数値(lambda・引数)の呼出し。 -/
  | callLocal (f : Expr) (args : List Expr)
  /-- stdlib メソッド(`Set` / `List` / `Option` / `Result` / `Table` / `Nat` / `Int` / `String`)。
  実引数はメソッド表の仮引数の順。`recvTy` は受け手の型(解決済み)。 -/
  | method (tyName name : String) (recv : Expr) (args : List Expr) (recvTy : TyV)
  /-- 組み込みの構築子・静的関数(`Some` `None` `Ok` `Err` `Set.empty` `Set.singleton` `Set.of`
  `List.empty` `List.range` `Table.empty`)。`ty` は結果の型。引数なしで関数として参照したときは `ty` が関数型。 -/
  | builtin (name : String) (args : List Expr) (ty : TyV)
  /-- enum の構築子。引数なしの variant は `args = []`。 -/
  | variant (enumKey variant : String) (args : List Expr)
  /-- record の欄。`recordKey` は record の修飾名。 -/
  | field (recv : Expr) (recordKey name : String)
  /-- 二項演算。`ty` は被演算子の型(解決済み)。 -/
  | binop (op : String) (l r : Expr) (ty : TyV)
  | unop (op : String) (e : Expr)
  | ite (c t e : Expr)
  | match_ (scrut : Expr) (scrutTy : TyV) (arms : List Arm)
  /-- `let name: ty = val; body`。`e;` 文は `name = "_"`。 -/
  | let_ (name : String) (ty : TyV) (val body : Expr)
  /-- record literal / update。欄は宣言の順。 -/
  | record (key : String) (fields : List (String × Expr)) (base : Option Expr)
  /-- `[a, b]`。`elem` は要素の型。 -/
  | list (elems : List Expr) (elem : TyV)
  | tuple (elems : List Expr)
  | lambda (params : List (String × TyV)) (body : Expr)
  /-- 量化(spec 専用)。 -/
  | quant (q : Quant) (binders : List (String × TyV)) (body : Expr)
  /-- 誤りの位置(診断は報告済み。backend には届かない)。 -/
  | error

inductive Arm where
  | mk (pat : Pat) (guard : Option Expr) (body : Expr)
end

instance : Inhabited Expr := ⟨.error⟩
instance : Inhabited Arm := ⟨.mk .wild none .error⟩

structure Param where
  name : String
  ty : TyV
deriving Inhabited

/-- scenario の文(`let` と `observe`。先頭の input 束縛は `Decl.scenario` の `inputs`)。 -/
inductive ScenarioStmt where
  | let_ (name : String) (ty : TyV) (val : Expr)
  /-- `observe e;`。`label` は表示用のソース文字列、`ty` は observer の戻り型(解決済み)、`e` は observer の呼出し(`call`)。 -/
  | observe (label : String) (ty : TyV) (e : Expr)
deriving Inhabited

/-- トップレベル宣言(解決・型付け済み)。`key` は修飾名、`name` は単純名。 -/
inductive Decl where
  | typeAlias (key name : String) (ty : TyV)
  /-- record / state。欄は宣言の順。 -/
  | record (key name : String) (isState : Bool) (fields : List (String × TyV)) (derives : List String)
  | enum (key name : String) (variants : List (String × List TyV)) (derives : List String)
  /-- fn / input(本体なし)/ observer / predicate / condition / regime / property / claim。 -/
  | fn (key name : String) (kind : DeclKind) (params : List Param) (ret : TyV) (body : Option Expr)
  /-- scenario。`inputs` は先頭の `input f(x) = e;`(input の修飾名、仮引数と型、値)をソースの順に、
  `stmts` は続く `let` / `observe`。閉じた scenario(本体が使う input はすべて `inputs` にある)だけが backend に届く。 -/
  | scenario (key name : String) (inputs : List (String × List (String × TyV) × Expr)) (stmts : List ScenarioStmt)
  /-- claim bundle。項目名 → claim(または入れ子の bundle)の修飾名。 -/
  | claimBundle (key name : String) (items : List (String × String))
deriving Inhabited

def Decl.key : Decl → String
  | .typeAlias k .. | .record k .. | .enum k .. | .fn k .. | .scenario k .. | .claimBundle k .. => k

def Decl.name : Decl → String
  | .typeAlias _ n .. | .record _ n .. | .enum _ n .. | .fn _ n .. | .scenario _ n .. | .claimBundle _ n .. => n

def Decl.kind : Decl → DeclKind
  | .typeAlias .. => .typeAlias
  | .record _ _ isState .. => if isState then .state else .record
  | .enum .. => .enum
  | .fn _ _ k .. => k
  | .scenario .. => .scenario
  | .claimBundle .. => .claimBundle

def Decl.phase (d : Decl) : Phase := d.kind.phase

structure Module where
  file : String
  name : List String
  decls : Array Decl
deriving Inhabited

-- 式が参照する大域名(fn / input / 型 / enum / record の修飾名)。重複あり、出現順。
mutual
partial def Expr.refs : Expr → List String
  | .lit _ ty => ty.namedKeys
  | .var _ => []
  | .global k => [k]
  | .call k args => k :: args.flatMap Expr.refs
  | .callLocal f args => f.refs ++ args.flatMap Expr.refs
  | .method _ _ recv args recvTy => recvTy.namedKeys ++ recv.refs ++ args.flatMap Expr.refs
  | .builtin _ args ty => ty.namedKeys ++ args.flatMap Expr.refs
  | .variant k _ args => k :: args.flatMap Expr.refs
  | .field recv k _ => k :: recv.refs
  | .binop _ l r ty => ty.namedKeys ++ l.refs ++ r.refs
  | .unop _ e => e.refs
  | .ite c t e => c.refs ++ t.refs ++ e.refs
  | .match_ s sty arms => sty.namedKeys ++ s.refs ++ arms.flatMap Arm.refs
  | .let_ _ ty v b => ty.namedKeys ++ v.refs ++ b.refs
  | .record k fs base => k :: fs.flatMap (·.2.refs) ++ (base.map Expr.refs).getD []
  | .list es ty => ty.namedKeys ++ es.flatMap Expr.refs
  | .tuple es => es.flatMap Expr.refs
  | .lambda ps b => ps.flatMap (·.2.namedKeys) ++ b.refs
  | .quant _ bs b => bs.flatMap (·.2.namedKeys) ++ b.refs
  | .error => []

partial def Arm.refs : Arm → List String
  | .mk p g b => Pat.refs p ++ (g.map Expr.refs).getD [] ++ b.refs

partial def Pat.refs : Pat → List String
  | .variant k _ args => k :: args.flatMap Pat.refs
  | .builtin _ args | .tuple args => args.flatMap Pat.refs
  | _ => []
end

def ScenarioStmt.refs : ScenarioStmt → List String
  | .let_ _ ty v => ty.namedKeys ++ v.refs
  | .observe _ ty e => ty.namedKeys ++ e.refs

/-- 宣言が参照する大域名(署名と本体)。重複あり。scenario は束縛した input の修飾名も含む。 -/
def Decl.refs : Decl → List String
  | .typeAlias _ _ ty => ty.namedKeys
  | .record _ _ _ fields _ => fields.flatMap (·.2.namedKeys)
  | .enum _ _ variants _ => variants.flatMap fun (_, ts) => ts.flatMap TyV.namedKeys
  | .fn _ _ _ params ret body =>
    params.flatMap (·.ty.namedKeys) ++ ret.namedKeys ++ (body.map Expr.refs).getD []
  | .scenario _ _ inputs stmts =>
    inputs.flatMap (fun (k, ps, v) => k :: ps.flatMap (·.2.namedKeys) ++ v.refs) ++ stmts.flatMap ScenarioStmt.refs
  | .claimBundle _ _ items => items.map (·.2)

end Core

end Naru
