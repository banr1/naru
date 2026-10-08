import Std.Data.HashMap
import Std.Data.HashSet
import Naru.Core
import Naru.Totality

/-!
# Model backend — Core IR → Lean(`generated/Model`)

runtime 宣言(type / record / state / enum / input / fn / observer / scenario)だけを Lean に落とす。
spec 宣言(predicate / … / claim bundle)は Statements backend の仕事で、ここでは出力しない。

出力の規則(決定性のため、表に依存する順序は使わず、ソースの順と名前の順だけで並べる):
- naru モジュール `A.B` → Lean モジュール `Model.A.B`(ファイル `Model/A/B.lean`)。宣言は `Model.A.B.name` と
  完全修飾で参照する(Lean core の名前と衝突しない)。モジュール同士の参照は `import` になるので循環は E017。
- 1 モジュールの中では宣言を依存順に並べる。互いに参照する宣言(相互再帰の enum / fn)は `mutual … end`。
- 型: `Nat` `Int` `Bool` `String` `Unit` はそのまま、`Option<T>` → `Option T`、`List<T>` → `List T`、
  `Result<T, E>` → `NaruStd.Result T E`、`Set<T>` → `NaruStd.Set T`、`Table<K, V>` → `NaruStd.Table K V`、
  tuple → `×`。型別名は展開済み(`abbrev` も出すが参照は展開した型で書く)。
- `derive eq` → `DecidableEq` と `Ord`(`Set` / `Table` の正規化に使う隠れた全順序。宣言の欄・variant の順の辞書式)、
  `derive order` → `Ord`。`Repr` は常に生成する(simulate の表示用)。`finite` はまだ何も生成しない。
- `input` は Lean の宣言にならない。それを(推移的に)使う fn / observer / scenario の先頭の引数
  `name'`(naru の名前 + `'`)になり、呼出しで引き回す。
- 再帰(`Totality` が受理したもの): 明示 fuel は `termination_by n` と `decreasing_by`、構造的再帰は
  `termination_by structural p`。再帰する fn の `if` は `if _h' : c then` にして分岐の事実を証明に残し(`_h'` は naru で書けない名前)、
  `Nat` の `match` の bind / `_` の腕は `n@(_ + m)`(m = 先行するガード無しリテラル腕が 0 から覆った値の次)に
  落として `n ≥ m` を残す(`match _hm' : n with` の等式経由)。
- `match` の腕のガードは Lean に無いので、`| p => if g then body else REST` と `| _ => REST`
  (REST = 残りの腕の match)に落とす(ガード 1 つにつき残りの腕が 2 回現れる)。
- 比較: `Nat` / `Int` / `String` は `Decidable.decide (a < b)`、他は `Ord.compare a b == .lt` 等(`Ord` だけで決める)。
- 生成コードが使う Lean の組み込み名は完全修飾(`Option.some` / `Ord.compare` …)し、naru の局所名・欄名は常に `«»` で
  囲む。naru の局所名が生成コードの名前を捕獲しない。
-/

namespace Naru.Backend.Model
open Std

/-- 生成ファイルの先頭コメントに入れる版と hash。 -/
structure Meta where
  compilerVersion : String
  /-- コンパイラのソース(`compiler/**/*.lean`)の hash。 -/
  compilerHash : String
  stdlibVersion : String
  stdlibHash : String
  /-- コンパイル単位(全ソース)の hash。 -/
  unitHash : String
  /-- ソースファイル → sha256。 -/
  fileHashes : List (String × String)

structure Env where
  decls : HashMap String Core.Decl := {}
  moduleOf : HashMap String (List String) := {}
  /-- fn / observer / scenario の修飾名 → 推移的に使う input の修飾名(名前順)。 -/
  inputs : HashMap String (List String) := {}
  /-- 再帰する fn の修飾名 → (成分の fn、測度の仮引数の位置、成分に Nat の測度があるか)。 -/
  recs : HashMap String (List String × Nat × Bool) := {}

/-! ## 名前 -/

/-- Lean の予約語(naru の識別子として書けるもの)。`«»` で囲んで逃がす。 -/
def leanKeywords : List String :=
  ["at", "by", "do", "else", "end", "from", "fun", "have", "if", "in", "let", "match", "mut", "open",
   "partial", "private", "protected", "public", "return", "show", "structure", "then", "this", "unsafe",
   "variable", "where", "with", "instance", "class", "deriving", "theorem", "lemma", "def", "abbrev",
   "inductive", "coinductive", "namespace", "section", "import", "export", "universe", "axiom", "example",
   "local", "scoped", "notation", "macro", "macro_rules", "syntax", "elab", "elab_rules", "meta", "opaque",
   "noncomputable", "nonrec", "omit", "include", "termination_by", "decreasing_by", "nomatch", "nofun",
   "calc", "attribute", "mutual", "rec", "using", "suffices", "obtain", "for", "unless", "break", "continue",
   "try", "catch", "finally", "sorry", "Type", "Sort", "Prop", "true", "false", "set_option", "hiding",
   "renaming", "extends", "generalizing", "initialize", "builtin_initialize", "declare_syntax_cat",
   "binder_predicate", "infix", "infixl", "infixr", "prefix", "postfix", "only", "exposing", "module",
   "exact"]

/-- 大域名の区切り・variant 名: Lean の予約語なら `«»` で囲む。 -/
def escSeg (s : String) : String :=
  if leanKeywords.contains s then s!"«{s}»" else s

/-- 局所名と欄名は常に `«»` で囲む(予約語の一覧に頼らず、生成コードの組み込み名を捕獲しない)。 -/
def escLocal (s : String) : String := s!"«{s}»"

/-- 大域の修飾名 → Lean の完全修飾名(`Model.A.B.name`)。 -/
def leanName (key : String) : String :=
  "Model." ++ ".".intercalate ((key.splitOn ".").map escSeg)

def leanModule (name : List String) : String :=
  "Model." ++ ".".intercalate (name.map escSeg)

def modulePath (name : List String) : String :=
  "Model/" ++ "/".intercalate name ++ ".lean"

def localName (s : String) : String := escLocal s

/-- input の修飾名 → それを引き回す引数の名前(naru の名前 + `'`。naru の識別子には `'` が無いので衝突しない)。 -/
def inputBinder (key : String) : String :=
  ((key.splitOn ".").getLast!) ++ "'"

def indent (n : Nat) : String := "".pushn ' ' n

/-! ## 型 -/

partial def ty : TyV → String
  | .bool => "Bool"
  | .nat => "Nat"
  | .int => "Int"
  | .string => "String"
  | .unit => "Unit"
  | .option t => s!"(Option {ty t})"
  | .result t e => s!"(NaruStd.Result {ty t} {ty e})"
  | .list t => s!"(List {ty t})"
  | .set t => s!"(NaruStd.Set {ty t})"
  | .table k v => s!"(NaruStd.Table {ty k} {ty v})"
  | .tuple [] => "Unit"
  | .tuple [t] => ty t
  | .tuple ts => "(" ++ " × ".intercalate (ts.map ty) ++ ")"
  | .named k _ => leanName k
  | .fn [] r => ty r
  | .fn ps r => "(" ++ " → ".intercalate ((ps ++ [r]).map ty) ++ ")"
  | .mvar n => s!"_?{n}"
  | .unknown => "_"

def isDecideTy : TyV → Bool
  | .nat | .int | .string => true
  | _ => false

/-! ## 式 -/

def escapeString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | c => c.toString

def litStr : Lit → TyV → String
  | .nat n, .int => s!"({n} : Int)"
  | .nat n, _ => s!"({n} : Nat)"
  | .str s, _ => "\"" ++ escapeString s ++ "\""
  | .bool b, _ => if b then "true" else "false"
  | .unit, _ => "()"

def patLit : Lit → String
  | .nat n => toString n
  | .str s => "\"" ++ escapeString s ++ "\""
  | .bool b => if b then "true" else "false"
  | .unit => "()"

/-- 文脈: いまの fn が再帰するか(`if _h' :` と `match` の refine が要る)。 -/
structure ECtx where
  recursive : Bool

def app (f : String) (args : List String) : String :=
  if args.isEmpty then f else f ++ " " ++ " ".intercalate args

/-- 引数の位置にそのまま置ける(括弧が要らない)式か。出力が自分で括弧を持つものも含む。 -/
def isAtom (env : Env) : Core.Expr → Bool
  | .var _ | .lit .. | .field .. | .list .. | .tuple .. | .record .. | .error => true
  | .global k => (env.inputs.getD k []).isEmpty
  | .variant _ _ [] => true
  | .builtin "None" [] _ | .builtin "Set.empty" [] _ | .builtin "List.empty" [] _
  | .builtin "Table.empty" [] _ => true
  | _ => false

/-- パターン。構築子の適用は括弧で囲む(入れ子で引数に置けるように)。 -/
partial def pat (p : Core.Pat) : String :=
  match p with
  | .wild => "_"
  | .bind n => localName n
  | .lit l => patLit l
  | .tuple [] => "()"
  | .tuple [q] => pat q
  | .tuple ps => "(" ++ ", ".intercalate (ps.map pat) ++ ")"
  | .builtin "Some" [q] => "(Option.some " ++ pat q ++ ")"
  | .builtin "None" [] => "Option.none"
  | .builtin "Ok" [q] => "(NaruStd.Result.ok " ++ pat q ++ ")"
  | .builtin "Err" [q] => "(NaruStd.Result.err " ++ pat q ++ ")"
  | .builtin n qs => "(" ++ app n (qs.map pat) ++ ")"
  | .variant k v [] => leanName k ++ "." ++ escSeg v
  | .variant k v qs => "(" ++ app (leanName k ++ "." ++ escSeg v) (qs.map pat) ++ ")"

/-- 必ず成功するパターンか(その後の `| _ =>` は Lean で「到達しない」誤りになるので出さない)。
variant 1 つだけの enum の構築子と `()` も必ず成功する。 -/
partial def irrefutable (env : Env) : Core.Pat → Bool
  | .wild | .bind _ | .lit .unit => true
  | .tuple ps => ps.all (irrefutable env)
  | .variant k _ args =>
    (match env.decls.get? k with
      | some (.enum _ _ variants _) => variants.length == 1
      | _ => false) && args.all (irrefutable env)
  | _ => false

/-- `Totality.firstMissing` と同じ: `covered` に含まれない最小の自然数。 -/
def firstMissing (covered : List Nat) : Nat := Id.run do
  let mut k := 0
  for _ in [0:covered.length + 1] do
    if covered.contains k then k := k + 1 else return k
  return k

mutual

/-- 括弧なしの形(`let` の右辺・分岐・fn の本体など、式が 1 つ置ける位置)。
`ind` はこの式の最初の行の字下げ(続く行はそれに合わせる)。 -/
partial def emitE (env : Env) (c : ECtx) (ind : Nat) (e : Core.Expr) : String :=
  match e with
  | .lit l t => litStr l t
  | .var n => localName n
  | .global k =>
    if let some (.fn _ _ .input ..) := env.decls.get? k then inputBinder k
    else app (leanName k) ((env.inputs.getD k []).map inputBinder)
  | .call k args =>
    let f := if let some (.fn _ _ .input ..) := env.decls.get? k then inputBinder k else leanName k
    app f ((env.inputs.getD k []).map inputBinder ++ args.map (emitP env c ind))
  | .callLocal f args => app (emitP env c ind f) (args.map (emitP env c ind))
  | .method tn n recv args _ => emitMethod env c ind tn n recv args
  | .builtin n args t => emitBuiltin env c ind n args t
  | .variant k v args => app (leanName k ++ "." ++ escSeg v) (args.map (emitP env c ind))
  | .field r _ n => emitP env c ind r ++ "." ++ escLocal n
  | .binop op l r t =>
    let ls := emitP env c ind l
    let rs := emitP env c ind r
    match op with
    | "&&" => s!"{ls} && {rs}"
    | "||" => s!"{ls} || {rs}"
    | "implies" => s!"!{ls} || {rs}"
    | "==" => s!"{ls} == {rs}"
    | "!=" => s!"{ls} != {rs}"
    | "<" | "<=" | ">" | ">=" =>
      if isDecideTy t then s!"Decidable.decide ({ls} {op} {rs})"
      else
        let test := match op with
          | "<" => "== .lt"
          | "<=" => "!= .gt"
          | ">" => "== .gt"
          | _ => "!= .lt"
        s!"Ord.compare {ls} {rs} {test}"
    | _ => s!"{ls} {op} {rs}"
  | .unop "!" a => "!" ++ emitP env c ind a
  | .unop "-" a => "-" ++ emitP env c ind a
  | .unop op a => op ++ emitP env c ind a
  | .ite cond t el =>
    let h := if c.recursive then "_h' : " else ""
    s!"if {h}{emitE env c ind cond} then\n{indent (ind + 2)}{emitE env c (ind + 2) t}\n{indent ind}else\n{indent (ind + 2)}{emitE env c (ind + 2) el}"
  | .match_ s st arms => emitMatch env c ind s st arms
  | .let_ n t v b =>
    let name := if n == "_" then "_" else localName n
    s!"let {name} : {ty t} := {emitE env c (ind + 2) v}\n{indent ind}{emitE env c ind b}"
  | .record k fs base =>
    let fields := fs.map fun (f, x) => s!"{escLocal f} := {emitE env c (ind + 2) x}"
    match base with
    | some b =>
      if fs.isEmpty then emitP env c ind b
      else s!"(\{ {emitP env c ind b} with {", ".intercalate fields} } : {leanName k})"
    | none => s!"(\{ {", ".intercalate fields} } : {leanName k})"
  | .list [] t => s!"([] : (List {ty t}))"
  | .list es _ => "[" ++ ", ".intercalate (es.map (emitE env c (ind + 2))) ++ "]"
  | .tuple [] => "()"
  | .tuple [x] => emitE env c ind x
  | .tuple es => "(" ++ ", ".intercalate (es.map (emitE env c (ind + 2))) ++ ")"
  | .lambda [] b => emitE env c ind b
  | .lambda ps b =>
    let binders := ps.map fun (n, t) => s!"({localName n} : {ty t})"
    s!"fun {" ".intercalate binders} =>\n{indent (ind + 2)}{emitE env c (ind + 2) b}"
  | .quant .. => "(panic! \"naru: quantifier in runtime code\")"
  | .error => "(panic! \"naru: elaboration error\")"

/-- 引数の位置に置ける形(必要なら括弧で囲む)。 -/
partial def emitP (env : Env) (c : ECtx) (ind : Nat) (e : Core.Expr) : String :=
  if isAtom env e then emitE env c ind e
  else "(" ++ emitE env c (ind + 1) e ++ ")"

partial def emitBuiltin (env : Env) (c : ECtx) (ind : Nat) (name : String) (args : List Core.Expr) (t : TyV) : String :=
  let as := args.map (emitP env c ind)
  let asValue := args.isEmpty && (match t with | .fn (_ :: _) _ => true | _ => false)
  match name with
  | "Some" => app "Option.some" as
  | "None" => s!"(Option.none : {ty t})"
  | "Ok" => if asValue then "NaruStd.Result.ok" else app "NaruStd.Result.ok" as
  | "Err" => if asValue then "NaruStd.Result.err" else app "NaruStd.Result.err" as
  | "Set.empty" => s!"(NaruStd.Set.empty : {ty t})"
  | "Set.singleton" => if asValue then "NaruStd.Set.singleton" else app "NaruStd.Set.singleton" as
  | "Set.of" => if asValue then "NaruStd.Set.of" else app "NaruStd.Set.of" as
  | "List.empty" => s!"([] : {ty t})"
  | "List.range" => if asValue then "List.range" else app "List.range" as
  | "Table.empty" => s!"(NaruStd.Table.empty : {ty t})"
  | _ => s!"(panic! \"naru: unknown built-in {name}\")"

partial def emitMethod (env : Env) (c : ECtx) (ind : Nat) (tn n : String) (recv : Core.Expr) (args : List Core.Expr) : String :=
  let r := emitP env c ind recv
  let as := args.map (emitP env c ind)
  let a (i : Nat) : String := as.getD i "_"
  match tn, n with
  | "Set", "sort" => app "NaruStd.Set.sortBy" (r :: as)
  | "Set", m => app ("NaruStd.Set." ++ m) (r :: as)
  | "List", "size" => app "List.length" [r]
  | "List", "isEmpty" => app "List.isEmpty" [r]
  | "List", "contains" => app "List.contains" [r, a 0]
  | "List", "push" => s!"{r} ++ [{emitE env c ind (args.getD 0 Core.Expr.error)}]"
  | "List", "append" => s!"{r} ++ {a 0}"
  | "List", "head?" => app "List.head?" [r]
  | "List", "last?" => app "List.getLast?" [r]
  | "List", "get?" => s!"{r}[{emitE env c ind (args.getD 0 Core.Expr.error)}]?"
  | "List", "find?" => app "List.find?" [a 0, r]
  | "List", "filter" => app "List.filter" [a 0, r]
  | "List", "map" => app "List.map" [a 0, r]
  | "List", "flatMap" => app "List.flatMap" [a 0, r]
  | "List", "filterMap" => app "List.filterMap" [a 0, r]
  | "List", "any" => app "List.any" [r, a 0]
  | "List", "all" => app "List.all" [r, a 0]
  | "List", "count" => app "List.countP" [a 0, r]
  | "List", "fold" => app "List.foldl" [a 1, a 0, r]
  | "List", "sort" => app "NaruStd.List.sortBy" [r, a 0]
  | "List", "minBy?" => app "NaruStd.List.minBy?" [r, a 0]
  | "List", "maxBy?" => app "NaruStd.List.maxBy?" [r, a 0]
  | "List", "reverse" => app "List.reverse" [r]
  | "List", "take" => app "List.take" [a 0, r]
  | "List", "drop" => app "List.drop" [a 0, r]
  | "List", "sum" => app "NaruStd.List.sumBy" [r, a 0]
  | "List", "toSet" => app "NaruStd.List.toSet" [r]
  | "Option", "isSome" => app "Option.isSome" [r]
  | "Option", "isNone" => app "Option.isNone" [r]
  | "Option", "getOr" => app "Option.getD" [r, a 0]
  | "Option", "map" => app "Option.map" [a 0, r]
  | "Option", "andThen" => app "Option.bind" [r, a 0]
  | "Option", "filter" => app "Option.filter" [a 0, r]
  | "Result", m => app ("NaruStd.Result." ++ m) [r]
  | "Table", "entries" => app "NaruStd.Table.entriesSet" [r]
  | "Table", m => app ("NaruStd.Table." ++ m) (r :: as)
  | "Nat", "toInt" => app "Int.ofNat" [r]
  | "Int", "abs" => app "Int.natAbs" [r]
  | "Int", "fdiv" => app "Int.fdiv" [r, a 0]
  | "Int", "toNat" => app "Int.toNat" [r]
  | _, "min" => app "Min.min" [r, a 0]
  | _, "max" => app "Max.max" [r, a 0]
  | "String", "size" => app "String.length" [r]
  | "String", "append" => s!"{r} ++ {a 0}"
  | _, _ => s!"(panic! \"naru: unknown method {tn}.{n}\")"

/-- `match`。腕のガードは Lean に無いので、3 つの形に落とす:
- 再帰する fn の中で `Nat` の局所変数を match し、ガードが無い: `match _hm' : v with` で等式を残し、bind / `_` の腕を
  `_ + m` に落とす(m = 先行するガード無しリテラル腕が 0 から覆った値の次)。停止性の証明に `v ≥ m` が要る。
- 同じくガードがある: `if _h' : v == k && g then … else …` の連鎖(事実がすべて `_h'` に残る)。
- それ以外でガードがある: 最初のガード付き腕 i の前の腕をそのまま出し、`| _ =>` の中で
  `match (match s with | p_i => if g then some b else none | _ => none) with | some g' => g' | none => REST`
  (REST = i 以外の腕の match。`none` の分岐は遅延評価なので再帰も安全)。 -/
partial def emitMatch (env : Env) (c : ECtx) (ind : Nat) (s : Core.Expr) (st : TyV) (arms : List Core.Arm) :
    String :=
  let natVar : Option String := match s, st with
    | .var v, .nat => if c.recursive then some v else none
    | _, _ => none
  let hasGuard := arms.any fun | .mk _ g _ => g.isSome
  match natVar with
  | some v => if hasGuard then emitNatChain env c ind v arms else emitMatchPlain env c ind s arms (some v)
  | none => emitMatchGuarded env c ind s st arms

/-- ガード無しの match。再帰 fn の `Nat` の局所変数 `v` を match するときは `match _hm' : v with` として
等式 `_hm' : v = <パターン>` を証明に残し、bind / `_` の腕を `_ + m`(m = 先行するガード無しリテラル腕が
0 から覆った値の次。m = 0 なら `_`)に落とし、束縛名は `let k := v` の別名にする(束縛名を match の変数にすると
Lean がそれを v から切り離し、`v ≥ m` や外側の `if` の事実が証明に届かない)。 -/
partial def emitMatchPlain (env : Env) (c : ECtx) (ind : Nat) (s : Core.Expr) (arms : List Core.Arm)
    (natVar : Option String) : String := Id.run do
  let eq := if natVar.isSome then "_hm' : " else ""
  let mut out := s!"match {eq}{emitP env c ind s} with"
  let mut covered : List Nat := []
  for arm in arms do
    let .mk p _ b := arm
    let (ps, prefix_) : String × String := match natVar, p with
      | some v, .bind k =>
        let m := firstMissing covered
        (if m > 0 then s!"_ + {m}" else "_",
         if k == v then "" else s!"let {localName k} : Nat := {localName v}\n{indent (ind + 2)}")
      | some _, .wild =>
        let m := firstMissing covered
        (if m > 0 then s!"_ + {m}" else "_", "")
      | _, _ => (pat p, "")
    out := out ++ s!"\n{indent ind}| {ps} =>\n{indent (ind + 2)}{prefix_}{emitE env c (ind + 2) b}"
    if let .lit (.nat k) := p then covered := k :: covered
  return out

/-- 再帰する fn の中の、ガード付きの `Nat` の match → `if` の連鎖。 -/
partial def emitNatChain (env : Env) (c : ECtx) (ind : Nat) (v : String) (arms : List Core.Arm) : String :=
  match arms with
  | [] => s!"(panic! \"naru: match on `{v}` is not exhaustive\")"
  | .mk p g b :: rest =>
    let vn := localName v
    let body := emitE env c (ind + 2) b
    let chain (cond : String) : String :=
      s!"if _h' : {cond} then\n{indent (ind + 2)}{body}\n{indent ind}else\n{indent (ind + 2)}{emitNatChain env c (ind + 2) v rest}"
    let guardStr := g.map (emitE env c (ind + 2))
    let alias (k : String) : String :=
      if k == v then "" else s!"let {localName k} : Nat := {vn}\n{indent ind}"
    match p, guardStr with
    | .lit (.nat k), some gs => chain s!"({vn} == ({k} : Nat)) && ({gs})"
    | .lit (.nat k), none => chain s!"{vn} == ({k} : Nat)"
    | .bind k, some gs => alias k ++ chain gs
    | .bind k, none => alias k ++ body
    | .wild, some gs => chain gs
    | .wild, none => body
    | _, _ => s!"(panic! \"naru: unsupported pattern in a match on Nat\")"

/-- ガード付きの腕を Option の match に落とす一般形。 -/
partial def emitMatchGuarded (env : Env) (c : ECtx) (ind : Nat) (s : Core.Expr) (st : TyV) (arms : List Core.Arm) :
    String := Id.run do
  let scrut := emitP env c ind s
  let h := if c.recursive then "_h' : " else ""
  let mut lead : List Core.Arm := []
  let mut rest := arms
  while !rest.isEmpty do
    let .mk _ g _ := rest.head!
    if g.isSome then break
    lead := lead ++ [rest.head!]
    rest := rest.tail!
  let armStr (ind : Nat) (arm : Core.Arm) : String :=
    let .mk p _ b := arm
    s!"\n{indent ind}| {pat p} =>\n{indent (ind + 2)}{emitE env c (ind + 2) b}"
  match rest with
  | [] => return s!"match {scrut} with" ++ "".intercalate (lead.map (armStr ind))
  | .mk p (some g) b :: after =>
    let tailInd := if lead.isEmpty then ind else ind + 2
    let inner := s!"match {scrut} with\n{indent (tailInd + 2)}| {pat p} =>\n{indent (tailInd + 4)}if {h}{emitE env c (tailInd + 4) g} then\n{indent (tailInd + 6)}some ({emitE env c (tailInd + 6) b})\n{indent (tailInd + 4)}else\n{indent (tailInd + 6)}none"
      ++ (if irrefutable env p then "" else s!"\n{indent (tailInd + 2)}| _ =>\n{indent (tailInd + 4)}none")
    -- REST には i より前の腕も入れる(そこでは一致しない死んだ腕だが、Lean の網羅性検査に要る。
    -- 本当に網羅していない match は、REST でも網羅していないので Lean が拒否する)
    let restArms := lead ++ after
    let restStr :=
      if restArms.isEmpty then "(panic! \"naru: no arm matched\")"
      else emitMatchGuarded env c (tailInd + 2) s st restArms
    let tail := s!"match ({inner}) with\n{indent tailInd}| some g' =>\n{indent (tailInd + 2)}g'\n{indent tailInd}| none =>\n{indent (tailInd + 2)}{restStr}"
    if lead.isEmpty then return tail
    return s!"match {scrut} with" ++ "".intercalate (lead.map (armStr ind)) ++ s!"\n{indent ind}| _ =>\n{indent (ind + 2)}{tail}"
  | _ => return "(panic! \"naru: unreachable\")"

end

/-- scenario の文の列 → `List NaruStd.Observation` の式。`let` は `let` に、`observe` は `NaruStd.observe` /
`NaruStd.observeList`(observer の戻り型が `List` なら 1 要素 1 行)の cons に落とし、末尾は `[]`。
`::` の右は `let` が続きうるので常に括弧で囲む。 -/
partial def emitScenarioStmts (env : Env) (c : ECtx) (ind : Nat) : List Core.ScenarioStmt → String
  | [] => "[]"
  | .let_ n t v :: rest =>
    let name := if n == "_" then "_" else localName n
    s!"let {name} : {ty t} := {emitE env c (ind + 2) v}\n{indent ind}{emitScenarioStmts env c ind rest}"
  | .observe label t e :: rest =>
    let f := match t with
      | .list _ => "NaruStd.observeList"
      | _ => "NaruStd.observe"
    s!"{f} \"{escapeString label}\" {emitP env c ind e} ::\n{indent ind}({emitScenarioStmts env c (ind + 1) rest})"

/-! ## 宣言 -/

def derivingList (derives : List String) : List String :=
  let eq := derives.contains "eq"
  let ord := derives.contains "order" || eq
  (if eq then ["DecidableEq"] else []) ++ (if ord then ["Ord"] else []) ++ ["Repr"]

def isInput : Core.Decl → Bool
  | .fn _ _ .input .. => true
  | _ => false

def isRuntimeValue : Core.Decl → Bool
  | .fn _ _ k .. => k == .fn || k == .observer
  | .scenario .. => true
  | _ => false

def isTypeDecl : Core.Decl → Bool
  | .typeAlias .. | .record .. | .enum .. => true
  | _ => false

/-- Model に出す宣言か(runtime で、Lean の宣言になるもの)。 -/
def emitted (d : Core.Decl) : Bool :=
  d.phase == .runtime && !(isInput d) && (isTypeDecl d || isRuntimeValue d)

/-- input の修飾名 → それを引き回す引数の型(`(T1 → … → U)`。仮引数 0 個なら `U`)。 -/
def inputTy (env : Env) (ik : String) : String :=
  match env.decls.get? ik with
  | some (.fn _ _ _ ps ret _) => ty (.fn (ps.map (·.ty)) ret)
  | _ => "_"

def inputBinders (env : Env) (key : String) : List String :=
  (env.inputs.getD key []).map fun ik => s!"({inputBinder ik} : {inputTy env ik})"

def decreasingBy : String :=
  "decreasing_by all_goals (try simp_all) <;> (first | omega | decreasing_tactic)"

/-- 再帰する fn の `termination_by` / `decreasing_by`。 -/
def terminationClause (env : Env) (key : String) (params : List Core.Param) : String :=
  match env.recs.get? key with
  | none => ""
  | some (_, i, anyNat) =>
    match params[i]? with
    | none => ""
    | some p =>
      let name := localName p.name
      match p.ty with
      | .nat => s!"\ntermination_by {name}\n{decreasingBy}"
      | _ =>
        if anyNat then s!"\ntermination_by SizeOf.sizeOf {name}\n{decreasingBy}"
        else s!"\ntermination_by structural {name}"

def isRecursive (env : Env) (key : String) : Bool := (env.recs.get? key).isSome

/-- 1 つの宣言。`standaloneDeriving` は `mutual` の中(deriving 句を後に出す)。 -/
def emitDecl (env : Env) (d : Core.Decl) (standaloneDeriving : Bool := false) : String :=
  match d with
  | .typeAlias k _ t => s!"abbrev {leanName k} : Type := {ty t}"
  | .record k _ isState fields derives =>
    let head := if isState then "state" else "record"
    let fs := fields.map fun (f, t) => s!"\n  {escLocal f} : {ty t}"
    let body := if fields.isEmpty then s!"structure {leanName k}" else s!"structure {leanName k} where" ++ "".intercalate fs
    let dv := ", ".intercalate (derivingList derives)
    s!"-- naru {head}\n" ++ body ++ (if standaloneDeriving then "" else s!"\nderiving {dv}")
  | .enum k _ variants derives =>
    let vs := variants.map fun (v, ts) =>
      let args := (ts.zipIdx).map fun (t, i) => s!" (a{i} : {ty t})"
      s!"\n  | {escSeg v}" ++ "".intercalate args
    let dv := ", ".intercalate (derivingList derives)
    s!"inductive {leanName k} where" ++ "".intercalate vs ++ (if standaloneDeriving then "" else s!"\nderiving {dv}")
  | .fn k _ kind params ret body =>
    let binders := inputBinders env k ++ params.map fun p => s!"({localName p.name} : {ty p.ty})"
    let sig := app s!"def {leanName k}" binders ++ s!" : {ty ret} :="
    let c : ECtx := { recursive := isRecursive env k }
    let b := match body with
      | some b => emitE env c 2 b
      | none => "(panic! \"naru: no body\")"
    s!"-- naru {kind.describe}\n{sig}\n  {b}" ++ terminationClause env k params
  | .scenario k _ inputs stmts =>
    -- 束縛した input は本体の先頭の `let f' := fun … =>`(呼出しはこの局所名を引き回す)。束縛していない input は
    -- 型検査(E015)が退けるので普通は無いが、あれば従来どおり引数にする
    let boundKeys := inputs.map (·.1)
    let binders := ((env.inputs.getD k []).filter fun ik => !boundKeys.contains ik).map fun ik =>
      s!"({inputBinder ik} : {inputTy env ik})"
    let sig := app s!"def {leanName k}" binders ++ " : List NaruStd.Observation :="
    let c : ECtx := { recursive := false }
    let bindLines := inputs.map fun (ik, ps, v) =>
      s!"let {inputBinder ik} : {inputTy env ik} := {emitE env c 4 (.lambda ps v)}\n  "
    s!"-- naru scenario\n{sig}\n  " ++ "".intercalate bindLines ++ emitScenarioStmts env c 2 stmts
  | .claimBundle .. => ""

/-- deriving 句を `mutual` の後に出す形。 -/
def standaloneDerivingOf : Core.Decl → Option String
  | .record k _ _ _ derives | .enum k _ _ derives =>
    some s!"deriving instance {", ".intercalate (derivingList derives)} for {leanName k}"
  | _ => none

/-! ## 依存順 -/

/-- 宣言が参照する大域名のうち、同じモジュールで出力される宣言の鍵(重複なし、出現順)。 -/
def localDeps (env : Env) (keys : List String) (d : Core.Decl) : List String := Id.run do
  let mut out : List String := []
  let refs := d.refs ++ ((env.inputs.getD d.key []).flatMap fun ik =>
    match env.decls.get? ik with
    | some i => i.refs
    | none => [])
  for r in refs do
    if keys.contains r && !out.contains r then out := out ++ [r]
  return out

/-- 到達可能集合(1 回以上の辺)。 -/
partial def reach (adj : List (String × List String)) (start : String) : List String :=
  let rec go (todo : List String) (seen : List String) : List String :=
    match todo with
    | [] => seen
    | x :: rest =>
      let next := (adj.lookup x).getD [] |>.filter fun y => !seen.contains y
      go (next ++ rest) (seen ++ next)
  let init := (adj.lookup start).getD []
  go init init

/-- 強連結成分を依存順に並べる(成分の中はソースの順、成分の並びは依存先が先。同順ならソースの順)。 -/
def orderGroups (env : Env) (decls : List Core.Decl) : List (List Core.Decl) := Id.run do
  let keys := decls.map (·.key)
  let adj : List (String × List String) := decls.map fun d => (d.key, localDeps env keys d)
  let reachOf : List (String × List String) := keys.map fun k => (k, reach adj k)
  let mut assigned : List String := []
  let mut groups : List (List String) := []
  for k in keys do
    if assigned.contains k then continue
    let rk := (reachOf.lookup k).getD []
    let members := keys.filter fun g =>
      g == k || (rk.contains g && ((reachOf.lookup g).getD []).contains k)
    assigned := assigned ++ members
    groups := groups ++ [members]
  -- Kahn: 外の依存がすべて出力済みの成分を、ソースの順で選ぶ
  let mut done : List String := []
  let mut ordered : List (List String) := []
  let mut remaining := groups
  let mut guard := groups.length + 1
  while !remaining.isEmpty && guard > 0 do
    guard := guard - 1
    match remaining.find? (fun g => g.all fun m =>
        ((adj.lookup m).getD []).all fun dep => g.contains dep || done.contains dep) with
    | some g =>
      ordered := ordered ++ [g]
      done := done ++ g
      remaining := remaining.filter (· != g)
    | none =>
      -- 起きないはず(条件付き DAG)。残りをそのまま出す
      ordered := ordered ++ remaining
      remaining := []
  return ordered.map fun g => g.filterMap fun k => decls.find? (·.key == k)

/-- 成分を出力する。複数なら `mutual … end`(型なら deriving 句を後に)。 -/
def emitGroup (env : Env) (g : List Core.Decl) : String :=
  match g with
  | [d] => emitDecl env d
  | ds =>
    let inner := "\n\n".intercalate (ds.map (emitDecl env · true))
    let derivs := ds.filterMap standaloneDerivingOf
    s!"mutual\n\n{inner}\n\nend" ++ (if derivs.isEmpty then "" else "\n" ++ "\n".intercalate derivs)

/-! ## モジュールとヘッダ -/

def header (info : Meta) (source hash : String) : String :=
  s!"-- Generated by naru from {source}. Do not edit by hand: `generated/` is machine-generated (IDEAL.md).\n" ++
  s!"-- naru-compiler: {info.compilerVersion} sha256:{info.compilerHash}\n" ++
  s!"-- naru-stdlib: {info.stdlibVersion} sha256:{info.stdlibHash}\n" ++
  s!"-- naru-source: {source} sha256:{hash}\n" ++
  s!"-- naru-unit: sha256:{info.unitHash}\n"

/-- モジュールが参照する他のモジュール(名前順、重複なし)。 -/
def moduleDeps (env : Env) (m : Core.Module) : List (List String) := Id.run do
  let mut out : List (List String) := []
  for d in m.decls do
    if !(emitted d) then continue
    let refs := d.refs ++ ((env.inputs.getD d.key []).flatMap fun ik =>
      match env.decls.get? ik with
      | some i => i.refs
      | none => [])
    for r in refs do
      if let some other := env.moduleOf.get? r then
        if other != m.name && !out.contains other then out := out ++ [other]
  return out.mergeSort fun a b => renderPath a ≤ renderPath b

def buildEnv (mods : Array Core.Module) (recs : Array Totality.Recursion) : Env := Id.run do
  let mut env : Env := {}
  for m in mods do
    for d in m.decls do
      env := { env with decls := env.decls.insert d.key d, moduleOf := env.moduleOf.insert d.key m.name }
  -- input の推移閉包(不動点)
  let all := mods.toList.flatMap fun m => m.decls.toList
  let inputKeys := (all.filter isInput).map (·.key)
  let valueKeys := (all.filter isRuntimeValue).map (·.key)
  let mut table : List (String × List String) := valueKeys.map fun k => (k, [])
  let direct (d : Core.Decl) : List String := d.refs.filter inputKeys.contains
  let mut changed := true
  let mut guard := all.length + 1
  while changed && guard > 0 do
    guard := guard - 1
    changed := false
    let mut next : List (String × List String) := []
    for (k, cur) in table do
      let d := (env.decls.get? k).get!
      let viaFns := d.refs.filter valueKeys.contains |>.flatMap fun g => (table.lookup g).getD []
      let merged := (direct d ++ viaFns).foldl (init := cur) fun acc x => if acc.contains x then acc else acc ++ [x]
      if merged.length != cur.length then changed := true
      next := next ++ [(k, merged)]
    table := next
  for (k, ins) in table do
    env := { env with inputs := env.inputs.insert k (ins.mergeSort (· ≤ ·)) }
  for r in recs do
    let anyNat := r.measures.any fun (q, i) =>
      match env.decls.get? q with
      | some (.fn _ _ _ ps ..) => match ps[i]? with
        | some p => match p.ty with | .nat => true | _ => false
        | none => false
      | _ => false
    for (q, i) in r.measures do
      env := { env with recs := env.recs.insert q (r.members, i, anyNat) }
  return env

/-- モジュール同士の参照の循環を探す(あれば、その経路)。 -/
def findCycle (deps : List (List String × List (List String))) : Option (List (List String)) := Id.run do
  for (m, _) in deps do
    -- m から m に戻る経路
    let mut stack : List (List String × List (List String)) := [(m, [m])]
    let mut seen : List (List String) := []
    while !stack.isEmpty do
      let (cur, path) := stack.head!
      stack := stack.tail!
      for n in (deps.lookup cur).getD [] do
        if n == m then return some (path ++ [m])
        if !seen.contains n then
          seen := seen ++ [n]
          stack := (n, path ++ [n]) :: stack
  return none

/-- Core のモジュール列から生成ファイル(`generated/` からの相対パス、内容)を作る。 -/
def emitModel (mods : Array Core.Module) (recs : Array Totality.Recursion) (info : Meta) :
    Except Diagnostic (Array (String × String)) := do
  -- 同名のモジュール
  let mut seen : List (List String × String) := []
  for m in mods do
    if let some other := seen.lookup m.name then
      throw { file := m.file, span := {}, code := Code.moduleStructure,
              msg := s!"module `{renderPath m.name}` is also declared in {other}; each module needs its own name (it becomes one generated Lean file)" }
    seen := seen ++ [(m.name, m.file)]
  let env := buildEnv mods recs
  let deps := mods.toList.map fun m => (m.name, moduleDeps env m)
  if let some cycle := findCycle deps then
    let names := cycle.map fun n => s!"`{renderPath n}`"
    let first := mods.find? (·.name == cycle.head!)
    throw { file := (first.map (·.file)).getD "", span := {}, code := Code.moduleStructure,
            msg := s!"modules refer to each other in a cycle ({" → ".intercalate names}); generated Lean modules import each other, so move the shared declarations into one module" }
  let mut files : Array (String × String) := #[]
  for m in mods do
    let hash := (info.fileHashes.lookup m.file).getD ""
    let imports := "import NaruStd\n" ++ "".intercalate (((deps.lookup m.name).getD []).map fun n => s!"import {leanModule n}\n")
    let groups := orderGroups env (m.decls.toList.filter emitted)
    let inputsNote := (m.decls.toList.filter isInput).map fun d =>
      s!"-- naru input `{d.name}`: supplied by the environment as parameter `{inputBinder d.key}` of every function that uses it"
    let bodyParts := inputsNote ++ groups.map (emitGroup env)
    let body := if bodyParts.isEmpty then "" else "\n" ++ "\n\n".intercalate bodyParts ++ "\n"
    let content := header info m.file hash ++ imports ++ s!"\n/-! naru module `{renderPath m.name}` ({m.file}) -/\n" ++ body
    files := files.push (modulePath m.name, content)
  -- ルート `Model.lean`: 全モジュールを import する
  let rootImports := "".intercalate (mods.toList.map fun m => s!"import {leanModule m.name}\n")
  let root := header info "all sources" info.unitHash ++ rootImports ++
    "\n/-! Generated Model: one Lean module per naru module. Build with `lake build Model`. -/\n"
  files := files.push ("Model.lean", root)
  return files

end Naru.Backend.Model
