import NaruSem.Scope

/-!
# Surface AST の保存対象と整形性(IDEAL.md C48、用語「Surface AST の保存対象」)

構文解析の出力 `Naru.Expr`(`compiler/Naru/Ast.lean`)のうち、用語「今回の保存対象」の Nat / Bool の Core 構文・演算に対応する部分を、
frontend(`compiler/Naru/Typecheck.lean` の elaboration)から独立に Lean の型 `Surf.Expr` として定め、その整形性(型付け・スコープ・
値 / 命題の束縛文脈・`match` の網羅性)を `wtR` / `wtS` で判定する。意味は `SurfaceEval.lean`(runtime の表示的意味論 `eval`、spec の評価関係 `Sem`)、
整形性から意味が定まることは `SurfaceTotality.lean` が証明する。これらは frontend の変換結果(Core)や Core の意味(`Eval.lean` / `Sem.lean`)を
参照しない(Core の意味を AST の意味と定義しない)。

- `Surf.Expr` / `Arm` / `Stmt` / `Pat` / `Ty` / `Binder` — 対象の構文。構文解析の `Naru.Expr` の構築子のうち、リテラル(`.lit`)、局所名(`.var`)、
  Nat の `min` / `max`(`.method`、位置引数 1 つ)、二項演算(`.binop`)、`!`(`.unop`)、`if`(`.ite`)、ガード付き `match`(`.matchE`。パターンは `_` / 変数 /
  Nat・Bool のリテラル)、ブロック(`.block`: `let`(型注釈は任意)の列と末尾式)、量化(`.quant`: 束縛型 Nat / Bool、spec だけ)。位置情報 `Span` は
  構文解析の出力をそのまま持つ(意味には関与しない)。
- `Expr.toAst` — 構文解析の型 `Naru.Expr` への埋め込み(構築子ごとに同じ構築子へ。`List` は `Array` に)。`lake exe naru_test semantics` は、検査する
  `Surf.Expr` の埋め込みが実際に構文解析された `Naru.Expr` と `==` で一致することを照合する(`SurfaceQuote.lean`)。対象外の構文のうち呼出し・欄・
  record / list / tuple のリテラル・lambda・名前付き引数・`e;` 文は `Surf.Expr` に写らない(`SurfaceQuote.ofAst?` が `none`)。リテラル(`.lit`)は文字列・
  `()` も含めて写るが、`wtR` / `wtS` が Nat / Bool 以外を `none` にする(対象外)。
- `Decl` / `wtDecl` — 最小の非再帰 fn / spec 宣言の包装(用語「Surface AST の保存対象」): 種別(runtime は `fn`、spec は `predicate` 等)、仮引数(型注釈は
  Nat / Bool)、runtime の戻り型(Nat / Bool)、本体。`wtDecl` は仮引数の注釈から文脈を作り、runtime なら本体が戻り型の型(`wtR`)、spec なら戻り型の注釈が
  無く本体が論理の位置の型(`wtS`)であることを判定する。`Decl.toAst` が構文解析の `Naru.Decl` に埋め込む(fn / spec 宣言が使わない欄は既定値)。
- 意味論が見ない前提: Surface AST は大域の宣言表を持たないので、`x.min(y)` / `x.max(y)` は常に Nat のメソッドとして読む(frontend は同名のユーザ宣言の
  fn があれば UFCS の呼出しに落とす — その場合は Core が `.call` になり、AST → Core の接続検査が一致しない)。量化の束縛は型注釈のあるものだけを対象にする
  (frontend は注釈を推論で補うが、対象外として扱う)。
- `wtR Γ e = some t` — runtime の式の型付け(対象範囲の判定を兼ねる): 対象の構文だけから成り、スコープ内の名前だけを参照し、型が合い、`match` が
  網羅的。ブロックは `let` の列を前から型付けして文脈を伸ばし(`wtStmtsR`)、末尾式の型。型注釈があれば値の型と一致しなければならない。
- `wtS Γ e = some τ` — spec の式の型付け: Core の `wtS`(`Scope.lean`)と同じ区分で、論理の位置の式は `.val .bool` か `.prop`、値を要求する位置は
  `wtR Γ.vals`(命題に束ねた名前はスコープ外)。ブロックの `let` は、値が命題(`proppyS`: コンパイラの `proppy` と同じ構文的な区分。
  型注釈は無いか `Bool`)なら名前を `.prop` に、そうでなければ値の型(`wtR Γ.vals`。型注釈があれば一致)に束ねる。量化は `.prop`。
-/

namespace NaruSem.Surf
open Naru

/-- 型の注釈(Surface の `Naru.Ty.named`)。対象は `Nat` / `Bool` の名前だけ(`toTy?`)。 -/
inductive Ty where
  | named (span : Span) (name : List String) (args : List Ty)

def Ty.toAst : Ty → Naru.Ty
  | .named sp n args => .named sp n (argsToAst args).toArray
where
  argsToAst : List Ty → List Naru.Ty
    | [] => []
    | t :: rest => t.toAst :: argsToAst rest

/-- 注釈の型 → 対象の型。`Nat` / `Bool`(型引数なし)だけ。 -/
def Ty.toTy? : Ty → Option NaruSem.Ty
  | .named _ ["Nat"] [] => some .nat
  | .named _ ["Bool"] [] => some .bool
  | _ => none

/-- 対象のパターン: `_` / 変数 / リテラル。 -/
inductive Pat where
  | wild (span : Span)
  | bind (span : Span) (name : String)
  | lit (span : Span) (l : Lit)

def Pat.toAst : Pat → Naru.Pattern
  | .wild sp => .wild sp
  | .bind sp x => .bind sp x
  | .lit sp l => .lit sp l

/-- 量化の束縛変数(Surface の `Naru.Binder`)。 -/
structure Binder where
  name : String
  ty : Option Ty
  span : Span

def Binder.toAst (b : Binder) : Naru.Binder :=
  { name := b.name, ty := b.ty.map Ty.toAst, span := b.span }

mutual

/-- 対象の式(構文解析の出力の部分集合。位置情報つき)。 -/
inductive Expr where
  | lit (span : Span) (l : Lit)
  | var (span : Span) (name : List String)
  /-- `recv.name(args)`(位置引数だけ)。対象は Nat の `min` / `max`(引数 1 つ)。 -/
  | method (span : Span) (recv : Expr) (name : String) (args : List Expr)
  | binop (span : Span) (op : String) (lhs rhs : Expr)
  | unop (span : Span) (op : String) (arg : Expr)
  | ite (span : Span) (cond thn els : Expr)
  | matchE (span : Span) (scrut : Expr) (arms : List Arm)
  /-- `{ let x = v; …; tail }`。対象は末尾式のあるブロック。 -/
  | block (span : Span) (stmts : List Stmt) (tail : Option Expr)
  /-- `forall x: T { body }` / `exists x: T { body }`(spec 専用)。 -/
  | quant (span : Span) (q : Quant) (binders : List Binder) (body : Expr)

inductive Arm where
  | mk (pat : Pat) (guard : Option Expr) (body : Expr)

inductive Stmt where
  /-- `let name[: ty] = val;`。 -/
  | letS (span : Span) (name : String) (ty : Option Ty) (val : Expr)

end

instance : Inhabited Expr := ⟨.lit {} .unit⟩
instance : Inhabited Arm := ⟨.mk (.wild {}) none default⟩
instance : Inhabited Stmt := ⟨.letS {} "" none default⟩

mutual

/-- 構文解析の型への埋め込み(構築子ごとに同じ構築子へ)。 -/
def Expr.toAst : Expr → Naru.Expr
  | .lit sp l => .lit sp l
  | .var sp n => .var sp n
  | .method sp r n args => .method sp r.toAst n (argsToAst args).toArray
  | .binop sp op l r => .binop sp op l.toAst r.toAst
  | .unop sp op a => .unop sp op a.toAst
  | .ite sp c t e => .ite sp c.toAst t.toAst e.toAst
  | .matchE sp s arms => .matchE sp s.toAst (armsToAst arms).toArray
  | .block sp stmts tail =>
    .block sp (stmtsToAst stmts).toArray (match tail with | some e => some e.toAst | none => none)
  | .quant sp q bs b => .quant sp q (bs.map Binder.toAst).toArray b.toAst

def argsToAst : List Expr → List Naru.Arg
  | [] => []
  | e :: rest => .pos e.toAst :: argsToAst rest

def armsToAst : List Arm → List Naru.Arm
  | [] => []
  | a :: rest => a.toAst :: armsToAst rest

def Arm.toAst : Arm → Naru.Arm
  | .mk p g b => .mk p.toAst (match g with | some g => some g.toAst | none => none) b.toAst

def stmtsToAst : List Stmt → List Naru.Stmt
  | [] => []
  | s :: rest => s.toAst :: stmtsToAst rest

def Stmt.toAst : Stmt → Naru.Stmt
  | .letS sp x ty v => .letS sp x (ty.map Ty.toAst) v.toAst

end

/-! ## パターン -/

/-- 対象のパターンの型付け: scrutinee の型 `t` に対して、束縛する名前と型。 -/
def wtPat (t : NaruSem.Ty) : Pat → Option (List (String × NaruSem.Ty))
  | .wild _ => some []
  | .bind _ x => some [(x, t)]
  | .lit _ (.nat _) => if t = .nat then some [] else none
  | .lit _ (.bool _) => if t = .bool then some [] else none
  | .lit _ _ => none

/-- 必ず一致するパターン。 -/
def irrefutable : Pat → Bool
  | .wild _ | .bind _ _ => true
  | _ => false

/-- `match` の網羅性(Core の `exhaustiveFrom` と同じ規則): 腕を前から見て、ガードの無い必ず一致する腕に達すれば網羅的。Bool の scrutinee では
ガードの無いリテラルの腕 `true` と `false` の両方に達しても網羅的。Nat のリテラルは全体を覆えない。ガードのある腕は数えない。 -/
def exhaustiveFrom (t : NaruSem.Ty) (sawT sawF : Bool) : List Arm → Bool
  | [] => false
  | .mk p none _ :: rest =>
    match p with
    | .wild _ | .bind _ _ => true
    | .lit _ (.bool true) => (t = .bool && sawF) || exhaustiveFrom t true sawF rest
    | .lit _ (.bool false) => (t = .bool && sawT) || exhaustiveFrom t sawT true rest
    | _ => exhaustiveFrom t sawT sawF rest
  | .mk _ (some _) _ :: rest => exhaustiveFrom t sawT sawF rest

def exhaustive (t : NaruSem.Ty) (arms : List Arm) : Bool := exhaustiveFrom t false false arms

/-- 二項演算の型付け(注釈は無いので被演算子の型だけから): 算術は Nat → Nat、比較・等値は同じ型(Nat / Bool)→ Bool、論理は Bool → Bool。 -/
def binopResult : BinOp → NaruSem.Ty → NaruSem.Ty → Option NaruSem.Ty
  | .arith _, .nat, .nat => some .nat
  | .cmp _, .nat, .nat => some .bool
  | .cmp _, .bool, .bool => some .bool
  | .eq _, .nat, .nat => some .bool
  | .eq _, .bool, .bool => some .bool
  | .logic _, .bool, .bool => some .bool
  | _, _, _ => none

/-- 型注釈と値の型の照合: 注釈が無ければ値の型、あれば対象の型でかつ一致。 -/
def annot (ty : Option Ty) (tv : NaruSem.Ty) : Option NaruSem.Ty :=
  match ty with
  | none => some tv
  | some τ =>
    match τ.toTy? with
    | some ta => if ta = tv then some tv else none
    | none => none

/-! ## runtime の型付けと対象範囲 -/

mutual

/-- runtime の式の型付け(対象範囲の判定を兼ねる)。`some t` なら対象の構文だけから成り、`Γ` の下で型 `t` を持つ。 -/
def wtR (Γ : Ctx) : Expr → Option NaruSem.Ty
  | .lit _ (.nat _) => some .nat
  | .lit _ (.bool _) => some .bool
  | .var _ [x] => Γ x
  | .binop _ op l r =>
    match BinOp.ofString? op, wtR Γ l, wtR Γ r with
    | some k, some tl, some tr => binopResult k tl tr
    | _, _, _ => none
  | .unop _ op a =>
    if op = "!" then
      match wtR Γ a with
      | some .bool => some .bool
      | _ => none
    else none
  | .method _ r m [a] =>
    match NatMethod.ofString? m, wtR Γ r, wtR Γ a with
    | some _, some .nat, some .nat => some .nat
    | _, _, _ => none
  | .ite _ c t e =>
    match wtR Γ c, wtR Γ t, wtR Γ e with
    | some .bool, some tt, some te => if tt = te then some tt else none
    | _, _, _ => none
  | .matchE _ s arms =>
    match wtR Γ s with
    | some ts => if exhaustive ts arms then wtArmsR Γ ts arms else none
    | none => none
  | .block _ stmts (some e) =>
    match wtStmtsR Γ stmts with
    | some Γ' => wtR Γ' e
    | none => none
  | _ => none

/-- ブロックの `let` の列: 前から値を型付けし、注釈と照合して文脈を伸ばす。 -/
def wtStmtsR (Γ : Ctx) : List Stmt → Option Ctx
  | [] => some Γ
  | .letS _ x ty v :: rest =>
    match wtR Γ v with
    | some tv =>
      match annot ty tv with
      | some t => wtStmtsR (Γ.ext x t) rest
      | none => none
    | none => none

/-- `match` の腕の型付け: 各腕のパターンが scrutinee の型に合い、ガードは Bool、本体の型がすべて同じ。腕が無ければ `none`。 -/
def wtArmsR (Γ : Ctx) (ts : NaruSem.Ty) : List Arm → Option NaruSem.Ty
  | [] => none
  | arm :: rest =>
    match wtArmR Γ ts arm, rest with
    | none, _ => none
    | some t1, [] => some t1
    | some t1, _ :: _ =>
      match wtArmsR Γ ts rest with
      | some t2 => if t1 = t2 then some t1 else none
      | none => none

/-- 1 つの腕: パターンが scrutinee の型に合い、束縛を足した文脈でガードは Bool、結果は本体の型。 -/
def wtArmR (Γ : Ctx) (ts : NaruSem.Ty) : Arm → Option NaruSem.Ty
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none => wtR (Γ.extPat bs) b
      | some g =>
        match wtR (Γ.extPat bs) g with
        | some .bool => wtR (Γ.extPat bs) b
        | _ => none

end

/-! ## spec の型付けと対象範囲 -/

/-- ブロックの `let` が文脈に足す束縛の名前(`proppyS` のため: 値の型を知らずに `.val .nat` で足す。Core の `proppyS` と同じ)。 -/
def stmtsCtxP (Γ : SCtx) : List Stmt → SCtx
  | [] => Γ
  | .letS _ x _ _ :: rest => stmtsCtxP (Γ.ext x (.val .nat)) rest

mutual

/-- spec の式が命題でしか表せないか(量化、命題に束ねた局所名を含む)。コンパイラ(`Typecheck.proppy`)・Core の `proppyS` と同じ構文的な区分。 -/
def proppyS (Γ : SCtx) : Expr → Bool
  | .quant .. => true
  | .var _ [x] => match Γ x with | some .prop => true | _ => false
  | .block _ stmts tail =>
    proppyStmts Γ stmts || (match tail with | some e => proppyS (stmtsCtxP Γ stmts) e | none => false)
  | .ite _ c t e => proppyS Γ c || proppyS Γ t || proppyS Γ e
  | .binop _ _ l r => proppyS Γ l || proppyS Γ r
  | .unop _ _ a => proppyS Γ a
  | .matchE _ s arms => proppyS Γ s || proppyArms Γ arms
  | .method _ r _ [a] => proppyS Γ r || proppyS Γ a
  | _ => false

/-- `let` の値のどれかが命題か(前の `let` の束縛は同名の命題の局所名を隠す)。 -/
def proppyStmts (Γ : SCtx) : List Stmt → Bool
  | [] => false
  | .letS _ x _ v :: rest => proppyS Γ v || proppyStmts (Γ.ext x (.val .nat)) rest

/-- 腕の中では、パターンの束縛(値)が同名の命題の局所名を隠す。 -/
def proppyArms (Γ : SCtx) : List Arm → Bool
  | [] => false
  | .mk p g b :: rest =>
    let Γ' := match p with
      | .bind _ x => Γ.ext x (.val .nat)
      | _ => Γ
    (match g with | some g => proppyS Γ' g | none => false) || proppyS Γ' b || proppyArms Γ rest

end

/-- 量化の束縛を文脈に足す。束縛型の注釈が無い・Nat / Bool でなければ `none`。 -/
def SCtx.extBinders (Γ : SCtx) : List Binder → Option SCtx
  | [] => some Γ
  | b :: rest =>
    match b.ty with
    | some τ =>
      match τ.toTy? with
      | some t => SCtx.extBinders (Γ.ext b.name (.val t)) rest
      | none => none
    | none => none

/-- 命題の `let` の注釈: 無いか `Bool`。 -/
def annotProp : Option Ty → Bool
  | none => true
  | some τ => τ.toTy? = some .bool

mutual

/-- spec の式の型付け(対象範囲の判定を兼ねる)。`some (.val t)` なら Bool / Nat の値、`some .prop` なら命題。
値を要求する位置(算術・比較・等値(Nat)・`min` / `max` の被演算子、`match` の scrutinee、値の `let` の値)は `wtR Γ.vals`
(命題に束ねた名前はスコープ外)で判定し、命題を戻さない。 -/
def wtS (Γ : SCtx) : Expr → Option STy
  | .lit _ (.nat _) => some (.val .nat)
  | .lit _ (.bool _) => some (.val .bool)
  | .var _ [x] => Γ x
  | .ite _ c t e =>
    match wtS Γ c, wtS Γ t, wtS Γ e with
    | some tc, some tt, some te =>
      match tc.join tt with
      | some j => j.join te
      | none => none
    | _, _, _ => none
  | .binop _ op l r =>
    match BinOp.ofString? op with
    | some (.logic _) =>
      match wtS Γ l, wtS Γ r with
      | some tl, some tr => tl.join tr
      | _, _ => none
    | some (.eq _) =>
      -- 両辺が Nat の値なら値の等値、そうでなければ論理の位置(Bool の値どうしの等値、または命題の同値)
      if wtR Γ.vals l = some .nat ∧ wtR Γ.vals r = some .nat then some (.val .bool)
      else
        match wtS Γ l, wtS Γ r with
        | some tl, some tr => tl.join tr
        | _, _ => none
    | some (.cmp _) =>
      match wtR Γ.vals l, wtR Γ.vals r with
      | some tl, some tr => if tl = tr then some (.val .bool) else none
      | _, _ => none
    | some (.arith _) =>
      match wtR Γ.vals l, wtR Γ.vals r with
      | some .nat, some .nat => some (.val .nat)
      | _, _ => none
    | none => none
  | .unop _ op a =>
    if op = "!" then
      match wtS Γ a with
      | some t => if t.isForm then some t else none
      | none => none
    else none
  | .method _ r m [a] =>
    match NatMethod.ofString? m, wtR Γ.vals r, wtR Γ.vals a with
    | some _, some .nat, some .nat => some (.val .nat)
    | _, _, _ => none
  | .matchE _ s arms =>
    match wtR Γ.vals s with
    | some ts => if exhaustive ts arms then wtArmsS Γ ts arms else none
    | none => none
  | .block _ stmts (some e) =>
    match wtStmtsS Γ stmts with
    | some Γ' => wtS Γ' e
    | none => none
  | .quant _ _ bs b =>
    match bs with
    | [] => none
    | _ =>
      match SCtx.extBinders Γ bs with
      | some Γ' =>
        match wtS Γ' b with
        | some t => if t.isForm then some .prop else none
        | none => none
      | none => none
  | _ => none

/-- ブロックの `let` の列(spec): 値が命題なら名前を命題に束ね(注釈は無いか `Bool`)、そうでなければ値の型に束ねる(注釈があれば一致)。 -/
def wtStmtsS (Γ : SCtx) : List Stmt → Option SCtx
  | [] => some Γ
  | .letS _ x ty v :: rest =>
    if proppyS Γ v then
      if annotProp ty then
        match wtS Γ v with
        | some .prop => wtStmtsS (Γ.ext x .prop) rest
        | _ => none
      else none
    else
      match wtR Γ.vals v with
      | some tv =>
        match annot ty tv with
        | some t => wtStmtsS (Γ.ext x (.val t)) rest
        | none => none
      | none => none

/-- `match` の腕(spec): パターンの束縛は値、ガードと本体は論理の位置。結果は全腕の結び。 -/
def wtArmsS (Γ : SCtx) (ts : NaruSem.Ty) : List Arm → Option STy
  | [] => none
  | arm :: rest =>
    match wtArmS Γ ts arm, rest with
    | none, _ => none
    | some t1, [] => some t1
    | some t1, _ :: _ =>
      match wtArmsS Γ ts rest with
      | some t2 => t1.join t2
      | none => none

/-- 1 つの腕: パターンの束縛は値、束縛を足した文脈でガードと本体は論理の位置で、結果はその結び。 -/
def wtArmS (Γ : SCtx) (ts : NaruSem.Ty) : Arm → Option STy
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none =>
        match wtS (Γ.extVals bs) b with
        | some t => if t.isForm then some t else none
        | none => none
      | some g =>
        match wtS (Γ.extVals bs) g, wtS (Γ.extVals bs) b with
        | some tg, some tb => tg.join tb
        | _, _ => none

end

/-! ## 最小の fn / spec 宣言の包装 -/

/-- 仮引数(Surface の `Naru.Param`)。 -/
structure Param where
  name : String
  ty : Ty
  span : Span

def Param.toAst (p : Param) : Naru.Param := { name := p.name, ty := p.ty.toAst, span := p.span }

/-- 最小の非再帰 fn / spec 宣言: 構文解析の `Naru.Decl` のうち fn / predicate / condition / regime / property / claim が使う欄。 -/
structure Decl where
  kind : DeclKind
  name : String
  span : Span
  params : List Param
  /-- runtime の戻り型の注釈。spec 宣言には無い。 -/
  ret : Option Ty
  body : Expr

def Decl.toAst (d : Decl) : Naru.Decl :=
  { kind := d.kind, name := d.name, span := d.span, params := (d.params.map Param.toAst).toArray, ret := d.ret.map Ty.toAst,
    body := some d.body.toAst }

/-- 仮引数の型注釈から文脈の項目(名前, 型)。Nat / Bool 以外の注釈があれば `none`。 -/
def paramsCtx : List Param → Option (List (String × NaruSem.Ty))
  | [] => some []
  | p :: rest =>
    match p.ty.toTy? with
    | some t => (paramsCtx rest).map fun r => (p.name, t) :: r
    | none => none

/-- 宣言の適格性の結果: phase、仮引数の文脈、本体の型。 -/
inductive DeclTy where
  | runtime (ctx : List (String × NaruSem.Ty)) (t : NaruSem.Ty)
  | spec (ctx : List (String × NaruSem.Ty)) (τ : STy)
deriving DecidableEq, Repr

/-- 宣言の適格性: runtime は `fn` で、仮引数と戻り型の注釈が Nat / Bool、本体が戻り型の型(`wtR`)。spec は phase が spec の宣言で、戻り型の注釈が無く、
本体が論理の位置の型(`wtS`、`isForm`)。それ以外(observer・input・戻り型の無い fn・注釈が対象外 …)は `none`。 -/
def wtDecl (d : Decl) : Option DeclTy :=
  match paramsCtx d.params with
  | none => none
  | some entries =>
    match d.kind.phase, d.ret with
    | .runtime, some rτ =>
      if d.kind = .fn then
        match rτ.toTy? with
        | some tr => if wtR (Ctx.ofList entries) d.body = some tr then some (.runtime entries tr) else none
        | none => none
      else none
    | .spec, none =>
      match wtS (SCtx.ofList (entries.map fun (x, t) => (x, .val t))) d.body with
      | some τ => if τ.isForm then some (.spec entries τ) else none
      | none => none
    | _, _ => none

end NaruSem.Surf
