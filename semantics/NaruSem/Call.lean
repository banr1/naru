import NaruSem.SemTotality

/-!
# 関数・input の保存対象の Core の意味論と適格性(IDEAL.md C54、用語「関数・input の保存対象」)

C39〜C53 の Nat / Bool の式・演算・束縛・ガード付き `match`・spec の量化(`Scope.lean` / `Eval.lean` / `Sem.lean`)を土台に、
有限で非循環の宣言群に対する **大域名で静的に識別できる非再帰の fn / spec 宣言の呼出し** と **input の呼出し** を加えた Core の意味論を、
backend(`Backend/Model.lean` / `Backend/Statements.lean`)と frontend から独立に定める。既存の定義は変えず(C39〜C53 の条件はこの追加で拡大しない)、
呼出しを含む式・宣言群のための定義をここに並置する(名前空間 `NaruSem.Call`)。

- **署名と環境**: 宣言の識別は修飾名(`Core.Expr.call` の鍵)。署名 `Sig` は fn(仮引数の型と Nat / Bool の戻り型)/ input(同じ。本体は無く解釈は環境から)/
  spec 宣言(仮引数の型。結論は命題)で phase を持つ。`SigEnv`(鍵 → 署名)が型付けの文脈、`FEnv`(鍵 → 値の列 → 値)が runtime の呼出し先(fn の意味と
  input の解釈)の環境、`PEnv`(鍵 → 値の列 → 命題)が spec 宣言の意味の環境。
- **型付け**: `wtR Δ Γ e = some t`(runtime)は `Scope.lean` の `wtR` に `.call k args` を加えたもの: 鍵が fn / input の署名を持ち(spec 宣言は runtime から
  呼べない = phase)、実引数の数と型が仮引数に一致(`wtArgs`)すれば戻り型。`wtS Δ Γ e = some τ`(spec)は fn / input の呼出しを値(`.val t`)、spec 宣言の
  呼出しを命題(`.prop`)にし、実引数は値の位置(`wtR Δ Γ.vals`)。`proppyS` は spec 宣言の呼出しを命題でしか表せない式に数える(コンパイラの `proppy` と同じ)。
- **意味**: `eval Φ ρ e`(runtime)は `.call k args` を「実引数を順に評価し、環境の関数 `Φ k` に渡す」と読む(鍵が無い・引数が評価できない・関数が値を返さない
  ときは `none`: 既定値で埋めない)。`Sem Δ Φ Ψ ρ e P`(spec)は fn / input の呼出しの Bool の結果を「true である」という命題に写し(`callVal`)、spec 宣言の
  呼出しを `Ψ k` の命題にする(`callSpec`)。命題を Bool に戻す規則は無い。
- **宣言群**: `Prog` は宣言(`Decl`: fn / spec / input)の列で、**依存順**(呼出し先が前)に並べたものを適格とする。`wtProg Δ₀ P` は各宣言の本体を
  それより前の宣言(と外から与えた Δ₀)の署名だけで型付けし(= 呼出しグラフは非循環で、自己再帰・相互再帰・未解決の呼出し先は不適格)、鍵の重複を退け、
  署名を足していく。`interp I P` は宣言群の意味: input の解釈 `I : FEnv` から始めて、fn の本体の意味を関数として、spec 宣言の本体の意味を命題として
  順に環境に足す(`Interp.step`。各宣言の本体はそれより前の宣言の環境で読む)。
- **input の解釈**: 鍵ごとの `List Val → Option Val`。署名に従う(`FEnv.RespectsInputs`: 型の合う実引数に型の合う結果を返す)任意の解釈を環境から受け取る。
  特定の scenario の束縛ではない。解釈が署名に合わなければ前提が成り立たず、呼出しの評価は `none` になりうる(既定値に置き換えない)。

`CallTotality.lean` は、適格な式と対応する環境(文脈に合う局所環境、署名を守る関数環境、spec 宣言の環境が定義されている)について runtime の評価結果が
存在して一意であり(`eval_total` / `Eval_unique`)、spec の意味が存在して一意である(`Sem_exists` / `Sem_unique`)こと、適格な宣言群の意味がその署名を
守る(`interp_respects` / `interp_defined`: 各 fn の意味は型の合う実引数に型の合う値を返し、各 spec 宣言の意味は定義されている)ことを証明する。
翻訳の正しさや呼出し先の正しさは仮定しない(backend の出力は現れない)。
-/

namespace NaruSem.Call
open Naru

/-! ## 署名と環境 -/

/-- 宣言の署名。fn と input は runtime(値の位置で呼べる)、spec 宣言は spec(結論は命題)。 -/
inductive Sig where
  | fn (params : List Ty) (ret : Ty)
  | input (params : List Ty) (ret : Ty)
  | spec (params : List Ty)
deriving DecidableEq, Repr

def Sig.phase : Sig → Phase
  | .fn .. | .input .. => .runtime
  | .spec _ => .spec

/-- 値の位置で呼べる署名(fn / input): 仮引数の型と戻り型。 -/
def Sig.value? : Sig → Option (List Ty × Ty)
  | .fn ps t => some (ps, t)
  | .input ps t => some (ps, t)
  | .spec _ => none

/-- spec 宣言の署名: 仮引数の型。 -/
def Sig.spec? : Sig → Option (List Ty)
  | .spec ps => some ps
  | _ => none

/-- 署名の文脈: 修飾名 → 署名(宣言が無ければ `none`)。 -/
abbrev SigEnv := String → Option Sig

def SigEnv.empty : SigEnv := fun _ => none

def SigEnv.ext (Δ : SigEnv) (k : String) (s : Sig) : SigEnv := fun y => if y = k then some s else Δ y

/-- 鍵が fn / input なら、その仮引数の型と戻り型。 -/
def valueSig? (Δ : SigEnv) (k : String) : Option (List Ty × Ty) := (Δ k).bind Sig.value?

/-- 鍵が spec 宣言なら、その仮引数の型。 -/
def specSig? (Δ : SigEnv) (k : String) : Option (List Ty) := (Δ k).bind Sig.spec?

def isSpecKey (Δ : SigEnv) (k : String) : Bool := (specSig? Δ k).isSome

def isValueKey (Δ : SigEnv) (k : String) : Bool := (valueSig? Δ k).isSome

/-- runtime の呼出し先の環境: 修飾名 → (実引数の値の列 → 結果)。fn の意味と input の解釈。 -/
abbrev FEnv := String → Option (List Val → Option Val)

def FEnv.empty : FEnv := fun _ => none

def FEnv.ext (Φ : FEnv) (k : String) (f : List Val → Option Val) : FEnv := fun y => if y = k then some f else Φ y

/-- spec 宣言の意味の環境: 修飾名 → (実引数の値の列 → 命題)。 -/
abbrev PEnv := String → Option (List Val → Prop)

def PEnv.empty : PEnv := fun _ => none

def PEnv.ext (Ψ : PEnv) (k : String) (F : List Val → Prop) : PEnv := fun y => if y = k then some F else Ψ y

/-! ## runtime の型付けと対象範囲 -/

mutual

/-- runtime の式の型付け(対象範囲の判定を兼ねる)。`Scope.lean` の `wtR` に呼出しを加えたもの。 -/
def wtR (Δ : SigEnv) (Γ : Ctx) : Core.Expr → Option Ty
  | .lit (.nat _) .nat => some .nat
  | .lit (.bool _) .bool => some .bool
  | .var x => Γ x
  | .call k args =>
    match valueSig? Δ k with
    | some (ps, t) => if wtArgs Δ Γ args ps then some t else none
    | none => none
  | .let_ x ty v b =>
    match wtR Δ Γ v, TyV.toTy? ty with
    | some tv, some ta => if tv = ta then wtR Δ (Γ.ext x tv) b else none
    | _, _ => none
  | .ite c t e =>
    match wtR Δ Γ c, wtR Δ Γ t, wtR Δ Γ e with
    | some .bool, some tt, some te => if tt = te then some tt else none
    | _, _, _ => none
  | .binop op l r ty =>
    match BinOp.ofString? op, wtR Δ Γ l, wtR Δ Γ r, TyV.toTy? ty with
    | some k, some tl, some tr, some ta => k.result tl tr ta
    | _, _, _, _ => none
  | .unop op a =>
    if op = "!" then
      match wtR Δ Γ a with
      | some .bool => some .bool
      | _ => none
    else none
  | .method tn m r [a] rt =>
    if tn = "Nat" then
      match NatMethod.ofString? m, wtR Δ Γ r, wtR Δ Γ a, rt with
      | some _, some .nat, some .nat, .nat => some .nat
      | _, _, _, _ => none
    else none
  | .match_ s st arms =>
    match wtR Δ Γ s, TyV.toTy? st with
    | some ts, some ta => if ts = ta && exhaustive ts arms then wtArmsR Δ Γ ts arms else none
    | _, _ => none
  | _ => none

/-- 実引数の列の型付け: 仮引数の型の列と同じ長さで、順に型が合う。 -/
def wtArgs (Δ : SigEnv) (Γ : Ctx) : List Core.Expr → List Ty → Bool
  | [], [] => true
  | a :: as, t :: ts => decide (wtR Δ Γ a = some t) && wtArgs Δ Γ as ts
  | _, _ => false

def wtArmsR (Δ : SigEnv) (Γ : Ctx) (ts : Ty) : List Core.Arm → Option Ty
  | [] => none
  | arm :: rest =>
    match wtArmR Δ Γ ts arm, rest with
    | none, _ => none
    | some t1, [] => some t1
    | some t1, _ :: _ =>
      match wtArmsR Δ Γ ts rest with
      | some t2 => if t1 = t2 then some t1 else none
      | none => none

def wtArmR (Δ : SigEnv) (Γ : Ctx) (ts : Ty) : Core.Arm → Option Ty
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none => wtR Δ (Γ.extPat bs) b
      | some g =>
        match wtR Δ (Γ.extPat bs) g with
        | some .bool => wtR Δ (Γ.extPat bs) b
        | _ => none

end

/-! ## spec の型付けと対象範囲 -/

mutual

/-- spec の式が命題でしか表せないか(量化、命題に束ねた局所名、spec 宣言の呼出しを含む)。コンパイラの `proppy` と同じ構文的な区分。 -/
def proppyS (Δ : SigEnv) (Γ : SCtx) : Core.Expr → Bool
  | .quant .. => true
  | .var x => match Γ x with | some .prop => true | _ => false
  | .call k args => isSpecKey Δ k || proppyArgs Δ Γ args
  | .let_ x _ v b => proppyS Δ Γ v || proppyS Δ (Γ.ext x (.val .nat)) b
  | .ite c t e => proppyS Δ Γ c || proppyS Δ Γ t || proppyS Δ Γ e
  | .binop _ l r _ => proppyS Δ Γ l || proppyS Δ Γ r
  | .unop _ a => proppyS Δ Γ a
  | .match_ s _ arms => proppyS Δ Γ s || proppyArms Δ Γ arms
  | .method _ _ r [a] _ => proppyS Δ Γ r || proppyS Δ Γ a
  | _ => false

def proppyArgs (Δ : SigEnv) (Γ : SCtx) : List Core.Expr → Bool
  | [] => false
  | a :: as => proppyS Δ Γ a || proppyArgs Δ Γ as

def proppyArms (Δ : SigEnv) (Γ : SCtx) : List Core.Arm → Bool
  | [] => false
  | .mk p g b :: rest =>
    let Γ' := match p with
      | .bind x => Γ.ext x (.val .nat)
      | _ => Γ
    (match g with | some g => proppyS Δ Γ' g | none => false) || proppyS Δ Γ' b || proppyArms Δ Γ rest

end

mutual

/-- spec の式の型付け(対象範囲の判定を兼ねる)。`Scope.lean` の `wtS` に呼出しを加えたもの: fn / input の呼出しは値(`.val t`)、spec 宣言の呼出しは
命題(`.prop`)。実引数は値の位置(`wtR Δ Γ.vals`: 命題に束ねた名前はスコープ外で、命題を渡さない)。 -/
def wtS (Δ : SigEnv) (Γ : SCtx) : Core.Expr → Option STy
  | .lit (.nat _) .nat => some (.val .nat)
  | .lit (.bool _) .bool => some (.val .bool)
  | .var x => Γ x
  | .call k args =>
    match Δ k with
    | some (.spec ps) => if wtArgs Δ Γ.vals args ps then some .prop else none
    | some (.fn ps t) => if wtArgs Δ Γ.vals args ps then some (.val t) else none
    | some (.input ps t) => if wtArgs Δ Γ.vals args ps then some (.val t) else none
    | none => none
  | .let_ x ty v b =>
    match TyV.toTy? ty with
    | some .nat =>
      match wtR Δ Γ.vals v with
      | some .nat => wtS Δ (Γ.ext x (.val .nat)) b
      | _ => none
    | some .bool =>
      if proppyS Δ Γ v then
        match wtS Δ Γ v with
        | some .prop => wtS Δ (Γ.ext x .prop) b
        | _ => none
      else
        match wtR Δ Γ.vals v with
        | some .bool => wtS Δ (Γ.ext x (.val .bool)) b
        | _ => none
    | none => none
  | .ite c t e =>
    match wtS Δ Γ c, wtS Δ Γ t, wtS Δ Γ e with
    | some tc, some tt, some te =>
      match tc.join tt with
      | some j => j.join te
      | none => none
    | _, _, _ => none
  | .binop op l r ty =>
    match BinOp.ofString? op, TyV.toTy? ty with
    | some (.logic _), some .bool =>
      match wtS Δ Γ l, wtS Δ Γ r with
      | some tl, some tr => tl.join tr
      | _, _ => none
    | some (.eq _), some .bool =>
      match wtS Δ Γ l, wtS Δ Γ r with
      | some tl, some tr => tl.join tr
      | _, _ => none
    | some (.eq _), some .nat =>
      match wtR Δ Γ.vals l, wtR Δ Γ.vals r with
      | some .nat, some .nat => some (.val .bool)
      | _, _ => none
    | some (.cmp _), some ta =>
      match wtR Δ Γ.vals l, wtR Δ Γ.vals r with
      | some tl, some tr => if tl = ta && tr = ta then some (.val .bool) else none
      | _, _ => none
    | some (.arith _), some .nat =>
      match wtR Δ Γ.vals l, wtR Δ Γ.vals r with
      | some .nat, some .nat => some (.val .nat)
      | _, _ => none
    | _, _ => none
  | .unop op a =>
    if op = "!" then
      match wtS Δ Γ a with
      | some t => if t.isForm then some t else none
      | none => none
    else none
  | .method tn m r [a] rt =>
    if tn = "Nat" then
      match NatMethod.ofString? m, wtR Δ Γ.vals r, wtR Δ Γ.vals a, rt with
      | some _, some .nat, some .nat, .nat => some (.val .nat)
      | _, _, _, _ => none
    else none
  | .match_ s st arms =>
    match wtR Δ Γ.vals s, TyV.toTy? st with
    | some ts, some ta => if ts = ta && exhaustive ts arms then wtArmsS Δ Γ ts arms else none
    | _, _ => none
  | .quant _ bs b =>
    match bs with
    | [] => none
    | _ =>
      match Γ.extBinders bs with
      | some Γ' =>
        match wtS Δ Γ' b with
        | some t => if t.isForm then some .prop else none
        | none => none
      | none => none
  | _ => none

def wtArmsS (Δ : SigEnv) (Γ : SCtx) (ts : Ty) : List Core.Arm → Option STy
  | [] => none
  | arm :: rest =>
    match wtArmS Δ Γ ts arm, rest with
    | none, _ => none
    | some t1, [] => some t1
    | some t1, _ :: _ =>
      match wtArmsS Δ Γ ts rest with
      | some t2 => t1.join t2
      | none => none

def wtArmS (Δ : SigEnv) (Γ : SCtx) (ts : Ty) : Core.Arm → Option STy
  | .mk p g b =>
    match wtPat ts p with
    | none => none
    | some bs =>
      match g with
      | none =>
        match wtS Δ (Γ.extVals bs) b with
        | some t => if t.isForm then some t else none
        | none => none
      | some g =>
        match wtS Δ (Γ.extVals bs) g, wtS Δ (Γ.extVals bs) b with
        | some tg, some tb => tg.join tb
        | _, _ => none

end

/-! ## runtime の意味 -/

mutual

/-- runtime の式の意味。`Eval.lean` の `eval` に呼出しを加えたもの: 実引数を順に評価し、環境の関数 `Φ k` に渡す。
鍵が無い・実引数が評価できない・関数が値を返さないときは `none`(行き詰まり。既定値で埋めない)。 -/
def eval (Φ : FEnv) (ρ : Env) : Core.Expr → Option Val
  | .lit (.nat n) .nat => some (.nat n)
  | .lit (.bool b) .bool => some (.bool b)
  | .var x => ρ x
  | .call k args =>
    match Φ k, evalArgs Φ ρ args with
    | some f, some vs => f vs
    | _, _ => none
  | .let_ x _ v b =>
    match eval Φ ρ v with
    | some w => eval Φ (ρ.ext x w) b
    | none => none
  | .ite c t e =>
    match eval Φ ρ c with
    | some (.bool true) => eval Φ ρ t
    | some (.bool false) => eval Φ ρ e
    | _ => none
  | .binop op l r _ =>
    match BinOp.ofString? op, eval Φ ρ l, eval Φ ρ r with
    | some k, some a, some b => k.apply a b
    | _, _, _ => none
  | .unop op a =>
    if op = "!" then
      match eval Φ ρ a with
      | some (.bool x) => some (.bool (!x))
      | _ => none
    else none
  | .method tn m r [a] _ =>
    if tn = "Nat" then
      match NatMethod.ofString? m, eval Φ ρ r, eval Φ ρ a with
      | some k, some (.nat x), some (.nat y) => some (.nat (k.eval x y))
      | _, _, _ => none
    else none
  | .match_ s _ arms =>
    match eval Φ ρ s with
    | some v => evalArms Φ ρ v arms
    | none => none
  | _ => none

/-- 実引数の列の評価(順に)。どれかが行き詰まれば `none`。 -/
def evalArgs (Φ : FEnv) (ρ : Env) : List Core.Expr → Option (List Val)
  | [] => some []
  | a :: as =>
    match eval Φ ρ a, evalArgs Φ ρ as with
    | some v, some vs => some (v :: vs)
    | _, _ => none

def evalArms (Φ : FEnv) (ρ : Env) (v : Val) : List Core.Arm → Option Val
  | [] => none
  | .mk p g b :: rest =>
    match matchPat p v with
    | none => evalArms Φ ρ v rest
    | some bs =>
      match g with
      | none => eval Φ (ρ.extList bs) b
      | some g =>
        match eval Φ (ρ.extList bs) g with
        | some (.bool true) => eval Φ (ρ.extList bs) b
        | some (.bool false) => evalArms Φ ρ v rest
        | _ => none

end

/-- 評価関係の形: `Eval Φ ρ e v` は `eval Φ ρ e = some v`。 -/
def Eval (Φ : FEnv) (ρ : Env) (e : Core.Expr) (v : Val) : Prop := eval Φ ρ e = some v

/-! ## spec の意味 -/

/-- spec の式の意味。`Sem.lean` の `Sem` に呼出しを加えたもの。`Δ` は署名(`let` の値が命題か(`proppyS`)と、呼出し先の phase の判定)、`Φ` は runtime の
呼出し先、`Ψ` は spec 宣言の意味。 -/
inductive Sem (Δ : SigEnv) (Φ : FEnv) (Ψ : PEnv) : SEnv → Core.Expr → Prop → Prop where
  | lit {ρ : SEnv} {b : Bool} : Sem Δ Φ Ψ ρ (.lit (.bool b) .bool) (b = true)
  | varVal {ρ : SEnv} {x : String} {b : Bool} (h : ρ x = some (.val (.bool b))) : Sem Δ Φ Ψ ρ (.var x) (b = true)
  | varProp {ρ : SEnv} {x : String} {P : Prop} (h : ρ x = some (.prop P)) : Sem Δ Φ Ψ ρ (.var x) P
  /-- fn / input の呼出し(論理の位置): Bool の結果を「true である」という命題に写す。実引数は値の位置で評価する。 -/
  | callVal {ρ : SEnv} {k : String} {args : List Core.Expr} {f : List Val → Option Val} {vs : List Val} {b : Bool}
      (hk : isValueKey Δ k = true) (hf : Φ k = some f) (ha : evalArgs Φ ρ.vals args = some vs) (hv : f vs = some (.bool b)) :
      Sem Δ Φ Ψ ρ (.call k args) (b = true)
  /-- spec 宣言の呼出し: その宣言の意味(命題)に実引数の値を渡す。 -/
  | callSpec {ρ : SEnv} {k : String} {args : List Core.Expr} {F : List Val → Prop} {vs : List Val}
      (hk : isSpecKey Δ k = true) (hF : Ψ k = some F) (ha : evalArgs Φ ρ.vals args = some vs) :
      Sem Δ Φ Ψ ρ (.call k args) (F vs)
  | logic {ρ : SEnv} {op : String} {k : LogicOp} {l r : Core.Expr} {P Q : Prop}
      (hk : BinOp.ofString? op = some (.logic k)) (hl : Sem Δ Φ Ψ ρ l P) (hr : Sem Δ Φ Ψ ρ r Q) :
      Sem Δ Φ Ψ ρ (.binop op l r .bool) (k.prop P Q)
  | eqNat {ρ : SEnv} {op : String} {k : EqOp} {l r : Core.Expr} {a b : Nat}
      (hk : BinOp.ofString? op = some (.eq k)) (hl : eval Φ ρ.vals l = some (.nat a)) (hr : eval Φ ρ.vals r = some (.nat b)) :
      Sem Δ Φ Ψ ρ (.binop op l r .nat) (k.propNat a b)
  | eqForm {ρ : SEnv} {op : String} {k : EqOp} {l r : Core.Expr} {P Q : Prop}
      (hk : BinOp.ofString? op = some (.eq k)) (hl : Sem Δ Φ Ψ ρ l P) (hr : Sem Δ Φ Ψ ρ r Q) :
      Sem Δ Φ Ψ ρ (.binop op l r .bool) (k.propIff P Q)
  | cmpNat {ρ : SEnv} {op : String} {k : CmpOp} {l r : Core.Expr} {a b : Nat}
      (hk : BinOp.ofString? op = some (.cmp k)) (hl : eval Φ ρ.vals l = some (.nat a)) (hr : eval Φ ρ.vals r = some (.nat b)) :
      Sem Δ Φ Ψ ρ (.binop op l r .nat) (k.propNat a b)
  | cmpBool {ρ : SEnv} {op : String} {k : CmpOp} {l r : Core.Expr} {a b : Bool}
      (hk : BinOp.ofString? op = some (.cmp k)) (hl : eval Φ ρ.vals l = some (.bool a)) (hr : eval Φ ρ.vals r = some (.bool b)) :
      Sem Δ Φ Ψ ρ (.binop op l r .bool) (k.evalBool a b = true)
  | not {ρ : SEnv} {a : Core.Expr} {P : Prop} (h : Sem Δ Φ Ψ ρ a P) : Sem Δ Φ Ψ ρ (.unop "!" a) (¬ P)
  | ite {ρ : SEnv} {c t e : Core.Expr} {C P Q : Prop} (hc : Sem Δ Φ Ψ ρ c C) (ht : Sem Δ Φ Ψ ρ t P) (he : Sem Δ Φ Ψ ρ e Q) :
      Sem Δ Φ Ψ ρ (.ite c t e) ((C → P) ∧ (¬ C → Q))
  | letNat {ρ : SEnv} {x : String} {v b : Core.Expr} {n : Nat} {Q : Prop}
      (hv : eval Φ ρ.vals v = some (.nat n)) (hb : Sem Δ Φ Ψ (ρ.ext x (.val (.nat n))) b Q) :
      Sem Δ Φ Ψ ρ (.let_ x .nat v b) Q
  | letBoolVal {ρ : SEnv} {x : String} {v b : Core.Expr} {w : Bool} {Q : Prop}
      (hp : proppyS Δ ρ.ctx v = false) (hv : eval Φ ρ.vals v = some (.bool w)) (hb : Sem Δ Φ Ψ (ρ.ext x (.val (.bool w))) b Q) :
      Sem Δ Φ Ψ ρ (.let_ x .bool v b) Q
  | letProp {ρ : SEnv} {x : String} {v b : Core.Expr} {P Q : Prop}
      (hp : proppyS Δ ρ.ctx v = true) (hv : Sem Δ Φ Ψ ρ v P) (hb : Sem Δ Φ Ψ (ρ.ext x (.prop P)) b Q) :
      Sem Δ Φ Ψ ρ (.let_ x .bool v b) Q
  | matchSkip {ρ : SEnv} {s : Core.Expr} {st : TyV} {p : Core.Pat} {g : Option Core.Expr} {b : Core.Expr} {rest : List Core.Arm}
      {v : Val} {P : Prop}
      (hs : eval Φ ρ.vals s = some v) (hp : matchPat p v = none) (hr : Sem Δ Φ Ψ ρ (.match_ s st rest) P) :
      Sem Δ Φ Ψ ρ (.match_ s st (.mk p g b :: rest)) P
  | matchHit {ρ : SEnv} {s : Core.Expr} {st : TyV} {p : Core.Pat} {b : Core.Expr} {rest : List Core.Arm}
      {v : Val} {bs : List (String × Val)} {P : Prop}
      (hs : eval Φ ρ.vals s = some v) (hp : matchPat p v = some bs) (hb : Sem Δ Φ Ψ (ρ.extVals bs) b P) :
      Sem Δ Φ Ψ ρ (.match_ s st (.mk p none b :: rest)) P
  | matchGuard {ρ : SEnv} {s : Core.Expr} {st : TyV} {p : Core.Pat} {g b : Core.Expr} {rest : List Core.Arm}
      {v : Val} {bs : List (String × Val)} {G P R : Prop}
      (hs : eval Φ ρ.vals s = some v) (hp : matchPat p v = some bs) (hg : Sem Δ Φ Ψ (ρ.extVals bs) g G)
      (hb : Sem Δ Φ Ψ (ρ.extVals bs) b P) (hr : Sem Δ Φ Ψ ρ (.match_ s st rest) R) :
      Sem Δ Φ Ψ ρ (.match_ s st (.mk p (some g) b :: rest)) ((G → P) ∧ (¬ G → R))
  | quantNil {ρ : SEnv} {q : Quant} {b : Core.Expr} {P : Prop} (h : Sem Δ Φ Ψ ρ b P) : Sem Δ Φ Ψ ρ (.quant q [] b) P
  | forallCons {ρ : SEnv} {x : String} {tv : TyV} {t : Ty} {bs : List (String × TyV)} {b : Core.Expr} {F : t.carrier → Prop}
      (ht : TyV.toTy? tv = some t)
      (h : ∀ a : t.carrier, Sem Δ Φ Ψ (ρ.ext x (.val (Val.of t a))) (.quant .forall_ bs b) (F a)) :
      Sem Δ Φ Ψ ρ (.quant .forall_ ((x, tv) :: bs) b) (∀ a, F a)
  | existsCons {ρ : SEnv} {x : String} {tv : TyV} {t : Ty} {bs : List (String × TyV)} {b : Core.Expr} {F : t.carrier → Prop}
      (ht : TyV.toTy? tv = some t)
      (h : ∀ a : t.carrier, Sem Δ Φ Ψ (ρ.ext x (.val (Val.of t a))) (.quant .exists_ bs b) (F a)) :
      Sem Δ Φ Ψ ρ (.quant .exists_ ((x, tv) :: bs) b) (∃ a, F a)

/-! ## 宣言群 -/

/-- 対象の宣言(Core)。fn は runtime の本体を持ち、spec 宣言は命題の本体を持ち、input は本体を持たない(解釈は環境から)。 -/
inductive Decl where
  | fn (key : String) (params : List (String × Ty)) (ret : Ty) (body : Core.Expr)
  | spec (key : String) (params : List (String × Ty)) (body : Core.Expr)
  | input (key : String) (params : List (String × Ty)) (ret : Ty)

def Decl.key : Decl → String
  | .fn k .. | .spec k .. | .input k .. => k

def Decl.params : Decl → List (String × Ty)
  | .fn _ ps .. | .spec _ ps .. | .input _ ps .. => ps

def Decl.sig : Decl → Sig
  | .fn _ ps t _ => .fn (ps.map (·.2)) t
  | .spec _ ps _ => .spec (ps.map (·.2))
  | .input _ ps t => .input (ps.map (·.2)) t

def Decl.phase (d : Decl) : Phase := d.sig.phase

/-- 宣言群: 依存順(呼出し先が前)に並べた宣言の列。 -/
abbrev Prog := List Decl

/-- 仮引数の文脈(runtime)。 -/
def paramCtx (ps : List (String × Ty)) : Ctx := Ctx.ofList ps

/-- 仮引数の文脈(spec。仮引数は値)。 -/
def paramSCtx (ps : List (String × Ty)) : SCtx := SCtx.ofList (ps.map fun (x, t) => (x, .val t))

/-- 宣言 1 つの適格性(署名の文脈 `Δ` = それより前の宣言の署名): fn は本体が戻り型の型、spec 宣言は本体が論理の位置の型、input は署名だけ。 -/
def wtDecl (Δ : SigEnv) : Decl → Bool
  | .fn _ ps t body => decide (wtR Δ (paramCtx ps) body = some t)
  | .spec _ ps body =>
    match wtS Δ (paramSCtx ps) body with
    | some τ => τ.isForm
    | none => false
  | .input _ _ _ => true

/-- 宣言群の適格性: 前から順に、鍵が未使用で(重複なし)、本体がそれまでの署名だけで適格(呼出し先は前の宣言か input: 非循環)なら署名を足す。
結果はすべての署名の文脈。自己再帰・相互再帰・未解決の呼出し先・phase の誤り・引数の不一致は `none`(保証対象でない)。 -/
def wtProg (Δ : SigEnv) : Prog → Option SigEnv
  | [] => some Δ
  | d :: rest => if (Δ d.key).isNone && wtDecl Δ d then wtProg (Δ.ext d.key d.sig) rest else none

/-- 仮引数に実引数の値を束ねる: 数と型が合えば環境(後ろが前を隠す)、合わなければ `none`。 -/
def bindParams (ps : List (String × Ty)) (vs : List Val) : Option Env :=
  if vs.map Val.ty = ps.map (·.2) then some (Env.ofList ((ps.map (·.1)).zip vs)) else none

/-- 値の環境を spec の環境(すべて値)にする。 -/
def Env.toSEnv (ρ : Env) : SEnv := fun x => (ρ x).map SVal.val

/-- 宣言群の意味: 署名・runtime の呼出し先(fn の意味と input の解釈)・spec 宣言の意味。 -/
structure Interp where
  Δ : SigEnv
  Φ : FEnv
  Ψ : PEnv

/-- 宣言 1 つの意味を足す。fn: 実引数を仮引数に束ねて本体を(それまでの環境で)評価する関数。spec 宣言: 実引数を束ねた環境での本体の意味
(`∃ P, Sem … P ∧ P`。適格なら意味は存在して一意なので、これは本体の意味そのもの — `CallTotality.lean` の `Interp.spec_meaning`)。input: 署名だけ
(解釈は最初の環境 `I` にある)。 -/
def Interp.step (m : Interp) : Decl → Interp
  | .fn k ps t body =>
    { Δ := m.Δ.ext k (.fn (ps.map (·.2)) t),
      Φ := m.Φ.ext k fun vs =>
        match bindParams ps vs with
        | some ρ => eval m.Φ ρ body
        | none => none,
      Ψ := m.Ψ }
  | .spec k ps body =>
    { Δ := m.Δ.ext k (.spec (ps.map (·.2))), Φ := m.Φ,
      Ψ := m.Ψ.ext k fun vs => ∃ ρ, bindParams ps vs = some ρ ∧ ∃ P, Sem m.Δ m.Φ m.Ψ (Env.toSEnv ρ) body P ∧ P }
  | .input k ps t => { m with Δ := m.Δ.ext k (.input (ps.map (·.2)) t) }

def interpFrom (m : Interp) : Prog → Interp
  | [] => m
  | d :: rest => interpFrom (m.step d) rest

/-- 最初の環境: 署名と spec 宣言は無く、runtime の呼出し先は input の解釈 `I`。 -/
def Interp.init (I : FEnv) : Interp := { Δ := SigEnv.empty, Φ := I, Ψ := PEnv.empty }

/-- 宣言群の意味(input の解釈 `I` の下で)。 -/
def interp (I : FEnv) (P : Prog) : Interp := interpFrom (Interp.init I) P

/-! ## 環境と署名の対応 -/

/-- 関数環境が署名を守る: fn / input の署名のある鍵には関数があり、型の合う実引数に型の合う結果を返す。 -/
def FEnv.Respects (Φ : FEnv) (Δ : SigEnv) : Prop :=
  ∀ k ps t, valueSig? Δ k = some (ps, t) →
    ∃ f, Φ k = some f ∧ ∀ vs : List Val, vs.map Val.ty = ps → ∃ v, f vs = some v ∧ v.ty = t

/-- spec 宣言の環境が定義されている: spec 宣言の署名のある鍵には意味がある。 -/
def PEnv.Defined (Ψ : PEnv) (Δ : SigEnv) : Prop :=
  ∀ k ps, specSig? Δ k = some ps → ∃ F, Ψ k = some F

/-- input の解釈が宣言群の input の署名を守る(任意の全域関数の解釈: 型の合う実引数に型の合う結果を返す)。 -/
def FEnv.RespectsInputs (I : FEnv) (P : Prog) : Prop :=
  ∀ k ps t, Decl.input k ps t ∈ P →
    ∃ f, I k = some f ∧ ∀ vs : List Val, vs.map Val.ty = ps.map (·.2) → ∃ v, f vs = some v ∧ v.ty = t

end NaruSem.Call
