import NaruSem.SurfaceCallLower
import NaruSem.DenoteProp

/-! 呼出しの局所的な合成補題の非空な検体。引数・環境は任意であり、
callee の存在や成功は仮定しない。全式・宣言群の保存の代用ではない。 -/
namespace NaruSem.Surf.Call
open Naru

def pairParams : List (String × NaruSem.Ty) := [("left", .nat), ("right", .nat)]

theorem named_call (T : Table) (Γ : SCtx) (ρ : SEnv) (Φ : NaruSem.Call.FEnv)
    (n m : Nat) (k : String)
    (hr : T.resolve ["Examples", "pair"] = some k)
    (hs : (T.sig k).bind DeclSig.value? = some (pairParams, .nat)) :
    lower T Γ (.call ⟨0, 0⟩ (.var ⟨0, 0⟩ ["Examples", "pair"])
      [.named "right" (.lit ⟨0, 0⟩ (.nat m)), .named "left" (.lit ⟨0, 0⟩ (.nat n))]) =
        some (.call k [.lit (.nat n) .nat, .lit (.nat m) .nat]) ∧
    eval T Φ ρ (.call ⟨0, 0⟩ (.var ⟨0, 0⟩ ["Examples", "pair"])
      [.named "right" (.lit ⟨0, 0⟩ (.nat m)), .named "left" (.lit ⟨0, 0⟩ (.nat n))]) =
        NaruSem.Call.eval Φ ρ.vals (.call k [.lit (.nat n) .nat, .lit (.nat m) .nat]) := by
  apply lower_call_eval (ps := pairParams) (t := .nat)
    (cargs := [(some "right", .lit (.nat m) .nat), (some "left", .lit (.nat n) .nat)])
    (vals := [(some "right", .nat m), (some "left", .nat n)]) (vs := [.nat n, .nat m])
  all_goals first | exact hr | exact hs | rfl

theorem ufcs_call (T : Table) (Γ : SCtx) (ρ : SEnv) (Φ : NaruSem.Call.FEnv)
    (n m : Nat) (k : String)
    (hg : ufcs T Γ "pair" = true) (hρ : ufcs T ρ "pair" = true)
    (hr : T.resolve ["pair"] = some k)
    (hs : (T.sig k).bind DeclSig.value? = some (pairParams, .nat)) :
    lower T Γ (.method ⟨0, 0⟩ (.lit ⟨0, 0⟩ (.nat n)) "pair"
      [.named "right" (.lit ⟨0, 0⟩ (.nat m))]) =
        some (.call k [.lit (.nat n) .nat, .lit (.nat m) .nat]) ∧
    eval T Φ ρ (.method ⟨0, 0⟩ (.lit ⟨0, 0⟩ (.nat n)) "pair"
      [.named "right" (.lit ⟨0, 0⟩ (.nat m))]) =
        NaruSem.Call.eval Φ ρ.vals (.call k [.lit (.nat n) .nat, .lit (.nat m) .nat]) := by
  apply lower_ufcs_eval (ps := pairParams) (t := .nat)
    (cr := .lit (.nat n) .nat) (rv := .nat n)
    (cargs := [(some "right", .lit (.nat m) .nat)])
    (vals := [(some "right", .nat m)]) (vs := [.nat n, .nat m])
  all_goals first | exact hg | exact hρ | exact hr | exact hs | rfl

theorem zero_args (Φ : NaruSem.Call.FEnv) (ρ : Env) :
    NaruSem.Call.evalArgs Φ ρ [] = some [] :=
  arrange_eval (ps := []) (args := []) (vals := []) rfl rfl rfl

theorem named_wt (Δ : NaruSem.Call.SigEnv) (Γ : Ctx) (n m : Nat) :
    NaruSem.Call.wtArgs Δ Γ [.lit (.nat n) .nat, .lit (.nat m) .nat] [.nat, .nat] = true :=
  arrange_wt (ps := pairParams)
    (args := [(some "right", .lit (.nat m) .nat), (some "left", .lit (.nat n) .nat)])
    (tys := [(some "right", .nat), (some "left", .nat)]) rfl rfl rfl

/-- 型が同じでも順序を交換した値は対応しない。 -/
theorem swapped_values :
    NaruSem.Call.evalArgs NaruSem.Call.FEnv.empty Env.empty
      [.lit (.nat 5) .nat, .lit (.nat 3) .nat] ≠ some [.nat 3, .nat 5] := by decide


/-- 同名のNat束縛をBoolで隠すブロック。任意の関数・局所環境で対応する。 -/
theorem block_shadow (T : Table) (Γ : SCtx) (Φ : NaruSem.Call.FEnv)
    (n : Nat) (b : Bool) :
    lower T Γ (.block ⟨0, 0⟩
      [.letS ⟨0, 0⟩ "x" none (.lit ⟨0, 0⟩ (.nat n)),
       .letS ⟨0, 0⟩ "x" none (.lit ⟨0, 0⟩ (.bool b))]
      (some (.var ⟨0, 0⟩ ["x"]))) =
      some (Surf.mkLets [("x", .nat, .lit (.nat n) .nat),
        ("x", .bool, .lit (.bool b) .bool)] (.var "x")) ∧
    ∀ ρ, eval T Φ ρ (.block ⟨0, 0⟩
      [.letS ⟨0, 0⟩ "x" none (.lit ⟨0, 0⟩ (.nat n)),
       .letS ⟨0, 0⟩ "x" none (.lit ⟨0, 0⟩ (.bool b))]
      (some (.var ⟨0, 0⟩ ["x"]))) =
      NaruSem.Call.eval Φ ρ.vals (Surf.mkLets [("x", .nat, .lit (.nat n) .nat),
        ("x", .bool, .lit (.bool b) .bool)] (.var "x")) := by
  apply lower_block_eval (Γ' := (Γ.ext "x" (.val .nat)).ext "x" (.val .bool))
  · rfl
  · rfl
  · rfl
  · intro ρ
    change some ((ρ.ext "x" (.val (.nat n))).ext "x" (.val (.bool b))).vals =
      some ((ρ.vals.ext "x" (.nat n)).ext "x" (.bool b))
    rw [SEnv.vals_ext_val, SEnv.vals_ext_val]
  · intro ρ
    rfl

/-- 子式と後続列の証拠からletを合成する非空な検体。 -/
theorem stmt_shadow (T : Table) (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (n : Nat) :
    (evalStmts T Φ ρ [.letS ⟨0, 0⟩ "x" none (.lit ⟨0, 0⟩ (.nat n))]).map SEnv.vals =
      evalBinds Φ ρ.vals [("x", .nat, .lit (.nat n) .nat)] := by
  apply lowerStmts_cons_eval
  · rfl
  · intro w
    change some (ρ.ext "x" (.val w)).vals = some (ρ.vals.ext "x" w)
    rw [SEnv.vals_ext_val]

/-- 同名束縛で型を変更しても末尾の型は最新の束縛で決まる。 -/
theorem binds_shadow_wt (Δ : NaruSem.Call.SigEnv) (Γ : Ctx) (n : Nat) (b : Bool) :
    NaruSem.Call.wtR Δ Γ (Surf.mkLets [("x", .nat, .lit (.nat n) .nat),
      ("x", .bool, .lit (.bool b) .bool)] (.var "x")) = some .bool := by
  apply wtR_mkLets (Γ' := (Γ.ext "x" .nat).ext "x" .bool)
  · rfl
  · simp [NaruSem.Call.wtR, Ctx.ext]

/-- 後から上書きしても、先のcallee不在を成功で埋めない。 -/
theorem binds_missing_call (Φ : NaruSem.Call.FEnv) (ρ : Env) (k : String) (n : Nat)
    (hk : Φ k = none) :
    NaruSem.Call.eval Φ ρ (Surf.mkLets [("x", .nat, .call k []),
      ("x", .nat, .lit (.nat n) .nat)] (.var "x")) = none := by
  rw [eval_mkLets]
  simp [evalBinds, NaruSem.Call.eval, hk]

/-- 型が合わない注釈を束縛列の適格性が拒否する。 -/
theorem binds_wrong_annotation (Δ : NaruSem.Call.SigEnv) (Γ : Ctx) (b : Bool) :
    wtBinds Δ Γ [("x", .nat, .lit (.bool b) .bool)] = none := by
  rfl


/-- calleeがある場合も、その失敗を後続の上書きで隠さない。 -/
theorem binds_failed_call (Φ : NaruSem.Call.FEnv) (ρ : Env) (k : String) (n : Nat)
    (f : List Val → Option Val) (hk : Φ k = some f) (hf : f [] = none) :
    NaruSem.Call.eval Φ ρ (Surf.mkLets [("x", .nat, .call k []),
      ("x", .nat, .lit (.nat n) .nat)] (.var "x")) = none := by
  rw [eval_mkLets]
  simp [evalBinds, NaruSem.Call.eval, NaruSem.Call.evalArgs_nil, hk, hf]

/-- 呼出しが成功した場合だけ後続の同名束縛を読み、任意の結果を扱う。 -/
theorem binds_call_shadow (Φ : NaruSem.Call.FEnv) (ρ : Env) (k : String) (n : Nat)
    (f : List Val → Option Val) (w : Val) (hk : Φ k = some f) (hf : f [] = some w) :
    NaruSem.Call.eval Φ ρ (Surf.mkLets [("x", .nat, .call k []),
      ("x", .nat, .lit (.nat n) .nat)] (.var "x")) = some (.nat n) := by
  rw [eval_mkLets]
  simp [evalBinds, NaruSem.Call.eval, NaruSem.Call.evalArgs_nil, hk, hf, Env.ext]

def guardExpr : Expr := .call {} (.var {} ["Guard", "test"]) []
def guardArms : List Arm :=
  [.mk (.bind {} "x") (some guardExpr) (.var {} ["x"]),
   .mk (.wild {}) none (.var {} ["x"])]
def guardCoreArms (k : String) : List Core.Arm :=
  [.mk (.bind "x") (some (.call k [])) (.var "x"), .mk .wild none (.var "x")]

/-- パターン束縛があっても修飾名のゼロ引数inputは同じ環境へ届く。 -/
theorem guard_call (T : Table) (Γ : SCtx) (ρ : SEnv) (Φ : NaruSem.Call.FEnv) (k : String)
    (hr : T.resolve ["Guard", "test"] = some k)
    (hs : (T.sig k).bind DeclSig.value? = some ([], .bool)) :
    lower T Γ guardExpr = some (.call k []) ∧
      eval T Φ ρ guardExpr = NaruSem.Call.eval Φ ρ.vals (.call k []) := by
  apply lower_call_eval (ps := []) (t := .bool) (cargs := []) (vals := []) (vs := [])
  all_goals first | exact hr | exact hs | rfl

/-- ガード付き束縛腕と元の環境を読む後続腕の証拠を合成する。 -/
theorem guard_arms_eval (T : Table) (Γ : SCtx) (ρ : SEnv) (Φ : NaruSem.Call.FEnv)
    (v : Val) (k : String) (hr : T.resolve ["Guard", "test"] = some k)
    (hs : (T.sig k).bind DeclSig.value? = some ([], .bool)) :
    evalArms T Φ ρ v guardArms = NaruSem.Call.evalArms Φ ρ.vals v (guardCoreArms k) := by
  apply lowerArms_eval
  refine .cons ?_ (.cons ?_ .nil)
  · intro rest crest hrest
    apply lowerArm_eval (Γ := Γ) (ts := .nat) (bts := [("x", .nat)]) rfl
    · dsimp only [lowerArm, wtPat]
      rw [(guard_call T (Γ.extVals [("x", .nat)]) ρ Φ k hr hs).1]
      rfl
    · intro bs cb _ hl
      change some (.var "x") = some cb at hl
      cases hl
      rw [← SEnv.vals_extVals]
      rfl
    · intro g cg bs hg _ hl
      cases hg
      rw [(guard_call T (Γ.extVals [("x", .nat)]) ρ Φ k hr hs).1] at hl
      cases hl
      rw [← SEnv.vals_extVals]
      exact (guard_call T Γ (ρ.extVals bs) Φ k hr hs).2
    · exact hrest
  · intro rest crest hrest
    apply lowerArm_eval (Γ := Γ) (ts := .nat) (bts := []) rfl rfl
    · intro bs cb _ hl
      change some (.var "x") = some cb at hl
      cases hl
      rw [← SEnv.vals_extVals]
      rfl
    · intros; contradiction
    · exact hrest

/-- 任意の局所・関数/input環境で実際のmatchのloweringと評価を合成する。 -/
theorem match_call_guard (T : Table) (Γ : SCtx) (ρ : SEnv) (Φ : NaruSem.Call.FEnv)
    (n : Nat) (k : String) (hr : T.resolve ["Guard", "test"] = some k)
    (hs : (T.sig k).bind DeclSig.value? = some ([], .bool)) :
    lower T Γ (.matchE {} (.lit {} (.nat n)) guardArms) =
      some (.match_ (.lit (.nat n) .nat) .nat (guardCoreArms k)) ∧
    eval T Φ ρ (.matchE {} (.lit {} (.nat n)) guardArms) =
      NaruSem.Call.eval Φ ρ.vals (.match_ (.lit (.nat n) .nat) .nat (guardCoreArms k)) := by
  apply lower_match_eval (ts := .nat) rfl rfl
  · dsimp only [guardArms, guardCoreArms, lowerArms, lowerArm, wtPat]
    rw [(guard_call T (Γ.extVals [("x", .nat)]) ρ Φ k hr hs).1]
    rfl
  · rfl
  · intro v
    exact guard_arms_eval T Γ ρ Φ v k hr hs

/-- Boolの二つのリテラル腕で網羅性の走査を実際のloweringへ運ぶ。 -/
theorem bool_arms_exhaustive (T : Table) (Γ : SCtx) :
    NaruSem.exhaustive .bool
      [.mk (.lit (.bool true)) none (.lit (.nat 1) .nat),
       .mk (.lit (.bool false)) none (.lit (.nat 2) .nat)] = true := by
  have h := exhaustiveFrom_lowerArms (T := T) (Γ := Γ) (ts := .bool)
    (arms := [.mk (.lit {} (.bool true)) none (.lit {} (.nat 1)),
      .mk (.lit {} (.bool false)) none (.lit {} (.nat 2))]) (by rfl)
  simp only [Surf.lowerPat] at h
  rw [NaruSem.exhaustive, ← h]
  rfl

/-- ガード付きのwildcardだけでは網羅性を保証しない。 -/
theorem guard_only_not_exhaustive (T : Table) (Γ : SCtx) :
    NaruSem.exhaustive .nat [.mk .wild (some (.lit (.bool true) .bool)) (.lit (.nat 1) .nat)] = false := by
  have h := exhaustiveFrom_lowerArms (T := T) (Γ := Γ) (ts := .nat)
    (arms := [.mk (.wild {}) (some (.lit {} (.bool true))) (.lit {} (.nat 1))]) (by rfl)
  simp only [Surf.lowerPat] at h
  rw [NaruSem.exhaustive, ← h]
  rfl

def guardTable (k : String) : Table :=
  ⟨fun _ => some k, fun _ => some (.input [] .bool)⟩

/-- 呼出し署名、束縛腕と後続腕の型、網羅性からmatch全体の型を合成する。 -/
theorem match_call_guard_wt (Γ : SCtx) (n : Nat) (k : String)
    (hx : Γ.vals "x" = some .nat) :
    NaruSem.Call.wtR (guardTable k).Δ Γ.vals
      (.match_ (.lit (.nat n) .nat) .nat (guardCoreArms k)) = some .nat := by
  apply lower_match_wt (T := guardTable k) (Γ := Γ) (ts := .nat) (arms := guardArms)
  · dsimp only [guardArms, guardCoreArms, lowerArms, lowerArm, wtPat]
    rw [(guard_call (guardTable k) (Γ.extVals [("x", .nat)]) SEnv.empty
      NaruSem.Call.FEnv.empty k rfl rfl).1]
    rfl
  · rfl
  · rfl
  · simp [guardCoreArms, NaruSem.Call.wtArmsR, NaruSem.Call.wtArmR,
      NaruSem.wtPat, NaruSem.Call.wtR, NaruSem.Call.valueSig?, NaruSem.Call.Sig.value?, NaruSem.Call.wtArgs, Table.Δ,
      guardTable, DeclSig.toSig, Ctx.extPat, Ctx.extList, Ctx.ext, hx]

/-- falseガードの後は、scrutineeで上書きしたxを後続へ漏らさない。 -/
theorem guard_false_restores_outer (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (n m : Nat) (k : String)
    (f : List Val → Option Val) (hk : Φ k = some f) (hf : f [] = some (.bool false))
    (hx : ρ.vals "x" = some (.nat m)) :
    eval (guardTable k) Φ ρ (.matchE {} (.lit {} (.nat n)) guardArms) = some (.nat m) := by
  rw [(match_call_guard (guardTable k) SCtx.empty ρ Φ n k rfl rfl).2]
  simp [NaruSem.Call.eval, NaruSem.Call.evalArms, NaruSem.Call.evalArgs_nil,
    guardCoreArms, NaruSem.matchPat, hk, hf, Env.extList, hx]

/-- trueガードの本体では同名の外側の値/命題をscrutineeが隠す。 -/
theorem guard_true_shadows_outer (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (n : Nat) (k : String)
    (f : List Val → Option Val) (hk : Φ k = some f) (hf : f [] = some (.bool true)) :
    eval (guardTable k) Φ ρ (.matchE {} (.lit {} (.nat n)) guardArms) = some (.nat n) := by
  rw [(match_call_guard (guardTable k) SCtx.empty ρ Φ n k rfl rfl).2]
  simp [NaruSem.Call.eval, NaruSem.Call.evalArms, NaruSem.Call.evalArgs_nil,
    guardCoreArms, NaruSem.matchPat, hk, hf, Env.extList, Env.ext]

/-- ガード失敗後に束縛を漏らしてscrutineeを返す結果は正しい意味と異なる。 -/
theorem guard_false_wrong_shadow (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (n m : Nat) (k : String)
    (f : List Val → Option Val) (hk : Φ k = some f) (hf : f [] = some (.bool false))
    (hx : ρ.vals "x" = some (.nat m)) (hnm : n ≠ m) :
    eval (guardTable k) Φ ρ (.matchE {} (.lit {} (.nat n)) guardArms) ≠ some (.nat n) := by
  rw [guard_false_restores_outer Φ ρ n m k f hk hf hx]
  intro h
  cases h
  exact hnm rfl

/-- callee不在はガードfalseと区別し、後続で成功にしない。 -/
theorem guard_missing_stops (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (n : Nat) (k : String)
    (hk : Φ k = none) :
    eval (guardTable k) Φ ρ (.matchE {} (.lit {} (.nat n)) guardArms) = none := by
  rw [(match_call_guard (guardTable k) SCtx.empty ρ Φ n k rfl rfl).2]
  simp [NaruSem.Call.eval, NaruSem.Call.evalArms, guardCoreArms, NaruSem.matchPat, hk]

/-- calleeの失敗もfalseガードに置き換えない。 -/
theorem guard_failure_stops (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (n : Nat) (k : String)
    (f : List Val → Option Val) (hk : Φ k = some f) (hf : f [] = none) :
    eval (guardTable k) Φ ρ (.matchE {} (.lit {} (.nat n)) guardArms) = none := by
  rw [(match_call_guard (guardTable k) SCtx.empty ρ Φ n k rfl rfl).2]
  simp [NaruSem.Call.eval, NaruSem.Call.evalArms, NaruSem.Call.evalArgs_nil,
    guardCoreArms, NaruSem.matchPat, hk, hf]

/-- 署名に従わない環境のNatガードも両側で失敗する。保証の適格性とは区別する。 -/
theorem guard_nonbool_stops (Φ : NaruSem.Call.FEnv) (ρ : SEnv) (n m : Nat) (k : String)
    (f : List Val → Option Val) (hk : Φ k = some f) (hf : f [] = some (.nat m)) :
    eval (guardTable k) Φ ρ (.matchE {} (.lit {} (.nat n)) guardArms) = none := by
  rw [(match_call_guard (guardTable k) SCtx.empty ρ Φ n k rfl rfl).2]
  simp [NaruSem.Call.eval, NaruSem.Call.evalArms, NaruSem.Call.evalArgs_nil,
    guardCoreArms, NaruSem.matchPat, hk, hf]

/-- パターン不一致では失敗するガードを呼ばず、後続の元の環境へ進む。 -/
theorem guard_mismatch_skips (T : Table) (Γ : SCtx) (Φ : NaruSem.Call.FEnv) (ρ : SEnv)
    (k : String) (rest : List Arm) (crest : List Core.Arm)
    (hr : T.resolve ["Guard", "test"] = some k)
    (hs : (T.sig k).bind DeclSig.value? = some ([], .bool))
    (he : evalArms T Φ ρ (.bool false) rest = NaruSem.Call.evalArms Φ ρ.vals (.bool false) crest) :
    evalArms T Φ ρ (.bool false) (.mk (.lit {} (.bool true)) (some guardExpr) (.lit {} (.nat 1)) :: rest) =
      NaruSem.Call.evalArms Φ ρ.vals (.bool false)
        (.mk (.lit (.bool true)) (some (.call k [])) (.lit (.nat 1) .nat) :: crest) := by
  apply lowerArm_eval (Γ := Γ) (ts := .bool) (bts := []) rfl
  · dsimp only [lowerArm, wtPat]
    simp only [ite_true]
    rw [(guard_call T (Γ.extVals []) ρ Φ k hr hs).1]
    rfl
  · intros; contradiction
  · intros; contradiction
  · exact he

end NaruSem.Surf.Call
