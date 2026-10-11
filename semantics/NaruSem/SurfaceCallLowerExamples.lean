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

end NaruSem.Surf.Call
