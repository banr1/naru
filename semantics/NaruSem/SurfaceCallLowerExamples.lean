import NaruSem.SurfaceCallLower

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

end NaruSem.Surf.Call
