import NaruSem.SurfaceCallLowerSpec

/-! spec 呼出しの構造的 lowering の境界検体。一般同値の代用にはしない。 -/
namespace NaruSem.Surf.Call
open Naru

def specLowerTable : Table :=
  { resolve := fun p => if p = ["p"] then some "M.p" else if p = ["flag"] then some "M.flag" else none
    sig := fun k => if k = "M.p" then some (.spec [("x", .nat)])
      else if k = "M.flag" then some (.input [("b", .bool)] .bool) else none }

def specLowerCall : Expr := .call {} (.var {} ["p"]) [.pos (.var {} ["x"])]

theorem spec_lower_call : lowerS specLowerTable (SCtx.ofList [("x", .val .nat)]) specLowerCall =
    some (.call "M.p" [.var "x"]) := rfl

theorem spec_lower_runtime_reject : lower specLowerTable (SCtx.ofList [("x", .val .nat)]) specLowerCall = none := rfl

theorem spec_lower_missing : lowerS specLowerTable SCtx.empty (.call {} (.var {} ["missing"]) []) = none := rfl

theorem spec_lower_shadow : lowerS specLowerTable (SCtx.ofList [("p", .prop)]) specLowerCall = none := rfl

theorem spec_lower_value_arg_reject : lowerS specLowerTable SCtx.empty
    (.call {} (.var {} ["flag"]) [.pos (.quant {} .forall_ [{name := "n", ty := some (.named {} ["Nat"] []), span := {}}] (.lit {} (.bool true)))]) = none := rfl

theorem spec_lower_bool_value : lowerS specLowerTable SCtx.empty
    (.call {} (.var {} ["flag"]) [.pos (.lit {} (.bool true))]) =
    some (.call "M.flag" [.lit (.bool true) .bool]) := rfl

theorem spec_lower_bool_let : lowerS specLowerTable SCtx.empty
    (.block {} [.letS {} "b" none (.call {} (.var {} ["flag"]) [.pos (.lit {} (.bool true))])]
      (some (.var {} ["b"]))) =
    some (.let_ "b" .bool (.call "M.flag" [.lit (.bool true) .bool]) (.var "b")) := rfl

theorem spec_lower_prop_let : lowerS specLowerTable (SCtx.ofList [("x", .val .nat)])
    (.block {} [.letS {} "q" none specLowerCall] (some (.var {} ["q"]))) =
    some (.let_ "q" .bool (.call "M.p" [.var "x"]) (.var "q")) := rfl

theorem spec_lower_prop_let_kind : proppyS specLowerTable (SCtx.ofList [("x", .val .nat)]) specLowerCall = true ∧
    proppyS specLowerTable SCtx.empty (.call {} (.var {} ["flag"]) [.pos (.lit {} (.bool true))]) = false := by decide

theorem spec_lower_match_guard : lowerS specLowerTable (SCtx.ofList [("x", .val .nat), ("q", .prop)])
    (.matchE {} (.var {} ["x"])
      [.mk (.bind {} "x") (some specLowerCall) (.var {} ["q"]), .mk (.wild {}) none specLowerCall]) =
    some (.match_ (.var "x") .nat
      [.mk (.bind "x") (some (.call "M.p" [.var "x"])) (.var "q"), .mk .wild none (.call "M.p" [.var "x"])]) := rfl

theorem spec_lower_prop_scrutinee_reject : lowerS specLowerTable SCtx.empty
    (.matchE {} (.call {} (.var {} ["p"]) [.pos (.lit {} (.nat 1))])
      [.mk (.wild {}) none (.lit {} (.bool true))]) = none := rfl

end NaruSem.Surf.Call
