-- naru-obligation: Sample.Rules.incPositive sha256:7746fce82fede706f6e234924728b534e03aecadd60a3ef6d44c405e235c5987
-- naru-obligation: Sample.Rules.seeded sha256:7746fce82fede706f6e234924728b534e03aecadd60a3ef6d44c405e235c5987
-- naru-obligation: Sample.Rules.biased sha256:7746fce82fede706f6e234924728b534e03aecadd60a3ef6d44c405e235c5988
-- naru-obligation: Sample.Rules.Inner sha256:7746fce82fede706f6e234924728b534e03aecadd60a3ef6d44c405e235c5987
import Statements.Sample.Rules

/-!
証明基盤の検体(C70): 証明状況の検体。
- `incPositive`: 正しい証明と現在の束縛 hash → proved。
- `seeded`: `sorry` の証明(束縛は現在の hash)→ sorry。
- `biased`: 正しい証明だが束縛行の hash を 1 文字変えてある(末尾 `…5987` → `…5988`)→ stale。
- `tautology`: 正しい証明だが束縛行が無い → stale。
- `Inner`: 項目の証明から組み立てた bundle の証明と現在の束縛 hash → proved(項目 `biased` の束縛が古くても bundle 自身の状況には影響しない)。
`lonely` / `Outer` / `farClaim` には theorem が無い → missing。
-/

theorem Proofs.Sample.Rules.incPositive : ∀ («n» : Nat), Statements.Sample.Rules.incPositive «n» := by
  intro n
  unfold Statements.Sample.Rules.incPositive Statements.Sample.Rules.Positive Model.Sample.Base.inc
  omega

theorem Proofs.Sample.Rules.seeded : ∀ (seed' : Nat), Statements.Sample.Rules.seeded seed' := by
  intro _
  sorry

theorem Proofs.Sample.Rules.biased : ∀ (bias' : (Nat → Nat)) («n» : Nat), Statements.Sample.Rules.biased bias' «n» := by
  intro _ _
  unfold Statements.Sample.Rules.biased
  rfl

theorem Proofs.Sample.Rules.tautology : ∀ («b» : Bool), Statements.Sample.Rules.tautology «b» := by
  intro b
  unfold Statements.Sample.Rules.tautology
  cases b <;> simp

theorem Proofs.Sample.Rules.Inner : ∀ (bias' : (Nat → Nat)), Statements.Sample.Rules.Inner bias' :=
  fun bias' => { incPositive := Proofs.Sample.Rules.incPositive, biased := Proofs.Sample.Rules.biased bias' }
