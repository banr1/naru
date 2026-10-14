-- naru-obligation: Sample.Rules.other sha256:7746fce82fede706f6e234924728b534e03aecadd60a3ef6d44c405e235c5987
-- naru-obligation: Sample.Rules.viaAxiom sha256:7746fce82fede706f6e234924728b534e03aecadd60a3ef6d44c405e235c5987
-- naru-obligation: Sample.Rules.mixed sha256:7746fce82fede706f6e234924728b534e03aecadd60a3ef6d44c405e235c5987
-- naru-obligation: Sample.Rules.coerced sha256:7746fce82fede706f6e234924728b534e03aecadd60a3ef6d44c405e235c5987
-- naru-obligation: Sample.Rules.nonexistent sha256:7746fce82fede706f6e234924728b534e03aecadd60a3ef6d44c405e235c5987
import Statements.Sample.Rules

/-!
証明基盤の検体(C70): invalid の検体(`naru_test proofs` はこのファイルを除いた複製でも走らせる: そこでは `other` / `viaAxiom` / `mixed` / `coerced` が missing になり exit 0)。
- `other`: 別の義務(`lonely`)の型の theorem に `other` の名前を付けたもの → 型が義務の型と違う → invalid。
- `viaAxiom`: 独自の `axiom` に依存する証明 → invalid。
- `mixed`: `sorry` と独自の `axiom` の両方に依存する証明 → sorry より先に invalid(sorry の下書きが独自公理を隠さない)。
- `coerced`: 別の義務(`lonely`)の型の theorem に `coerced` の名前を付け、`lonely` の型から `coerced` の型への coercion(独自の `axiom` で作る)を
  用意したもの。`example : <型> := Proofs.Sample.Rules.coerced` は coercion の補完で通りうるが、検査用の theorem の公理監査が coercion の axiom を捕まえる → invalid。
- 束縛行 `Sample.Rules.nonexistent`: 一覧に無い修飾名 → invalid。
-/

theorem Proofs.Sample.Rules.other : ∀ («n» : Nat), Statements.Sample.Rules.lonely «n» := by
  intro n
  unfold Statements.Sample.Rules.lonely
  rfl

axiom Proofs.Sample.Rules.assumed : ∀ («n» : Nat), Statements.Sample.Rules.viaAxiom «n»

theorem Proofs.Sample.Rules.viaAxiom : ∀ («n» : Nat), Statements.Sample.Rules.viaAxiom «n» :=
  Proofs.Sample.Rules.assumed

theorem Proofs.Sample.Rules.mixed : ∀ («n» : Nat), Statements.Sample.Rules.mixed «n» := by
  intro n
  have _h := Proofs.Sample.Rules.assumed n
  exact sorry

axiom Proofs.Sample.Rules.coerce : (∀ («n» : Nat), Statements.Sample.Rules.lonely «n») → ∀ («n» : Nat), Statements.Sample.Rules.coerced «n»

instance : Coe (∀ («n» : Nat), Statements.Sample.Rules.lonely «n») (∀ («n» : Nat), Statements.Sample.Rules.coerced «n») :=
  ⟨Proofs.Sample.Rules.coerce⟩

theorem Proofs.Sample.Rules.coerced : ∀ («n» : Nat), Statements.Sample.Rules.lonely «n» := by
  intro n
  unfold Statements.Sample.Rules.lonely
  rfl
