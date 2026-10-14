import Model.Consensus.Protocol.ValidatorClient
import Proofs.Consensus.Tables
import Proofs.Consensus.Sets
import Mathlib.Tactic

/-!
# validator client の署名の記録(C71 の補題)

生成 Model の `Record`(`Model/Consensus/Protocol/ValidatorClient.lean`: 高さごとの `target` / `timeout` / `lock`)と、
attestation を作る `createAttestation`(finality pair `finalityPair` と height pair `heightPair` を決め、`recordAttestation` で記録を 1 回
更新する)について、同じ validator の 2 つの attestation が E1 / E2 の証拠にならないために要る記録の性質を示す:
- `target` は書き込み 1 回(`recordAttestation` は `recordTarget = none` のときだけ `withTarget`)で、既にある値は変わらない、
- `lock` は finality pair の高さに書かれ、`finalityPair` の検査(`lock ∈ {none, some j}`)で既にある値は変わらない、
- `timeout` は増えるだけ、
- `LockCompatible`(lock がある高さは timeout でなく、target は空かその lock に等しい)は `createAttestation` で保たれる、
- `FinalitySafeAt`(finality pair を出した高さは timeout でなく lock がその target)は finality pair を出した直後に成立し、以後保たれる、
- 出した height pair の target は記録され(`create_saves`)、既に target / lock のある高さに出す target はその値に等しい
  (`create_target_eq_of_record` / `create_target_eq_of_lock`)。
名前付きの `namedCreate`(`NamedRecord`)は `legacyCreate` = `createAttestation` の行を `encodeRow` で名前付きにするだけで、
消去 `eraseAttestation` は元の行に戻る(`namedCreate_erase`)。
手書き `Proofs.Records.LockCompatible` / `HealingSurface.record_attestation_target_recorded` / `height_pair_target_compat` /
`create_attestation_saves` / `lockCompatible_create_attestation` / `create_attestation_lock_mono` / `FinalitySafeAt` /
`create_attestation_finalitySafeAt(_mono)` / `create_attestation_no_self_E1`
(`DecoupledConsensusProofs/Protocol/ValidatorClient/{RecordCore,FinalityPairCore,SlashableBound,Divergence}.lean`)に当たる。
-/

namespace Proofs.Consensus.Records

open Model.Consensus.Objects.Blocks Model.Consensus.Objects.Identifiers Model.Consensus.Objects.NamedBlocks
open Model.Consensus.Protocol.ValidatorClient
open Proofs.Consensus.Tables Proofs.Consensus.Sets

/-! ## `Nat` を鍵にする `Table` / `Set` -/

theorem nat_compare_eq_iff (a b : Nat) : compare a b = .eq ↔ a = b := Nat.compare_eq_eq

theorem nat_compare_eq_trans (a b c : Nat) (hab : compare a b = .eq) (hbc : compare b c = .eq) :
    compare a c = .eq := by
  rw [Nat.compare_eq_eq] at hab hbc ⊢
  exact hab.trans hbc

theorem get?_insert_self {ν : Type} (t : NaruStd.Table Nat ν) (k : Nat) (v : ν) : (t.insert k v).get? k = some v := by
  simp [NaruStd.Table.get?, NaruStd.Table.insert, find?_insertSorted_self nat_compare_eq_iff k v t.entries]

theorem get?_insert_ne {ν : Type} (t : NaruStd.Table Nat ν) (k : Nat) (v : ν) (k' : Nat) (hne : k ≠ k') :
    (t.insert k v).get? k' = t.get? k' := by
  rcases find?_insertSorted nat_compare_eq_trans k v k' t.entries with ⟨hk, _⟩ | hf
  · exact absurd (Nat.compare_eq_eq.mp hk) hne
  · simp [NaruStd.Table.get?, NaruStd.Table.insert, hf]

theorem contains_insert_iff (s : NaruStd.Set Nat) (x z : Nat) :
    (s.insert x).contains z = true ↔ z = x ∨ s.contains z = true := by
  rw [contains_iff_mem nat_compare_eq_iff, contains_iff_mem nat_compare_eq_iff, mem_insert_iff nat_compare_eq_iff]

/-! ## 記録の欄の読み書き -/

theorem recordTarget_withTarget_self (rec : Record) (h : Nat) (t : BlockId) :
    recordTarget (withTarget rec h t) h = some t := by
  simp [recordTarget, withTarget, get?_insert_self]

theorem recordTarget_withTarget_ne (rec : Record) (h : Nat) (t : BlockId) (g : Nat) (hne : h ≠ g) :
    recordTarget (withTarget rec h t) g = recordTarget rec g := by
  simp [recordTarget, withTarget, get?_insert_ne _ _ _ _ hne]

theorem recordTarget_withTimeout (rec : Record) (h g : Nat) : recordTarget (withTimeout rec h) g = recordTarget rec g := rfl

theorem recordTarget_withLock (rec : Record) (h : Nat) (j : BlockId) (g : Nat) :
    recordTarget (withLock rec h j) g = recordTarget rec g := rfl

theorem recordLock_withLock_self (rec : Record) (h : Nat) (j : BlockId) : recordLock (withLock rec h j) h = some j := by
  simp [recordLock, withLock, get?_insert_self]

theorem recordLock_withLock_ne (rec : Record) (h : Nat) (j : BlockId) (g : Nat) (hne : h ≠ g) :
    recordLock (withLock rec h j) g = recordLock rec g := by
  simp [recordLock, withLock, get?_insert_ne _ _ _ _ hne]

theorem recordLock_withTarget (rec : Record) (h : Nat) (t : BlockId) (g : Nat) :
    recordLock (withTarget rec h t) g = recordLock rec g := rfl

theorem recordLock_withTimeout (rec : Record) (h g : Nat) : recordLock (withTimeout rec h) g = recordLock rec g := rfl

theorem recordTimeout_withTimeout_iff (rec : Record) (h g : Nat) :
    recordTimeout (withTimeout rec h) g = true ↔ g = h ∨ recordTimeout rec g = true := by
  simp only [recordTimeout, withTimeout]
  exact contains_insert_iff _ _ _

theorem recordTimeout_withTarget (rec : Record) (h : Nat) (t : BlockId) (g : Nat) :
    recordTimeout (withTarget rec h t) g = recordTimeout rec g := rfl

theorem recordTimeout_withLock (rec : Record) (h : Nat) (j : BlockId) (g : Nat) :
    recordTimeout (withLock rec h j) g = recordTimeout rec g := rfl

/-! ## `finalityPair` / `ownLock` / `heightPair` -/

/-- finality pair `some p` が出るのは `p = ⟨hJ, j⟩` で、高さ `hJ` が timeout でなく、target / lock が空か `j` のとき。 -/
theorem finalityPair_some {rec : Record} {hJ : Nat} {j : BlockId} {hF : Nat} {p : FinalityPair}
    (h : finalityPair rec hJ j hF = some p) :
    p = ⟨hJ, j⟩ ∧ recordTimeout rec hJ = false ∧ (recordTarget rec hJ = none ∨ recordTarget rec hJ = some j) ∧
      (recordLock rec hJ = none ∨ recordLock rec hJ = some j) := by
  simp only [finalityPair] at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h2
    exact ⟨rfl, h2.1.2, h2.1.1, h2.2⟩

theorem ownLock_none (rec : Record) (h : Nat) : ownLock rec h none = recordLock rec h := rfl

theorem ownLock_some_eq (rec : Record) (h : Nat) (p : FinalityPair) (hp : p.height = h) :
    ownLock rec h (some p) = some p.target := by
  simp [ownLock, hp]

theorem ownLock_some_ne (rec : Record) (h : Nat) (p : FinalityPair) (hp : p.height ≠ h) :
    ownLock rec h (some p) = recordLock rec h := by
  simp [ownLock, hp]

/-- `some (hC, tC, nu)` の height pair は `Empty` / `Timeout hC` / `Target hC tC` のどれか。 -/
theorem heightPair_shape (rec : Record) (hC : Nat) (tC : BlockId) (nu : Bool) (fp : Option FinalityPair) :
    heightPair rec (some (hC, tC, nu)) fp = .Empty ∨ heightPair rec (some (hC, tC, nu)) fp = .Timeout hC ∨
      heightPair rec (some (hC, tC, nu)) fp = .Target hC tC := by
  simp only [heightPair]
  by_cases hto : recordTimeout rec hC = true
  · rw [ite_eq_left hto]
    exact Or.inr (Or.inl rfl)
  · rw [ite_eq_right hto]
    cases hol : ownLock rec hC fp with
    | some l =>
      simp only
      by_cases hl : (l == tC) = true
      · rw [ite_eq_left hl]
        exact Or.inr (Or.inr rfl)
      · rw [ite_eq_right hl]
        exact Or.inl rfl
    | none =>
      simp only
      cases ht : recordTarget rec hC with
      | some r =>
        simp only
        by_cases hr : (r == tC) = true
        · rw [ite_eq_left hr]
          exact Or.inr (Or.inr rfl)
        · rw [ite_eq_right hr]
          exact Or.inr (Or.inl rfl)
      | none =>
        simp only
        cases nu
        · exact Or.inr (Or.inr (by simp))
        · exact Or.inr (Or.inl (by simp))

/-- `Target h U` が出たら `fields = some (h, U, nu)`。 -/
theorem heightPair_target_fields {rec : Record} {fields : Option (Nat × BlockId × Bool)} {fp : Option FinalityPair}
    {h : Nat} {U : BlockId} (hp : heightPair rec fields fp = .Target h U) :
    ∃ nu, fields = some (h, U, nu) := by
  cases fields with
  | none => simp [heightPair] at hp
  | some f =>
    obtain ⟨hC, tC, nu⟩ := f
    rcases heightPair_shape rec hC tC nu fp with h1 | h1 | h1 <;> rw [h1] at hp
    · exact absurd hp (by simp)
    · exact absurd hp (by simp)
    · simp only [HeightPair.Target.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨nu, rfl⟩

/-- `Timeout h` が出たら `fields = some (h, tC, nu)`。 -/
theorem heightPair_timeout_fields {rec : Record} {fields : Option (Nat × BlockId × Bool)} {fp : Option FinalityPair}
    {h : Nat} (hp : heightPair rec fields fp = .Timeout h) :
    ∃ tC nu, fields = some (h, tC, nu) := by
  cases fields with
  | none => simp [heightPair] at hp
  | some f =>
    obtain ⟨hC, tC, nu⟩ := f
    rcases heightPair_shape rec hC tC nu fp with h1 | h1 | h1 <;> rw [h1] at hp
    · exact absurd hp (by simp)
    · simp only [HeightPair.Timeout.injEq] at hp
      subst hp
      exact ⟨tC, nu, rfl⟩
    · exact absurd hp (by simp)

/-- 有効な lock `X` のある高さに出す target は `X`。 -/
theorem heightPair_target_eq_of_ownLock {rec : Record} {fields : Option (Nat × BlockId × Bool)} {fp : Option FinalityPair}
    {h : Nat} {X U : BlockId} (hol : ownLock rec h fp = some X) (hp : heightPair rec fields fp = .Target h U) : U = X := by
  obtain ⟨nu, rfl⟩ := heightPair_target_fields hp
  simp only [heightPair] at hp
  by_cases hto : recordTimeout rec h = true
  · rw [ite_eq_left hto] at hp
    exact absurd hp (by simp)
  · rw [ite_eq_right hto, hol] at hp
    simp only at hp
    by_cases hx : (X == U) = true
    · exact (beq_iff_eq.mp hx).symm
    · rw [ite_eq_right hx] at hp
      exact absurd hp (by simp)

/-- 有効な lock が無く記録された target `X` のある高さに出す target は `X`。 -/
theorem heightPair_target_eq_of_target {rec : Record} {fields : Option (Nat × BlockId × Bool)} {fp : Option FinalityPair}
    {h : Nat} {X U : BlockId} (hol : ownLock rec h fp = none) (ht : recordTarget rec h = some X)
    (hp : heightPair rec fields fp = .Target h U) : U = X := by
  obtain ⟨nu, rfl⟩ := heightPair_target_fields hp
  simp only [heightPair] at hp
  by_cases hto : recordTimeout rec h = true
  · rw [ite_eq_left hto] at hp
    exact absurd hp (by simp)
  · rw [ite_eq_right hto, hol] at hp
    simp only at hp
    rw [ht] at hp
    simp only at hp
    by_cases hx : (X == U) = true
    · exact (beq_iff_eq.mp hx).symm
    · rw [ite_eq_right hx] at hp
      exact absurd hp (by simp)

/-- timeout でなく有効な lock のある高さには timeout を出さない。 -/
theorem heightPair_ne_timeout_of_ownLock {rec : Record} {fields : Option (Nat × BlockId × Bool)}
    {fp : Option FinalityPair} {h : Nat} {X : BlockId} (hto : recordTimeout rec h = false)
    (hol : ownLock rec h fp = some X) : heightPair rec fields fp ≠ .Timeout h := by
  intro hp
  obtain ⟨tC, nu, rfl⟩ := heightPair_timeout_fields hp
  simp only [heightPair] at hp
  rw [ite_eq_right (by rw [hto]; exact Bool.false_ne_true), hol] at hp
  simp only at hp
  by_cases hx : (X == tC) = true
  · rw [ite_eq_left hx] at hp
    exact absurd hp (by simp)
  · rw [ite_eq_right hx] at hp
    exact absurd hp (by simp)

/-! ## `LockCompatible` -/

/-- lock のある高さは timeout でなく、target は空かその lock に等しい(手書き F3 `LockCompatible`)。 -/
def LockCompatible (rec : Record) : Prop :=
  ∀ (h : Nat) (T : BlockId), recordLock rec h = some T →
    recordTimeout rec h = false ∧ (recordTarget rec h = none ∨ recordTarget rec h = some T)

theorem lockCompatible_initial : LockCompatible initialRecord := by
  intro h T hl
  have : recordLock initialRecord h = none := rfl
  rw [this] at hl
  exact absurd hl (by simp)

/-- lock `T` のある高さの有効な lock は `T`(finality pair がその高さなら `finalityPair` の検査でその target も `T`)。 -/
theorem ownLock_eq_of_lock {rec : Record} {h : Nat} {T : BlockId} (hlock : recordLock rec h = some T)
    (hJ : Nat) (j : BlockId) (hF : Nat) : ownLock rec h (finalityPair rec hJ j hF) = some T := by
  cases hfp : finalityPair rec hJ j hF with
  | none => rw [ownLock_none]; exact hlock
  | some p =>
    obtain ⟨rfl, -, -, hl⟩ := finalityPair_some hfp
    by_cases hph : hJ = h
    · subst hph
      rw [ownLock_some_eq rec hJ ⟨hJ, j⟩ rfl]
      rcases hl with hl | hl
      · rw [hlock] at hl; exact absurd hl (by simp)
      · rw [hlock] at hl
        exact hl.symm
    · rw [ownLock_some_ne _ _ _ hph]
      exact hlock

/-- `LockCompatible` の下で、有効な lock `X` のある高さの target は空か `X`。 -/
theorem ownLock_compatible {rec : Record} (hla : LockCompatible rec) {h : Nat} {X : BlockId} {hJ : Nat} {j : BlockId}
    {hF : Nat} (hol : ownLock rec h (finalityPair rec hJ j hF) = some X) :
    recordTarget rec h = none ∨ recordTarget rec h = some X := by
  cases hfp : finalityPair rec hJ j hF with
  | none =>
    rw [hfp, ownLock_none] at hol
    exact (hla h X hol).2
  | some p =>
    obtain ⟨rfl, -, ht, -⟩ := finalityPair_some hfp
    rw [hfp] at hol
    by_cases hph : hJ = h
    · subst hph
      rw [ownLock_some_eq rec hJ ⟨hJ, j⟩ rfl] at hol
      have : j = X := Option.some.inj hol
      subst this
      exact ht
    · rw [ownLock_some_ne _ _ _ hph] at hol
      exact (hla h X hol).2

/-- `LockCompatible` の下で、出した target `T` の高さの target は空か `T`。 -/
theorem heightPair_target_compat {rec : Record} (hla : LockCompatible rec) {fields : Option (Nat × BlockId × Bool)}
    {hJ : Nat} {j : BlockId} {hF : Nat} {h : Nat} {T : BlockId}
    (hp : heightPair rec fields (finalityPair rec hJ j hF) = .Target h T) :
    recordTarget rec h = none ∨ recordTarget rec h = some T := by
  cases hol : ownLock rec h (finalityPair rec hJ j hF) with
  | some X =>
    rw [heightPair_target_eq_of_ownLock hol hp]
    exact ownLock_compatible hla hol
  | none =>
    cases ht : recordTarget rec h with
    | some X =>
      rw [heightPair_target_eq_of_target hol ht hp]
      exact Or.inr rfl
    | none => exact Or.inl rfl

/-! ## `recordAttestation` -/

/-- `recordAttestation` の前半: finality pair の lock を書く。 -/
def afterLockOf (rec : Record) (a : CombinedAttestation) : Record :=
  match a.finalityPair with
  | some p => withLock rec p.height p.target
  | none => rec

/-- `recordAttestation` の後半: height pair を timeout / target に書く(target は空のときだけ)。 -/
def heightStep (r : Record) (hp : HeightPair) : Record :=
  match hp with
  | .Empty => r
  | .Timeout h => withTimeout r h
  | .Target h t => if recordTarget r h == none then withTarget r h t else r

theorem recordAttestation_eq (rec : Record) (a : CombinedAttestation) :
    recordAttestation rec a = heightStep (afterLockOf rec a) a.heightPair := by
  unfold recordAttestation afterLockOf heightStep
  cases a.finalityPair <;> cases a.heightPair <;> rfl

theorem afterLockOf_target (rec : Record) (a : CombinedAttestation) (g : Nat) :
    recordTarget (afterLockOf rec a) g = recordTarget rec g := by
  unfold afterLockOf
  cases a.finalityPair <;> rfl

theorem afterLockOf_timeout (rec : Record) (a : CombinedAttestation) (g : Nat) :
    recordTimeout (afterLockOf rec a) g = recordTimeout rec g := by
  unfold afterLockOf
  cases a.finalityPair <;> rfl

theorem afterLockOf_lock (rec : Record) (a : CombinedAttestation) (g : Nat) :
    recordLock (afterLockOf rec a) g = ownLock rec g a.finalityPair := by
  unfold afterLockOf
  cases hfp : a.finalityPair with
  | none => rfl
  | some p =>
    by_cases hpg : p.height = g
    · rw [ownLock_some_eq _ _ _ hpg, ← hpg, recordLock_withLock_self]
    · rw [ownLock_some_ne _ _ _ hpg, recordLock_withLock_ne _ _ _ _ hpg]

theorem heightStep_lock (r : Record) (hp : HeightPair) (g : Nat) : recordLock (heightStep r hp) g = recordLock r g := by
  cases hp with
  | Empty => rfl
  | Timeout h => rfl
  | Target h t =>
    simp only [heightStep]
    split_ifs <;> rfl

theorem heightStep_target_mono (r : Record) (hp : HeightPair) {g : Nat} {T : BlockId} (hs : recordTarget r g = some T) :
    recordTarget (heightStep r hp) g = some T := by
  cases hp with
  | Empty => exact hs
  | Timeout h => exact hs
  | Target h t =>
    simp only [heightStep]
    split_ifs with hn
    · by_cases hg : h = g
      · subst hg
        rw [beq_iff_eq] at hn
        rw [hn] at hs
        exact absurd hs (by simp)
      · rw [recordTarget_withTarget_ne _ _ _ _ hg]
        exact hs
    · exact hs

theorem heightStep_target_recorded (r : Record) {g : Nat} {T : BlockId}
    (hpre : recordTarget r g = none ∨ recordTarget r g = some T) :
    recordTarget (heightStep r (.Target g T)) g = some T := by
  simp only [heightStep]
  split_ifs with hn
  · exact recordTarget_withTarget_self _ _ _
  · rcases hpre with hpre | hpre
    · exact absurd (by rw [hpre]; rfl) hn
    · exact hpre

theorem heightStep_target_compatible_of (r : Record) (hp : HeightPair) {g : Nat} {T : BlockId}
    (hpre : recordTarget r g = none ∨ recordTarget r g = some T) (hrow : ∀ U, hp = .Target g U → U = T) :
    recordTarget (heightStep r hp) g = none ∨ recordTarget (heightStep r hp) g = some T := by
  cases hp with
  | Empty => exact hpre
  | Timeout h => exact hpre
  | Target h t =>
    by_cases hg : h = g
    · subst hg
      have := hrow t rfl
      subst this
      exact Or.inr (heightStep_target_recorded r hpre)
    · simp only [heightStep]
      split_ifs
      · rw [recordTarget_withTarget_ne _ _ _ _ hg]
        exact hpre
      · exact hpre

theorem heightStep_timeout_true (r : Record) (g : Nat) : recordTimeout (heightStep r (.Timeout g)) g = true :=
  (recordTimeout_withTimeout_iff _ _ _).mpr (Or.inl rfl)

theorem heightStep_timeout_mono (r : Record) (hp : HeightPair) {g : Nat} (hs : recordTimeout r g = true) :
    recordTimeout (heightStep r hp) g = true := by
  cases hp with
  | Empty => exact hs
  | Timeout h => exact (recordTimeout_withTimeout_iff _ _ _).mpr (Or.inr hs)
  | Target h t =>
    simp only [heightStep]
    split_ifs <;> exact hs

theorem heightStep_timeout_false_of_ne (r : Record) (hp : HeightPair) {g : Nat} (hpre : recordTimeout r g = false)
    (hne : hp ≠ .Timeout g) : recordTimeout (heightStep r hp) g = false := by
  cases hp with
  | Empty => exact hpre
  | Timeout h =>
    cases hx : recordTimeout (heightStep r (.Timeout h)) g with
    | false => rfl
    | true =>
      have hx' := (recordTimeout_withTimeout_iff r h g).mp hx
      rcases hx' with rfl | hx'
      · exact absurd rfl hne
      · rw [hpre] at hx'
        exact Bool.noConfusion hx'
  | Target h t =>
    simp only [heightStep]
    split_ifs <;> exact hpre

theorem recordAttestation_target_mono (rec : Record) (a : CombinedAttestation) {g : Nat} {T : BlockId}
    (hs : recordTarget rec g = some T) : recordTarget (recordAttestation rec a) g = some T := by
  rw [recordAttestation_eq]
  exact heightStep_target_mono _ _ (by rw [afterLockOf_target]; exact hs)

theorem recordAttestation_lock_eq_ownLock (rec : Record) (a : CombinedAttestation) (g : Nat) :
    recordLock (recordAttestation rec a) g = ownLock rec g a.finalityPair := by
  rw [recordAttestation_eq, heightStep_lock, afterLockOf_lock]

theorem recordAttestation_timeout_mono (rec : Record) (a : CombinedAttestation) {g : Nat}
    (hs : recordTimeout rec g = true) : recordTimeout (recordAttestation rec a) g = true := by
  rw [recordAttestation_eq]
  exact heightStep_timeout_mono _ _ (by rw [afterLockOf_timeout]; exact hs)

theorem recordAttestation_timeout_true (rec : Record) {a : CombinedAttestation} {g : Nat}
    (hhp : a.heightPair = .Timeout g) : recordTimeout (recordAttestation rec a) g = true := by
  rw [recordAttestation_eq, hhp]
  exact heightStep_timeout_true _ _

theorem recordAttestation_timeout_false_of_ne (rec : Record) {a : CombinedAttestation} {g : Nat}
    (hpre : recordTimeout rec g = false) (hne : a.heightPair ≠ .Timeout g) :
    recordTimeout (recordAttestation rec a) g = false := by
  rw [recordAttestation_eq]
  exact heightStep_timeout_false_of_ne _ _ (by rw [afterLockOf_timeout]; exact hpre) hne

theorem recordAttestation_target_recorded (rec : Record) {a : CombinedAttestation} {g : Nat} {T : BlockId}
    (hhp : a.heightPair = .Target g T) (hpre : recordTarget rec g = none ∨ recordTarget rec g = some T) :
    recordTarget (recordAttestation rec a) g = some T := by
  rw [recordAttestation_eq, hhp]
  exact heightStep_target_recorded _ (by rw [afterLockOf_target]; exact hpre)

theorem recordAttestation_target_compatible_of (rec : Record) (a : CombinedAttestation) {g : Nat} {T : BlockId}
    (hpre : recordTarget rec g = none ∨ recordTarget rec g = some T)
    (hrow : ∀ U, a.heightPair = .Target g U → U = T) :
    recordTarget (recordAttestation rec a) g = none ∨ recordTarget (recordAttestation rec a) g = some T := by
  rw [recordAttestation_eq]
  exact heightStep_target_compatible_of _ _ (by rw [afterLockOf_target]; exact hpre) hrow

/-! ## `createAttestation` -/

section Create

variable (rec : Record) (vi : ValidatorId) (r : Nat) (c : Option BlockId) (fields : Option (Nat × BlockId × Bool))
  (hJ : Nat) (j : BlockId) (hF : Nat)

theorem createAttestation_snd :
    (createAttestation rec vi r c fields hJ j hF).2 =
      ⟨vi, r, c, heightPair rec fields (finalityPair rec hJ j hF), finalityPair rec hJ j hF⟩ := rfl

theorem createAttestation_fst :
    (createAttestation rec vi r c fields hJ j hF).1 = recordAttestation rec (createAttestation rec vi r c fields hJ j hF).2 :=
  rfl

theorem createAttestation_heightPair :
    (createAttestation rec vi r c fields hJ j hF).2.heightPair = heightPair rec fields (finalityPair rec hJ j hF) := rfl

theorem createAttestation_finalityPair :
    (createAttestation rec vi r c fields hJ j hF).2.finalityPair = finalityPair rec hJ j hF := rfl

/-- attestation `a` が高さ `g` に名指す target: height pair の `Target g T` か finality pair の `⟨g, T⟩`。 -/
def targets (a : CombinedAttestation) (g : Nat) (T : BlockId) : Prop :=
  a.heightPair = .Target g T ∨ a.finalityPair = some ⟨g, T⟩

/-- `LockCompatible` は `createAttestation` で保たれる。 -/
theorem lockCompatible_create {rec : Record} (hla : LockCompatible rec) :
    LockCompatible (createAttestation rec vi r c fields hJ j hF).1 := by
  intro g X hlock
  rw [createAttestation_fst, recordAttestation_lock_eq_ownLock, createAttestation_finalityPair] at hlock
  have hpre : recordTimeout rec g = false ∧ (recordTarget rec g = none ∨ recordTarget rec g = some X) := by
    cases hfp : finalityPair rec hJ j hF with
    | none =>
      rw [hfp, ownLock_none] at hlock
      exact hla g X hlock
    | some p =>
      obtain ⟨rfl, hto, ht, -⟩ := finalityPair_some hfp
      rw [hfp] at hlock
      by_cases hph : hJ = g
      · subst hph
        rw [ownLock_some_eq rec hJ ⟨hJ, j⟩ rfl] at hlock
        have : j = X := Option.some.inj hlock
        subst this
        exact ⟨hto, ht⟩
      · rw [ownLock_some_ne _ _ _ hph] at hlock
        exact hla g X hlock
  refine ⟨?_, ?_⟩
  · rw [createAttestation_fst]
    exact recordAttestation_timeout_false_of_ne rec hpre.1 (heightPair_ne_timeout_of_ownLock hpre.1 hlock)
  · rw [createAttestation_fst]
    exact recordAttestation_target_compatible_of rec _ hpre.2 (fun U hU => heightPair_target_eq_of_ownLock hlock hU)

theorem create_target_mono {rec : Record} {g : Nat} {T : BlockId} (hs : recordTarget rec g = some T) :
    recordTarget (createAttestation rec vi r c fields hJ j hF).1 g = some T :=
  recordAttestation_target_mono rec _ hs

theorem create_lock_mono {rec : Record} {g : Nat} {T : BlockId} (hs : recordLock rec g = some T) :
    recordLock (createAttestation rec vi r c fields hJ j hF).1 g = some T := by
  rw [createAttestation_fst, recordAttestation_lock_eq_ownLock, createAttestation_finalityPair]
  exact ownLock_eq_of_lock hs hJ j hF

theorem create_timeout_mono {rec : Record} {g : Nat} (hs : recordTimeout rec g = true) :
    recordTimeout (createAttestation rec vi r c fields hJ j hF).1 g = true :=
  recordAttestation_timeout_mono rec _ hs

/-- 出した height pair の target は記録される。 -/
theorem create_saves {rec : Record} (hla : LockCompatible rec) {g : Nat} {T : BlockId}
    (hhp : (createAttestation rec vi r c fields hJ j hF).2.heightPair = .Target g T) :
    recordTarget (createAttestation rec vi r c fields hJ j hF).1 g = some T := by
  rw [createAttestation_fst]
  exact recordAttestation_target_recorded rec hhp (heightPair_target_compat hla hhp)

/-- 出した finality pair の target は lock に書かれる。 -/
theorem create_finality_locked {rec : Record} {g : Nat} {T : BlockId}
    (hfp : (createAttestation rec vi r c fields hJ j hF).2.finalityPair = some ⟨g, T⟩) :
    recordLock (createAttestation rec vi r c fields hJ j hF).1 g = some T := by
  rw [createAttestation_fst, recordAttestation_lock_eq_ownLock, createAttestation_finalityPair]
  rw [createAttestation_finalityPair] at hfp
  rw [hfp]
  exact ownLock_some_eq _ _ _ rfl

/-- 出した height pair の target の高さの target は空かその値。 -/
theorem create_target_compatible {rec : Record} (hla : LockCompatible rec) {g : Nat} {T : BlockId}
    (hT : targets (createAttestation rec vi r c fields hJ j hF).2 g T) :
    recordTarget (createAttestation rec vi r c fields hJ j hF).1 g = none ∨
      recordTarget (createAttestation rec vi r c fields hJ j hF).1 g = some T := by
  rcases hT with hhp | hfp
  · exact Or.inr (create_saves vi r c fields hJ j hF hla hhp)
  · exact ((lockCompatible_create vi r c fields hJ j hF hla) g T (create_finality_locked vi r c fields hJ j hF hfp)).2

/-- 記録済みの target `X` のある高さに出す target は `X`。 -/
theorem create_target_eq_of_record {rec : Record} (hla : LockCompatible rec) {g : Nat} {X T : BlockId}
    (hs : recordTarget rec g = some X) (hT : targets (createAttestation rec vi r c fields hJ j hF).2 g T) : T = X := by
  have hmono := create_target_mono vi r c fields hJ j hF hs
  rcases create_target_compatible vi r c fields hJ j hF hla hT with hn | hsame
  · rw [hmono] at hn; exact absurd hn (by simp)
  · rw [hsame] at hmono
    exact Option.some.inj hmono

/-- lock `X` のある高さに出す target は `X`。 -/
theorem create_target_eq_of_lock {rec : Record} {g : Nat} {X T : BlockId} (hs : recordLock rec g = some X)
    (hT : targets (createAttestation rec vi r c fields hJ j hF).2 g T) : T = X := by
  rcases hT with hhp | hfp
  · rw [createAttestation_heightPair] at hhp
    exact heightPair_target_eq_of_ownLock (ownLock_eq_of_lock hs hJ j hF) hhp
  · rw [createAttestation_finalityPair] at hfp
    obtain ⟨hp, -, -, hl⟩ := finalityPair_some hfp
    have hh : g = hJ := congrArg FinalityPair.height hp
    have ht : T = j := congrArg FinalityPair.target hp
    subst hh
    subst ht
    rcases hl with hl | hl
    · rw [hs] at hl; exact absurd hl (by simp)
    · rw [hs] at hl
      exact (Option.some.inj hl).symm

/-- 1 つの attestation の height pair の target と finality pair の target は同じ高さなら等しい(自分と E1 にならない)。 -/
theorem create_no_self_E1 {rec : Record} {g : Nat} {T T' : BlockId}
    (hhp : (createAttestation rec vi r c fields hJ j hF).2.heightPair = .Target g T)
    (hfp : (createAttestation rec vi r c fields hJ j hF).2.finalityPair = some ⟨g, T'⟩) : T = T' := by
  rw [createAttestation_heightPair] at hhp
  rw [createAttestation_finalityPair] at hfp
  rw [hfp] at hhp
  exact heightPair_target_eq_of_ownLock (ownLock_some_eq _ _ _ rfl) hhp

/-- finality pair を出した高さは timeout でなく lock がその target(手書き `FinalitySafeAt`)。 -/
def FinalitySafeAt (rec : Record) (g : Nat) (T : BlockId) : Prop :=
  recordTimeout rec g = false ∧ recordLock rec g = some T

theorem create_finalitySafeAt {rec : Record} {g : Nat} {T : BlockId}
    (hfp : (createAttestation rec vi r c fields hJ j hF).2.finalityPair = some ⟨g, T⟩) :
    FinalitySafeAt (createAttestation rec vi r c fields hJ j hF).1 g T := by
  have hlock := create_finality_locked vi r c fields hJ j hF hfp
  rw [createAttestation_finalityPair] at hfp
  obtain ⟨hp, hto, -, -⟩ := finalityPair_some hfp
  have hh : g = hJ := congrArg FinalityPair.height hp
  subst hh
  have hol : ownLock rec g (finalityPair rec g j hF) = some T := by
    rw [hfp]
    exact ownLock_some_eq rec g ⟨g, T⟩ rfl
  refine ⟨?_, hlock⟩
  rw [createAttestation_fst]
  refine recordAttestation_timeout_false_of_ne rec hto ?_
  rw [createAttestation_heightPair]
  exact heightPair_ne_timeout_of_ownLock hto hol

theorem create_finalitySafeAt_mono {rec : Record} {g : Nat} {T : BlockId} (hsafe : FinalitySafeAt rec g T) :
    FinalitySafeAt (createAttestation rec vi r c fields hJ j hF).1 g T := by
  have hol : ownLock rec g (finalityPair rec hJ j hF) = some T := ownLock_eq_of_lock hsafe.2 hJ j hF
  refine ⟨?_, ?_⟩
  · rw [createAttestation_fst]
    refine recordAttestation_timeout_false_of_ne rec hsafe.1 ?_
    rw [createAttestation_heightPair]
    exact heightPair_ne_timeout_of_ownLock hsafe.1 hol
  · rw [createAttestation_fst, recordAttestation_lock_eq_ownLock, createAttestation_finalityPair]
    exact hol

theorem create_timeout_true {rec : Record} {g : Nat}
    (hhp : (createAttestation rec vi r c fields hJ j hF).2.heightPair = .Timeout g) :
    recordTimeout (createAttestation rec vi r c fields hJ j hF).1 g = true :=
  recordAttestation_timeout_true rec hhp

end Create

/-! ## `namedCreate`(名前付きの記録) -/

/-- `encodeHeight` の名前付き height pair の消去は元の height pair。 -/
theorem eraseHeightPair_encodeHeight (rec : Record) (fields : Option (Nat × BlockId × Bool)) (fp : Option FinalityPair) :
    eraseHeightPair (encodeHeight fields (heightPair rec fields fp)) = heightPair rec fields fp := by
  cases fields with
  | none => rfl
  | some f =>
    obtain ⟨hC, tC, nu⟩ := f
    rcases heightPair_shape rec hC tC nu fp with h1 | h1 | h1 <;> rw [h1] <;> rfl

theorem legacyCreate_eq (rec : Record) (inp : RecordInput) :
    legacyCreate rec inp = createAttestation rec inp.valIndex inp.round inp.confirmed inp.fields inp.hJ inp.j inp.hF := rfl

theorem namedCreate_legacy (rec : NamedRecord) (inp : RecordInput) :
    (namedCreate rec inp).1.legacy = (legacyCreate rec.legacy inp).1 := rfl

theorem namedCreate_row (rec : NamedRecord) (inp : RecordInput) :
    (namedCreate rec inp).2 = encodeRow inp.fields (legacyCreate rec.legacy inp).2 := rfl

/-- 名前付きの行の消去は `legacyCreate`(= `createAttestation`)の行。 -/
theorem namedCreate_erase (rec : NamedRecord) (inp : RecordInput) :
    eraseAttestation (namedCreate rec inp).2 = (legacyCreate rec.legacy inp).2 := by
  rw [namedCreate_row, legacyCreate_eq, createAttestation_snd]
  simp only [eraseAttestation, encodeRow]
  rw [eraseHeightPair_encodeHeight]

end Proofs.Consensus.Records
