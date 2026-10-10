import Holant.Proofs.Recognition.TensorDecisionTransport

/-!
# Denominator-free constraints for original-table tensor recognition

Every searched branch is a finite conjunction of polynomial equalities and a
single nonzero pivot test. No division remains in either the reconstruction
constraints or the one-hot factor constraints. The original source equivalences
therefore expose exactly the finite ground-polynomial decisions required by a
RootCode implementation, without assuming an evaluator or a factorization.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionCleared

open scoped BigOperators
open Holant.Tractable TensorDecisionNormalization

variable {K : Type*} [Field K] {n : ℕ}

/-- Numerators of all block restrictions are literal entries of the original table. -/
def sliceProduct (f : Signature K n) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot x : Fin n → Bool) : K :=
  ∏ i, f (blockWord count arity ports pivot i (fun j => x (ports ⟨i,j⟩)))

/-- Clearing the common nonzero pivot denominator in one reconstruction row. -/
theorem row_iff (f : Signature K n) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) (hp : f pivot ≠ 0) (x : Fin n → Bool) :
    (f pivot * ∏ i, normalizedSlice f count arity ports pivot i
      (fun j => x (ports ⟨i,j⟩)) = f x) ↔
      f pivot * sliceProduct f count arity ports pivot x = f x * f pivot ^ count := by
  simp only [normalizedSlice, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, sliceProduct]
  rw [← mul_div_assoc, div_eq_iff (pow_ne_zero count hp)]

/-- Division by the nonzero pivot does not affect the tested support zeros. -/
theorem oneHot_slice_iff (f : Signature K n) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) (hp : f pivot ≠ 0) (i : Fin count) :
    Signature.OneHot (normalizedSlice f count arity ports pivot i) ↔
      ∀ y, 1 < Holant.weight y → f (blockWord count arity ports pivot i y) = 0 := by
  simp only [Signature.OneHot, normalizedSlice, div_eq_zero_iff, hp, or_false]

/-- A finite family of polynomial equalities on the original table entries. -/
def Rows (f : Signature K n) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) : Prop :=
  ∀ x, f pivot * sliceProduct f count arity ports pivot x = f x * f pivot ^ count

/-- Unary/binary branch constraints, with the pivot guard kept explicit. -/
def ArityTwoAccepts (f : Signature K n) (S : TensorDecision.Shape n)
    (pivot : Fin n → Bool) : Prop :=
  f pivot ≠ 0 ∧ Rows f S.count S.arity S.ports pivot

theorem arityTwo_accepts_iff (f : Signature K n) (S : TensorDecision.Shape n)
    (pivot : Fin n → Bool) :
    TensorDecision.Accepts f S pivot ↔ ArityTwoAccepts f S pivot := by
  constructor
  · rintro ⟨hp,hrows⟩
    exact ⟨hp,fun x => (row_iff f S.count S.arity S.ports pivot hp x).mp (hrows x)⟩
  · rintro ⟨hp,hrows⟩
    exact ⟨hp,fun x => (row_iff f S.count S.arity S.ports pivot hp x).mpr (hrows x)⟩

/-- The one-hot branch adds only zero tests on specified literal input entries. -/
def OneHotAccepts (f : Signature K n) (S : TensorDecisionStable.Shape n)
    (pivot : Fin n → Bool) : Prop :=
  f pivot ≠ 0 ∧
    (∀ i y, 1 < Holant.weight y → f (blockWord S.count S.arity S.ports pivot i y) = 0) ∧
    Rows f S.count S.arity S.ports pivot

theorem oneHot_accepts_iff (f : Signature K n) (S : TensorDecisionStable.Shape n)
    (pivot : Fin n → Bool) :
    TensorDecisionStable.Accepts (fun _ g => Signature.OneHot g) f S pivot ↔
      OneHotAccepts f S pivot := by
  constructor
  · rintro ⟨hp,hfactors,hrows⟩
    exact ⟨hp,fun i => (oneHot_slice_iff f S.count S.arity S.ports pivot hp i).mp (hfactors i),
      fun x => (row_iff f S.count S.arity S.ports pivot hp x).mp (hrows x)⟩
  · rintro ⟨hp,hfactors,hrows⟩
    exact ⟨hp,fun i => (oneHot_slice_iff f S.count S.arity S.ports pivot hp i).mpr (hfactors i),
      fun x => (row_iff f S.count S.arity S.ports pivot hp x).mpr (hrows x)⟩

/-- Fully finite, denominator-free arity-two recognition specification. -/
def ArityTwoTest (f : Signature K n) : Prop :=
  (∀ x, f x = 0) ∨ ∃ S : TensorDecision.Shape n, ∃ pivot, ArityTwoAccepts f S pivot

/-- Fully finite, denominator-free one-hot tensor recognition specification. -/
def OneHotTest (f : Signature K n) : Prop :=
  (∀ x, f x = 0) ∨ ∃ S : TensorDecisionStable.Shape n, ∃ pivot, OneHotAccepts f S pivot

theorem arityTwo_test_iff (f : Signature K n) :
    ArityTwoTest f ↔ f = 0 ∨ Signature.TensorClosure (fun m _ => m = 1 ∨ m = 2) f := by
  rw [← TensorDecision.finiteTest_iff]
  simp only [ArityTwoTest, TensorDecision.FiniteTest, arityTwo_accepts_iff]

theorem oneHot_test_iff (f : Signature K n) :
    OneHotTest f ↔ f = 0 ∨ Signature.TensorClosure (fun _ g => Signature.OneHot g) f := by
  rw [← TensorDecisionStable.finiteTest_iff _ TensorDecisionMatching.oneHot_divisionClosed]
  simp only [OneHotTest, TensorDecisionStable.FiniteTest, oneHot_accepts_iff]

/-- Literal original algebraic unary/binary source predicate, reduced to finitely
many ground polynomial tests on original entries. -/
theorem arityTwo_source_iff (f : Signature AlgebraicComplex n) :
    SourceTensorClosure (fun m _ => m = 1 ∨ m = 2) f ↔ ArityTwoTest f :=
  (arityTwo_test_iff f).symm

/-- Literal original algebraic K/KX tensor predicate, with no factorization input.
The entries tested are the fixed transformed original table, never selected factors. -/
theorem matching_source_iff (opposite : Bool) (f : Signature AlgebraicComplex n) :
    SourceTensorClosure (matchingImage opposite) f ↔
      OneHotTest ((TensorDecisionMatching.basis opposite).symm.action f) := by
  rw [TensorDecisionMatching.sourceMatching_iff]
  exact (oneHot_test_iff _).symm

section Executable
variable [DecidableEq K]

instance (f : Signature K n) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool) :
    Decidable (Rows f count arity ports pivot) :=
  inferInstanceAs (Decidable
    (∀ x, f pivot * sliceProduct f count arity ports pivot x = f x * f pivot ^ count))

instance (f : Signature K n) (S : TensorDecision.Shape n) (pivot : Fin n → Bool) :
    Decidable (ArityTwoAccepts f S pivot) :=
  inferInstanceAs (Decidable (f pivot ≠ 0 ∧ Rows f S.count S.arity S.ports pivot))

instance (f : Signature K n) (S : TensorDecisionStable.Shape n) (pivot : Fin n → Bool) :
    Decidable (OneHotAccepts f S pivot) :=
  inferInstanceAs (Decidable (f pivot ≠ 0 ∧
    (∀ i y, 1 < Holant.weight y → f (blockWord S.count S.arity S.ports pivot i y) = 0) ∧
    Rows f S.count S.arity S.ports pivot))

instance (f : Signature K n) : Decidable (ArityTwoTest f) :=
  inferInstanceAs (Decidable
    ((∀ x, f x = 0) ∨ ∃ S : TensorDecision.Shape n, ∃ pivot, ArityTwoAccepts f S pivot))

instance (f : Signature K n) : Decidable (OneHotTest f) :=
  inferInstanceAs (Decidable
    ((∀ x, f x = 0) ∨ ∃ S : TensorDecisionStable.Shape n, ∃ pivot, OneHotAccepts f S pivot))

/-- The arity-two executable test now requires no coefficient division. -/
def recognizeArityTwo (f : Signature K n) : Bool := decide (ArityTwoTest f)

/-- The one-hot executable test now requires no coefficient division. -/
def recognizeOneHot (f : Signature K n) : Bool := decide (OneHotTest f)

theorem recognizeArityTwo_eq (f : Signature K n) :
    recognizeArityTwo f = TensorDecision.recognize f := by
  apply Bool.eq_iff_iff.mpr
  simp only [recognizeArityTwo, decide_eq_true_eq, TensorDecision.recognize_eq_true_iff,
    arityTwo_test_iff]

theorem recognizeOneHot_eq (f : Signature K n) :
    recognizeOneHot f = TensorDecisionMatching.recognizeOneHot f := by
  apply Bool.eq_iff_iff.mpr
  simp only [recognizeOneHot, decide_eq_true_eq, TensorDecisionMatching.recognizeOneHot_eq_true_iff,
    oneHot_test_iff]
end Executable

end Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionCleared
