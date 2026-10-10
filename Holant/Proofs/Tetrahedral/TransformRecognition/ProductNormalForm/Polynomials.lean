import Holant.Proofs.Tetrahedral.TransformRecognition.ProductNormalForm.Source
import Mathlib.Algebra.MvPolynomial.Eval


namespace Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open Holant Holant.Tractable
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def entryPolynomial (R : Type*) [CommSemiring R] {n : ℕ}
    (S : Skeleton n) (x : Fin n → Bool) : MvPolynomial (Parameter n) R :=
  if holds S x then MvPolynomial.X none * ∏ j, MvPolynomial.X (some (j,x j)) else 0

/-- Exact specialization, also valid over C or a number field. No coefficient
nonvanishing is required to match the source Product zero branches. -/
theorem eval₂_entry {R K : Type*} [CommSemiring R] [CommSemiring K]
    (φ : R →+* K) {n : ℕ} (S : Skeleton n) (θ : Parameter n → K) (x : Fin n → Bool) :
    MvPolynomial.eval₂ φ θ (entryPolynomial R S x) = evaluate S θ x := by
  rw [entry_formula]
  by_cases h : holds S x <;> simp [entryPolynomial, h]

theorem evaluate_map {K L : Type*} [CommSemiring K] [CommSemiring L]
    (φ : K →+* L) {n : ℕ} (S : Skeleton n) (θ : Parameter n → K) (x : Fin n → Bool) :
    evaluate S (fun i => φ (θ i)) x = φ (evaluate S θ x) := by
  rw [entry_formula, entry_formula]
  by_cases h : holds S x <;> simp [h]

def entryEquation {n : ℕ} (f : Signature AlgebraicComplex n) (S : Skeleton n)
    (x : Fin n → Bool) : MvPolynomial (Parameter n) AlgebraicComplex :=
  MvPolynomial.C (f x) - entryPolynomial AlgebraicComplex S x

theorem entryEquation_zero_iff {n : ℕ} (f : Signature AlgebraicComplex n)
    (S : Skeleton n) (θ : Parameter n → AlgebraicComplex) (x : Fin n → Bool) :
    MvPolynomial.eval θ (entryEquation f S x) = 0 ↔ f x = evaluate S θ x := by
  have he := eval₂_entry (RingHom.id AlgebraicComplex) S θ x
  change MvPolynomial.eval θ (entryPolynomial AlgebraicComplex S x) = evaluate S θ x at he
  simp [entryEquation, he, sub_eq_zero]

/-- Precisely 2^n indexed entry equations for each finite skeleton. This
theorem only characterizes their zero set; it does not decide nonemptiness. -/
theorem product_iff_polynomial_solution {n : ℕ} (f : Signature AlgebraicComplex n) :
    Product f ↔ ∃ S ∈ allSkeletons n, ∃ θ : Parameter n → AlgebraicComplex,
      ∀ x : Fin n → Bool, MvPolynomial.eval θ (entryEquation f S x) = 0 := by
  rw [finite_enumeration]
  constructor
  · rintro ⟨S,hS,θ,rfl⟩
    exact ⟨S,hS,θ,fun x => (entryEquation_zero_iff _ S θ x).mpr rfl⟩
  · rintro ⟨S,hS,θ,hθ⟩
    exact ⟨S,hS,θ,funext (fun x => (entryEquation_zero_iff f S θ x).mp (hθ x))⟩

theorem equation_index_count (n : ℕ) : Fintype.card (Fin n → Bool) = 2^n := by simp

/-- Finite polynomial tables can be consumed without any factor-list bound
or a user-supplied template-completeness hypothesis. -/
theorem fixed_template_family (n : ℕ) :
    (allSkeletons n).card = 2^(2*n*n) ∧ Fintype.card (Parameter n) = 1+2*n ∧
      Fintype.card (Fin n → Bool) = 2^n :=
  ⟨allSkeletons_count n,parameter_count n,equation_index_count n⟩

end
end Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
