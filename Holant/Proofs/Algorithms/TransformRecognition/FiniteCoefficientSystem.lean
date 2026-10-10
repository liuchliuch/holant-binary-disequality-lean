import Holant.Proofs.Algorithms.TransformRecognition.CoefficientIdeal
import Holant.Proofs.Algorithms.TransformRecognition.ConstructibleDescent
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic


namespace Holant.LocalDrafts.MainChain.TransformRecognition.FiniteCoefficientSystem
open MvPolynomial Holant.Tractable
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
variable {ι σ : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ AlgebraicComplex)

def coefficients : Finset AlgebraicComplex :=
  Finset.univ.biUnion (fun i => (p i).coeffs)

def field : IntermediateField ℚ AlgebraicComplex :=
  IntermediateField.adjoin ℚ (coefficients p : Set AlgebraicComplex)

instance : FiniteDimensional ℚ (field p) :=
  IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R:=ℚ) x).isIntegral)

theorem coefficient_mem (i : ι) (d : σ →₀ ℕ) : (p i).coeff d ∈ field p := by
  classical
  by_cases h : (p i).coeff d = 0
  · rw [h]; exact (field p).zero_mem
  · apply IntermediateField.subset_adjoin
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,coeff_mem_coeffs d h⟩

/-- A literal support sum, with each original coefficient merely restricted
to the proven generated subfield. No polynomial preimage is assumed. -/
def lower (i : ι) : MvPolynomial σ (field p) :=
  ∑ d ∈ (p i).support, monomial d ⟨(p i).coeff d,coefficient_mem p i d⟩

@[simp] theorem map_lower (i : ι) :
    map (algebraMap (field p) AlgebraicComplex) (lower p i) = p i := by
  classical
  simp [lower]

theorem proper_iff :
    Ideal.span (Set.range (lower p)) ≠ ⊤ ↔ Ideal.span (Set.range p) ≠ ⊤ := by
  have h := CoefficientIdeal.span_map_ne_top_iff
    (E:=AlgebraicComplex) (lower p)
  simpa only [map_lower] using h.symm

variable [Finite σ]

/-- Solutions are allowed in the algebraic closure, NOT restricted to the
finite coefficient field. This is the criterion usable by base-field ideal
membership after the independent sparse encoding bridge is established. -/
theorem solution_iff_proper :
    (∃ x : σ → AlgebraicComplex, ∀ i, aeval x (p i)=0) ↔
      Ideal.span (Set.range (lower p)) ≠ ⊤ := by
  rw [proper_iff]
  constructor
  · rintro ⟨x,hx⟩ ht
    have hker : Ideal.span (Set.range p) ≤ RingHom.ker (aeval x).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hx i
    have hone : (1 : MvPolynomial σ AlgebraicComplex) ∈ Ideal.span (Set.range p) := by
      rw [ht]; trivial
    have he := hker hone
    change aeval x 1 = 0 at he
    simpa using he
  · intro hp
    obtain ⟨x,hx⟩ := ConstructibleDescent.point_of_proper (Ideal.span (Set.range p)) hp
    exact ⟨x,fun i => hx _ (Ideal.subset_span ⟨i,rfl⟩)⟩

end
end Holant.LocalDrafts.MainChain.TransformRecognition.FiniteCoefficientSystem
