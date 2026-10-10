import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.AlgebraicIdentity
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.Primitive


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
open Holant.Tractable Holant.LocalDrafts.EffectiveAlgebraic PowerArithmetic MvPolynomial
open scoped BigOperators
noncomputable section
variable {m n q : ℕ}

abbrev CoefficientIndex (m : ℕ) (H : Fin q → MvPolynomial (Fin n) AlgebraicComplex) :=
  Fin m ⊕ (Σ i : Fin q, {a : Fin n →₀ ℕ // a ∈ (H i).support})

/-- Coordinates for a finite family of genuine algebraic polynomials, using
one common primitive for their coefficients AND the literal original inputs. -/
theorem multiplier_coordinates (w : Fin m → AlgebraicComplex)
    (H : Fin q → MvPolynomial (Fin n) AlgebraicComplex) :
    ∃ (θ : ℂ) (d : ℕ) (c : Vector d) (e : Fin m → RationalPolynomialCode)
      (P : Fin q → Poly n d),
      IsAlgebraic ℚ θ ∧ PowerArithmetic.polynomial c = minpoly ℚ θ ∧
      (PowerArithmetic.polynomial c).Separable ∧
      (∀ j, Polynomial.aeval θ (e j).polynomial = (w j : ℂ)) ∧
      (∀ i, value θ (P i) = MvPolynomial.map (algebraMap AlgebraicComplex ℂ) (H i)) := by
  classical
  let z : CoefficientIndex m H → AlgebraicComplex
    | .inl j => w j
    | .inr ⟨i, a⟩ => (H i).coeff a
  obtain ⟨θ, hθ, _, _, d, c, e, hmin, _, hsep, he, hd⟩ :=
    CommonPrimitive.tuple_primitive (fun a => (z a : ℂ)) (fun a => (z a).property.isAlgebraic)
  let R : CoefficientIndex m H → Vector d := fun a => CommonFieldCheck.reduce c (e a)
  have hR (a : CoefficientIndex m H) : decode θ (R a) = (z a : ℂ) := hd a
  let P : Fin q → Poly n d := fun i => (H i).support.attach.toList.map
    (fun a => ((fun j => a.val j), R (.inr ⟨i, a⟩)))
  refine ⟨θ, d, c, fun j => e (.inl j), P, hθ, hmin, hsep,
    fun j => he (.inl j), ?_⟩
  intro i
  simp only [P, value, List.map_map, Function.comp_def]
  rw [Finset.sum_map_toList]
  simp only [Sparse.exponent_coe, hR, z]
  rw [Finset.sum_attach (f := fun a => MvPolynomial.monomial a ((H i).coeff a : ℂ))]
  have hm := congrArg (MvPolynomial.map (algebraMap AlgebraicComplex ℂ)) (H i).as_sum
  simpa only [map_sum, map_monomial,IntermediateField.algebraMap_apply] using hm.symm

/-- The actual identity gives zero COORDINATES in the completeness witness's
minimal relation. This is the only direction that uses injectivity. -/
theorem identity_coordinates (w : Fin m → AlgebraicComplex) (S : EncodedSystem.System m n)
    (hn : NoAlgebraicSolution w S) :
    ∃ (θ : ℂ) (d : ℕ) (c : Vector d) (e : Fin m → RationalPolynomialCode)
      (P : Fin S.length → Poly n d),
      IsAlgebraic ℚ θ ∧ PowerArithmetic.polynomial c = minpoly ℚ θ ∧
      (PowerArithmetic.polynomial c).Separable ∧
      (∀ j, Polynomial.aeval θ (e j).polynomial = (w j : ℂ)) ∧
      zeroCoefficients (defect c e S P) = true := by
  obtain ⟨H, hH⟩ := exists_multipliers w S hn
  obtain ⟨θ, d, c, e, P, hθ, hmin, hsep, he, hP⟩ := multiplier_coordinates w H
  have hr : θ^(d+1) = decode θ c :=
    relation_of_root θ c (by rw [hmin]; exact minpoly.aeval ℚ θ)
  have hw (j : Fin m) : decode θ (CommonFieldCheck.familyCoordinates c e j) = (w j : ℂ) := by
    rw [CommonFieldCheck.familyCoordinates, CommonFieldCheck.decode_reduce θ c hr, he]
  have hv : value θ (defect c e S P) = 0 := by
    rw [value_defect θ c hr e (fun j => (w j : ℂ)) hw, sub_eq_zero]
    simpa only [hP] using map_multiplier_identity w S H hH
  exact ⟨θ, d, c, e, P, hθ, hmin, hsep, he,
    zeroCoefficients_complete θ c hmin _ hv⟩

end
end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
