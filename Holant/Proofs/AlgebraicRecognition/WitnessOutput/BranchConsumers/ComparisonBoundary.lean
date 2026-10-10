import Holant.Proofs.AlgebraicRecognition.WitnessOutput.BranchConsumers.Recovery


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.BranchConsumers
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Polynomial

def splitRoot : RootCode := ⟨[(2,1),(1,-1)],⟨-1/2,1/2,-1/2,1/2⟩⟩

theorem splitRoot_polynomial : splitRoot.polynomial=(X : ℚ[X])^2-X := by
  simp [splitRoot,RootCode.polynomial,RationalPolynomialCode.polynomial,
    ←Polynomial.C_mul_X_pow_eq_monomial,sub_eq_add_neg]

theorem splitRoot_derivative_at_zero :
    Polynomial.aeval (0 : ℂ) (Polynomial.derivative splitRoot.polynomial) ≠ 0 := by
  norm_num [splitRoot_polynomial,Polynomial.derivative_sub,Polynomial.derivative_X_sq]

/-- This obstruction occurs at a legitimate uniquely specified root, rather
than at a malformed descriptor or an arbitrary evaluation point. -/
theorem splitRoot_represents_zero : splitRoot.Represents 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have hc := congrArg (fun p : ℚ[X] => p.coeff 2) h
    norm_num [splitRoot_polynomial,Polynomial.coeff_X] at hc
  · norm_num [splitRoot,RationalRectangle.Contains]
  · simp [splitRoot_polynomial]
  · intro z hz hp
    have h : z*z-z=0 := by simpa [splitRoot_polynomial,pow_two] using hp
    have hm : z*(z-1)=0 := by linear_combination h
    rcases mul_eq_zero.mp hm with hzero | hone
    · exact hzero
    · have he : z=1 := sub_eq_zero.mp hone
      subst z
      norm_num [splitRoot,RationalRectangle.Contains] at hz

theorem reducible_relation_boundary :
    (0 : ℂ)^2=decodeList (0 : ℂ) [0,1] ∧
      CommonFieldMachine.Coordinates.isZero [0,1]=false ∧
      decodeList (0 : ℂ) [0,1]=0 := by
  norm_num [decodeList,List.range_succ,CommonFieldMachine.Coordinates.isZero,Algebra.smul_def]

theorem coordinate_zero_not_complete :
    ¬ (∀ z : ℂ, ∀ v : List ℚ, z^2=decodeList z [0,1] →
      decodeList z v=0 → CommonFieldMachine.Coordinates.isZero v=true) := by
  intro h
  have hc := h 0 [0,1] reducible_relation_boundary.1 reducible_relation_boundary.2.2
  rw [reducible_relation_boundary.2.1] at hc
  cases hc

end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.BranchConsumers
