import Holant.Pauli.ExoticKlein.SixPortAtlasData

/-! Kernel-checked literal identities for the seventeen candidate vectors.
They establish numeric normalization, distinctness, and the exact displayed
direction/scale reconstruction; exhaustive960coverage is checked separately. -/
namespace Holant.Pauli.ExoticKlein.SixPort.Atlas
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option Elab.async false
open scoped BigOperators

theorem candidate_pivot_check (i : Fin 17) :
    (candidateMultiplier i : GZ)*doubleBase (candidateIndex i) 0 = 2 := by
  revert i
  decide +kernel

theorem candidate_integer_injective : Function.Injective candidateInteger := by
  decide +kernel

theorem candidate_reconstruction_check (i : Fin 17) (w : Fin 64) :
    2*candidateInteger i w =
      ∑ a : Fin 4, integerTensor (candidateState i) w a*(candidateScale2 i a : GZ) := by
  revert i w
  decide +kernel

theorem candidate_multiplier_eval (i : Fin 17) :
    (candidateMultiplier i : ℂ) = Algebraic.gaussianToComplex (productScale (candidateIndex i)) := by
  have hh := congrArg evalInteger (candidate_pivot_check i)
  simp only [map_mul,map_natCast,map_ofNat] at hh
  have hp : evalInteger (doubleBase (candidateIndex i) 0) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hh
    norm_num at hh
  rw [productScale_eval]
  exact (eq_div_iff hp).mpr hh

theorem candidateInteger_eval (i : Fin 17) (w : Fin 64) :
    evalInteger (candidateInteger i w) = candidate i ((wordEquiv 6).symm w) := by
  rw [candidateInteger,map_mul,map_natCast,candidate_multiplier_eval]
  have hh := eval_rawProduct (candidateIndex i) ((wordEquiv 6).symm w)
  exact congrArg (Algebraic.gaussianToComplex (productScale (candidateIndex i))*·) hh

theorem candidate_injective : Function.Injective candidate := by
  intro i j hij
  apply candidate_integer_injective
  funext w
  apply evalInteger_injective
  rw [candidateInteger_eval,candidateInteger_eval]
  exact congrFun hij _

theorem eval_integerTensor (state : DirectionTriple) (w : Fin 64) (a : Fin 4) :
    evalInteger (integerTensor state w a) =
      E (labelEquiv a) ((wordEquiv 6).symm w 0) ((wordEquiv 6).symm w 1)*
        optionDirection (cardDirections state a) (tail4 ((wordEquiv 6).symm w)) := by
  change Algebraic.gaussianToComplex (integerToGaussian (integerTensor state w a)) = _
  rw [integerTensor_correct]
  simp only [tensorMatrix,map_mul,map_gaussianE,map_gaussianOptionDirection]

/-- Literal source reconstruction, with the zero triple and all sixteen
signed half-scale cases represented by their actual coefficients. -/
theorem candidate_reconstruction (i : Fin 17) :
    candidate i = normalizedTensor (candidateState i) (candidateScale i) := by
  funext x
  obtain ⟨w,rfl⟩ := (wordEquiv 6).symm.surjective x
  have hh := congrArg evalInteger (candidate_reconstruction_check i w)
  simp only [map_mul,map_ofNat,candidateInteger_eval,map_sum,eval_integerTensor,map_intCast] at hh
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  rw [hh]
  simp only [normalizedTensor,Finset.mul_sum,candidateScale]
  apply Finset.sum_congr rfl
  intro a ha
  ring

end
end Holant.Pauli.ExoticKlein.SixPort.Atlas
