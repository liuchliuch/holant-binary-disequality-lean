import Holant.Certificates.RainbowOrbit.Proportional

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Uniqueness of the two literal factors, including their separate nonzero scales. -/
theorem outer_factors {ι κ : Type*} (u u' : ι → ℂ) (v v' : κ → ℂ)
    (hu : ∃ i,u i≠0) (hv : ∃ j,v j≠0)
    (h : Proportional (Matrix.vecMulVec u v) (Matrix.vecMulVec u' v')) :
    Proportional u u' ∧ Proportional v v' := by
  obtain ⟨c,hc,he⟩ := h
  obtain ⟨i,hi⟩ := hu
  obtain ⟨j,hj⟩ := hv
  have he' (a : ι) (b : κ) : u a*v b=c*(u' a*v' b) := by
    simpa [Matrix.vecMulVec,Matrix.smul_apply] using congrFun (congrFun he a) b
  have hp : u' i*v' j≠0 := by
    intro hz
    have := he' i j
    rw [hz,mul_zero] at this
    exact mul_ne_zero hi hj this
  have hi' := (mul_ne_zero_iff.mp hp).1
  have hj' := (mul_ne_zero_iff.mp hp).2
  constructor
  · refine ⟨c*v' j/v j,div_ne_zero (mul_ne_zero hc hj') hj,?_⟩
    funext a
    simp only [Pi.smul_apply,smul_eq_mul]
    apply (mul_right_cancel₀ hj)
    calc u a*v j=c*(u' a*v' j) := he' a j
      _=(c*v' j)*u' a := by ring
      _=((c*v' j/v j)*u' a)*v j := by field_simp
  · refine ⟨c*u' i/u i,div_ne_zero (mul_ne_zero hc hi') hi,?_⟩
    funext b
    simp only [Pi.smul_apply,smul_eq_mul]
    apply (mul_left_cancel₀ hi)
    calc u i*v b=c*(u' i*v' b) := he' i b
      _=u i*((c*u' i/u i)*v' b) := by field_simp

theorem proportional_matching_factors (r : Fin 3) (U V U' V' : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0)
    (h : Proportional (matchingTensor r U V) (matchingTensor r U' V')) :
    Proportional U U' ∧ Proportional V V' := by
  have hf : Proportional (Matrix.vecMulVec (fun p : Bool×Bool => U p.1 p.2)
      (fun p : Bool×Bool => V p.1 p.2))
      (Matrix.vecMulVec (fun p : Bool×Bool => U' p.1 p.2) (fun p : Bool×Bool => V' p.1 p.2)) := by
    obtain ⟨c,hc,he⟩ := h
    refine ⟨c,hc,?_⟩
    have hh := congrArg (flatten r) he
    rw [flatten_smul] at hh
    fin_cases r <;> simpa [flatten,matchingTensor] using hh
  obtain ⟨a,b,hab⟩ := binary_has_nonzero_entry U hU
  obtain ⟨c,d,hcd⟩ := binary_has_nonzero_entry V hV
  obtain ⟨⟨s,hs,he⟩,⟨t,ht,hf⟩⟩ := outer_factors _ _ _ _ ⟨(a,b),hab⟩ ⟨(c,d),hcd⟩ hf
  constructor
  · refine ⟨s,hs,?_⟩
    ext a b
    exact congrFun he (a,b)
  · refine ⟨t,ht,?_⟩
    ext a b
    exact congrFun hf (a,b)

end
end Holant.Certificates.RainbowOrbit
