import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankThreeAlphaCore
import Holant.Proofs.Hardness.EOBinaryPlaneClassification

/-! The actual square of a full ternary row transports the binary signed
cross relation between its parallel faces. No pointwise phase is discarded. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginParallelFace
open Holant Holant.Tractable Holant.Tractable.AffinePhase
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
  (Full CommonFourth SignedCross Cross full_affine_iff affine_signed_cross)
end B
namespace C
export OrdinaryNegativeRankThreeAlphaCore (cubicRatio origin_cube_ratio)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def face (h : Signature AlgebraicComplex 3) (bit : Bool) : Signature AlgebraicComplex 2 :=
  fun x=>h (Fin.cons bit x)

variable (h : Signature AlgebraicComplex 3)
variable (full : ∀x,h x≠0) (square : Affine (fun x=>h x^2))
variable (fourth : ∀x y,h x^4=h y^4)

include full square fourth in
theorem affine_parallel (base : Affine (face h false)) : Affine (face h true) := by
  have baseSquare : (h ![false,false,false]*h ![false,true,true])^2=
      (h ![false,false,true]*h ![false,true,false])^2 := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mpr (B.affine_signed_cross (face h false) (fun x=>full _) base)
  have cube := thirdTrivial_of_affine (fun x=>pow_ne_zero 2 (full x)) square
    (origin 3) (basis 0) (basis 1) (basis 2)
  rw [C.origin_cube_ratio] at cube
  have den : (h ![true,true,false]^2*h ![true,false,true]^2*
      h ![false,true,true]^2*h ![false,false,false]^2)≠0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (full _))
      (pow_ne_zero 2 (full _))) (pow_ne_zero 2 (full _))) (pow_ne_zero 2 (full _))
  have cubeEq : h ![true,true,true]^2*h ![true,false,false]^2*
      h ![false,true,false]^2*h ![false,false,true]^2=
      h ![true,true,false]^2*h ![true,false,true]^2*
      h ![false,true,true]^2*h ![false,false,false]^2 := by
    exact (div_eq_one_iff_eq den).mp cube
  have topSquare : (h ![true,false,false]*h ![true,true,true])^2=
      (h ![true,false,true]*h ![true,true,false])^2 := by
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 (full ![false,false,true]))
      (pow_ne_zero 2 (full ![false,true,false])))
    calc
      _=h ![true,true,true]^2*h ![true,false,false]^2*
          h ![false,true,false]^2*h ![false,false,true]^2 := by ring
      _=h ![true,true,false]^2*h ![true,false,true]^2*
          h ![false,true,true]^2*h ![false,false,false]^2 := cubeEq
      _=(h ![true,false,true]*h ![true,true,false])^2*
          (h ![false,false,false]*h ![false,true,true])^2 := by ring
      _=_ := by rw [baseSquare];ring
  apply (B.full_affine_iff (face h true) (fun x=>full _)).mpr
  refine ⟨?_,sq_eq_sq_iff_eq_or_eq_neg.mp topSquare⟩
  intro x
  exact fourth _ _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginParallelFace
end
