import Holant.Certificates.RainbowOrbit.MarkedOrbit
import Holant.Certificates.RainbowOrbit.InitialData
import Holant.Certificates.OctahedralSeparator.TensorData
import Holant.Certificates.OctahedralSeparator.TensorSemantics

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def primeInitial (r : Fin 3) : FourTensor := complexTensor (primeInitialScalar r)
def primeScale : Fin 3→ℂ := ![1,-1,-1]

theorem complex_base_scalar (r : Fin 3) : complexTensor (![aTensor,bTensor,cTensor] r)=base r := by
  fin_cases r <;> funext x <;>
    rcases h0 : x 0 with _|_ <;> rcases h1 : x 1 with _|_ <;>
    rcases h2 : x 2 with _|_ <;> rcases h3 : x 3 with _|_ <;>
    simp [h0,h1,h2,h3,complexTensor,aTensor,bTensor,cTensor,p0,p1,p2,base,A,B,C,P0,P1,P2,q,mat,
      Q0,Q2,Signature.equality,embed_mul,embed_one,embed_zero]

theorem prime_initial_exact (r : Fin 3) : act (markLegs 1) (base r)=primeScale r • primeInitial r := by
  have hh := congrArg complexTensor (prime_initial_certificate r)
  rw [complexTensor_action,complex_base_scalar] at hh
  change act (markLegs 1) (base r)=_ at hh
  change _=complexTensor (fun x => primeScaleScalar r*primeInitialScalar r x) at hh
  rw [complexTensor_scale] at hh
  have he : embed (primeScaleScalar r)=primeScale r := by fin_cases r <;> simp [primeScaleScalar,primeScale,embed_one]
  simpa only [he,primeInitial] using hh

theorem primeScale_ne_zero (r : Fin 3) : primeScale r≠0 := by
  fin_cases r <;> norm_num [primeScale]

/-- Exactly the displayed ordered O' representative in A.18. -/
theorem prime_initial_display : primeInitial=
    ![P0 (complexTheta 1 (Matrix.of Q0)) (complexTheta 1 (Matrix.of Q0)),
      P1 (complexTheta 1 (Matrix.of Q1)) (complexTheta 1 (Matrix.of Q1)),
      P2 (complexTheta 1 (Matrix.of Q2)) (complexTheta 1 (Matrix.of Q2))] := by
  funext r
  fin_cases r <;> funext x <;>
    simp [primeInitial,primeInitialScalar,complexTensor,p0,p1,p2,P0,P1,P2,embed_mul,
      ←complexMatrix_apply,complexMatrix_theta,complexMatrix_q,quaternionBasis]

def markedInitial (f : Form) (r : Fin 3) : FourTensor := act (markLegs f) (base r)

theorem markedInitial_nonzero (f : Form) (r : Fin 3) : markedInitial f r≠0 :=
  act_nonzero _ (markLegs_det f) (base_nonzero r)

theorem primeInitial_nonzero (r : Fin 3) : primeInitial r≠0 := by
  intro hz
  have hh := prime_initial_exact r
  rw [hz,smul_zero] at hh
  exact markedInitial_nonzero 1 r hh

theorem prime_initial_projective (r : Fin 3) :
    Projectivization.mk ℂ (markedInitial 1 r) (markedInitial_nonzero 1 r)=
      Projectivization.mk ℂ (primeInitial r) (primeInitial_nonzero r) :=
  (proportional_point_iff _ _ _ _).mp ⟨primeScale r,primeScale_ne_zero r,prime_initial_exact r⟩

end
end Holant.Certificates.RainbowOrbit
