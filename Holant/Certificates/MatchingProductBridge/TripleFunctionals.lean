import Holant.Certificates.MatchingProductBridge.OrthogonalTriples
import Holant.Certificates.MatchingProductBridge.Exceptionals

namespace Holant.Certificates.MatchingProductBridge
noncomputable section

def traceCoefficient (f : FourTensor) : ℂ := recover f 0 0 + recover f 1 1 + recover f 2 2

theorem traceCoefficient_add (f g : FourTensor) : traceCoefficient (f+g) = traceCoefficient f + traceCoefficient g := by
  simp [traceCoefficient,recover,symmetricCoefficient,signedCoefficient]
  ring

theorem antisymmetricCoefficient_add (f g : FourTensor) :
    antisymmetricCoefficient (f+g) = antisymmetricCoefficient f + antisymmetricCoefficient g := by
  simp [antisymmetricCoefficient]
  ring

theorem traceCoefficient_zero : traceCoefficient 0 = 0 := by
  norm_num [traceCoefficient,recover,symmetricCoefficient,signedCoefficient]
theorem antisymmetricCoefficient_zero : antisymmetricCoefficient 0 = 0 := by
  norm_num [antisymmetricCoefficient]

theorem traceCoefficient_half_A : traceCoefficient ((1/2 : ℂ) • A) = 3/2 := by
  norm_num [traceCoefficient,recover,symmetricCoefficient,signedCoefficient,A,P0,Q0,Holant.Signature.equality,smul_eq_mul]
  ring_nf
  norm_num [Complex.I_sq]
theorem traceCoefficient_half_B : traceCoefficient ((1/2 : ℂ) • B) = 3/2 := by
  norm_num [traceCoefficient,recover,symmetricCoefficient,signedCoefficient,B,P1,Q0,Holant.Signature.equality,smul_eq_mul]
  ring_nf
  norm_num [Complex.I_sq]
theorem antisymmetricCoefficient_half_A : antisymmetricCoefficient ((1/2 : ℂ) • A) = 1/4 := by
  norm_num [antisymmetricCoefficient,A,P0,Q0,Holant.Signature.equality,smul_eq_mul]
theorem antisymmetricCoefficient_half_B : antisymmetricCoefficient ((1/2 : ℂ) • B) = -(1/4) := by
  norm_num [antisymmetricCoefficient,B,P1,Q0,Holant.Signature.equality,smul_eq_mul]

theorem traceCoefficient_R (u : Fin 3 → ℝ) (hu : u ≠ 0) : traceCoefficient (R u) = 1 := by
  have hn : (normSquare u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (normSquare_pos u hu))
  rw [R_eq_polarize]
  simp only [traceCoefficient,recover_polarize,realProjector]
  field_simp [hn] <;> norm_cast <;> simp [normSquare,pow_two]

theorem antisymmetricCoefficient_R (u : Fin 3 → ℝ) : antisymmetricCoefficient (R u) = 0 := by
  rw [R_eq_polarize,antisymmetric_polarize]

theorem traceCoefficient_target : traceCoefficient (fun x => (A x+B x)/2) = 3 := by
  rw [← polarize_identity]
  norm_num [traceCoefficient,recover_polarize,Matrix.one_apply]

theorem antisymmetricCoefficient_target : antisymmetricCoefficient (fun x => (A x+B x)/2) = 0 := by
  rw [← polarize_identity,antisymmetric_polarize]

end
end Holant.Certificates.MatchingProductBridge
