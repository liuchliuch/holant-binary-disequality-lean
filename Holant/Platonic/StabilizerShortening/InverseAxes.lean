import Holant.Platonic.StabilizerShortening.ActualKernels
import Holant.Platonic.StabilizerErasure.BellCoefficients
import Holant.Platonic.StabilizerShortening.AffineTools

/-! The finite matrices used to pull back the selected actual card really
are the inverses of the exact normalized physical axis frames. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem inverseAxis_mul_axis (p : Fin 4) :
    Kernel.mul (inverseAxis p) (axisMatrix p)=Signature.equality := by
  ext a b
  fin_cases p <;> cases a <;> cases b
  all_goals simp [Kernel.mul_apply,inverseAxis,inverseAxisRaw,inverseAxisScale,
    axisMatrix,qubitPauli,localH,localSinv,Signature.equality]
  all_goals (try ring_nf)
  all_goals (try simp only [Complex.I_sq,
    show ((Real.sqrt 2 : ℂ)⁻¹)^2=(1/2 : ℂ) from sqrtTwo_complex_inv_sq])
  all_goals ring

theorem axis_mul_inverseAxis (p : Fin 4) :
    Kernel.mul (axisMatrix p) (inverseAxis p)=Signature.equality := by
  ext a b
  fin_cases p <;> cases a <;> cases b
  all_goals simp [Kernel.mul_apply,inverseAxis,inverseAxisRaw,inverseAxisScale,
    axisMatrix,qubitPauli,localH,localSinv,Signature.equality]
  all_goals (try ring_nf)
  all_goals (try simp only [Complex.I_sq,
    show ((Real.sqrt 2 : ℂ)⁻¹)^2=(1/2 : ℂ) from sqrtTwo_complex_inv_sq])
  all_goals ring

theorem inverseAxis_coordinate_cancel {n : ℕ} (p : Fin n → Fin 4)
    (f : Signature ℂ n) :
    Signature.coordinateAction (fun r=>inverseAxis (p r))
      (Signature.coordinateAction (fun r=>axisMatrix (p r)) f)=f :=
  Signature.coordinateAction_cancel _ _ (fun r=>inverseAxis_mul_axis (p r)) f

theorem axis_inverse_coordinate_cancel {n : ℕ} (p : Fin n → Fin 4)
    (f : Signature ℂ n) :
    Signature.coordinateAction (fun r=>axisMatrix (p r))
      (Signature.coordinateAction (fun r=>inverseAxis (p r)) f)=f :=
  Signature.coordinateAction_cancel _ _ (fun r=>axis_mul_inverseAxis (p r)) f

theorem effectiveKernel_affine (p q : Fin 4) :
    ComplexAffine (fun x : Word 2=>effectiveKernel p q (x 0) (x 1)) :=
  ⟨inverseAxisScale p*inverseAxisScale q*effectiveScale p q,
    fun x=>fourthRootPhase ((effectivePhase p q).eval x),
    affine_quadratic_phase _,effectiveKernel_formula p q⟩

theorem effectiveKernel_inverse_affine (p q : Fin 4) :
    ComplexAffine (fun x : Word 2=>(effectiveKernel p q (x 0) (x 1))⁻¹) :=
  affine_complex_inverse (effectiveKernel_affine p q)
    (fun x=>effectiveKernel_full_support p q (x 0) (x 1))

end
end Holant.Platonic.StabilizerShortening
