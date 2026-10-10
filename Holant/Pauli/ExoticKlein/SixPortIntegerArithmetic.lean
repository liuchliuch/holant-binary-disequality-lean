import Holant.Pauli.ExoticKlein.SixPortSparseCertificate

/-! Exact Gaussian integer coefficients, embedded faithfully in the existing
Gaussian rational field. All denominator clearing below is proved. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open LinearCertificate
abbrev GZ := QuadraticAlgebra ℤ (-1) 0

def integerToGaussian : GZ →+* Q where
  toFun z := ⟨z.re,z.im⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' u v := by ext <;> simp
  map_mul' u v := by ext <;> simp <;> ring

theorem integerToGaussian_injective : Function.Injective integerToGaussian := by
  intro u v h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  apply QuadraticAlgebra.ext
  · exact Int.cast_injective (α := ℚ) hr
  · exact Int.cast_injective (α := ℚ) hi

def integerI : GZ := ⟨0,1⟩

@[simp] theorem integerToGaussian_i : integerToGaussian integerI = gaussianI := rfl

theorem integerToGaussian_E (a : Label) (u v : Bool) :
    integerToGaussian (EOver integerI a u v) = gaussianE a u v := by
  revert a u v
  decide +kernel

def integerDual4 (a : Label) (u v : Bool) : GZ :=
  (if a.1 = 0 then 2 else 1)*EOver integerI (theta a) u v

theorem integerToGaussian_dual4 (a : Label) (u v : Bool) :
    integerToGaussian (integerDual4 a u v) = 4*dualOver gaussianI a u v := by
  simp only [integerDual4,map_mul,integerToGaussian_E,dualOver]
  unfold dOver
  split_ifs <;> norm_num [gaussianE,map_ofNat] <;> ring

theorem integerToGaussian_direction (d : Direction) (x : Fin 4 → Bool) :
    integerToGaussian (directionTensorOver integerI d x) = gaussianDirection d x := by
  change integerToGaussian (directionTensorOver integerI d x) = directionTensorOver gaussianI d x
  unfold directionTensorOver
  split_ifs <;> simp only [map_mul,integerToGaussian_E,gaussianE]

theorem integerToGaussian_option (d : Option Direction) (x : Fin 4 → Bool) :
    integerToGaussian (optionDirectionOver integerI d x) = gaussianOptionDirection d x := by
  cases d with
  | none => exact map_zero _
  | some d => exact integerToGaussian_direction d x

end
end Holant.Pauli.ExoticKlein.SixPort
