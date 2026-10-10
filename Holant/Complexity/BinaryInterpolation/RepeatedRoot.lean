import Holant.Complexity.BinaryInterpolation.BinaryFactors

/-! The repeated characteristic-root case, with its derived nonzero nilpotent
part and exact normalized transfer-power formula. -/
namespace Holant.Complexity.BinaryInterpolation
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency false

def nilpotentPart (A : Binary (K := K)) (a : K) : Binary (K := K) := A-a • (1 : Binary)

theorem nilpotentPart_square (A : Binary (K := K)) (a : K)
    (ht : Matrix.trace A=a+a) (hd : Matrix.det A=a*a) :
    nilpotentPart A a*nilpotentPart A a=0 := by
  unfold nilpotentPart
  simp only [sub_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,
    smul_smul]
  rw [cayley_two,ht,hd]
  module

theorem nilpotentPart_nonzero (A : Binary (K := K)) (a : K) (ha : a≠0)
    (hi : ¬ProjectivelyFinite A) : nilpotentPart A a≠0 := by
  intro hz
  have he : A=a • (1 : Binary) := sub_eq_zero.mp hz
  exact hi ⟨1,by decide,a,ha,by simpa using he⟩

theorem nilpotentPart_det (A : Binary (K := K)) (a : K)
    (ht : Matrix.trace A=a+a) (hd : Matrix.det A=a*a) :
    Matrix.det (nilpotentPart A a)=0 := by
  rw [nilpotentPart,shifted_determinant,ht,hd]
  ring

theorem repeated_power (A : Binary (K := K)) (a : K) (ha : a≠0)
    (ht : Matrix.trace A=a+a) (hd : Matrix.det A=a*a) (t : ℕ) :
    A^t=a^t • (1+(t:K) • (a⁻¹ • nilpotentPart A a)) := by
  have hn := nilpotentPart_square A a ht hd
  have hn' : (a⁻¹ • nilpotentPart A a)*(a⁻¹ • nilpotentPart A a)=0 := by
    simp only [Matrix.smul_mul,Matrix.mul_smul,hn,smul_zero]
  have he : A=a • (1+a⁻¹ • nilpotentPart A a) := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ ha,one_smul]
    unfold nilpotentPart
    module
  calc
    A^t=(a • (1+a⁻¹ • nilpotentPart A a))^t := congrArg (fun M => M^t) he
    _ = a^t • ((1+a⁻¹ • nilpotentPart A a)^t) := smul_pow ..
    _ = _ := by rw [one_add_pow_of_square_zero hn' t]

end
end Holant.Complexity.BinaryInterpolation
