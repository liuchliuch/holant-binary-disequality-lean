import Holant.Certificates.PlatonicIncidence.SpanTransport
import Holant.Certificates.RainbowOrbit.ExternalGroup
import Holant.Certificates.OppositeIcosahedral.KernelDictionary

/-! Actual invertible coefficient dictionaries for all marked domain rows.
These maps are analytic dictionaries; no physical realization is asserted. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- O, O', O_dt and O_td use their exact frozen conjugators. -/
def thetaEquiv (f : OctahedralSeparator.Form) : Mat ≃ₗ[ℂ] Mat where
  toFun := OctahedralSeparator.complexTheta f
  invFun := OctahedralSeparator.complexPull f
  left_inv := OctahedralSeparator.complexPull_complexTheta f
  right_inv := OctahedralSeparator.complexTheta_complexPull f
  map_add' U V := by simp [OctahedralSeparator.complexTheta,mul_add,add_mul]
  map_smul' c U := OctahedralSeparator.complexTheta_smul f c U

@[simp] theorem thetaEquiv_apply (f : OctahedralSeparator.Form) (U : Mat) :
    thetaEquiv f U=OctahedralSeparator.complexTheta f U := rfl

/-- Literal odd-permutation icosahedral display, linked to 9.2's proved
conjugation dictionary. -/
def oppositeEquiv : Mat ≃ₗ[ℂ] Mat where
  toFun := OppositeIcosahedral.conjugate
  invFun := OppositeIcosahedral.pull
  left_inv := OppositeIcosahedral.pull_conjugate
  right_inv := OppositeIcosahedral.conjugate_pull
  map_add' U V := by simp [OppositeIcosahedral.conjugate,mul_add,add_mul]
  map_smul' c U := OppositeIcosahedral.conjugate_smul c U

@[simp] theorem oppositeEquiv_apply (U : Mat) :
    oppositeEquiv U=OppositeIcosahedral.conjugate U := rfl

/-- The retained literal-I kernel dictionary itself, with no replacement of I. -/
def kappaEquiv : Mat ≃ₗ[ℂ] Mat where
  toFun := OppositeIcosahedral.kappa
  invFun := OppositeIcosahedral.unkappa
  left_inv := OppositeIcosahedral.unkappa_kappa
  right_inv := OppositeIcosahedral.kappa_unkappa
  map_add' U V := by simp [OppositeIcosahedral.kappa,mul_add,add_mul]
  map_smul' c U := OppositeIcosahedral.kappa_smul c U

@[simp] theorem kappaEquiv_apply (U : Mat) : kappaEquiv U=OppositeIcosahedral.kappa U := rfl

theorem external_dictionary (i : Fin 12) :
    thetaEquiv 2 (representative .tetrahedral i)=External.representative i :=
  (External.representative_eq_theta i).symm

theorem opposite_dictionary (i : Fin 60) :
    oppositeEquiv (representative .icosahedral i)=OppositeIcosahedral.oppositeRepresentative i := rfl

/-- Exact fixed representative, index and nonzero scalar from the literal
kernel-class bijection in 9.2. -/
theorem retained_I_kernel_dictionary (i : Fin 60) :
    OppositeIcosahedral.kernelScale i≠0 ∧
    kappaEquiv (representative .icosahedral i)=OppositeIcosahedral.kernelScale i •
      OppositeIcosahedral.oppositeRepresentative (OppositeIcosahedral.kernelIndex i) :=
  ⟨OppositeIcosahedral.kernelScale_ne_zero i,OppositeIcosahedral.kernel_representative_exact i⟩

end
end Holant.Certificates.PlatonicIncidence
