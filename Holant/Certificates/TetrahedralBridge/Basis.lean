import Holant.Certificates.TetrahedralOrientation.Data
import Holant.Certificates.MatchingProductBridge.QuaternionCoordinates

/-! The four quaternion kernels are an actual complex basis. Linear coefficient
maps are exactly the bilinear contractions of their Frobenius reconstruction. -/
namespace Holant.Certificates.TetrahedralBridge
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem quaternionCoefficient_add (U V : Binary) (k : Fin 4) :
    quaternionCoefficient (U+V) k = quaternionCoefficient U k+quaternionCoefficient V k := by
  fin_cases k <;> simp [quaternionCoefficient] <;> ring

theorem quaternionCoefficient_smul (c : ℂ) (U : Binary) (k : Fin 4) :
    quaternionCoefficient (c • U) k = c*quaternionCoefficient U k := by
  fin_cases k <;> simp [quaternionCoefficient,smul_eq_mul] <;> ring

theorem quaternionCoefficient_basis (j k : Fin 4) :
    quaternionCoefficient (quaternionBasis j) k = if k = j then 1 else 0 := by
  fin_cases j <;> fin_cases k <;>
    norm_num [quaternionCoefficient,quaternionBasis,Q0,Q1,Q2,Q3,Signature.equality] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem basis_expansion (U : Binary) :
    U = ∑ k : Fin 4, quaternionCoefficient U k • quaternionBasis k := by
  funext a b
  cases a <;> cases b <;>
    simp [quaternionCoefficient,quaternionBasis,Fin.sum_univ_succ,Q0,Q1,Q2,Q3,
      Signature.equality,smul_eq_mul] <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

def mapFromImages (F : Fin 4 → FourTensor) : Binary →ₗ[ℂ] FourTensor where
  toFun := fun U => ∑ k : Fin 4, quaternionCoefficient U k • F k
  map_add' U V := by simp [quaternionCoefficient_add,add_smul,Finset.sum_add_distrib]
  map_smul' c U := by simp [quaternionCoefficient_smul,mul_smul,Finset.smul_sum]

theorem mapFromImages_basis (F : Fin 4 → FourTensor) (j : Fin 4) :
    mapFromImages F (quaternionBasis j) = F j := by
  simp [mapFromImages,quaternionCoefficient_basis]

theorem map_ext_basis {Φ Ψ : Binary →ₗ[ℂ] FourTensor}
    (h : ∀ k : Fin 4, Φ (quaternionBasis k) = Ψ (quaternionBasis k)) : Φ = Ψ := by
  apply LinearMap.ext
  intro U
  rw [basis_expansion U]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k]

def reconstruct (F : Fin 4 → FourTensor) : Signature ℂ 6 := fun x =>
  ∑ k : Fin 4, TetrahedralOrientation.dual k (x 0) (x 1)*F k (fun j => x j.succ.succ)

theorem mapFromImages_eq_contract (F : Fin 4 → FourTensor) (U : Binary) :
    mapFromImages F U = Signature.contract U (reconstruct F) := by
  funext x
  simp [mapFromImages,Signature.contract,reconstruct,quaternionCoefficient,
    TetrahedralOrientation.dual,Fin.sum_univ_succ,Q0,Q1,Q2,Q3,Signature.equality,smul_eq_mul]
  ring

end
end Holant.Certificates.TetrahedralBridge
