import Holant.Platonic.FixedMatchingRuling.TetrahedralExtension
import Holant.Certificates.RainbowOrbit.GroupRepresentatives
import Holant.Certificates.MatchingProductBridge.GroupInverses

/-! Actual tetrahedral matrix multiplication and the four paired sign points.
All changes of input coordinates are proved invertible matrix multiplications. -/
namespace Holant.Platonic.ActiveSupport
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Platonic.FixedMatchingRuling
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def anchor : Binary := quaternion ![1,-1,-1,-1]

def paired : Fin 4 → Binary :=
  ![quaternion ![1,1,1,1],quaternion ![1,1,-1,-1],
    quaternion ![1,-1,1,-1],quaternion ![1,-1,-1,1]]

theorem anchor_base : tetrahedralBase anchor := by
  exact Or.inr ⟨fun _ => true,rfl⟩

theorem paired_base (j : Fin 4) : tetrahedralBase (paired j) := by
  fin_cases j
  · exact Or.inr ⟨![false,false,false],rfl⟩
  · exact Or.inr ⟨![false,true,true],rfl⟩
  · exact Or.inr ⟨![true,false,true],rfl⟩
  · exact Or.inr ⟨![true,true,false],rfl⟩

def pairSign (j : Fin 4) : ℂ := if j=0 then 1 else -1

theorem pairSign_ne_zero (j : Fin 4) : pairSign j≠0 := by
  unfold pairSign
  split_ifs <;> norm_num

theorem anchor_pair_axis (j : Fin 4) :
    anchor+pairSign j • paired j=(2*pairSign j) • quaternionBasis j := by
  fin_cases j <;> ext a b <;>
    simp [anchor,paired,pairSign,quaternion,quaternionBasis,smul_eq_mul] <;> ring

theorem paired_relation :
    (2:ℂ) • anchor=-paired 0+paired 1+paired 2+paired 3 := by
  ext a b
  simp [anchor,paired,quaternion,smul_eq_mul]
  ring

def pairedCoefficient (K : Binary) : Fin 4→ℂ :=
  let c := quaternionCoefficient K
  ![(c 0+c 1+c 2+c 3)/4,(c 0+c 1-c 2-c 3)/4,
    (c 0-c 1+c 2-c 3)/4,(c 0-c 1-c 2+c 3)/4]

theorem paired_reconstruction (K : Binary) :
    ∑j : Fin 4,pairedCoefficient K j • paired j=K := by
  ext a b
  cases a <;> cases b <;>
    simp [pairedCoefficient,paired,quaternionCoefficient,quaternion,Fin.sum_univ_succ,
      smul_eq_mul,Q0,Q1,Q2,Q3,Holant.Signature.equality] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem pairedCoefficient_synthesis (c : Fin 4→ℂ) :
    pairedCoefficient (∑j : Fin 4,c j • paired j)=c := by
  ext j
  fin_cases j <;>
    simp [pairedCoefficient,paired,quaternionCoefficient,quaternion,Fin.sum_univ_succ,
      smul_eq_mul,Q0,Q1,Q2,Q3,Holant.Signature.equality] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- The four sign points are a literal complex matrix basis, rather than an
assumed spanning family or an abstract four-dimensional surrogate. -/
def pairedCoordinateEquiv : Binary ≃ₗ[ℂ] (Fin 4→ℂ) where
  toFun := pairedCoefficient
  invFun c := ∑j : Fin 4,c j • paired j
  left_inv := paired_reconstruction
  right_inv := pairedCoefficient_synthesis
  map_add' K J := by
    ext j
    fin_cases j <;> simp [pairedCoefficient,quaternionCoefficient] <;> ring
  map_smul' c K := by
    ext j
    fin_cases j <;> simp [pairedCoefficient,quaternionCoefficient,smul_eq_mul] <;> ring

def pairedBasis : Module.Basis (Fin 4) ℂ Binary :=
  Module.Basis.ofEquivFun pairedCoordinateEquiv

@[simp] theorem pairedBasis_apply (j : Fin 4) : pairedBasis j=paired j := by
  rw [pairedBasis,Module.Basis.coe_ofEquivFun]
  change (∑i : Fin 4,(Pi.single j (1:ℂ) : Fin 4→ℂ) i • paired i)=paired j
  exact Fintype.linearCombination_apply_single ℂ paired j 1 |>.trans (one_smul _ _)

def leftMultiply (L : Matrix Bool Bool ℂ) : Binary →ₗ[ℂ] Binary where
  toFun K := L*(Matrix.of K)
  map_add' K J := Matrix.mul_add L K J
  map_smul' c K := Matrix.mul_smul L c K

theorem leftMultiply_surjective (L : Matrix Bool Bool ℂ) (hL : L.det≠0) :
    Function.Surjective (leftMultiply L) := by
  intro K
  refine ⟨L⁻¹*(Matrix.of K),?_⟩
  change L*(L⁻¹*(Matrix.of K))=K
  rw [←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL),Matrix.one_mul]
  rfl

theorem leftMultiply_direction (L : Matrix Bool Bool ℂ)
    (hL : groupDirection .tetrahedral L) {K : Binary}
    (hK : groupDirection .tetrahedral K) :
    groupDirection .tetrahedral (leftMultiply L K) :=
  Holant.Certificates.RainbowOrbit.groupDirection_mul .tetrahedral hL hK

/-- The literal tetrahedral points span all four complex matrix coordinates. -/
theorem exists_nonzero_tetrahedral {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Φ : Binary →ₗ[ℂ] V) (hΦ : Φ≠0) :
    ∃K,tetrahedralBase K ∧ Φ K≠0 := by
  by_contra h
  push Not at h
  apply hΦ
  apply LinearMap.ext
  intro K
  rw [←quaternionLinear_reconstruction K]
  change Φ (∑j : Fin 4,quaternionCoefficient K j • quaternionBasis j)=0
  simp only [map_sum,map_smul]
  apply Finset.sum_eq_zero
  intro j _
  rw [h _ (Or.inl ⟨j,rfl⟩),smul_zero]

/-- A genuine element of the actual tetrahedral matrix group moves the fixed
anchor to a nonzero test value. Its left action remains surjective. -/
theorem exists_tetrahedral_transport {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Φ : Binary →ₗ[ℂ] V) (hΦ : Φ≠0) :
    ∃L : Matrix Bool Bool ℂ,groupDirection .tetrahedral L ∧
      Function.Surjective (leftMultiply L) ∧ Φ (leftMultiply L anchor)≠0 := by
  obtain ⟨K,hK,hΦK⟩ := exists_nonzero_tetrahedral Φ hΦ
  have hKd : groupDirection .tetrahedral K := ⟨1,one_ne_zero,K,hK,by simp⟩
  have hAd : groupDirection .tetrahedral anchor := ⟨1,one_ne_zero,anchor,anchor_base,by simp⟩
  let A : Matrix Bool Bool ℂ := Matrix.of anchor
  let L : Matrix Bool Bool ℂ := (Matrix.of K)*A⁻¹
  have hAi : groupDirection .tetrahedral (A⁻¹ : Matrix Bool Bool ℂ) :=
    groupDirection_inverse .tetrahedral hAd
  have hL : groupDirection .tetrahedral L :=
    Holant.Certificates.RainbowOrbit.groupDirection_mul .tetrahedral hKd hAi
  refine ⟨L,hL,leftMultiply_surjective L (groupDirection_det_ne_zero .tetrahedral hL),?_⟩
  have he : leftMultiply L anchor=K := by
    change ((Matrix.of K)*A⁻¹)*A=K
    have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr
      (groupDirection_det_ne_zero .tetrahedral hAd)
    rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul A hdet,Matrix.mul_one]
    rfl
  rwa [he]

end
end Holant.Platonic.ActiveSupport
