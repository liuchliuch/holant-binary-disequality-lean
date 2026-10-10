import Holant.Certificates.MatchingProductBridge.QuaternionCoordinates

/-! The concrete Platonic families are stable under even coordinate permutations
and independent real sign changes. Only the closure actually needed for A.15's
axis products and inverse transpose is proved; no projective-group axiom is used. -/
namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem tetrahedral_twist_direction (g : PlatonicModel) (π : Equiv.Perm (Fin 4))
    (δ : Fin 4 → Bool) (v : Fin 4 → ℝ) (hv : tetrahedralBase (quaternion v)) :
    groupDirection g (quaternion (twistVector π δ v)) := by
  rcases hv with ⟨i,hi⟩ | ⟨ε,hε⟩
  · have he : v = axisVector i := quaternion_injective (hi.trans (quaternion_axis i).symm)
    rw [he,twistVector_axis,quaternion_real_smul,quaternion_axis]
    exact groupDirection_smul g (quaternion_axis_direction g _) (Complex.ofReal_ne_zero.mpr (signBit_ne_zero _))
  · have he : v = signVector ![false,ε 0,ε 1,ε 2] := by
      apply quaternion_injective
      rw [hε]
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [he,twistVector_sign]
    exact signVector_tetrahedral_direction g _

theorem octahedral_two_axes_ordered (i j : Fin 4) (hij : i < j) (a b : Bool) :
    groupDirection .octahedral (quaternion (signBit a • axisVector i+signBit b • axisVector j)) := by
  have hbase : modelBase .octahedral
      (quaternionBasis i+(signBit (b ^^ a) : ℂ) • quaternionBasis j) :=
    Or.inr ⟨i,j,hij,b ^^ a,rfl⟩
  refine ⟨(signBit a : ℂ),Complex.ofReal_ne_zero.mpr (signBit_ne_zero a),_,hbase,?_⟩
  rw [quaternion_add,quaternion_real_smul,quaternion_real_smul,quaternion_axis,quaternion_axis,smul_add,smul_smul]
  congr 1
  have he : (signBit a : ℂ)*(signBit (b ^^ a) : ℂ) = (signBit b : ℂ) := by exact_mod_cast signBit_twist a b
  rw [he]

theorem octahedral_two_axes_direction (i j : Fin 4) (hij : i ≠ j) (a b : Bool) :
    groupDirection .octahedral (quaternion (signBit a • axisVector i+signBit b • axisVector j)) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact octahedral_two_axes_ordered i j hlt a b
  · rw [add_comm]
    exact octahedral_two_axes_ordered j i hgt b a

theorem octahedral_twist_direction (π : Equiv.Perm (Fin 4)) (δ : Fin 4 → Bool)
    (v : Fin 4 → ℝ) (hv : octahedralBase (quaternion v)) :
    groupDirection .octahedral (quaternion (twistVector π δ v)) := by
  rcases hv with ht | ⟨i,j,hij,ε,hε⟩
  · exact tetrahedral_twist_direction _ π δ v ht
  · have he : v = axisVector i+signBit ε • axisVector j := by
      apply quaternion_injective
      rw [hε,quaternion_add,quaternion_real_smul,quaternion_axis,quaternion_axis]
    rw [he,twistVector_add,twistVector_smul,twistVector_axis,twistVector_axis,smul_smul,← signBit_xor]
    exact octahedral_two_axes_direction (π i) (π j) (fun hh => (ne_of_lt hij) (π.injective hh)) _ _

def transformedGoldenBits (π σ : Equiv.Perm (Fin 4)) (δ : Fin 4 → Bool) (ε : Fin 3 → Bool) : Fin 3 → Bool :=
  fun j => δ (σ (π j.succ)) ^^ ε j

theorem twistVector_golden (π σ : Equiv.Perm (Fin 4)) (δ : Fin 4 → Bool) (ε : Fin 3 → Bool) :
    twistVector σ δ (fun i => goldenVector ε (π.symm i)) =
      fun i => goldenVector (transformedGoldenBits π σ δ ε) ((π.trans σ).symm i) := by
  funext i
  obtain ⟨j,rfl⟩ := (π.trans σ).surjective i
  simp only [twistVector,Equiv.trans_apply,Equiv.symm_apply_apply]
  fin_cases j <;>
    simp [goldenVector,transformedGoldenBits,signBit_xor,mul_assoc]

theorem icosahedral_twist_direction (σ : Equiv.Perm (Fin 4)) (hσ : Equiv.Perm.sign σ = 1)
    (δ : Fin 4 → Bool) (v : Fin 4 → ℝ) (hv : icosahedralBase (quaternion v)) :
    groupDirection .icosahedral (quaternion (twistVector σ δ v)) := by
  rcases hv with ht | ⟨π,hπ,ε,hε⟩
  · exact tetrahedral_twist_direction _ σ δ v ht
  · have he : v = fun i => goldenVector ε (π.symm i) := quaternion_injective hε
    rw [he,twistVector_golden]
    refine ⟨1,one_ne_zero,quaternion (fun i => goldenVector (transformedGoldenBits π σ δ ε) ((π.trans σ).symm i)),?_,by simp⟩
    exact Or.inr ⟨π.trans σ,by rw [Equiv.Perm.sign_trans,hπ,hσ,mul_one],
      transformedGoldenBits π σ δ ε,rfl⟩

/-- All three actual source families satisfy the signed-even-permutation closure. -/
theorem modelBase_twist_direction (g : PlatonicModel) (σ : Equiv.Perm (Fin 4))
    (hσ : Equiv.Perm.sign σ = 1) (δ : Fin 4 → Bool) (v : Fin 4 → ℝ)
    (hv : modelBase g (quaternion v)) : groupDirection g (quaternion (twistVector σ δ v)) := by
  cases g
  · exact tetrahedral_twist_direction _ σ δ v hv
  · exact octahedral_twist_direction σ δ v hv
  · exact icosahedral_twist_direction σ hσ δ v hv

end
end Holant.Certificates.MatchingProductBridge
