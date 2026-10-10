import Holant.Certificates.OppositeIcosahedral.Algebra

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Direction

theorem smul {U : Mat} (hU : Direction U) {c : ℂ} (hc : c≠0) : Direction (c • U) := by
  obtain ⟨d,hd,V,hV,rfl⟩ := hU
  exact ⟨c*d,mul_ne_zero hc hd,V,hV,by rw [smul_smul]⟩

theorem of_tetrahedral {U : Mat} (hU : groupDirection .tetrahedral U) : Direction U := by
  obtain ⟨c,hc,V,hV,he⟩ := hU
  exact ⟨c,hc,V,Or.inl hV,he⟩

end Direction

theorem tetrahedral_standard {U : Mat} (hU : groupDirection .tetrahedral U) :
    groupDirection .icosahedral U := by
  obtain ⟨c,hc,V,hV,he⟩ := hU
  exact ⟨c,hc,V,Or.inl hV,he⟩

theorem conjugate_tetrahedral_base {U : Binary} (hU : tetrahedralBase U) :
    groupDirection .tetrahedral (conjugate (Matrix.of U)) := by
  obtain ⟨v,hv,he⟩ := tetrahedralBase_quaternion hU
  rw [he] at hU ⊢
  rw [conjugate_quaternion]
  exact tetrahedral_twist_direction .tetrahedral chiralitySwap forwardSigns v hU

theorem pull_tetrahedral_base {U : Binary} (hU : tetrahedralBase U) :
    groupDirection .tetrahedral (pull (Matrix.of U)) := by
  obtain ⟨v,hv,he⟩ := tetrahedralBase_quaternion hU
  rw [he] at hU ⊢
  rw [pull_quaternion]
  exact tetrahedral_twist_direction .tetrahedral chiralitySwap inverseSigns v hU

/-- Every literal even-permutation source representative is sent to the
literal odd-permutation display, retaining its original complex scale. -/
theorem conjugate_standard {U : Mat} (hU : groupDirection .icosahedral U) : Direction (conjugate U) := by
  obtain ⟨c,hc,V,hV,he⟩ := hU
  change U=c • Matrix.of V at he
  rw [he,conjugate_smul]
  apply Direction.smul _ hc
  rcases hV with ht | ⟨π,hπ,ε,rfl⟩
  · exact Direction.of_tetrahedral (conjugate_tetrahedral_base ht)
  · rw [conjugate_quaternion,twistVector_golden]
    refine ⟨1,one_ne_zero,_,Or.inr ⟨π.trans chiralitySwap,?_,
      transformedGoldenBits π chiralitySwap forwardSigns ε,rfl⟩,by simp⟩
    rw [Equiv.Perm.sign_trans,hπ,chiralitySwap_sign,mul_one]

/-- The inverse coefficient map proves exhaustive coverage of the displayed
opposite set; no marked-subgroup classification is assumed. -/
theorem pull_opposite {U : Mat} (hU : Direction U) : groupDirection .icosahedral (pull U) := by
  obtain ⟨c,hc,V,hV,rfl⟩ := hU
  rw [pull_smul]
  apply groupDirection_smul .icosahedral _ hc
  rcases hV with ht | ⟨π,hπ,ε,rfl⟩
  · exact tetrahedral_standard (pull_tetrahedral_base ht)
  · rw [pull_quaternion,twistVector_golden]
    refine ⟨1,one_ne_zero,_,Or.inr ⟨π.trans chiralitySwap,?_,
      transformedGoldenBits π chiralitySwap inverseSigns ε,rfl⟩,by funext a b; simp⟩
    rw [Equiv.Perm.sign_trans,hπ,chiralitySwap_sign]
    norm_num

theorem direction_iff_conjugate (U : Mat) :
    Direction U ↔ ∃V : Mat,groupDirection .icosahedral V ∧ U=conjugate V := by
  constructor
  · intro h
    exact ⟨pull U,pull_opposite h,(conjugate_pull U).symm⟩
  · rintro ⟨V,hV,rfl⟩
    exact conjugate_standard hV

theorem direction_conjugate_iff (U : Mat) : Direction (conjugate U) ↔ groupDirection .icosahedral U := by
  constructor
  · intro h
    have hh := pull_opposite h
    rwa [pull_conjugate] at hh
  · exact conjugate_standard

theorem conjugate_mul (U V : Mat) : conjugate (U*V)=conjugate U*conjugate V := by
  simp only [conjugate,mul_assoc]
  rw [←mul_assoc Dinv,Dinv_D,one_mul]

theorem Direction.mul {U V : Mat} (hU : Direction U) (hV : Direction V) : Direction (U*V) := by
  obtain ⟨U',hU',rfl⟩ := (direction_iff_conjugate U).mp hU
  obtain ⟨V',hV',rfl⟩ := (direction_iff_conjugate V).mp hV
  rw [←conjugate_mul]
  exact conjugate_standard (RainbowOrbit.groupDirection_mul .icosahedral hU' hV')

theorem Direction.det_ne_zero {U : Mat} (hU : Direction U) : U.det≠0 := by
  obtain ⟨V,hV,rfl⟩ := (direction_iff_conjugate U).mp hU
  have hv : V.det≠0 := groupDirection_det_ne_zero .icosahedral hV
  simp [conjugate,Matrix.det_mul,←D_inverse,Matrix.det_nonsing_inv,D_det_ne_zero,hv]

end
end Holant.Certificates.OppositeIcosahedral
