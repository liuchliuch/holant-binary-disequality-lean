import Holant.Certificates.RainbowOrbit.GroupSources
import Holant.Certificates.RainbowOrbit.GroupTetrahedralRows0
import Holant.Certificates.RainbowOrbit.GroupOctahedralRows0
import Holant.Certificates.RainbowOrbit.GroupOctahedralRows1
import Holant.Certificates.RainbowOrbit.GroupIcosahedralRows0
import Holant.Certificates.RainbowOrbit.GroupIcosahedralRows1
import Holant.Certificates.RainbowOrbit.GroupIcosahedralRows2
import Holant.Certificates.RainbowOrbit.GroupIcosahedralRows3
import Holant.Certificates.RainbowOrbit.GroupIcosahedralRows4

/-! Complete finite projective dictionaries for the literal T/O/I source families.
All multiplication and separation statements are transported from kernel-checked
integer calculations to their actual complex matrices. -/
namespace Holant.Certificates.RainbowOrbit
noncomputable section
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def size : PlatonicModel → ℕ
  | .tetrahedral => 12
  | .octahedral => 24
  | .icosahedral => 60

def raw : (g : PlatonicModel) → Fin (size g) → GoldenVector
  | .tetrahedral => tetrahedralRaw
  | .octahedral => octahedralRaw
  | .icosahedral => icosahedralRaw

def representative (g : PlatonicModel) (i : Fin (size g)) : Matrix Bool Bool ℂ :=
  goldenMatrix (raw g i)

def productIndex : (g : PlatonicModel) → Fin (size g) → Fin (size g) → Fin (size g)
  | .tetrahedral => tetrahedralProductIndex
  | .octahedral => octahedralProductIndex
  | .icosahedral => icosahedralProductIndex

def productScale : (g : PlatonicModel) → Fin (size g) → Fin (size g) → ℤ
  | .tetrahedral => tetrahedralProductScale
  | .octahedral => octahedralProductScale
  | .icosahedral => icosahedralProductScale

def separation : (g : PlatonicModel) → Fin (size g) → Fin (size g) → Fin 4 × Fin 4
  | .tetrahedral => tetrahedralSeparation
  | .octahedral => octahedralSeparation
  | .icosahedral => icosahedralSeparation

theorem raw_certificate (g : PlatonicModel) (i j : Fin (size g)) :
    productScale g i j ≠ 0 ∧
    goldenQuaternionProduct (raw g i) (raw g j) =
      goldenScale (productScale g i j) (raw g (productIndex g i j)) ∧
    (i ≠ j → GoldenInt.norm (goldenCross (raw g i) (raw g j)
      (separation g i j).1 (separation g i j).2) ≠ 0) := by
  cases g
  · fin_cases i
    · exact tetrahedral_row_0 j
    · exact tetrahedral_row_1 j
    · exact tetrahedral_row_2 j
    · exact tetrahedral_row_3 j
    · exact tetrahedral_row_4 j
    · exact tetrahedral_row_5 j
    · exact tetrahedral_row_6 j
    · exact tetrahedral_row_7 j
    · exact tetrahedral_row_8 j
    · exact tetrahedral_row_9 j
    · exact tetrahedral_row_10 j
    · exact tetrahedral_row_11 j
  · fin_cases i
    · exact octahedral_row_0 j
    · exact octahedral_row_1 j
    · exact octahedral_row_2 j
    · exact octahedral_row_3 j
    · exact octahedral_row_4 j
    · exact octahedral_row_5 j
    · exact octahedral_row_6 j
    · exact octahedral_row_7 j
    · exact octahedral_row_8 j
    · exact octahedral_row_9 j
    · exact octahedral_row_10 j
    · exact octahedral_row_11 j
    · exact octahedral_row_12 j
    · exact octahedral_row_13 j
    · exact octahedral_row_14 j
    · exact octahedral_row_15 j
    · exact octahedral_row_16 j
    · exact octahedral_row_17 j
    · exact octahedral_row_18 j
    · exact octahedral_row_19 j
    · exact octahedral_row_20 j
    · exact octahedral_row_21 j
    · exact octahedral_row_22 j
    · exact octahedral_row_23 j
  · fin_cases i
    · exact icosahedral_row_0 j
    · exact icosahedral_row_1 j
    · exact icosahedral_row_2 j
    · exact icosahedral_row_3 j
    · exact icosahedral_row_4 j
    · exact icosahedral_row_5 j
    · exact icosahedral_row_6 j
    · exact icosahedral_row_7 j
    · exact icosahedral_row_8 j
    · exact icosahedral_row_9 j
    · exact icosahedral_row_10 j
    · exact icosahedral_row_11 j
    · exact icosahedral_row_12 j
    · exact icosahedral_row_13 j
    · exact icosahedral_row_14 j
    · exact icosahedral_row_15 j
    · exact icosahedral_row_16 j
    · exact icosahedral_row_17 j
    · exact icosahedral_row_18 j
    · exact icosahedral_row_19 j
    · exact icosahedral_row_20 j
    · exact icosahedral_row_21 j
    · exact icosahedral_row_22 j
    · exact icosahedral_row_23 j
    · exact icosahedral_row_24 j
    · exact icosahedral_row_25 j
    · exact icosahedral_row_26 j
    · exact icosahedral_row_27 j
    · exact icosahedral_row_28 j
    · exact icosahedral_row_29 j
    · exact icosahedral_row_30 j
    · exact icosahedral_row_31 j
    · exact icosahedral_row_32 j
    · exact icosahedral_row_33 j
    · exact icosahedral_row_34 j
    · exact icosahedral_row_35 j
    · exact icosahedral_row_36 j
    · exact icosahedral_row_37 j
    · exact icosahedral_row_38 j
    · exact icosahedral_row_39 j
    · exact icosahedral_row_40 j
    · exact icosahedral_row_41 j
    · exact icosahedral_row_42 j
    · exact icosahedral_row_43 j
    · exact icosahedral_row_44 j
    · exact icosahedral_row_45 j
    · exact icosahedral_row_46 j
    · exact icosahedral_row_47 j
    · exact icosahedral_row_48 j
    · exact icosahedral_row_49 j
    · exact icosahedral_row_50 j
    · exact icosahedral_row_51 j
    · exact icosahedral_row_52 j
    · exact icosahedral_row_53 j
    · exact icosahedral_row_54 j
    · exact icosahedral_row_55 j
    · exact icosahedral_row_56 j
    · exact icosahedral_row_57 j
    · exact icosahedral_row_58 j
    · exact icosahedral_row_59 j

theorem representative_base (g : PlatonicModel) (i : Fin (size g)) :
    modelBase g (representative g i) := by
  cases g
  · exact tetrahedralRaw_source i
  · exact octahedralRaw_source i
  · exact icosahedralRaw_source i

theorem representative_mem (g : PlatonicModel) (i : Fin (size g)) :
    groupDirection g (representative g i) :=
  ⟨1,one_ne_zero,_,representative_base g i,by simp⟩

theorem complete (g : PlatonicModel) (U : Matrix Bool Bool ℂ) :
    groupDirection g U ↔ ∃ k : Fin (size g), ∃ c : ℂ, c ≠ 0 ∧ U = c • representative g k := by
  constructor
  · rintro ⟨c,hc,V,hV,rfl⟩
    cases g
    · obtain ⟨k,rfl⟩ := tetrahedralBase_complete hV
      exact ⟨k,c,hc,rfl⟩
    · obtain ⟨k,rfl⟩ := octahedralBase_complete hV
      exact ⟨k,c,hc,rfl⟩
    · obtain ⟨k,d,hd,rfl⟩ := icosahedralBase_complete hV
      exact ⟨k,c*d,mul_ne_zero hc hd,by simp [representative,raw,smul_smul]⟩
  · rintro ⟨k,c,hc,rfl⟩
    exact groupDirection_smul g (representative_mem g k) hc

theorem representative_det_ne_zero (g : PlatonicModel) (i : Fin (size g)) :
    Matrix.det (representative g i) ≠ 0 := groupDirection_det_ne_zero g (representative_mem g i)

theorem representative_ne_zero (g : PlatonicModel) (i : Fin (size g)) :
    representative g i ≠ 0 := by
  intro h
  have hd := representative_det_ne_zero g i
  rw [h,Matrix.det_zero] at hd
  exact hd rfl

theorem projectively_injective (g : PlatonicModel) (i j : Fin (size g)) (c : ℂ)
    (h : representative g i = c • representative g j) : i = j := by
  by_contra hij
  have hn := (raw_certificate g i j).2.2 hij
  have hz := goldenCross_projective_zero (raw g i) (raw g j) c h
    (separation g i j).1 (separation g i j).2
  exact GoldenInt.eval_ne_zero _ hn hz

theorem mul_exact (g : PlatonicModel) (i j : Fin (size g)) :
    representative g i * representative g j =
      (productScale g i j : ℂ) • representative g (productIndex g i j) := by
  unfold representative
  rw [← goldenMatrix_product,(raw_certificate g i j).2.1,goldenMatrix_scale]

theorem mul_certificate (g : PlatonicModel) (i j : Fin (size g)) :
    ∃ k : Fin (size g), ∃ c : ℂ, c ≠ 0 ∧ representative g i * representative g j = c • representative g k :=
  ⟨productIndex g i j,productScale g i j,Int.cast_ne_zero.mpr (raw_certificate g i j).1,mul_exact g i j⟩

theorem groupDirection_mul (g : PlatonicModel) {U V : Matrix Bool Bool ℂ}
    (hU : groupDirection g U) (hV : groupDirection g V) : groupDirection g (U*V) := by
  obtain ⟨i,c,hc,rfl⟩ := (complete g U).mp hU
  obtain ⟨j,d,hd,rfl⟩ := (complete g V).mp hV
  obtain ⟨k,e,he,hk⟩ := mul_certificate g i j
  apply (complete g _).mpr
  refine ⟨k,c*d*e,mul_ne_zero (mul_ne_zero hc hd) he,?_⟩
  rw [Matrix.smul_mul,Matrix.mul_smul,hk]
  simp [smul_smul,mul_assoc]

def identityIndex (g : PlatonicModel) : Fin (size g) := ⟨0,by cases g <;> decide⟩

theorem representative_identity (g : PlatonicModel) : representative g (identityIndex g) = 1 := by
  cases g <;> ext a b <;> cases a <;> cases b <;>
    simp [representative,raw,identityIndex,tetrahedralRaw,octahedralRaw,icosahedralRaw,
      goldenMatrix,GoldenInt.eval,quaternion,Q0,Q1,Q2,Q3,Holant.Signature.equality,Matrix.one_apply]

end
end Holant.Certificates.RainbowOrbit
