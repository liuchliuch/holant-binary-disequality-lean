import Holant.Certificates.RainbowOrbit.GoldenData

namespace Holant.Certificates.RainbowOrbit
noncomputable section
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

@[simp] theorem goldenSign_real (b : Bool) : (goldenSign b : ℝ) = signBit b := by
  cases b <;> norm_num [goldenSign,signBit]

theorem goldenMatrix_axis (i : Fin 4) :
    goldenMatrix (fun j => if j=i then GoldenInt.ofInt 1 else GoldenInt.zero) = quaternionBasis i := by
  rw [← quaternion_axis]
  unfold goldenMatrix
  congr 1
  funext j
  by_cases h : j=i <;> simp [h,axisVector]

theorem goldenMatrix_signed (ε : Fin 3 → Bool) :
    goldenMatrix ![GoldenInt.ofInt 1,GoldenInt.ofInt (goldenSign (ε 0)),
      GoldenInt.ofInt (goldenSign (ε 1)),GoldenInt.ofInt (goldenSign (ε 2))] =
      quaternion ![1,signBit (ε 0),signBit (ε 1),signBit (ε 2)] := by
  unfold goldenMatrix
  congr 1
  funext i
  fin_cases i <;> simp

theorem tetrahedralRaw_source (k : Fin 12) : tetrahedralBase (goldenMatrix (tetrahedralRaw k)) := by
  rcases tetrahedralRaw_description k with ⟨i,h⟩ | ⟨ε,h⟩
  · rw [h,goldenMatrix_axis]
    exact Or.inl ⟨i,rfl⟩
  · rw [h,goldenMatrix_signed]
    exact Or.inr ⟨ε,rfl⟩

theorem tetrahedralBase_complete {U : Binary} (h : tetrahedralBase U) :
    ∃ k : Fin 12, U = goldenMatrix (tetrahedralRaw k) := by
  rcases h with ⟨i,rfl⟩ | ⟨ε,rfl⟩
  · obtain ⟨k,hk⟩ := tetrahedralRaw_covers_axes i
    exact ⟨k,by rw [hk,goldenMatrix_axis]⟩
  · obtain ⟨k,hk⟩ := tetrahedralRaw_covers_signs ε
    exact ⟨k,by rw [hk,goldenMatrix_signed]⟩

theorem sourceGolden_eval (ε : Fin 3 → Bool) (i : Fin 4) :
    GoldenInt.eval (sourceGolden ε i) = goldenVector ε i := by
  fin_cases i <;> simp [sourceGolden,GoldenInt.eval,goldenVector,GoldenInt.reciprocal_eq] <;> ring

theorem permutedGolden_matrix (p : Fin 12) (ε : Fin 3 → Bool) :
    goldenMatrix (permutedGolden p ε) = quaternion (fun i => goldenVector ε ((evenPermutation p).symm i)) := by
  unfold goldenMatrix permutedGolden
  simp_rw [sourceGolden_eval]

theorem icosahedralRaw_source (k : Fin 60) : icosahedralBase (goldenMatrix (icosahedralRaw k)) := by
  rcases icosahedralRaw_description k with ⟨i,h⟩ | ⟨p,ε,h⟩
  · rw [h]
    exact Or.inl (tetrahedralRaw_source i)
  · rw [h,permutedGolden_matrix]
    exact Or.inr ⟨evenPermutation p,evenPermutation_sign p,ε,rfl⟩

theorem icosahedralBase_complete {U : Binary} (h : icosahedralBase U) :
    ∃ k : Fin 60, ∃ c : ℂ, c ≠ 0 ∧ U = c • goldenMatrix (icosahedralRaw k) := by
  rcases h with h | ⟨π,hπ,ε,rfl⟩
  · obtain ⟨i,rfl⟩ := tetrahedralBase_complete h
    obtain ⟨k,hk⟩ := icosahedralRaw_covers_tetrahedral i
    exact ⟨k,1,one_ne_zero,by rw [hk,one_smul]⟩
  · obtain ⟨p,rfl⟩ := evenPermutation_complete π hπ
    obtain ⟨k,c,hc,hk⟩ := icosahedralRaw_covers_golden p ε
    refine ⟨k,c,?_,?_⟩
    · rcases hc with rfl | rfl <;> norm_num
    · rw [← permutedGolden_matrix,hk,goldenMatrix_scale]

open Holant.Certificates.OctahedralSeparator in
 theorem octahedralRaw_standard (k : Fin 24) :
    goldenMatrix (octahedralRaw k) = complexMatrix (standard k) := by
  fin_cases k <;> ext a b <;> cases a <;> cases b <;>
    simp [octahedralRaw,goldenMatrix,GoldenInt.eval,quaternion,standard,signed,signs,
      complexMatrix,q,mat,ms,Q0,Q1,Q2,Q3,Holant.Signature.equality,
      embed_add,embed_sub,embed_mul,embed_neg,embed_imag,embed_zero,embed_one] <;> ring

theorem octahedralRaw_source (k : Fin 24) : octahedralBase (goldenMatrix (octahedralRaw k)) := by
  rw [octahedralRaw_standard]
  exact OctahedralSeparator.standard_source_base k

theorem octahedralBase_complete {U : Binary} (h : octahedralBase U) :
    ∃ k : Fin 24, U = goldenMatrix (octahedralRaw k) := by
  obtain ⟨k,hk⟩ := OctahedralSeparator.source_base_standard h
  exact ⟨k,by rw [octahedralRaw_standard]; exact hk⟩

end
end Holant.Certificates.RainbowOrbit
