import Holant.Complexity.BinaryInterpolation.SpectralForms
import Mathlib.LinearAlgebra.Matrix.Rank

/-! A nonzero singular Boolean binary is an exact product of two nonzero
unaries over the same coefficient field. This is algebraic factorization;
no oracle access to either factor is inferred here. -/
namespace Holant.Complexity.BinaryInterpolation
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

theorem singular_cross_products (A : Binary (K := K)) (hd : Matrix.det A=0)
    (i k j l : Bool) : A i j*A k l=A i l*A k j := by
  rw [det_entries] at hd
  cases i <;> cases k <;> cases j <;> cases l <;>
    first | ring | linear_combination hd | linear_combination -hd

theorem singular_binary_factors (A : Binary (K := K)) (hA : A≠0)
    (hd : Matrix.det A=0) :
    ∃u v : Bool→K,u≠0 ∧ v≠0 ∧ A=Matrix.vecMulVec u v := by
  classical
  have hex : ∃i j,A i j≠0 := by
    by_contra h
    push Not at h
    exact hA (by ext i j;exact h i j)
  obtain ⟨i,j,hp⟩ := hex
  let u : Bool→K := fun x => A x j/A i j
  let v : Bool→K := fun y => A i y
  refine ⟨u,v,?_,?_,?_⟩
  · intro hu
    have h := congrFun hu i
    simp [u,div_self hp] at h
  · intro hv
    exact hp (congrFun hv j)
  · ext x y
    change A x y=(A x j/A i j)*A i y
    apply (mul_right_inj' hp).mp
    field_simp
    simpa [mul_comm] using singular_cross_products A hd x i y j

theorem rank_positive_of_entry {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J K) (i : I) (j : J) (h : A i j≠0) : 1≤A.rank := by
  let r : Fin 1→I := fun _ => i
  let c : Fin 1→J := fun _ => j
  have hn : (A.submatrix r c).det≠0 := by simpa [Matrix.det_fin_one,r,c] using h
  have hr := Matrix.rank_of_det_ne_zero hn
  have hm := A.rank_submatrix_le r c
  simpa only [hr,Fintype.card_fin] using hm

theorem singular_binary_rank (A : Binary (K := K)) (hA : A≠0) (hd : Matrix.det A=0) :
    A.rank=1 := by
  obtain ⟨u,v,hu,hv,he⟩ := singular_binary_factors A hA hd
  apply le_antisymm
  · rw [he]
    exact Matrix.rank_vecMulVec_le _ _
  · classical
    have hex : ∃i j,A i j≠0 := by
      by_contra h
      push Not at h
      exact hA (by ext i j;exact h i j)
    obtain ⟨i,j,hp⟩ := hex
    exact rank_positive_of_entry A i j hp

end
end Holant.Complexity.BinaryInterpolation
