import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Exact matrix ranks for a matching cut after its physical coordinate split. -/
namespace Holant.Platonic.RainbowLocalization
noncomputable section
open scoped BigOperators

variable {L R C : Type*} [Fintype L] [Fintype R] [Fintype C] [DecidableEq C]

/-- Internal factors on the two sides surround the crossing matrix. -/
def separatedMatrix (u : L→ℂ) (v : R→ℂ) (B : Matrix C C ℂ) :
    Matrix (L×C) (R×C) ℂ := fun x y => u x.1*B x.2 y.2*v y.1

 theorem separatedMatrix_rank_le (u : L→ℂ) (v : R→ℂ) (B : Matrix C C ℂ) :
    (separatedMatrix u v B).rank≤Fintype.card C := by
  let A : Matrix (L×C) C ℂ := fun x y=>u x.1*B x.2 y
  let D : Matrix C (R×C) ℂ := fun x y=>if x=y.2 then v y.1 else 0
  have he : separatedMatrix u v B=A*D := by
    ext x y
    rw [Matrix.mul_apply]
    simp [separatedMatrix,A,D]
  rw [he]
  exact (Matrix.rank_mul_le_left A D).trans (Matrix.rank_le_card_width A)

 theorem separatedMatrix_rank (u : L→ℂ) (v : R→ℂ) (B : Matrix C C ℂ)
    (hu : ∃l,u l≠0) (hv : ∃r,v r≠0) (hB : IsUnit B) :
    (separatedMatrix u v B).rank=Fintype.card C := by
  obtain ⟨l,hl⟩ := hu
  obtain ⟨r,hr⟩ := hv
  apply le_antisymm (separatedMatrix_rank_le u v B)
  have he : (separatedMatrix u v B).submatrix (fun x=>(l,x)) (fun y=>(r,y))=
      (u l*v r) • B := by
    ext x y
    simp only [Matrix.submatrix_apply,separatedMatrix,Matrix.smul_apply,smul_eq_mul]
    ring
  have hle := Matrix.rank_submatrix_le (separatedMatrix u v B) (fun x=>(l,x)) (fun y=>(r,y))
  rw [he,Matrix.rank_smul_of_mem_nonZeroDivisors B
    (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hl hr)),Matrix.rank_of_isUnit B hB] at hle
  exact hle

/-- Literal tensor product of crossing binary matrices in ordered bit coordinates. -/
def binaryProductMatrix {ι : Type*} [Fintype ι] (A : ι→Matrix Bool Bool ℂ) :
    Matrix (ι→Bool) (ι→Bool) ℂ := fun x y=>∏i,A i (x i) (y i)

 theorem binaryProductMatrix_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ι→Matrix Bool Bool ℂ) :
    binaryProductMatrix (fun i=>A i*B i)=binaryProductMatrix A*binaryProductMatrix B := by
  ext x y
  simp only [binaryProductMatrix,Matrix.mul_apply,←Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i z=>A i (x i) z*B i z (y i))

 theorem binaryProductMatrix_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    binaryProductMatrix (fun _ : ι=>(1 : Matrix Bool Bool ℂ))=1 := by
  classical
  ext x y
  by_cases h : x=y
  · subst y
    simp [binaryProductMatrix]
  · have hex : ∃i,x i≠y i := Function.ne_iff.mp h
    obtain ⟨i,hi⟩ := hex
    simp only [Matrix.one_apply,if_neg h,binaryProductMatrix]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

 theorem binaryProductMatrix_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι→Matrix Bool Bool ℂ) (hA : ∀i,IsUnit (A i)) :
    IsUnit (binaryProductMatrix A) := by
  classical
  choose U hU using hA
  let V := binaryProductMatrix (fun i=>(U i)⁻¹.val)
  refine ⟨⟨binaryProductMatrix A,V,?_,?_⟩,rfl⟩
  · rw [←binaryProductMatrix_mul]
    have he : (fun i=>A i*((U i)⁻¹ : (Matrix Bool Bool ℂ)ˣ).val)=fun _=>1 := by
      funext i
      rw [←hU i]
      exact (U i).val_inv
    rw [he,binaryProductMatrix_one]
  · rw [←binaryProductMatrix_mul]
    have he : (fun i=>((U i)⁻¹ : (Matrix Bool Bool ℂ)ˣ).val*A i)=fun _=>1 := by
      funext i
      rw [←hU i]
      exact (U i).inv_val
    rw [he,binaryProductMatrix_one]

 theorem binaryProductMatrix_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι→Matrix Bool Bool ℂ) (hA : ∀i,IsUnit (A i)) :
    (binaryProductMatrix A).rank=2^Fintype.card ι := by
  rw [Matrix.rank_of_isUnit _ (binaryProductMatrix_isUnit A hA)]
  simp

 theorem separated_binary_product_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : L→ℂ) (v : R→ℂ) (A : ι→Matrix Bool Bool ℂ)
    (hu : ∃l,u l≠0) (hv : ∃r,v r≠0) (hA : ∀i,IsUnit (A i)) :
    (separatedMatrix u v (binaryProductMatrix A)).rank=2^Fintype.card ι := by
  rw [separatedMatrix_rank u v _ hu hv (binaryProductMatrix_isUnit A hA)]
  simp


 theorem binaryProductMatrix_det_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι→Matrix Bool Bool ℂ) (hA : ∀i,(A i).det≠0) :
    IsUnit (binaryProductMatrix A) :=
  binaryProductMatrix_isUnit A (fun i =>
    (Matrix.isUnit_iff_isUnit_det (A i)).mpr (isUnit_iff_ne_zero.mpr (hA i)))

 theorem separated_binary_product_det_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : L→ℂ) (v : R→ℂ) (A : ι→Matrix Bool Bool ℂ)
    (hu : ∃l,u l≠0) (hv : ∃r,v r≠0) (hA : ∀i,(A i).det≠0) :
    (separatedMatrix u v (binaryProductMatrix A)).rank=2^Fintype.card ι := by
  rw [separatedMatrix_rank u v _ hu hv (binaryProductMatrix_det_isUnit A hA)]
  simp

end
end Holant.Platonic.RainbowLocalization
