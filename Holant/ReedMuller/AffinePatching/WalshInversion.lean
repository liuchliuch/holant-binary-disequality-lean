import Holant.ReedMuller.AffinePatching.Walsh

/-! Exact Walsh orthogonality, inversion and the affine equivalence. No
transformability, normalization or numerical approximation is assumed. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem hadamard_orthogonal (a c : Bool) :
    ∑ b : Bool,hadamard a b*hadamard b c=if a=c then 2 else 0 := by
  cases a <;> cases c <;> norm_num [hadamard,Fintype.sum_bool]

theorem walshKernel_orthogonal (x z : Word n) :
    ∑ y : Word n,walshKernel x y*walshKernel y z=if x=z then (2:AlgebraicComplex)^n else 0 := by
  simp only [walshKernel,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i (b : Bool) => hadamard (x i) b*hadamard b (z i))]
  simp only [hadamard_orthogonal]
  by_cases h : x=z
  · subst z;simp
  · rw [if_neg h]
    have hi : ∃ i,x i≠z i := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨i,hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact if_neg hi

theorem walsh_inversion (f : Signature AlgebraicComplex n) :
    walsh (walsh f)=fun x => (2:AlgebraicComplex)^n*f x := by
  funext x
  unfold walsh
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ z,∑ y,walshKernel x y*(walshKernel y z*f z))=
        ∑ z,(∑ y,walshKernel x y*walshKernel y z)*f z := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.sum_mul,mul_assoc]
    _ = ∑ z,(if x=z then (2:AlgebraicComplex)^n else 0)*f z := by
      simp only [walshKernel_orthogonal]
    _ = (2:AlgebraicComplex)^n*f x := by simp [ite_mul]

 theorem walsh_affine_iff (f : Signature AlgebraicComplex n) : Affine (walsh f) ↔ Affine f := by
  constructor
  · intro h
    have hh := (walsh_affine _ h).scale ((2:AlgebraicComplex)^n)⁻¹
    rw [walsh_inversion] at hh
    have hp : (2:AlgebraicComplex)^n≠0 := pow_ne_zero _ (by norm_num)
    simpa only [←mul_assoc,inv_mul_cancel₀ hp,one_mul] using hh
  · exact walsh_affine f

end
end Holant.ReedMuller.AffinePatching
