import Holant.EightVertex.ProductAnchor.DenseClassification
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! An actual algebraic normalization of every dense form, including the
native-edge identity. The square root is chosen within algebraic complex
numbers; it is not a free physical basis gadget. -/
namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem imaginary_nonzero : imaginaryUnit≠0 := by
  intro h
  have H := imaginaryUnit_sq
  rw [h] at H
  norm_num at H

 def normalizationMatrix (r u : Scalar) : Mat :=
  matrix (u/2) (u/(2*r)) (imaginaryUnit*u/2) (-imaginaryUnit*u/(2*r))

 def normalizationInverse (r u : Scalar) : Mat :=
  matrix (1/u) (-imaginaryUnit/u) (r/u) (imaginaryUnit*r/u)

 theorem normalization_matrix_inverse (r u : Scalar) (hr : r≠0) (hu : u≠0) :
    Kernel.mul (normalizationMatrix r u) (normalizationInverse r u)=Signature.equality := by
  funext x y
  cases x <;> cases y <;>
    simp only [normalizationMatrix,normalizationInverse,Kernel.mul_apply,matrix,
      Signature.equality,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false] <;>
    field_simp [hr,hu] <;> ring_nf <;> norm_num [imaginaryUnit_sq]

 theorem normalization_inverse_matrix (r u : Scalar) (hr : r≠0) (hu : u≠0) :
    Kernel.mul (normalizationInverse r u) (normalizationMatrix r u)=Signature.equality := by
  funext x y
  cases x <;> cases y <;>
    simp only [normalizationMatrix,normalizationInverse,Kernel.mul_apply,matrix,
      Signature.equality,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false] <;>
    field_simp [hr,hu] <;> ring_nf <;> norm_num [imaginaryUnit_sq]

 def denseNormalization (r u : Scalar) (hr : r≠0) (hu : u≠0) : InvertibleKernel :=
  ⟨normalizationMatrix r u,normalizationInverse r u,
    normalization_matrix_inverse r u hr hu,normalization_inverse_matrix r u hr hu⟩

 theorem normalization_edge (r u : Scalar) (hu : u≠0) (hsq : u^2=2*r) :
    Kernel.pullback Signature.disequality (normalizationInverse r u)=Signature.equality := by
  funext x y
  cases x <;> cases y <;>
    simp [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,normalizationInverse,matrix,
      Signature.disequality,Signature.equality] <;>
    field_simp [hu] <;> ring_nf <;> (try simp only [imaginaryUnit_sq]) <;>
    linear_combination -hsq

 theorem normalization_times_balanced (r u : Scalar) (hr : r≠0) :
    Kernel.mul (normalizationMatrix r u) (balanced 1 r 1)=diagonalKernel u (imaginaryUnit*u) := by
  funext x y
  cases x <;> cases y <;>
    simp [normalizationMatrix,balanced,matrix,Kernel.mul_apply,diagonalKernel] <;>
    field_simp [hr] <;> ring

 theorem exists_algebraic_normalizing_root (r : Scalar) (hr : r≠0) :
    ∃ u : Scalar,u≠0 ∧ u^2=2*r := by
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq ((2*r : Scalar) : ℂ) (by decide : 0<2)
  let v : Scalar := ⟨u,IsIntegral.of_pow (n := 2) (by decide) (by
    rw [hu]
    exact (2*r : Scalar).property)⟩
  have hv : v^2=2*r := Subtype.ext hu
  refine ⟨v,?_,hv⟩
  intro hz
  have hn : (2:Scalar)*r≠0 := mul_ne_zero (by norm_num) hr
  exact hn (by simpa [hz] using hv.symm)

end
end Holant.EightVertex.ProductAnchor
