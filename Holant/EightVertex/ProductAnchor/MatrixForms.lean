import Holant.Tractable.SymmetricBinaryPullback.Product

/-! The actual common product witness has a monomial or balanced Hadamard
matrix. The transformed native edge is mandatory in this derivation. -/
namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
noncomputable section
abbrev Scalar := AlgebraicComplex
abbrev Mat := Kernel Scalar

def matrix (a b c d : Scalar) : Mat := fun x y => if x then if y then d else c else if y then b else a

def Monomial (T : Mat) : Prop :=
  (T false true=0 ∧ T true false=0) ∨ (T false false=0 ∧ T true true=0)

def balanced (a c r : Scalar) : Mat := matrix a (a*r) c (-c*r)

theorem pullback_entries (T : Mat) :
    Kernel.pullback Signature.disequality T=
      matrix (2*T false false*T true false)
        (T false false*T true true+T false true*T true false)
        (T false false*T true true+T false true*T true false)
        (2*T false true*T true true) := by
  funext x y
  cases x <;> cases y <;>
    simp [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,Signature.disequality,matrix] <;> ring

theorem determinant_pullback (T : Mat) :
    determinant (Kernel.pullback Signature.disequality T)= -(determinant T)^2 := by
  rw [pullback_entries]
  simp [determinant,matrix]
  ring

theorem pullback_det_ne_zero (T : InvertibleKernel) :
    determinant (Kernel.pullback Signature.disequality T.matrix)≠0 := by
  rw [determinant_pullback]
  exact neg_ne_zero.mpr (pow_ne_zero _ (determinant_ne_zero T))

theorem balanced_nonzero (a b c d : Scalar) (hdet : a*d-b*c≠0) (hbal : a*d+b*c=0) :
    a≠0 ∧ b≠0 ∧ c≠0 ∧ d≠0 := by
  have had : a*d≠0 := by
    intro h
    have hbc : b*c=0 := by simpa [h] using hbal
    exact hdet (by simp [h,hbc])
  have hbc : b*c≠0 := by
    intro h
    have had' : a*d=0 := by simpa [h] using hbal
    exact had had'
  exact ⟨(mul_ne_zero_iff.mp had).1,(mul_ne_zero_iff.mp hbc).1,
    (mul_ne_zero_iff.mp hbc).2,(mul_ne_zero_iff.mp had).2⟩

theorem balanced_of_offdiagonal_zero (T : InvertibleKernel)
    (h : T.matrix false false*T.matrix true true+T.matrix false true*T.matrix true false=0) :
    ∃ a c r : Scalar,a≠0 ∧ c≠0 ∧ r≠0 ∧ T.matrix=balanced a c r := by
  let a := T.matrix false false
  let b := T.matrix false true
  let c := T.matrix true false
  let d := T.matrix true true
  have hn := balanced_nonzero a b c d (determinant_ne_zero T) h
  refine ⟨a,c,b/a,hn.1,hn.2.2.1,div_ne_zero hn.2.1 hn.1,?_⟩
  funext x y
  cases x <;> cases y
  · rfl
  · change b=a*(b/a)
    field_simp [hn.1]
  · rfl
  · change d= -c*(b/a)
    rw [←mul_div_assoc]
    apply (eq_div_iff hn.1).mpr
    have hh : a*d+b*c=0 := h
    linear_combination hh

theorem monomial_of_diagonal_zero (T : InvertibleKernel)
    (h0 : 2*T.matrix false false*T.matrix true false=0)
    (h1 : 2*T.matrix false true*T.matrix true true=0) : Monomial T.matrix := by
  have hac : T.matrix false false*T.matrix true false=0 := by linear_combination h0/2
  have hbd : T.matrix false true*T.matrix true true=0 := by linear_combination h1/2
  rcases mul_eq_zero.mp hac with ha | hc <;> rcases mul_eq_zero.mp hbd with hb | hd
  · exact False.elim (determinant_ne_zero T (by simp [determinant,ha,hb]))
  · exact Or.inr ⟨ha,hd⟩
  · exact Or.inl ⟨hb,hc⟩
  · exact False.elim (determinant_ne_zero T (by simp [determinant,hc,hd]))

/-- Exact first step of Lemma4.2, from the actual source product predicate
on TᵀXT rather than from an assumed matrix normal form. -/
theorem common_product_matrix_forms (T : InvertibleKernel)
    (hedge : Product (kernelSignature (Kernel.pullback Signature.disequality T.matrix))) :
    Monomial T.matrix ∨
      ∃ a c r : Scalar,a≠0 ∧ c≠0 ∧ r≠0 ∧ T.matrix=balanced a c r := by
  rcases product_monomial hedge (pullback_det_ne_zero T) with h | h
  · right
    apply balanced_of_offdiagonal_zero T
    have H := h.1
    rw [pullback_entries] at H
    exact H
  · left
    apply monomial_of_diagonal_zero T
    · have H := h.1
      rw [pullback_entries] at H
      exact H
    · have H := h.2
      rw [pullback_entries] at H
      exact H

end
end Holant.EightVertex.ProductAnchor
