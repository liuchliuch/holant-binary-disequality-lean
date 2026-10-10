import Holant.EightVertex.AffineNormalization.BinaryShape
import Holant.Certificates.AffineEndpoint.CoreSource

/-! A genuine common affine witness is a nonzero diagonal times one of the
eighteen exact A.4 cores; no core-list membership is supplied as a premise. -/
namespace Holant.EightVertex.AffineNormalization
open Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open Holant.EightVertex.ProductAnchor Holant.Certificates.AffineEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false

def CoreFactorization (T : InvertibleKernel) : Prop :=
  ∃ a c : AlgebraicComplex,a≠0 ∧ c≠0 ∧
    ∃ K : Matrix Bool Bool AlgebraicComplex,SourceCore K ∧
      T.matrix=Kernel.mul (diagonal a c) K

theorem monomial_core (T : InvertibleKernel) (h : Monomial T.matrix) : CoreFactorization T := by
  rcases h with ⟨h01,h10⟩|⟨h00,h11⟩
  · have hn : T.matrix false false*T.matrix true true≠0 := by
      simpa [determinant,h01,h10] using determinant_ne_zero T
    refine ⟨_,_,(mul_ne_zero_iff.mp hn).1,(mul_ne_zero_iff.mp hn).2,1,Or.inl rfl,?_⟩
    funext a b
    cases a <;> cases b <;> simp [Kernel.mul_apply,diagonal,Matrix.one_apply,h01,h10]
  · have hn : T.matrix false true*T.matrix true false≠0 := by
      simpa [determinant,h00,h11] using determinant_ne_zero T
    refine ⟨_,_,(mul_ne_zero_iff.mp hn).1,(mul_ne_zero_iff.mp hn).2,
      (fun a b => Signature.disequality a b),Or.inr (Or.inl rfl),?_⟩
    funext a b
    cases a <;> cases b <;> simp [Kernel.mul_apply,diagonal,Signature.disequality,h00,h11]

theorem balanced_core (T : InvertibleKernel)
    (hE : Affine (kernelSignature (Kernel.pullback Signature.disequality T.matrix)))
    (hoff : T.matrix false false*T.matrix true true+T.matrix false true*T.matrix true false=0) :
    CoreFactorization T := by
  obtain ⟨a,c,r,ha,hc,hr,hT⟩ := balanced_of_offdiagonal_zero T hoff
  have h0 : (Kernel.pullback Signature.disequality T.matrix) false false≠0 := by
    rw [hT,pullback_entries]
    simpa [balanced,matrix] using mul_ne_zero (mul_ne_zero (by norm_num : (2:AlgebraicComplex)≠0) ha) hc
  have h1 : (Kernel.pullback Signature.disequality T.matrix) true true≠0 := by
    rw [hT,pullback_entries]
    simp [balanced,matrix,ha,hc,hr]
  have hp := hE.fourth_power_eq (![false,false]) (![true,true]) h0 h1
  have hp' : (2*a*c)^4=(-(2*a*c)*r^2)^4 := by
    rw [hT,pullback_entries] at hp
    simp [kernelSignature,balanced,matrix] at hp
    convert hp using 1 <;> ring
  have hn : (2*a*c)^4≠0 := pow_ne_zero _
    (mul_ne_zero (mul_ne_zero (by norm_num : (2:AlgebraicComplex)≠0) ha) hc)
  have hr8 : r^8=1 := by
    apply mul_left_cancel₀ hn
    calc
      (2*a*c)^4*r^8 = (-(2*a*c)*r^2)^4 := by ring
      _ = (2*a*c)^4 := hp'.symm
      _ = (2*a*c)^4*1 := by ring
  refine ⟨a,c,ha,hc,algMat 1 r 1 (-r),Or.inr (Or.inr (Or.inl ⟨r,hr8,rfl⟩)),?_⟩
  rw [hT]
  funext x y
  cases x <;> cases y <;> simp [balanced,matrix,Kernel.mul_apply,diagonal,algMat] <;> ring

theorem sum_product_roots (r t u : AlgebraicComplex)
    (hs : r+t=2*u) (hp : r*t= -u^2) :
    ∃ b : Bool,r=u*(1+(if b then -sqrtTwo else sqrtTwo)) ∧
      t=u*(1-(if b then -sqrtTwo else sqrtTwo)) := by
  have hsq : (r-u)^2=(u*sqrtTwo)^2 := by
    rw [mul_pow,sqrtTwo_sq]
    linear_combination r*hs-hp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h|h
  · refine ⟨false,?_,?_⟩ <;> dsimp
    · linear_combination h
    · linear_combination hs-h
  · refine ⟨true,?_,?_⟩ <;> dsimp
    · linear_combination h
    · linear_combination hs-h

theorem full_core (T : InvertibleKernel)
    (hE : Affine (kernelSignature (Kernel.pullback Signature.disequality T.matrix)))
    (hf : ∀ a b,(Kernel.pullback Signature.disequality T.matrix) a b≠0) :
    CoreFactorization T := by
  have hsym : Kernel.transpose (Kernel.pullback Signature.disequality T.matrix)=
      Kernel.pullback Signature.disequality T.matrix := by
    rw [pullback_entries]
    funext a b
    cases a <;> cases b <;> rfl
  obtain ⟨u,hu,h01,h11⟩ := full_symmetric_normal_form
    (Kernel.pullback Signature.disequality T.matrix) hE hsym hf (pullback_det_ne_zero T)
  let a := T.matrix false false
  let b := T.matrix false true
  let c := T.matrix true false
  let d := T.matrix true true
  have hac : 2*a*c≠0 := by simpa [a,c,pullback_entries,matrix] using hf false false
  have ha : a≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hac).1).2
  have hc : c≠0 := (mul_ne_zero_iff.mp hac).2
  have h01' : a*d+b*c=u*(2*a*c) := by simpa [a,b,c,d,pullback_entries,matrix] using h01
  have h11' : 2*b*d= -(u^2)*(2*a*c) := by simpa [a,b,c,d,pullback_entries,matrix] using h11
  have hs : b/a+d/c=2*u := by
    field_simp [ha,hc]
    linear_combination h01'
  have hp : (b/a)*(d/c)= -u^2 := by
    field_simp [ha,hc]
    linear_combination h11'/2
  obtain ⟨sign,hr,ht⟩ := sum_product_roots (b/a) (d/c) u hs hp
  refine ⟨a,c,ha,hc,
    algMat 1 (u*(1+(if sign then -sqrtTwo else sqrtTwo)))
      1 (u*(1-(if sign then -sqrtTwo else sqrtTwo))),
    Or.inr (Or.inr (Or.inr ⟨u,hu,sign,rfl⟩)),?_⟩
  rw [←hr,←ht]
  funext x y
  cases x <;> cases y <;> simp [Kernel.mul_apply,diagonal,algMat,a,b,c,d]
  · exact (mul_div_cancel₀ b ha).symm
  · exact (mul_div_cancel₀ d hc).symm

theorem affine_matrix_core (T : InvertibleKernel)
    (hE : Affine (kernelSignature (Kernel.pullback Signature.disequality T.matrix))) :
    CoreFactorization T := by
  have hsym : Kernel.transpose (Kernel.pullback Signature.disequality T.matrix)=
      Kernel.pullback Signature.disequality T.matrix := by
    rw [pullback_entries]
    funext a b
    cases a <;> cases b <;> rfl
  rcases symmetric_support_cases (Kernel.pullback Signature.disequality T.matrix) hE hsym with
    hoff|hdiag|hfull
  · apply balanced_core T hE
    simpa [pullback_entries,matrix] using hoff.1
  · apply monomial_core T
    apply monomial_of_diagonal_zero T
    · simpa [pullback_entries,matrix] using hdiag.1
    · simpa [pullback_entries,matrix] using hdiag.2
  · exact full_core T hE hfull

end
end Holant.EightVertex.AffineNormalization
