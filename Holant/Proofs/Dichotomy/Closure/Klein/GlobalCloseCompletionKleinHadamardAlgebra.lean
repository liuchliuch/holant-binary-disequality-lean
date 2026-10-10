import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinTwistedAlgebra
import Holant.Marked.Basic
import Holant.Projective.CyclicQuaternary.Physical

/-! The paired-square dense residual is sparse after one of two exact common
Clifford bases. The matrix is explicit; no gadget or source access is inferred
from this purely algebraic change of coordinates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHadamardAlgebra
open Holant Holant.Tractable Holant.Marked
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def H : InvertibleKernel := basisA 1 one_ne_zero
def HS : InvertibleKernel := basisA imaginaryUnit imaginaryUnit_ne_zero

theorem hadamard_normal (a b c d : AlgebraicComplex) :
    H.action (T.normal a b c d)=T.normal (2*(a+b+c+d)) (2*(a+b-c-d))
      (2*(a-b+c-d)) (2*(a-b-c+d)) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [H,basisA,UA,InvertibleKernel.action,Signature.coordinateAction,
      Holant.Projective.CyclicQuaternary.Physical.sum_words4,Fin.prod_univ_succ,
      T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> ring

theorem phased_normal (a b c d : AlgebraicComplex) :
    HS.action (T.normal a b c d)=T.normal (2*(a-b-c-d)) (2*(a-b+c+d))
      (2*(a+b-c+d)) (2*(a+b+c-d)) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [HS,basisA,UA,InvertibleKernel.action,Signature.coordinateAction,
      Holant.Projective.CyclicQuaternary.Physical.sum_words4,Fin.prod_univ_succ,
      T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq] <;> ring

/-- Dense paired squares give a nonzero sparse squared determinant in one of
the two bases. Every transformed coefficient and the selected basis are kept. -/
theorem paired_separates (a b c d : AlgebraicComplex) (ha : a≠0) (hc : c≠0)
    (hab : a^2=b^2) (hcd : c^2=d^2) :
    ∃U : InvertibleKernel, (U=H ∨ U=HS) ∧
      ∃A B C D : AlgebraicComplex,
        U.action (T.normal a b c d)=T.normal A B C D ∧
        (A^2-B^2)^2≠(C^2-D^2)^2 := by
  have live : (4096 : AlgebraicComplex)*a^2*c^2≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) (pow_ne_zero _ hc)
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hab.symm) with bpos|bneg <;>
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hcd.symm) with dpos|dneg
  · subst b; subst d
    refine ⟨H,Or.inl rfl,_,_,_,_,hadamard_normal a a c c,?_⟩
    intro eq
    apply live
    linear_combination eq
  · subst b; subst d
    refine ⟨HS,Or.inr rfl,_,_,_,_,phased_normal a a c (-c),?_⟩
    intro eq
    apply live
    linear_combination -eq
  · subst b; subst d
    refine ⟨HS,Or.inr rfl,_,_,_,_,phased_normal a (-a) c c,?_⟩
    intro eq
    apply live
    linear_combination eq
  · subst b; subst d
    refine ⟨H,Or.inl rfl,_,_,_,_,hadamard_normal a (-a) c (-c),?_⟩
    intro eq
    apply live
    linear_combination -eq


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHadamardAlgebra
end
