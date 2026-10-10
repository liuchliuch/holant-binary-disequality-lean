import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHadamardAlgebra
import Holant.Marked.Fusion
import Holant.Tractable.Conformal.MatrixSupport

/-! Use precisely the two already-compiled source bases: H inverse and B
inverse. The latter resolves the paired-sign mismatch without adding a new
field, phase gate, or arbitrary corrected-edge source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinBAlgebra
open Holant Holant.Tractable Holant.Marked
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
abbrev H := GlobalCloseCompletionKleinHadamardAlgebra.H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem H_normal (a b c d : AlgebraicComplex) :
    H.symm.action (T.normal a b c d)=T.normal ((a+b+c+d)/8) ((a+b-c-d)/8)
      ((a-b+c-d)/8) ((a-b-c+d)/8) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [H,GlobalCloseCompletionKleinHadamardAlgebra.H,basisA,UAInv,InvertibleKernel.action,
      InvertibleKernel.symm,Signature.coordinateAction,
      Holant.Projective.CyclicQuaternary.Physical.sum_words4,Fin.prod_univ_succ,
      T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> ring

private theorem phase_normal (a b c d : AlgebraicComplex) :
    Signature.coordinateAction (fun _ : Fin 4=>R imaginaryUnit) (T.normal a b c d)=
      T.normal a (-b) (-c) (-d) := by
  change Signature.coordinateAction (fun _=>diagonalKernel 1 imaginaryUnit) _=_
  rw [coordinateAction_diagonal]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [diagonalCoefficient,Fin.prod_univ_succ,T.normal,
      Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem B_normal (a b c d : AlgebraicComplex) :
    basisB.symm.action (T.normal a b c d)=T.normal ((a-b-c-d)/8) ((-a+b-c-d)/8)
      ((-a-b+c-d)/8) ((-a-b-c+d)/8) := by
  have matrix : basisB.inverse=Kernel.mul (R imaginaryUnit) (Kernel.mul H.inverse (R imaginaryUnit)) := by
    funext b c
    cases b <;> cases c <;>
      simp [basisB,UBInv,H,GlobalCloseCompletionKleinHadamardAlgebra.H,basisA,UAInv,R,
        diagonalKernel,Kernel.mul_apply,Signature.equality,Signature.disequality] <;>
      ring_nf <;> norm_num [imaginaryUnit_sq]
  change Signature.coordinateAction (fun _=>basisB.inverse) _=_
  rw [matrix,←Signature.coordinateAction_comp,←Signature.coordinateAction_comp,phase_normal]
  change Signature.coordinateAction (fun _=>R imaginaryUnit) (H.symm.action _) = _
  rw [H_normal,phase_normal]
  congr 1 <;> ring

theorem paired_separates (a b c d : AlgebraicComplex) (ha : a≠0) (hc : c≠0)
    (hab : a^2=b^2) (hcd : c^2=d^2) :
    ∃U : InvertibleKernel, (U=H ∨ U=basisB) ∧
      ∃A B C D : AlgebraicComplex,
        U.symm.action (T.normal a b c d)=T.normal A B C D ∧
        (A^2-B^2)^2≠(C^2-D^2)^2 := by
  have live : a^2*c^2≠0 := mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hc)
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hab.symm) with bpos|bneg <;>
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hcd.symm) with dpos|dneg
  · subst b; subst d
    refine ⟨H,Or.inl rfl,_,_,_,_,H_normal a a c c,?_⟩
    intro eq
    apply live
    linear_combination 16*eq
  · subst b; subst d
    refine ⟨basisB,Or.inr rfl,_,_,_,_,B_normal a a c (-c),?_⟩
    intro eq
    apply live
    linear_combination -16*eq
  · subst b; subst d
    refine ⟨basisB,Or.inr rfl,_,_,_,_,B_normal a (-a) c c,?_⟩
    intro eq
    apply live
    linear_combination 16*eq
  · subst b; subst d
    refine ⟨H,Or.inl rfl,_,_,_,_,H_normal a (-a) c (-c),?_⟩
    intro eq
    apply live
    linear_combination -16*eq

theorem B_Z : basisB.symm.action (fun x : Fin 2→Bool=>T.Z (x 0) (x 1))=
    fun x=>(1/2 : AlgebraicComplex)*T.Z (x 0) (x 1) := by
  change basisB.symm.action (kernelSignature T.Z)=_
  rw [InvertibleKernel.action,coordinateAction_kernelSignature]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [basisB,UBInv,InvertibleKernel.symm,kernelSignature,Kernel.mul_apply,Kernel.transpose,
      Signature.equality,Signature.disequality,T.Z,h0,h1] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem H_X : H.symm.action (kernelSignature Signature.disequality)=
    fun x=>(1/2 : AlgebraicComplex)*T.Z (x 0) (x 1) := by
  rw [InvertibleKernel.action,coordinateAction_kernelSignature]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [H,GlobalCloseCompletionKleinHadamardAlgebra.H,basisA,UAInv,InvertibleKernel.symm,
      kernelSignature,Kernel.mul_apply,Kernel.transpose,Signature.disequality,T.Z,h0,h1]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinBAlgebra
end
