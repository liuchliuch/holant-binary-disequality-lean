import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZFrame
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetAlgebra

/-! A single common algebraic diagonal basis normalizes a nonsingular
weighted equality while preserving native X exactly. Its coefficients are
source coordinate data, not asserted free matrix gadgets. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIWeightedEqualityFrame
open Holant Holant.Tractable
namespace D
export GlobalCloseCompletionSymmetricGHZFrame (diagonal diagonalBasis)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

def signature (a b : AlgebraicComplex) : Signature AlgebraicComplex 2:=
  fun x=>D.diagonal a b (x 0) (x 1)
def basis (r : AlgebraicComplex) (hr : r≠0) : InvertibleKernel:=D.diagonalBasis r r⁻¹ hr (inv_ne_zero hr)

theorem native (r : AlgebraicComplex) (hr : r≠0) :
    Kernel.pullback Signature.disequality (basis r hr).matrix=Signature.disequality := by
  funext p q
  cases p <;> cases q <;> simp [basis,D.diagonalBasis,D.diagonal,
    Kernel.pullback,Kernel.mul,Kernel.transpose,Signature.disequality,hr]

theorem normalized (a b r : AlgebraicComplex) (hr : r≠0) (hb : b≠0)
    (power : r^4=a/b) :
    (basis r hr).symm.action (signature a b)=
      fun x=>b*r^2*Signature.equality (x 0) (x 1) := by
  have he : a=b*r^4 := by
    apply (eq_div_iff hb).mp at power
    linear_combination -power
  subst a
  change Signature.coordinateAction (fun _ : Fin 2=>(basis r hr).inverse)
    (kernelSignature (D.diagonal (b*r^4) b))=_
  rw [coordinateAction_kernelSignature]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [basis,D.diagonalBasis,D.diagonal,kernelSignature,Kernel.mul,Kernel.transpose,
      Signature.equality,h0,h1,hr] <;> field_simp <;> ring

structure Frame (a b : AlgebraicComplex) where
  B : InvertibleKernel
  scalar : AlgebraicComplex
  nonzero : scalar≠0
  edge : Kernel.pullback Signature.disequality B.matrix=Signature.disequality
  row : B.symm.action (signature a b)=fun x=>scalar*Signature.equality (x 0) (x 1)

def produce (a b : AlgebraicComplex) (ha : a≠0) (hb : b≠0) : Frame a b := by
  classical
  apply Classical.choice
  letI : IsAlgClosed AlgebraicComplex:=IsAlgClosure.isAlgClosed ℚ
  obtain ⟨r,hr⟩:=IsAlgClosed.exists_pow_nat_eq (a/b) (by decide : 0<4)
  have nz : r≠0 := by
    intro zero
    rw [zero,zero_pow (by decide)] at hr
    exact div_ne_zero ha hb hr.symm
  exact ⟨⟨basis r nz,b*r^2,mul_ne_zero hb (pow_ne_zero _ nz),native r nz,normalized a b r nz hb hr⟩⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIWeightedEqualityFrame
end
