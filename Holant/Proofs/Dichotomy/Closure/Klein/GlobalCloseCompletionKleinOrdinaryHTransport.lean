import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinBAlgebra
import Holant.Certificates.EqualityQuaternary.KleinOrbitProgram

/-! Exact Hadamard transport of a native one-port attachment. Its ordinary
implementation uses the transformed actual binary and the retained native-X
row Z/2, hence carries the explicit factor 1/4 for every attachment. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryHTransport
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates.EqualityQuaternary
open Holant.Projective.CyclicDressing
namespace O
export Klein.Orbit (site site_coordinate)
end O
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z)
end T
abbrev H := GlobalCloseCompletionKleinBAlgebra.H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def zHalf : Kernel AlgebraicComplex := fun b c=>(1/2)*T.Z b c

theorem site_comp (A B : Kernel AlgebraicComplex) (i : Fin 4) (q : Signature AlgebraicComplex 4) :
    O.site A i (O.site B i q)=O.site (Kernel.mul A B) i q := by
  rw [O.site_coordinate,O.site_coordinate,O.site_coordinate,Signature.coordinateAction_comp]
  congr 1
  funext j
  by_cases h : j=i <;> simp [h]

theorem site_scale (A : Kernel AlgebraicComplex) (c : AlgebraicComplex)
    (i : Fin 4) (q : Signature AlgebraicComplex 4) :
    O.site (scale c A) i q=fun x=>c*O.site A i q x := by
  funext x
  simp only [O.site,scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem site_scalar (A : Kernel AlgebraicComplex) (c : AlgebraicComplex)
    (i : Fin 4) (q : Signature AlgebraicComplex 4) :
    O.site A i (fun x=>c*q x)=fun x=>c*O.site A i q x := by
  funext x
  simp only [O.site,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem onePort_transport (U : InvertibleKernel) (q : Signature AlgebraicComplex 4)
    (i : Fin 4) (B : Kernel AlgebraicComplex) :
    U.action (onePort q i B)=
      O.site (Kernel.mul (Kernel.mul U.matrix (Kernel.mul B Signature.disequality)) U.inverse) i (U.action q) := by
  calc
    U.action (onePort q i B)=U.action (onePort (U.symm.action (U.action q)) i B) := by
      rw [U.symm_action_action]
    _ = Signature.coordinateAction (fun j=>Kernel.mul
        (Kernel.mul U.matrix (if j=i then Kernel.mul B Signature.disequality else Signature.equality)) U.inverse)
          (U.action q) := by
      simp only [onePort,InvertibleKernel.action,InvertibleKernel.symm]
      rw [Signature.coordinateAction_comp,Signature.coordinateAction_comp]
    _ = _ := by
      rw [O.site_coordinate]
      congr 1
      funext j
      by_cases h : j=i <;> simp [h,U.matrix_inverse]

theorem local_matrix (B : Kernel AlgebraicComplex) :
    Kernel.mul (transport H B) zHalf=scale (1/4)
      (Kernel.mul (Kernel.mul H.inverse (Kernel.mul B Signature.disequality)) H.matrix) := by
  funext b c
  cases b <;> cases c <;>
    norm_num [transport,H,GlobalCloseCompletionKleinBAlgebra.H,GlobalCloseCompletionKleinHadamardAlgebra.H,
      basisA,UA,UAInv,zHalf,T.Z,Kernel.mul_apply,Kernel.transpose,Signature.disequality,scale] <;> ring

theorem dress_transport (q : Signature AlgebraicComplex 4) (i : Fin 4) (B : Kernel AlgebraicComplex) :
    O.site (transport H B) i (O.site zHalf i (H.symm.action q))=
      fun x=>(1/4)*H.symm.action (onePort q i B) x := by
  rw [site_comp,local_matrix,site_scale,onePort_transport]
  rfl

theorem action_reindex (U : InvertibleKernel) (e : Equiv.Perm (Fin 4)) (q : Signature AlgebraicComplex 4) :
    Tensor.reindex e (U.action q)=U.action (Tensor.reindex e q) :=
  Holant.Certificates.OctahedralSeparator.reindex_action (fun _=>U.matrix) e q

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryHTransport
end
