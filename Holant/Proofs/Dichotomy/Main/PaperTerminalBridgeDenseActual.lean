import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseOrders
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetAlgebra
import Holant.OpenNetworkComposition.Closure

/-! Exact native-X attachment of the two normalized anti-diagonals used by
the dense cancellation source. No literal identity vertex is required. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseActual
open Holant Holant.OpenNetworkComposition
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
namespace D
export PaperTerminalBridgeDenseCancellation (dress)
end D
namespace N
export NativeAntiTargetAlgebra (anti)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

theorem splice (f : Signature K n) (target : K) (i : Fin n) :
    spliceTensor f (Holant.Complexity.BinaryInterpolation.Chains.binarySignature (N.anti 1 target)) i=
      fun x=>(if x i then target else 1)*f x := by
  funext x
  cases hi : x i <;>
    simp [spliceTensor,Holant.Complexity.BinaryInterpolation.Chains.binarySignature,N.anti,Signature.disequality,hi,
      Function.update_eq_self,mul_comm]
  all_goals rw [←hi,Function.update_eq_self] <;> simp

theorem actual (F : SignatureFamily K) (f : Signature K 4)
    (actualF : Gadget.Realizes F .disequality f) (r t : K)
    (actualR : Gadget.Realizes F .disequality (Holant.Complexity.BinaryInterpolation.Chains.binarySignature (N.anti 1 r)))
    (actualT : Gadget.Realizes F .disequality (Holant.Complexity.BinaryInterpolation.Chains.binarySignature (N.anti 1 t))) :
    Gadget.Realizes F .disequality (D.dress f r t) := by
  have first := realizes_splice F f _ actualF actualR 0
  have second := realizes_splice F _ _ first actualT 1
  rw [splice,splice] at second
  convert second using 1
  funext x
  simp only [D.dress]
  ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseActual
end
