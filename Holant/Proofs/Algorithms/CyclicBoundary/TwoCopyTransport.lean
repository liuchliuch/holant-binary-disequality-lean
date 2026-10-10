import Holant.Proofs.Algorithms.CyclicBoundary.TwoCopyKernels
import Holant.EightVertex.ProductAnchor.TemplateTransport
import Holant.OpenNetworkComposition.ProjectiveSubstitution


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.TwoCopyTransport
open Holant.Certificates.FourthRootOdd
open Holant.ReedMuller.CoefficientAtlas
open TwoCopyKernels
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [CommSemiring K]

theorem contraction_as_contracts (f g : Signature K 4) (p : Fin 6) (A B : Kernel K) :
    contraction f g p A B = Signature.contract B (Signature.contract A
      (Tensor.reindex (copyEquiv p).symm (Signature.tensor f g))) := by
  rw [←network_denote,network,Network.denote_contract,Network.denote_contract,
    reorderNetwork_denote,Network.denote_tensor,singleVertexNetwork_denote,
    singleVertexNetwork_denote]

/-- Both internal edges receive both endpoint matrices. Boundary coordinates
remain explicitly transformed; the output is not asserted to be the same tensor. -/
theorem contraction_action (M : Kernel K) (f g : Signature K 4)
    (p : Fin 6) (A B : Kernel K) :
    contraction (Signature.coordinateAction (fun _ => M) f)
      (Signature.coordinateAction (fun _ => M) g) p A B =
      Signature.coordinateAction (fun _ => M)
        (contraction f g p (Kernel.pullback A M) (Kernel.pullback B M)) := by
  rw [contraction_as_contracts,←EightVertex.ProductAnchor.coordinateAction_tensor,
    ←coordinateAction_reindex,coordinateAction_contract,coordinateAction_contract,
    ←contraction_as_contracts]

theorem contraction_scales (c d a b : K) (f g : Signature K 4)
    (p : Fin 6) (A B : Kernel K) :
    contraction (c • f) (d • g) p (a • A) (b • B) =
      (a*b*c*d) • contraction f g p A B := by
  funext x
  simp [contraction,Finset.mul_sum]
  ring

end
noncomputable section
variable {K : Type*} [Field K]

/-- The literal two-copy, two-native-edge macro admits arbitrary actual
source gadgets at either vertex, including free boundary stubs. -/
theorem native_realizesUpTo (F : SignatureFamily K) (f g : Signature K 4)
    (hf : Gadget.RealizesUpTo F .disequality f)
    (hg : Gadget.RealizesUpTo F .disequality g) (p : Fin 6) (htwo : (2:K) ≠ 0) :
    Gadget.RealizesUpTo F .disequality
      (contraction f g p Signature.disequality Signature.disequality) := by
  rw [←network_denote]
  apply OpenNetworkComposition.realizesUpTo_network
  · intro v
    change Gadget.RealizesUpTo F .disequality
      ((Network.tensorFinite (singleVertexNetwork f) (singleVertexNetwork g)).vertex
        ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v))
    cases (Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v
    · exact hf
    · exact hg
  · intro e
    refine Fin.cases rfl (fun e => ?_) e
    refine Fin.cases rfl (fun e => ?_) e
    exact Fin.elim0 e
  · exact htwo

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.TwoCopyTransport
