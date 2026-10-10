import Holant.ReedMuller.CharacterFlat.VertexProduct
import Holant.ReedMuller.CharacterFlat.Collection
import Holant.ReedMuller.FlatNetwork.OrdinaryNetwork

/-! Signed affine self-dual closure for the literal network assignment sum,
including all internal loops, parallel edges, nullary and disconnected parts. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.Certificates.MatchingContractionClosure Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ordinary_network_CFlat {n : ℕ} (N : Network ℂ n)
    (hv : ∀ v,CFlat (N.vertex v)) (W : Fin N.shape.edges → EdgeKind)
    (he : ∀ e,N.edge e=(W e).value) : CFlat N.denote := by
  rw [networkDenote_eq_collection]
  have he' : N.edge=fun e => parityKernel (edgeParity (W e)) := by
    funext e
    rw [edgeParity_value,he]
  rw [he']
  exact (characterTensorOrZero_fin_iff _).mp
    (characterTensorOrZero_contractCollection N.shape.ports.symm (fun e => edgeParity (W e))
      (vertexProduct N.vertex) (vertexProduct_CFlat N.vertex hv))

end
end Holant.ReedMuller.CharacterFlat
