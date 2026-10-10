import Holant.Complexity.GraphPreprocessing.CanonicalStability.Parent

/-! Original-ID embeddings of the actual deterministically enumerated network.
The maps use the same executable increasing enumerations as orderedNetwork. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable
variable {K V E : Type*} [Fintype V] [Fintype E] [LinearOrder V] [LinearOrder E]

/-- Increasing residual vertex indices interpreted as their actual original IDs. -/
def orderedVertexMap (N : Holant.FiniteNetwork K V E 0) :
    N.orderedNetwork.incidenceGraph.Vertex ≃o V := Fintype.orderIsoFinOfCardEq V rfl

/-- Increasing residual edge indices interpreted as their actual original IDs. -/
def orderedEdgeMap (N : Holant.FiniteNetwork K V E 0) :
    N.orderedNetwork.incidenceGraph.Edge ≃o E :=
  (Fin.castOrderIso N.orderedNetwork.incidenceGraph_edges).trans (Fintype.orderIsoFinOfCardEq E rfl)

/-- Literal oriented endpoints commute with the original-index interpretation. -/
theorem ordered_endpoint (N : Holant.FiniteNetwork K V E 0)
    (d : N.orderedNetwork.incidenceGraph.Edge) (z : Bool) :
    orderedVertexMap N (N.orderedNetwork.incidenceGraph.endpoint d z) =
      N.endpoint (orderedEdgeMap N d) z := by
  rw [Holant.Network.incidenceGraph_endpoint]
  have hh := N.enumerate_endpoint
    (Fintype.orderIsoFinOfCardEq V rfl).symm.toEquiv
    (Fintype.orderIsoFinOfCardEq E rfl).symm.toEquiv (orderedEdgeMap N d) z
  have he : (Fintype.orderIsoFinOfCardEq E rfl).symm (orderedEdgeMap N d) =
      N.orderedNetwork.incidenceGraphEdgeEquiv d := by
    simp [orderedEdgeMap,Holant.Network.incidenceGraphEdgeEquiv]
    exact (Fintype.orderIsoFinOfCardEq E rfl).symm_apply_apply _
  change N.orderedNetwork.shape.endpoint
    ((Fintype.orderIsoFinOfCardEq E rfl).symm (orderedEdgeMap N d)) z =
    (Fintype.orderIsoFinOfCardEq V rfl).symm (N.endpoint (orderedEdgeMap N d) z) at hh
  rw [he] at hh
  rw [hh]
  exact (Fintype.orderIsoFinOfCardEq V rfl).apply_symm_apply _

end Holant.Complexity.GraphPreprocessing.CanonicalStability
