import Holant.Complexity.GraphPreprocessing.CanonicalStability.OrderedNetwork

/-! Canonical original BFS/parent choices under the actual computed connected
component restriction and its increasing vertex/edge enumeration. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable
variable {K : Type*} (N : Holant.Network K 0) (root : Fin N.shape.vertices)

/-- The actual component vertex index mapped back to its original vertex ID. -/
def componentVertexMap : (N.computedComponentNetwork root).incidenceGraph.Vertex ↪o
    N.incidenceGraph.Vertex :=
  (orderedVertexMap (N.computedComponent root)).toOrderEmbedding.trans (OrderEmbedding.subtype _)

/-- The actual component edge index mapped back to its original edge ID. -/
def componentEdgeMap : (N.computedComponentNetwork root).incidenceGraph.Edge ↪o
    N.incidenceGraph.Edge :=
  (orderedEdgeMap (N.computedComponent root)).toOrderEmbedding.trans (OrderEmbedding.subtype _)

/-- Exactly the root index passed by computedComponentCode to computedConnectedCode. -/
def componentRoot : (N.computedComponentNetwork root).incidenceGraph.Vertex :=
  (orderedVertexMap (N.computedComponent root)).symm (N.incidenceGraph.fiberRoot root)

@[simp] theorem component_root : componentVertexMap N root (componentRoot N root) = root := by
  change ((orderedVertexMap (N.computedComponent root))
    ((orderedVertexMap (N.computedComponent root)).symm (N.incidenceGraph.fiberRoot root))).val = _
  rw [OrderIso.apply_symm_apply]
  rfl

theorem component_endpoint (d : (N.computedComponentNetwork root).incidenceGraph.Edge) (z : Bool) :
    componentVertexMap N root ((N.computedComponentNetwork root).incidenceGraph.endpoint d z) =
      N.incidenceGraph.endpoint (componentEdgeMap N root d) z := by
  have hh := ordered_endpoint (N.computedComponent root) d z
  rw [N.computedComponent_endpoint] at hh
  exact congrArg Subtype.val hh

/-- Every selected original parent edge is itself an edge of this actual
component, so it appears in the increasing residual edge scan. -/
theorem component_parents_survive : ParentsSurvive N.incidenceGraph
    (N.computedComponentNetwork root).incidenceGraph (componentEdgeMap N root) root := by
  intro u
  let d := (N.incidenceGraph.fiberParentEnd root u).1
  refine ⟨(orderedEdgeMap (N.computedComponent root)).symm d,?_⟩
  change ((orderedEdgeMap (N.computedComponent root))
    ((orderedEdgeMap (N.computedComponent root)).symm d)).val = _
  rw [OrderIso.apply_symm_apply]
  rfl

/-- Recomputed component BFS layers are exactly the original BFS layers under
the original-vertex map, at every bounded round. -/
theorem component_reach (k : ℕ)
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    v ∈ (N.computedComponentNetwork root).incidenceGraph.reach (componentRoot N root) k ↔
      componentVertexMap N root v ∈ N.incidenceGraph.reach root k := by
  have hs : ParentsSurvive N.incidenceGraph (N.computedComponentNetwork root).incidenceGraph
      (componentEdgeMap N root) ((componentVertexMap N root).toEmbedding (componentRoot N root)) := by
    change ParentsSurvive _ _ _ (componentVertexMap N root (componentRoot N root))
    rw [component_root]
    exact component_parents_survive N root
  have hh := reach_iff_of_parents_survive N.incidenceGraph
    (N.computedComponentNetwork root).incidenceGraph (componentVertexMap N root).toEmbedding
    (componentEdgeMap N root) (component_endpoint N root) (componentRoot N root) hs k v
  exact hh.trans (by change (_ ∈ N.incidenceGraph.reach (componentVertexMap N root (componentRoot N root)) k) ↔ _; rw [component_root]; rfl)

/-- Recomputed component first-success depths retain their actual original values. -/
theorem component_depth
    (v : (N.computedComponentNetwork root).incidenceGraph.Fiber (componentRoot N root)) :
    (N.computedComponentNetwork root).incidenceGraph.depth (componentRoot N root) v =
      N.incidenceGraph.depth root (orderedVertexMap (N.computedComponent root) v.val) := by
  apply Nat.le_antisymm
  · apply Graph.depth_le_of_mem
    exact (component_reach N root _ _).mpr (N.incidenceGraph.depth_mem _ _)
  · apply Graph.depth_le_of_mem
    exact (component_reach N root _ _).mp (Graph.depth_mem _ _ _)

/-- Original nonroot component vertices, with the exact enumerated ID. -/
def componentNonroot
    (v : {v : (N.computedComponentNetwork root).incidenceGraph.Fiber (componentRoot N root) //
      v ≠ Graph.fiberRoot _ (componentRoot N root)}) :
    {v : N.incidenceGraph.Fiber root // v ≠ N.incidenceGraph.fiberRoot root} :=
  ⟨orderedVertexMap (N.computedComponent root) v.val.val, fun hh => v.property (Subtype.ext
    ((orderedVertexMap (N.computedComponent root)).injective (hh.trans
      (OrderIso.apply_symm_apply _ _).symm)))⟩

/-- The component recomputation selects literally the same original edge/end. -/
theorem component_parentEnd
    (v : {v : (N.computedComponentNetwork root).incidenceGraph.Fiber (componentRoot N root) //
      v ≠ Graph.fiberRoot _ (componentRoot N root)}) :
    (componentEdgeMap N root
      ((N.computedComponentNetwork root).incidenceGraph.parentEnd (componentRoot N root) v).1,
      ((N.computedComponentNetwork root).incidenceGraph.parentEnd (componentRoot N root) v).2) =
      N.incidenceGraph.parentEnd root (componentNonroot N root v) := by
  have hs : ParentsSurvive N.incidenceGraph (N.computedComponentNetwork root).incidenceGraph
      (componentEdgeMap N root) ((componentVertexMap N root).toEmbedding (componentRoot N root)) := by
    change ParentsSurvive _ _ _ (componentVertexMap N root (componentRoot N root))
    rw [component_root]
    exact component_parents_survive N root
  have hp := parentEnd_eq N.incidenceGraph (N.computedComponentNetwork root).incidenceGraph
    (componentVertexMap N root).toEmbedding (componentEdgeMap N root) (component_endpoint N root)
    (componentRoot N root) hs v
  exact hp.trans (parentEnd_congr N.incidenceGraph _ _ (component_root N root) _ _ rfl)

end Holant.Complexity.GraphPreprocessing.CanonicalStability
