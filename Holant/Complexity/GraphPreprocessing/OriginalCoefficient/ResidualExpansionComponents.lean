import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion

/-! Restriction and unused-edge conditioning commute on the actual ordered
original vertex fibers. The witness uses computed reachability, not a supplied
component partition, and exposes the precise original vertex in both orders. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
open Holant.OneHot.Computable CanonicalStability CanonicalExpansion
variable {s b : ℕ} {arity : ℕ → ℕ}

/-- The residual component has exactly the original component's vertices,
with the same increasing original order. This includes isolated vertices and
conditioning an unused edge in a different component. -/
 def componentVerticesEquiv (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root) :
    (residual a z x).incidenceGraph.Fiber (rootIndex a z x root) ≃o
      (network x).incidenceGraph.Fiber root where
  toFun := residualFiber (network x) (ResidualContext.edge x) a z root
  invFun u := ⟨(residualVertexMap (network x) (ResidualContext.edge x) a z).symm u.val,by
    apply ((residual a z x).incidenceGraph.reach_iff _ _).mpr
    apply (residual a z x).incidenceGraph.reach_sound
    exact (residual_reach (network x) (ResidualContext.edge x) a z root
      (unusedAt_of_rows (network x) (ResidualContext.edge x) (unused x) root hr) _ _).mpr
      (by rw [OrderIso.apply_symm_apply]; exact u.property)⟩
  left_inv u := by
    apply Subtype.ext
    exact OrderIso.symm_apply_apply _ _
  right_inv u := by
    apply Subtype.ext
    exact OrderIso.apply_symm_apply _ _
  map_rel_iff' := by
    intro u v
    exact (residualVertexMap (network x) (ResidualContext.edge x) a z).le_iff_le

/-- Restricting the residual by reachability selects exactly the original
component vertices after the same explicit original-ID map. -/
 theorem component_vertex_mem (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root)
    (v : (residual a z x).incidenceGraph.Vertex) :
    v ∈ (residual a z x).incidenceGraph.reach (rootIndex a z x root) (residual a z x).incidenceGraph.vertices ↔
      residualVertexMap (network x) (ResidualContext.edge x) a z v ∈
        (network x).incidenceGraph.reach root (network x).incidenceGraph.vertices := by
  constructor
  · intro hv
    exact (componentVerticesEquiv a z x root hr ⟨v,hv⟩).property
  · intro hv
    have h := ((componentVerticesEquiv a z x root hr).symm
      ⟨residualVertexMap (network x) (ResidualContext.edge x) a z v,hv⟩).property
    change (residualVertexMap (network x) (ResidualContext.edge x) a z).symm
      (residualVertexMap (network x) (ResidualContext.edge x) a z v) ∈ _ at h
    rw [OrderIso.symm_apply_apply] at h
    exact h

/-- The surviving original edges in either order are exactly those whose
original false endpoint is in the selected original component. -/
 theorem component_edge_mem (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root)
    (d : (residual a z x).incidenceGraph.Edge) :
    (residual a z x).incidenceGraph.endpoint d false ∈
        (residual a z x).incidenceGraph.reach (rootIndex a z x root) (residual a z x).incidenceGraph.vertices ↔
      (network x).incidenceGraph.endpoint
          (residualEdgeMap (network x) (ResidualContext.edge x) a z d) false ∈
        (network x).incidenceGraph.reach root (network x).incidenceGraph.vertices := by
  rw [component_vertex_mem a z x root hr,residual_endpoint]

/-- The computed component cardinality is unchanged by the actual unused cut. -/
 theorem component_vertices (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root) :
    (component a z x root).shape.vertices =
      ((network x).computedComponentNetwork root).shape.vertices :=
  Fintype.card_congr (componentVerticesEquiv a z x root hr).toEquiv

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
