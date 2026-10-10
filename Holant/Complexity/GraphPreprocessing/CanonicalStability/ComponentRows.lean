import Holant.Complexity.GraphPreprocessing.CanonicalStability.Component
import Holant.Complexity.GraphPreprocessing.CanonicalStability.Rows

/-! Least original roots and serializable canonical parent rows commute with
the actual connected-component restriction, including original edge/end IDs. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable
variable {K : Type*} (N : Holant.Network K 0) (root : Fin N.shape.vertices)

 theorem component_connected : (N.computedComponentNetwork root).incidenceGraph.Connected
    (componentRoot N root) :=
  (N.computedComponent root).orderedNetwork_connected (N.incidenceGraph.fiberRoot root)
    (N.computedComponent_connected root)

 theorem component_label (hr : N.incidenceGraph.label root = root)
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    (N.computedComponentNetwork root).incidenceGraph.label v = componentRoot N root := by
  let h := (N.computedComponentNetwork root).incidenceGraph
  have hm : ∀ w : h.Vertex, componentRoot N root ≤ w := by
    intro w
    apply (componentVertexMap N root).le_iff_le.mp
    rw [component_root]
    have hx := Finset.min'_le (N.incidenceGraph.reach root N.incidenceGraph.vertices)
      (orderedVertexMap (N.computedComponent root) w).val
      (orderedVertexMap (N.computedComponent root) w).property
    change N.incidenceGraph.label root ≤ componentVertexMap N root w at hx
    rw [hr] at hx
    exact hx
  apply le_antisymm
  · apply Finset.min'_le
    exact (h.reach_iff _ _).mpr (.symm _ _
      (h.reach_sound _ _ _ (component_connected N root v)))
  · exact Finset.le_min' _ _ _ (fun w _ => hm w)

 theorem component_label_original (hr : N.incidenceGraph.label root = root)
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    componentVertexMap N root ((N.computedComponentNetwork root).incidenceGraph.label v) =
      N.incidenceGraph.label (componentVertexMap N root v) := by
  rw [component_label N root hr,component_root]
  exact (label_eq_of_fiber N.incidenceGraph root hr
    (orderedVertexMap (N.computedComponent root) v)).symm

 theorem component_row_depth (hr : N.incidenceGraph.label root = root)
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    ((N.computedComponentNetwork root).incidenceGraph.parentRow v).depth =
      (N.incidenceGraph.parentRow (componentVertexMap N root v)).depth := by
  let u : (N.computedComponentNetwork root).incidenceGraph.Fiber (componentRoot N root) :=
    ⟨v,component_connected N root v⟩
  exact (row_depth_of_fiber _ _ (component_label N root hr _) u).trans
    ((component_depth N root u).trans
      (row_depth_of_fiber _ _ hr (orderedVertexMap (N.computedComponent root) v)).symm)

 theorem component_row_none (hr : N.incidenceGraph.label root = root)
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    ((N.computedComponentNetwork root).incidenceGraph.parentRow v).parent = none ↔
      (N.incidenceGraph.parentRow (componentVertexMap N root v)).parent = none := by
  rw [Graph.parentRow_none_iff,Graph.parentRow_none_iff]
  rw [← component_label_original N root hr]
  exact (componentVertexMap N root).injective.eq_iff.symm

/-- A present residual row is exactly the original row after interpreting its
edge number through the actual increasing component edge enumeration. -/
 theorem component_row_some (hr : N.incidenceGraph.label root = root)
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex) (q : ℕ × Bool)
    (hq : ((N.computedComponentNetwork root).incidenceGraph.parentRow v).parent = some q) :
    ∃ d : (N.computedComponentNetwork root).incidenceGraph.Edge, d.val = q.1 ∧
      (N.incidenceGraph.parentRow (componentVertexMap N root v)).parent =
        some ((componentEdgeMap N root d).val,q.2) := by
  let h := (N.computedComponentNetwork root).incidenceGraph
  have hv : v ≠ componentRoot N root := by
    intro hh
    have hn := (h.parentRow_none_iff v).mpr (by rw [component_label N root hr,hh])
    rw [hq] at hn
    contradiction
  let u : {u : h.Fiber (componentRoot N root) // u ≠ h.fiberRoot (componentRoot N root)} :=
    ⟨⟨v,component_connected N root v⟩,fun hh => hv (congrArg Subtype.val hh)⟩
  have hrow := row_parent_of_nonroot h _ (component_label N root hr _) u
  have heq := Option.some.inj (hrow.symm.trans hq)
  refine ⟨(h.parentEnd _ u).1,congrArg Prod.fst heq,?_⟩
  have hold := row_parent_of_nonroot N.incidenceGraph root hr (componentNonroot N root u)
  rw [component_parentEnd N root u |>.symm] at hold
  exact hold.trans (congrArg (fun z => some ((componentEdgeMap N root (h.parentEnd _ u).1).val,z))
    (congrArg Prod.snd heq))

end Holant.Complexity.GraphPreprocessing.CanonicalStability
