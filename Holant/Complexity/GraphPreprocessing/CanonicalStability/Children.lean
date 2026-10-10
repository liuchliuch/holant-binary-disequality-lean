import Holant.Complexity.GraphPreprocessing.CanonicalStability.ComponentRows
import Holant.Complexity.GraphPreprocessing.CanonicalStability.ResidualRows
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateGraph

/-! Exact increasing child-list transport, using the actual original parent
rows and the actual child predicate. List equality preserves execution order. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable OriginalCoefficient

 theorem child_predicate_of_rows (g h : Graph) (vs : h.Vertex ↪ g.Vertex)
    (es : h.Edge ↪o g.Edge) (he : ∀ d z, vs (h.endpoint d z) = g.endpoint (es d) z)
    (hnone : ∀ v, (h.parentRow v).parent = none ↔ (g.parentRow (vs v)).parent = none)
    (hsome : ∀ v q, (h.parentRow v).parent = some q → ∃ d : h.Edge, d.val = q.1 ∧
      (g.parentRow (vs v)).parent = some ((es d).val,q.2)) (target child : h.Vertex) :
    ChildPredicate.value (ChildPredicate.graphInput h target child) =
      ChildPredicate.value (ChildPredicate.graphInput g (vs target) (vs child)) := by
  cases hp : (h.parentRow child).parent with
  | none => rw [ChildPredicate.root_false h target child hp,
      ChildPredicate.root_false g (vs target) (vs child) ((hnone child).mp hp)]
  | some q =>
    obtain ⟨d,hd,hg⟩ := hsome child q hp
    have hh : (h.parentRow child).parent = some (d.val,q.2) := by rw [hd]; exact hp
    rw [ChildPredicate.original_edge h target child d q.2 hh,
      ChildPredicate.original_edge g (vs target) (vs child) (es d) q.2 hg,← he]
    simp only [vs.injective.eq_iff]

 theorem children_pairwise (g : Graph) (v : g.Vertex) :
    (ChildEnumerate.children g v).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange _).filter _

/-- A child's original parent row keeps it in exactly its parent's component. -/
 theorem child_same_component (g : Graph) (target child : g.Vertex)
    (hc : child ∈ ChildEnumerate.children g target) : g.label child = g.label target := by
  have hit := (ChildEnumerate.mem_children g target child).mp hc
  cases hp : (g.parentRow child).parent with
  | none => rw [ChildPredicate.root_false g target child hp] at hit; contradiction
  | some q =>
    obtain ⟨e,he,hchild,_⟩ := g.parentRow_some_spec child q hp
    have hp' : (g.parentRow child).parent = some (e.val,q.2) := by rw [he]; exact hp
    rw [ChildPredicate.original_edge g target child e q.2 hp'] at hit
    have htarget := of_decide_eq_true hit
    apply g.label_eq_of_reachable
    rw [← hchild,← htarget]
    cases q.2
    · exact .rel _ _ ⟨e,rfl,rfl⟩
    · exact .symm _ _ (.rel _ _ ⟨e,rfl,rfl⟩)

/-- Increasing enumerations plus exact predicates identify whole child lists,
not just their sets or their lengths. -/
 theorem children_map (g h : Graph) (vs : h.Vertex ↪o g.Vertex) (target : h.Vertex)
    (hp : ∀ child, ChildPredicate.value (ChildPredicate.graphInput h target child) =
      ChildPredicate.value (ChildPredicate.graphInput g (vs target) (vs child)))
    (hcover : ∀ child ∈ ChildEnumerate.children g (vs target), ∃ u, vs u = child) :
    (ChildEnumerate.children h target).map vs = ChildEnumerate.children g (vs target) := by
  apply List.Subset.antisymm_of_pairwise
    ((List.pairwise_map).mpr ((children_pairwise h target).imp (fun h => vs.strictMono h)))
    (children_pairwise g (vs target))
  · intro child hc
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hc
    apply (ChildEnumerate.mem_children _ _ _).mpr
    rw [← hp]
    exact (ChildEnumerate.mem_children _ _ _).mp hu
  · intro child hc
    obtain ⟨u,rfl⟩ := hcover child hc
    apply List.mem_map.mpr
    refine ⟨u,?_,rfl⟩
    apply (ChildEnumerate.mem_children _ _ _).mpr
    rw [hp]
    exact (ChildEnumerate.mem_children _ _ _).mp hc

variable {K : Type*} (N : Holant.Network K 0)

 theorem component_children (root : Fin N.shape.vertices) (hr : N.incidenceGraph.label root = root)
    (target : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    (ChildEnumerate.children (N.computedComponentNetwork root).incidenceGraph target).map
      (componentVertexMap N root) = ChildEnumerate.children N.incidenceGraph (componentVertexMap N root target) := by
  apply children_map N.incidenceGraph (N.computedComponentNetwork root).incidenceGraph
    (componentVertexMap N root) target
  · exact child_predicate_of_rows _ _ (componentVertexMap N root).toEmbedding (componentEdgeMap N root)
      (component_endpoint N root) (component_row_none N root hr) (component_row_some N root hr) target
  · intro child hc
    have hl := (child_same_component N.incidenceGraph _ child hc).trans
      (label_eq_of_fiber N.incidenceGraph root hr (orderedVertexMap (N.computedComponent root) target))
    let u : N.incidenceGraph.Fiber root := ⟨child,(N.incidenceGraph.reach_iff _ _).mpr
      (.symm _ _ ((N.incidenceGraph.label_eq_iff child root).mp (hl.trans hr.symm)))⟩
    refine ⟨(orderedVertexMap (N.computedComponent root)).symm u,?_⟩
    exact congrArg Subtype.val ((orderedVertexMap (N.computedComponent root)).apply_symm_apply u)

 theorem residual_children (e : Fin N.shape.edges) (a b : Bool) (hu : UnusedRows N e)
    (target : (residualGraph N e a b).Vertex) :
    (ChildEnumerate.children (residualGraph N e a b) target).map (residualVertexMap N e a b) =
      ChildEnumerate.children N.incidenceGraph (residualVertexMap N e a b target) := by
  apply children_map N.incidenceGraph (residualGraph N e a b) (residualVertexMap N e a b).toOrderEmbedding target
  · exact child_predicate_of_rows _ _ (residualVertexMap N e a b).toEmbedding (residualEdgeMap N e a b)
      (residual_endpoint N e a b) (residual_row_none N e a b hu) (residual_row_some N e a b hu) target
  · intro child hc
    exact ⟨(residualVertexMap N e a b).symm child,OrderIso.apply_symm_apply _ _⟩

end Holant.Complexity.GraphPreprocessing.CanonicalStability
