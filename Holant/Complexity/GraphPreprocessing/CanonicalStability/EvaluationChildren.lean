import Holant.Complexity.GraphPreprocessing.CanonicalStability.Children

/-! Literal child-order correspondence to the computed trees consumed by
computedTreeCode and conditionedCode, not merely to equal denotations. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation OriginalCoefficient
variable {K : Type*} (N : Holant.Network K 0)

 theorem child_iff_computed (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root = root) (target child : Fin N.shape.vertices) :
    child ∈ ChildEnumerate.children N.incidenceGraph target ↔
      child ≠ root ∧ parent (N.computedSpanning root hc) child = target := by
  by_cases hn : child = root
  · subst child
    have hz := (N.incidenceGraph.parentRow_none_iff root).mpr hr
    rw [ChildEnumerate.mem_children,ChildPredicate.root_false _ _ _ hz]
    simp
  · let u : {u : N.incidenceGraph.Fiber root // u ≠ N.incidenceGraph.fiberRoot root} :=
      ⟨⟨child,hc child⟩,fun hh => hn (congrArg Subtype.val hh)⟩
    have hp := row_parent_of_nonroot N.incidenceGraph root hr u
    rw [ChildEnumerate.mem_children,ChildPredicate.original_edge _ _ _ _ _ hp]
    simp only [decide_eq_true_eq,parent,dite_eq_right hn,and_iff_right hn]
    change N.incidenceGraph.endpoint (N.incidenceGraph.parentEnd root u).1
      (!(N.incidenceGraph.parentEnd root u).2) = target ↔
      N.shape.endpoint (N.incidenceGraphEdgeEquiv (N.incidenceGraph.parentEnd root u).1)
        (!(N.incidenceGraph.parentEnd root u).2) = target
    rw [N.incidenceGraph_endpoint]

/-- Actual raw parent-row children are exactly Evaluation.children, in order. -/
 theorem children_computed (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root = root) (target : Fin N.shape.vertices) :
    ChildEnumerate.children N.incidenceGraph target =
      (children (N.computedSpanning root hc) target).map Subtype.val := by
  have hs : ((children (N.computedSpanning root hc) target).map Subtype.val).Pairwise (· < ·) := by
    apply List.pairwise_map.mpr
    exact (Finset.univ.sortedLT_sort).pairwise
  apply List.Subset.antisymm_of_pairwise (children_pairwise _ _) hs
  · intro child hm
    have hp := (child_iff_computed N root hc hr target child).mp hm
    exact List.mem_map.mpr ⟨⟨child,hp⟩,mem_children _ _ _,rfl⟩
  · intro child hm
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hm
    exact (child_iff_computed N root hc hr target u.val).mpr u.property

/-- The exact evaluator child order after component restriction, transported
to the original vertex IDs used by the physical raw child compiler. -/
 theorem component_children_computed (root : Fin N.shape.vertices)
    (hr : N.incidenceGraph.label root = root)
    (target : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    (children ((N.computedComponentNetwork root).computedSpanning (componentRoot N root)
      (component_connected N root)) target).map (fun u => componentVertexMap N root u.val) =
      ChildEnumerate.children N.incidenceGraph (componentVertexMap N root target) := by
  have hh := component_children N root hr target
  rw [children_computed (N.computedComponentNetwork root) (componentRoot N root)
    (component_connected N root) (component_label N root hr _) target] at hh
  simpa only [List.map_map,Function.comp_def] using hh

 theorem residual_connected (e : Fin N.shape.edges) (a b : Bool) (root : Fin N.shape.vertices)
    (hu : UnusedAt N e root) (hc : N.incidenceGraph.Connected root) :
    (residualGraph N e a b).Connected (residualRoot N e a b root) := by
  intro v
  apply ((residualGraph N e a b).reach_iff _ _).mpr
  apply (residualGraph N e a b).reach_sound
  exact (residual_reach N e a b root hu _ v).mpr (hc _)

/-- The evaluator's recomputed residual child list has the original raw scan
order after exact original-index transport, for every conditioning branch. -/
 theorem residual_children_computed (e : Fin N.shape.edges) (a b : Bool)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root)
    (hr : N.incidenceGraph.label root = root) (hu : UnusedRows N e)
    (target : (residualGraph N e a b).Vertex) :
    (children ((N.asFinite.executableConditionEdge e a b).orderedNetwork.computedSpanning
      (residualRoot N e a b root)
      (residual_connected N e a b root (unusedAt_of_rows N e hu root hr) hc)) target).map
      (fun u => residualVertexMap N e a b u.val) =
      ChildEnumerate.children N.incidenceGraph (residualVertexMap N e a b target) := by
  have hroot : (residualGraph N e a b).label (residualRoot N e a b root) = residualRoot N e a b root := by
    apply (residualVertexMap N e a b).injective
    rw [residual_label N e a b hu,residual_root,hr]
  have hh := residual_children N e a b hu target
  rw [children_computed (N.asFinite.executableConditionEdge e a b).orderedNetwork
    (residualRoot N e a b root) (residual_connected N e a b root (unusedAt_of_rows N e hu root hr) hc)
    hroot target] at hh
  simpa only [List.map_map,Function.comp_def] using hh

end Holant.Complexity.GraphPreprocessing.CanonicalStability
