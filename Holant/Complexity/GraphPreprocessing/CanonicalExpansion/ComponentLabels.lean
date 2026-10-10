import Holant.Complexity.GraphPreprocessing.CanonicalExpansion.Labels
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildMeaning

/-! The recomputed component tree reads precisely the original raw table-entry
labels at its zero, parent-end and opposite child-end occurrences. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace Holant.Complexity.GraphPreprocessing.CanonicalExpansion
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation
open Holant.OneHot.StackProgram Holant.OneHot.Decomposition CanonicalStability OriginalCoefficient
variable {A : Type*}

 def parentLabel (N : Holant.Network A 0) (zero : A) {root : Fin N.shape.vertices}
    (t : RootedSpanning N.shape.endpoint root) (v : Fin N.shape.vertices) : A :=
  if h : v = root then zero else portLabel N (t.parentEnd ⟨v,h⟩)

 def childLabel (N : Holant.Network A 0) {root : Fin N.shape.vertices}
    (t : RootedSpanning N.shape.endpoint root) (u : {v : Fin N.shape.vertices // v ≠ root}) : A :=
  portLabel N ((t.parentEnd u).1,!(t.parentEnd u).2)

 theorem labelTree_eq (N : Holant.Network A 0) (zero : A) {root : Fin N.shape.vertices}
    (t : RootedSpanning N.shape.endpoint root) (D : ℕ) :
    labelTree N zero t D = tree t (zeroLabel N) (parentLabel N zero t) (childLabel N t) D := rfl

 abbrev componentTree (N : Holant.Network A 0) (root : Fin N.shape.vertices) :=
  (N.computedComponentNetwork root).computedSpanning (componentRoot N root) (component_connected N root)

 def originalNonroot (N : Holant.Network A 0) (root : Fin N.shape.vertices)
    (u : {v : (N.computedComponentNetwork root).incidenceGraph.Vertex // v ≠ componentRoot N root}) :
    {u : N.incidenceGraph.Fiber root // u ≠ N.incidenceGraph.fiberRoot root} :=
  componentNonroot N root ⟨⟨u.val,component_connected N root u.val⟩,
    fun hh => u.property (congrArg Subtype.val hh)⟩

 theorem component_parentPort (N : Holant.Network A 0) (root : Fin N.shape.vertices)
    (u : {v : (N.computedComponentNetwork root).incidenceGraph.Vertex // v ≠ componentRoot N root}) (flip : Bool) :
    portLabel (N.computedComponentNetwork root)
      (((componentTree N root).parentEnd u).1,ParentCoefficient.side flip ((componentTree N root).parentEnd u).2) =
      portLabel N
        (N.incidenceGraphEdgeEquiv (N.incidenceGraph.parentEnd root (originalNonroot N root u)).1,
          ParentCoefficient.side flip (N.incidenceGraph.parentEnd root (originalNonroot N root u)).2) := by
  let v : {v : (N.computedComponentNetwork root).incidenceGraph.Fiber (componentRoot N root) //
      v ≠ Graph.fiberRoot _ (componentRoot N root)} :=
    ⟨⟨u.val,component_connected N root u.val⟩,fun hh => u.property (congrArg Subtype.val hh)⟩
  change portLabel (N.computedComponentNetwork root)
    ((N.computedComponentNetwork root).incidenceGraphEdgeEquiv
      ((N.computedComponentNetwork root).incidenceGraph.parentEnd (componentRoot N root) v).1,
      ParentCoefficient.side flip ((N.computedComponentNetwork root).incidenceGraph.parentEnd (componentRoot N root) v).2) = _
  rw [component_port]
  exact congrArg (fun q => portLabel N (N.incidenceGraphEdgeEquiv q.1,ParentCoefficient.side flip q.2))
    (component_parentEnd N root v)

variable {s b : ℕ} {arity : ℕ → ℕ} (r : Holant.Complexity.RawClosedNetwork) (h : r.WellFormed s b arity)

 theorem raw_zero_value (v : Fin r.vertices.length) :
    OrdinaryCoefficient.zeroValue ⟨⟨r,h⟩,v⟩ = zeroLabel (r.labelNetwork h) v := rfl

 theorem raw_singleton_value (q : Fin r.edges.length × Bool) :
    SingletonLabel.label r h (r.lookup h q) = portLabel (r.labelNetwork h) q := rfl

 theorem raw_parent_value (root : Fin r.vertices.length) (hr : (r.graph h).label root = root)
    (u : {u : (r.graph h).Fiber root // u ≠ (r.graph h).fiberRoot root}) :
    ParentCoefficient.value false (ParentCoefficient.originalInput ⟨⟨r,h⟩,u.val.val⟩) =
      portLabel (r.labelNetwork h) (r.graphEdgeEquiv h ((r.graph h).parentEnd root u).1,
        ((r.graph h).parentEnd root u).2) := by
  exact ParentCoefficient.original_nonroot ⟨⟨r,h⟩,u.val.val⟩ _
    (row_parent_of_nonroot (r.graph h) root hr u)

end Holant.Complexity.GraphPreprocessing.CanonicalExpansion
