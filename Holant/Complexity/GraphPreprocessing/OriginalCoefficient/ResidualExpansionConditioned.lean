import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionRestriction

/-! Canonical geometry and literal labels when the original component is
restricted first and its actual surplus edge is conditioned second. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion.ConditionedComponent
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation
open Holant.OneHot.StackProgram Holant.OneHot.Decomposition
open CanonicalStability CanonicalExpansion
variable {A : Type*} (N : Holant.Network A 0) (root : Fin N.shape.vertices)

 def fullNonroot (hc : N.incidenceGraph.Connected root) (u : {v : Fin N.shape.vertices // v ≠ root}) :
    {v : N.incidenceGraph.Fiber root // v ≠ N.incidenceGraph.fiberRoot root} :=
  ⟨⟨u.val,hc u.val⟩,fun h => u.property (congrArg Subtype.val h)⟩

 theorem fullNonroot_val (hc : N.incidenceGraph.Connected root) (u : {v : Fin N.shape.vertices // v ≠ root}) :
    (fullNonroot N root hc u).val.val = u.val := rfl

 theorem computed_parentEnd (hc : N.incidenceGraph.Connected root) (u : {v : Fin N.shape.vertices // v ≠ root}) :
    (N.computedSpanning root hc).parentEnd u =
      (N.incidenceGraphEdgeEquiv (N.incidenceGraph.parentEnd root (fullNonroot N root hc u)).1,
        (N.incidenceGraph.parentEnd root (fullNonroot N root hc u)).2) := rfl

 abbrev base := N.computedComponentNetwork root
 abbrev start := componentRoot N root
 variable (e : (componentTree N root).Surplus) (a z : Bool)
 abbrev finite := (base N root).asFinite.executableConditionEdge e.val a z
 abbrev result := (finite N root e a z).orderedNetwork
 abbrev rootIndex := residualRoot (base N root) e.val a z (start N root)

 theorem unused (hr : N.incidenceGraph.label root = root) : UnusedRows (base N root) e.val :=
  unusedRows_surplus (base N root) (start N root) (component_connected N root)
    (component_label N root hr _) e

 theorem connected : (result N root e a z).incidenceGraph.Connected (rootIndex N root e a z) :=
  residual_connected (base N root) e.val a z (start N root)
    (unusedAt_surplus (base N root) (start N root) (component_connected N root) e)
    (component_connected N root)

 abbrev tree := (result N root e a z).computedSpanning (rootIndex N root e a z) (connected N root e a z)

 def vertices : (result N root e a z).incidenceGraph.Vertex ↪o N.incidenceGraph.Vertex :=
  (residualVertexMap (base N root) e.val a z).toOrderEmbedding.trans (componentVertexMap N root)
 def edges : (result N root e a z).incidenceGraph.Edge ↪o N.incidenceGraph.Edge :=
  (residualEdgeMap (base N root) e.val a z).trans (componentEdgeMap N root)

 @[simp] theorem vertices_apply (v : (result N root e a z).incidenceGraph.Vertex) :
    vertices N root e a z v = componentVertexMap N root (residualVertexMap (base N root) e.val a z v) := rfl
 @[simp] theorem edges_apply (d : (result N root e a z).incidenceGraph.Edge) :
    edges N root e a z d = componentEdgeMap N root (residualEdgeMap (base N root) e.val a z d) := rfl

 @[simp] theorem root_original : vertices N root e a z (rootIndex N root e a z) = root := by
  rw [vertices_apply,residual_root,component_root]

 theorem least (hr : N.incidenceGraph.label root = root) :
    (result N root e a z).incidenceGraph.label (rootIndex N root e a z) = rootIndex N root e a z := by
  apply (residualVertexMap (base N root) e.val a z).injective
  rw [residual_label (base N root) e.val a z (unused N root e hr),residual_root]
  exact component_label N root hr _

 theorem row_none (hr : N.incidenceGraph.label root = root)
    (v : (result N root e a z).incidenceGraph.Vertex) :
    ((result N root e a z).incidenceGraph.parentRow v).parent = none ↔
      (N.incidenceGraph.parentRow (vertices N root e a z v)).parent = none :=
  (residual_row_none (base N root) e.val a z (unused N root e hr) v).trans
    (component_row_none N root hr _)

 theorem row_some (hr : N.incidenceGraph.label root = root)
    (v : (result N root e a z).incidenceGraph.Vertex)
    (d : (result N root e a z).incidenceGraph.Edge) (side : Bool)
    (hp : ((result N root e a z).incidenceGraph.parentRow v).parent = some (d.val,side)) :
    (N.incidenceGraph.parentRow (vertices N root e a z v)).parent =
      some ((edges N root e a z d).val,side) := by
  obtain ⟨d',hd,hp'⟩ := residual_row_some (base N root) e.val a z (unused N root e hr) v _ hp
  have he : d' = d := Fin.ext hd
  subst d'
  obtain ⟨d',hd,hp''⟩ := component_row_some N root hr _ _ hp'
  have he : d' = residualEdgeMap (base N root) e.val a z d := Fin.ext hd
  subst d'
  exact hp''

 theorem endpoint (d : (result N root e a z).incidenceGraph.Edge) (side : Bool) :
    vertices N root e a z ((result N root e a z).incidenceGraph.endpoint d side) =
      N.incidenceGraph.endpoint (edges N root e a z d) side := by
  rw [vertices_apply,residual_endpoint,edges_apply,component_endpoint]

 theorem child_order (hr : N.incidenceGraph.label root = root)
    (v : (result N root e a z).incidenceGraph.Vertex) :
    (children (tree N root e a z) v).map (fun u => vertices N root e a z u.val) =
      ChildEnumerate.children N.incidenceGraph (vertices N root e a z v) := by
  have h := congrArg (List.map (componentVertexMap N root))
    (residual_children_computed (base N root) e.val a z (start N root)
      (component_connected N root) (component_label N root hr _) (unused N root e hr) v)
  rw [component_children N root hr] at h
  simp only [vertices_apply]
  simpa only [List.map_map,Function.comp_def] using h

 def originalRemaining (d : (result N root e a z).incidenceGraph.Edge) :
    Holant.FiniteNetwork.RemainingEdge (componentOriginalEdge N root e.val) :=
  componentRemainingEdge N root e.val (orderedEdgeMap (finite N root e a z) d)

 theorem originalRemaining_val (d : (result N root e a z).incidenceGraph.Edge) :
    (originalRemaining N root e a z d).val = N.incidenceGraphEdgeEquiv (edges N root e a z d) := by
  apply congrArg N.incidenceGraphEdgeEquiv
  apply congrArg (componentEdgeMap N root)
  apply Fin.ext
  rfl

 theorem original_remaining_endpoint (d : (result N root e a z).incidenceGraph.Edge) (side : Bool) :
    (N.asFinite.executableConditionEdge (componentOriginalEdge N root e.val) a z).endpoint
      (originalRemaining N root e a z d) side =
      vertices N root e a z ((result N root e a z).incidenceGraph.endpoint d side) := by
  rw [Holant.FiniteNetwork.executableConditionEdge_eq,Holant.FiniteNetwork.conditionEdge_endpoint,
    originalRemaining_val]
  exact (N.incidenceGraph_endpoint _ _).symm.trans (endpoint N root e a z d side).symm

 theorem zero (v : (result N root e a z).incidenceGraph.Vertex) :
    zeroLabel (result N root e a z) v =
      (N.asFinite.executableConditionEdge (componentOriginalEdge N root e.val) a z).vertex
        (vertices N root e a z v) (fun _ => false) :=
  component_conditioned_zero N root e.val a z _

 theorem port (d : (result N root e a z).incidenceGraph.Edge) (side : Bool) :
    portLabel (result N root e a z) ((result N root e a z).incidenceGraphEdgeEquiv d,side) =
      finitePortLabel (N.asFinite.executableConditionEdge (componentOriginalEdge N root e.val) a z)
        (originalRemaining N root e a z d,side) := by
  rw [ordered_port]
  exact component_conditioned_port N root e.val a z _

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion.ConditionedComponent
