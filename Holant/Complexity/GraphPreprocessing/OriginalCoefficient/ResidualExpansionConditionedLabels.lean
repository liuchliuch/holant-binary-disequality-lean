import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionConditioned

/-! The physical original-ID coefficient producers equal the literal labels
of the tree obtained by conditioning the already-restricted original component. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion.ConditionedLabels
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation
open Holant.OneHot.StackProgram Holant.OneHot.Decomposition
open CanonicalStability CanonicalExpansion

 theorem cut_port_congr {A V E : Type*} [DecidableEq E]
    (N : Holant.FiniteNetwork A V E 0) (cut cut' : E) (hc : cut = cut') (a z side : Bool)
    (d : Holant.FiniteNetwork.RemainingEdge cut) (d' : Holant.FiniteNetwork.RemainingEdge cut')
    (hd : d.val = d'.val) :
    finitePortLabel (N.executableConditionEdge cut a z) (d,side) =
      finitePortLabel (N.executableConditionEdge cut' a z) (d',side) := by
  subst cut'
  have he : d = d' := Subtype.ext hd
  subst d'
  rfl

variable {s b : ℕ} {arity : ℕ → ℕ} (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (e : (componentTree (network x) root).Surplus) (a z : Bool)
    (hcut : componentOriginalEdge (network x) root e.val = ResidualContext.edge x)

 abbrev result := ConditionedComponent.result (network x) root e a z
 def vertexMap : (result x root e a z).incidenceGraph.Vertex ↪o Fin (ResidualContext.source x).val.vertices.length :=
  ConditionedComponent.vertices (network x) root e a z
 def survivingEdge (d : (result x root e a z).incidenceGraph.Edge) : Holant.FiniteNetwork.RemainingEdge (ResidualContext.edge x) :=
  ⟨(ConditionedComponent.originalRemaining (network x) root e a z d).val,by
    rw [← hcut]
    exact (ConditionedComponent.originalRemaining (network x) root e a z d).property⟩

 theorem survivingEdge_val (d : (result x root e a z).incidenceGraph.Edge) :
    (survivingEdge x root e a z hcut d).val =
      (network x).incidenceGraphEdgeEquiv (ConditionedComponent.edges (network x) root e a z d) :=
  ConditionedComponent.originalRemaining_val (network x) root e a z d

 theorem port (d : (result x root e a z).incidenceGraph.Edge) (side : Bool) :
    finitePortLabel ((network x).asFinite.executableConditionEdge (ResidualContext.edge x) a z)
      (survivingEdge x root e a z hcut d,side) =
      portLabel (result x root e a z) ((result x root e a z).incidenceGraphEdgeEquiv d,side) := by
  exact (cut_port_congr (network x).asFinite _ _ hcut.symm a z side
    (survivingEdge x root e a z hcut d)
    (ConditionedComponent.originalRemaining (network x) root e a z d) rfl).trans
    (ConditionedComponent.port (network x) root e a z d side).symm

 theorem endpoint (d : (result x root e a z).incidenceGraph.Edge) (side : Bool) :
    ((network x).asFinite.executableConditionEdge (ResidualContext.edge x) a z).endpoint
      (survivingEdge x root e a z hcut d) side =
      vertexMap x root e a z ((result x root e a z).incidenceGraph.endpoint d side) := by
  rw [Holant.FiniteNetwork.executableConditionEdge_eq,Holant.FiniteNetwork.conditionEdge_endpoint,survivingEdge_val]
  exact ((network x).incidenceGraph_endpoint _ _).symm.trans
    (ConditionedComponent.endpoint (network x) root e a z d side).symm

include hcut
 theorem zero (v : (result x root e a z).incidenceGraph.Vertex) :
    ResidualOriginalCoefficient.zeroValue a z ⟨x,vertexMap x root e a z v⟩ = zeroLabel (result x root e a z) v := by
  have h := ConditionedComponent.zero (network x) root e a z v
  rw [hcut] at h
  exact (ResidualOriginalCoefficient.zero_conditioned a z _).trans h.symm

 theorem parent (hr : (network x).incidenceGraph.label root = root)
    (v : (result x root e a z).incidenceGraph.Vertex)
    (d : (result x root e a z).incidenceGraph.Edge) (side : Bool)
    (hp : ((result x root e a z).incidenceGraph.parentRow v).parent = some (d.val,side))
    (hv : (result x root e a z).incidenceGraph.endpoint d side = v) :
    ResidualOriginalCoefficient.parentValue a z ⟨x,vertexMap x root e a z v⟩ =
      portLabel (result x root e a z) ((result x root e a z).incidenceGraphEdgeEquiv d,side) := by
  have hold := ConditionedComponent.row_some (network x) root e a z hr v d side hp
  have hq : (⟨(ConditionedComponent.edges (network x) root e a z d).val,
      (ParentCoefficient.originalInput (ResidualContext.original ⟨x,vertexMap x root e a z v⟩)).property _ hold⟩ :
      Fin (ResidualContext.source x).val.edges.length) = (survivingEdge x root e a z hcut d).val := by
    apply Fin.ext
    exact (congrArg Fin.val (survivingEdge_val x root e a z hcut d)).symm
  apply (stored_port false a z (ResidualOriginalCoefficient.prepared ⟨x,vertexMap x root e a z v⟩)
    (survivingEdge x root e a z hcut d) side ?_ ?_).trans (port x root e a z hcut d side)
  · have h := ParentCoefficient.parent_some false
      (ParentCoefficient.originalInput (ResidualContext.original ⟨x,vertexMap x root e a z v⟩)) _ hold
    rw [hq] at h
    exact h
  · exact (endpoint x root e a z hcut d side).trans (congrArg (vertexMap x root e a z) hv)

 theorem child (hr : (network x).incidenceGraph.label root = root)
    (v child : (result x root e a z).incidenceGraph.Vertex)
    (d : (result x root e a z).incidenceGraph.Edge) (side : Bool)
    (hp : ((result x root e a z).incidenceGraph.parentRow child).parent = some (d.val,side))
    (hv : (result x root e a z).incidenceGraph.endpoint d (!side) = v) :
    ResidualActionChild.portValue a z ⟨⟨x,vertexMap x root e a z v⟩,vertexMap x root e a z child⟩ =
      portLabel (result x root e a z) ((result x root e a z).incidenceGraphEdgeEquiv d,!side) := by
  let input : ResidualActionChild.Input s b arity := ⟨⟨x,vertexMap x root e a z v⟩,vertexMap x root e a z child⟩
  have hold := ConditionedComponent.row_some (network x) root e a z hr child d side hp
  have hq : (⟨(ConditionedComponent.edges (network x) root e a z d).val,
      (ResidualActionChild.parentInput input).property _ hold⟩ :
      Fin (ResidualContext.source x).val.edges.length) = (survivingEdge x root e a z hcut d).val := by
    apply Fin.ext
    exact (congrArg Fin.val (survivingEdge_val x root e a z hcut d)).symm
  apply (stored_port true a z (ResidualActionChild.prepared input)
    (survivingEdge x root e a z hcut d) (!side) ?_ ?_).trans (port x root e a z hcut d (!side))
  · have h := ParentCoefficient.parent_some true (ResidualActionChild.parentInput input) _ hold
    rw [hq] at h
    exact h
  · exact (endpoint x root e a z hcut d (!side)).trans (congrArg (vertexMap x root e a z) hv)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion.ConditionedLabels
