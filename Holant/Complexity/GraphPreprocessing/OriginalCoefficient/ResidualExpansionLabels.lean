import Holant.Complexity.GraphPreprocessing.CanonicalExpansion.Component
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionTable

/-! Literal residual port coefficients. These bridges use the physically stored
original parent row and its actual orientation; no expansion premise is used. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation
open Holant.OneHot.StackProgram Holant.OneHot.Decomposition
open CanonicalStability CanonicalExpansion

 theorem finite_port_vertex {A V E : Type*} [DecidableEq E]
    (N : Holant.FiniteNetwork A V E 0) (q : E × Bool) (v : V)
    (hv : N.endpoint q.1 q.2 = v) :
    N.vertex v (fun j => decide (N.closedPorts ⟨v,j⟩ = q)) = finitePortLabel N q := by
  obtain ⟨⟨w,j⟩,rfl⟩ := N.closedPorts.surjective q
  have hw : w = v := by simpa only [Holant.FiniteNetwork.endpoint,Prod.eta,Equiv.symm_apply_apply] using hv
  clear hv
  subst v
  unfold finitePortLabel
  rw [N.closedPorts.symm_apply_apply]
  congr 1
  funext i
  exact decide_eq_decide.mpr (by simp only [N.closedPorts.injective.eq_iff,Sigma.mk.inj_iff,heq_eq_eq,true_and])

 theorem conditioned_port_vertex {A V E : Type*} [DecidableEq E]
    (N : Holant.FiniteNetwork A V E 0) (e : E) (a z : Bool)
    (q : Holant.FiniteNetwork.RemainingEdge e × Bool) (v : V)
    (hv : (N.executableConditionEdge e a z).endpoint q.1 q.2 = v) :
    (N.executableConditionEdge e a z).vertex v
      (fun j => decide (N.closedPorts ⟨v,(N.executableRemainingPortEquiv e v j).val⟩ = (q.1.val,q.2))) =
      finitePortLabel (N.executableConditionEdge e a z) q := by
  rw [← finite_port_vertex _ q v hv]
  congr 1
  funext j
  apply decide_eq_decide.mpr
  change (N.closedPorts ⟨v,(N.executableRemainingPortEquiv e v j).val⟩ = (q.1.val,q.2)) ↔
    (⟨(N.closedPorts ⟨v,(N.executableRemainingPortEquiv e v j).val⟩).1,
      (N.executableRemainingPortEquiv e v j).property⟩,
      (N.closedPorts ⟨v,(N.executableRemainingPortEquiv e v j).val⟩).2) = q
  constructor
  · intro h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact congrArg (fun p : E × Bool => p.2) h
  · intro h
    exact congrArg (fun p : Holant.FiniteNetwork.RemainingEdge e × Bool => (p.1.val,p.2)) h

variable {s b : ℕ} {arity : ℕ → ℕ}

 abbrev network (x : ResidualContext.Input s b arity) :=
  (ResidualContext.source x).val.labelNetwork (ResidualContext.source x).property
 abbrev residual (a z : Bool) (x : ResidualContext.Input s b arity) :=
  ((network x).asFinite.executableConditionEdge (ResidualContext.edge x) a z).orderedNetwork

 theorem unused (x : ResidualContext.Input s b arity) : UnusedRows (network x) (ResidualContext.edge x) :=
  x.property

/-- A stored surviving original endpoint is the exact port coefficient of the
actual conditioned network, at the vertex named in the physical query. -/
 theorem stored_port (flip a z : Bool) (x : ResidualStoredCoefficient.Input s b arity)
    (d : Holant.FiniteNetwork.RemainingEdge x.val.2) (side : Bool)
    (hp : ParentCoefficient.parent flip x.val.1 = some (d.val,side))
    (hv : (((x.val.1.val.1.1.val.labelNetwork x.val.1.val.1.1.property).asFinite).executableConditionEdge x.val.2 a z).endpoint d side = x.val.1.val.1.2) :
    ResidualStoredCoefficient.value flip a z x =
      finitePortLabel (((x.val.1.val.1.1.val.labelNetwork x.val.1.val.1.1.property).asFinite).executableConditionEdge x.val.2 a z) (d,side) := by
  rw [ResidualStoredCoefficient.value_conditioned]
  rw [← conditioned_port_vertex _ x.val.2 a z (d,side) x.val.1.val.1.2 hv]
  congr 1
  funext j
  simp only [ResidualParentCoefficient.survivingWord,ResidualStoredCoefficient.prepared,hp,Option.some.injEq]
  exact decide_eq_decide.mpr eq_comm

 theorem residual_zero (a z : Bool) (x : ResidualContext.Input s b arity)
    (v : (residual a z x).incidenceGraph.Vertex) :
    ResidualOriginalCoefficient.zeroValue a z ⟨x,residualVertexMap (network x) (ResidualContext.edge x) a z v⟩ =
      zeroLabel (residual a z x) v :=
  ResidualOriginalCoefficient.zero_conditioned a z _

 theorem row_some (a z : Bool) (x : ResidualContext.Input s b arity)
    (v : (residual a z x).incidenceGraph.Vertex)
    (d : (residual a z x).incidenceGraph.Edge) (side : Bool)
    (hp : ((residual a z x).incidenceGraph.parentRow v).parent = some (d.val,side)) :
    ((network x).incidenceGraph.parentRow
      (residualVertexMap (network x) (ResidualContext.edge x) a z v)).parent =
      some ((residualEdgeMap (network x) (ResidualContext.edge x) a z d).val,side) := by
  obtain ⟨d',hd,hh⟩ := residual_row_some (network x) (ResidualContext.edge x) a z (unused x) v _ hp
  have he : d' = d := Fin.ext hd
  subst d'
  exact hh

 theorem residual_parent (a z : Bool) (x : ResidualContext.Input s b arity)
    (v : (residual a z x).incidenceGraph.Vertex)
    (d : (residual a z x).incidenceGraph.Edge) (side : Bool)
    (hp : ((residual a z x).incidenceGraph.parentRow v).parent = some (d.val,side))
    (hv : (residual a z x).incidenceGraph.endpoint d side = v) :
    ResidualOriginalCoefficient.parentValue a z
      ⟨x,residualVertexMap (network x) (ResidualContext.edge x) a z v⟩ =
      portLabel (residual a z x) ((residual a z x).incidenceGraphEdgeEquiv d,side) := by
  rw [ordered_port]
  apply stored_port false
  · have hh := row_some a z x v d side hp
    exact (ParentCoefficient.parent_some false _ _ hh).trans (congrArg some (Prod.ext (Fin.ext rfl) rfl))
  · exact (ordered_endpoint ((network x).asFinite.executableConditionEdge (ResidualContext.edge x) a z) d side).symm.trans
      (congrArg (residualVertexMap (network x) (ResidualContext.edge x) a z) hv)

 theorem residual_child (a z : Bool) (x : ResidualContext.Input s b arity)
    (v child : (residual a z x).incidenceGraph.Vertex)
    (d : (residual a z x).incidenceGraph.Edge) (side : Bool)
    (hp : ((residual a z x).incidenceGraph.parentRow child).parent = some (d.val,side))
    (hv : (residual a z x).incidenceGraph.endpoint d (!side) = v) :
    ResidualActionChild.portValue a z
      ⟨⟨x,residualVertexMap (network x) (ResidualContext.edge x) a z v⟩,
        residualVertexMap (network x) (ResidualContext.edge x) a z child⟩ =
      portLabel (residual a z x) ((residual a z x).incidenceGraphEdgeEquiv d,!side) := by
  rw [ordered_port]
  apply stored_port true
  · have hh := row_some a z x child d side hp
    exact (ParentCoefficient.parent_some true _ _ hh).trans (congrArg some (Prod.ext (Fin.ext rfl) rfl))
  · exact (ordered_endpoint ((network x).asFinite.executableConditionEdge (ResidualContext.edge x) a z) d (!side)).symm.trans
      (congrArg (residualVertexMap (network x) (ResidualContext.edge x) a z) hv)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
