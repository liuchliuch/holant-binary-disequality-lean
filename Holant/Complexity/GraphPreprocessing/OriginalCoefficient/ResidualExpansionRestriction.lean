import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionComponents

/-! Literal ordered local-port transport through original component restriction
and through executable conditioning. These identities preserve coefficient
labels and every original assignment coordinate. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation
open Holant.OneHot.StackProgram Holant.OneHot.Decomposition
open CanonicalStability CanonicalExpansion

 theorem ordered_route {A V E : Type*} [Fintype V] [Fintype E] [LinearOrder V] [LinearOrder E]
    (N : Holant.FiniteNetwork A V E 0)
    (v : N.orderedNetwork.incidenceGraph.Vertex) (j : Fin (N.orderedNetwork.shape.arity v)) :
    (orderedEdgeMap N (N.orderedNetwork.incidenceGraphEdgeEquiv.symm
      (N.orderedNetwork.shape.closedPorts ⟨v,j⟩).1),
      (N.orderedNetwork.shape.closedPorts ⟨v,j⟩).2) =
      N.closedPorts ⟨orderedVertexMap N v,j⟩ := by
  cases hp : N.ports ⟨orderedVertexMap N v,j⟩ with
  | inl q => exact Fin.elim0 q
  | inr q =>
    simp [orderedEdgeMap,orderedVertexMap,Holant.Network.incidenceGraphEdgeEquiv,
    Holant.NetworkShape.closedPorts,Holant.FiniteNetwork.orderedNetwork,
    Holant.FiniteNetwork.enumerate,Holant.FiniteNetwork.closedPorts,Equiv.emptySum,Equiv.sigmaCongrLeft] at hp ⊢
    erw [hp]
    simp

 def componentOriginalEdge {A : Type*} (N : Holant.Network A 0) (root : Fin N.shape.vertices)
    (e : Fin (N.computedComponentNetwork root).shape.edges) : Fin N.shape.edges :=
  N.incidenceGraphEdgeEquiv (componentEdgeMap N root ((N.computedComponentNetwork root).incidenceGraphEdgeEquiv.symm e))

 theorem componentOriginalEdge_injective {A : Type*} (N : Holant.Network A 0) (root : Fin N.shape.vertices) :
    Function.Injective (componentOriginalEdge N root) :=
  N.incidenceGraphEdgeEquiv.injective.comp ((componentEdgeMap N root).injective.comp
    (N.computedComponentNetwork root).incidenceGraphEdgeEquiv.symm.injective)

 theorem component_route {A : Type*} (N : Holant.Network A 0) (root : Fin N.shape.vertices)
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex)
    (j : Fin ((N.computedComponentNetwork root).shape.arity v)) :
    (componentOriginalEdge N root (((N.computedComponentNetwork root).shape.closedPorts ⟨v,j⟩).1),
      (((N.computedComponentNetwork root).shape.closedPorts ⟨v,j⟩).2)) =
      N.shape.closedPorts ⟨componentVertexMap N root v,j⟩ := by
  have h := congrArg (fun q : N.incidenceGraph.FiberEdge root × Bool => (N.incidenceGraphEdgeEquiv q.1.val,q.2))
    (ordered_route (N.computedComponent root) v j)
  exact h.trans rfl

/-- The two removed occurrences receive their own bits; an optional surviving
original occurrence receives the one singleton bit. -/
 def conditionedOriginalWord {A V E : Type*} [DecidableEq E]
    (N : Holant.FiniteNetwork A V E 0) (cut : E) (a z : Bool)
    (p : Option (E × Bool)) (v : V) : Fin (N.arity v) → Bool :=
  fun j => if (N.closedPorts ⟨v,j⟩).1 = cut then
    (if (N.closedPorts ⟨v,j⟩).2 then z else a)
  else decide (p = some (N.closedPorts ⟨v,j⟩))

 def conditionedOriginalCoefficient {A V E : Type*} [DecidableEq E]
    (N : Holant.FiniteNetwork A V E 0) (cut : E) (a z : Bool)
    (p : Option (E × Bool)) (v : V) : A :=
  N.vertex v (conditionedOriginalWord N cut a z p v)

 theorem conditioned_selected_original {A V E : Type*} [DecidableEq E]
    (N : Holant.FiniteNetwork A V E 0) (cut : E) (a z : Bool)
    (p : Option (E × Bool)) (v : V) :
    (N.executableConditionEdge cut a z).vertex v
      (fun j => decide (p = some (N.closedPorts ⟨v,(N.executableRemainingPortEquiv cut v j).val⟩))) =
      conditionedOriginalCoefficient N cut a z p v := by
  apply congrArg (N.vertex v)
  funext j
  by_cases h : (N.closedPorts ⟨v,j⟩).1 = cut
  · simp only [conditionedOriginalWord,h,↓reduceDIte,↓reduceIte]
  · simp only [conditionedOriginalWord,h,↓reduceDIte,↓reduceIte]
    change decide (p = some (N.closedPorts ⟨v,(N.executableRemainingPortEquiv cut v
      ((N.executableRemainingPortEquiv cut v).symm ⟨j,h⟩)).val⟩)) = _
    rw [Equiv.apply_symm_apply]

 theorem conditioned_zero_original {A V E : Type*} [DecidableEq E]
    (N : Holant.FiniteNetwork A V E 0) (cut : E) (a z : Bool) (v : V) :
    (N.executableConditionEdge cut a z).vertex v (fun _ => false) =
      conditionedOriginalCoefficient N cut a z none v :=
  conditioned_selected_original N cut a z none v

 theorem conditioned_port_original {A V E : Type*} [DecidableEq E]
    (N : Holant.FiniteNetwork A V E 0) (cut : E) (a z : Bool)
    (q : Holant.FiniteNetwork.RemainingEdge cut × Bool) :
    finitePortLabel (N.executableConditionEdge cut a z) q =
      conditionedOriginalCoefficient N cut a z (some (q.1.val,q.2)) (N.endpoint q.1.val q.2) := by
  have hv : (N.executableConditionEdge cut a z).endpoint q.1 q.2 = N.endpoint q.1.val q.2 := by
    rw [Holant.FiniteNetwork.executableConditionEdge_eq,Holant.FiniteNetwork.conditionEdge_endpoint]
  rw [← conditioned_port_vertex N cut a z q _ hv,← conditioned_selected_original]
  congr 1
  funext j
  exact decide_eq_decide.mpr (by simp only [Option.some.injEq,eq_comm])

 theorem component_conditioned_original {A : Type*} (N : Holant.Network A 0)
    (root : Fin N.shape.vertices) (cut : Fin (N.computedComponentNetwork root).shape.edges)
    (a z : Bool) (p : Option (Fin (N.computedComponentNetwork root).shape.edges × Bool))
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    conditionedOriginalCoefficient (N.computedComponentNetwork root).asFinite cut a z p v =
      conditionedOriginalCoefficient N.asFinite (componentOriginalEdge N root cut) a z
        (p.map (fun q => (componentOriginalEdge N root q.1,q.2))) (componentVertexMap N root v) := by
  apply congrArg (N.vertex (componentVertexMap N root v))
  funext j
  unfold conditionedOriginalWord
  change (if ((N.computedComponentNetwork root).shape.closedPorts ⟨v,j⟩).1 = cut then
    (if ((N.computedComponentNetwork root).shape.closedPorts ⟨v,j⟩).2 then z else a)
    else decide (p = some ((N.computedComponentNetwork root).shape.closedPorts ⟨v,j⟩))) = _
  have hroute := component_route N root v j
  change _ = (if (N.shape.closedPorts ⟨componentVertexMap N root v,j⟩).1 = componentOriginalEdge N root cut then
    (if (N.shape.closedPorts ⟨componentVertexMap N root v,j⟩).2 then z else a)
    else decide (p.map (fun q => (componentOriginalEdge N root q.1,q.2)) =
      some (N.shape.closedPorts ⟨componentVertexMap N root v,j⟩)))
  rw [← hroute]
  simp only [(componentOriginalEdge_injective N root).eq_iff]
  congr 1
  apply decide_eq_decide.mpr
  cases p with
  | none => simp
  | some q => simp only [Option.map_some,Option.some.injEq,
      (componentOriginalEdge_injective N root).eq_iff,Prod.ext_iff]

 theorem component_original_endpoint {A : Type*} (N : Holant.Network A 0) (root : Fin N.shape.vertices)
    (d : Fin (N.computedComponentNetwork root).shape.edges) (side : Bool) :
    componentVertexMap N root ((N.computedComponentNetwork root).asFinite.endpoint d side) =
      N.asFinite.endpoint (componentOriginalEdge N root d) side := by
  have h := component_endpoint N root ((N.computedComponentNetwork root).incidenceGraphEdgeEquiv.symm d) side
  rw [Holant.Network.incidenceGraph_endpoint,Equiv.apply_symm_apply,Holant.Network.incidenceGraph_endpoint] at h
  exact h

 def componentRemainingEdge {A : Type*} (N : Holant.Network A 0) (root : Fin N.shape.vertices)
    (cut : Fin (N.computedComponentNetwork root).shape.edges)
    (d : Holant.FiniteNetwork.RemainingEdge cut) :
    Holant.FiniteNetwork.RemainingEdge (componentOriginalEdge N root cut) :=
  ⟨componentOriginalEdge N root d.val,fun h => d.property (componentOriginalEdge_injective N root h)⟩

 theorem component_conditioned_zero {A : Type*} (N : Holant.Network A 0)
    (root : Fin N.shape.vertices) (cut : Fin (N.computedComponentNetwork root).shape.edges)
    (a z : Bool) (v : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    ((N.computedComponentNetwork root).asFinite.executableConditionEdge cut a z).vertex v (fun _ => false) =
      (N.asFinite.executableConditionEdge (componentOriginalEdge N root cut) a z).vertex
        (componentVertexMap N root v) (fun _ => false) := by
  rw [conditioned_zero_original,conditioned_zero_original]
  exact component_conditioned_original N root cut a z none v

/-- Restricting the original component before inserting the two cut bits gives
exactly the same original coefficient label at every surviving oriented port. -/
 theorem component_conditioned_port {A : Type*} (N : Holant.Network A 0)
    (root : Fin N.shape.vertices) (cut : Fin (N.computedComponentNetwork root).shape.edges)
    (a z : Bool) (q : Holant.FiniteNetwork.RemainingEdge cut × Bool) :
    finitePortLabel ((N.computedComponentNetwork root).asFinite.executableConditionEdge cut a z) q =
      finitePortLabel (N.asFinite.executableConditionEdge (componentOriginalEdge N root cut) a z)
        (componentRemainingEdge N root cut q.1,q.2) := by
  rw [conditioned_port_original,conditioned_port_original,component_conditioned_original]
  rw [component_original_endpoint]
  rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
