import Holant.Complexity.GraphPreprocessing.CanonicalStability.RawNetwork

/-! Literal original zero and singleton labels under the actual component
port bijections. Vertex IDs may change; local argument positions do not. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalExpansion
open Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation
open Holant.OneHot.StackProgram CanonicalStability
variable {A : Type*}

/-- The actual original coefficient at a selected oriented port occurrence. -/
def portLabel (N : Holant.Network A 0) (q : Fin N.shape.edges × Bool) : A :=
  N.vertex (N.shape.closedPorts.symm q).1 (fun j => decide (j = (N.shape.closedPorts.symm q).2))

def zeroLabel (N : Holant.Network A 0) (v : Fin N.shape.vertices) : A :=
  N.vertex v (fun _ => false)

 theorem component_zero (N : Holant.Network A 0) (root : Fin N.shape.vertices)
    (v : (N.computedComponentNetwork root).incidenceGraph.Vertex) :
    zeroLabel (N.computedComponentNetwork root) v = zeroLabel N (componentVertexMap N root v) := rfl

/-- Singleton coefficients commute with a genuine dependent port reindexing. -/
 theorem coefficient_reindex {V W : Type*} (arity : V → ℕ)
    (f : (v : V) → (Fin (arity v) → Bool) → A) (e : W ≃ V)
    (p : (v : V) × Fin (arity v)) :
    f (e ((Equiv.sigmaCongrLeft (β := fun v => Fin (arity v)) e).symm p).1)
      (fun j => decide (j = ((Equiv.sigmaCongrLeft (β := fun v => Fin (arity v)) e).symm p).2)) =
      f p.1 (fun j => decide (j = p.2)) := by
  obtain ⟨q,rfl⟩ := (Equiv.sigmaCongrLeft (β := fun v => Fin (arity v)) e).surjective p
  exact congrArg (fun q' : (w : W) × Fin (arity (e w)) =>
    f (e q'.1) (fun j => decide (j = q'.2))) ((Equiv.sigmaCongrLeft (β := fun v => Fin (arity v)) e).symm_apply_apply q)

 def finitePortLabel {V E : Type*} (N : Holant.FiniteNetwork A V E 0) (q : E × Bool) : A :=
  N.vertex (N.closedPorts.symm q).1 (fun j => decide (j = (N.closedPorts.symm q).2))

 theorem ordered_port {V E : Type*} [Fintype V] [Fintype E] [LinearOrder V] [LinearOrder E]
    (N : Holant.FiniteNetwork A V E 0) (d : N.orderedNetwork.incidenceGraph.Edge) (z : Bool) :
    portLabel N.orderedNetwork (N.orderedNetwork.incidenceGraphEdgeEquiv d,z) =
      finitePortLabel N (orderedEdgeMap N d,z) :=
  coefficient_reindex N.arity N.vertex (Fintype.orderIsoFinOfCardEq V rfl).toEquiv
    (N.closedPorts.symm (orderedEdgeMap N d,z))

 theorem component_port (N : Holant.Network A 0) (root : Fin N.shape.vertices)
    (d : (N.computedComponentNetwork root).incidenceGraph.Edge) (z : Bool) :
    portLabel (N.computedComponentNetwork root)
      ((N.computedComponentNetwork root).incidenceGraphEdgeEquiv d,z) =
      portLabel N (N.incidenceGraphEdgeEquiv (componentEdgeMap N root d),z) := by
  exact (ordered_port (N.computedComponent root) d z).trans rfl

end Holant.Complexity.GraphPreprocessing.CanonicalExpansion
