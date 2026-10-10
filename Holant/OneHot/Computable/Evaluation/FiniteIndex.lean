import Holant.OneHot.Computable.Evaluation.RawTree
import Holant.OneHot.Decomposition.FiniteEvaluation

/-! Choice-free finite enumeration and computed parent extraction for residual graphs. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.FiniteNetwork

variable {K V E : Type*} {n : ℕ}

/-- Enumerate using supplied, executable finite equivalences. Original local port
numbers and edge orientations are unchanged. -/
def enumerate {v e : ℕ} (N : FiniteNetwork K V E n)
    (vs : V ≃ Fin v) (es : E ≃ Fin e) : Network K n where
  shape := {
    vertices := v
    arity := fun w => N.arity (vs.symm w)
    edges := e
    ports := (Equiv.sigmaCongrLeft vs.symm).trans
      (N.ports.trans (Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr es (Equiv.refl _)))) }
  vertex := fun w => N.vertex (vs.symm w)
  edge := fun d => N.edge (es.symm d)

/-- Literal finite enumeration preserves the original assignment sum. -/
theorem denote_enumerate [Fintype V] [Fintype E] [CommSemiring K]
    {v e : ℕ} (N : FiniteNetwork K V E n) (vs : V ≃ Fin v) (es : E ≃ Fin e) :
    (N.enumerate vs es).denote = N.denote := by
  classical
  funext x
  unfold Network.denote denote
  apply Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.prodCongr es.symm (Equiv.refl Bool)) (Equiv.refl Bool))
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv vs.symm
    intro w
    congr 1
    funext i
    dsimp [enumerate, NetworkShape.assignment]
    change Sum.elim x z ((Equiv.sumCongr (Equiv.refl _)
      (Equiv.prodCongr es (Equiv.refl _))) (N.ports ⟨vs.symm w, i⟩)) = _
    cases N.ports ⟨vs.symm w, i⟩ <;> rfl
  · apply Fintype.prod_equiv es.symm
    intro d
    simp [enumerate]

/-- Deterministic increasing index enumeration, with no `Fintype.equivFin`. -/
def orderedNetwork [Fintype V] [Fintype E] [LinearOrder V] [LinearOrder E]
    (N : FiniteNetwork K V E n) : Network K n :=
  N.enumerate (Fintype.orderIsoFinOfCardEq V rfl).symm.toEquiv
    (Fintype.orderIsoFinOfCardEq E rfl).symm.toEquiv

theorem denote_orderedNetwork [Fintype V] [Fintype E] [LinearOrder V] [LinearOrder E]
    [CommSemiring K] (N : FiniteNetwork K V E n) : N.orderedNetwork.denote = N.denote :=
  N.denote_enumerate _ _

end Holant.FiniteNetwork

namespace Holant.Network

open OneHot OneHot.Computable OneHot.Decomposition

variable {K : Type*} (N : Network K 0)

/-- Explicit incidence table of any executable input/residual network. -/
def incidenceGraph : Graph where
  vertices := N.shape.vertices
  edges := List.ofFn fun e : Fin N.shape.edges =>
    (N.shape.endpoint e false, N.shape.endpoint e true)

@[simp] theorem incidenceGraph_edges : N.incidenceGraph.edges.length = N.shape.edges := by
  simp [incidenceGraph]

def incidenceGraphEdgeEquiv : N.incidenceGraph.Edge ≃ Fin N.shape.edges :=
  finCongr N.incidenceGraph_edges

theorem incidenceGraph_endpoint (e : N.incidenceGraph.Edge) (z : Bool) :
    N.incidenceGraph.endpoint e z = N.shape.endpoint (N.incidenceGraphEdgeEquiv e) z := by
  cases z <;> simp [Graph.endpoint, incidenceGraph, incidenceGraphEdgeEquiv]
  all_goals congr 1

/-- Computed original-edge parents from finite reachability, for residual networks too. -/
def computedSpanning (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root) :
    RootedSpanning N.shape.endpoint root :=
  transportSpanning (Equiv.refl _) N.incidenceGraphEdgeEquiv
    N.incidenceGraph_endpoint (N.incidenceGraph.connectedSpanning root hc)

theorem computedSpanning_depth_le (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root) (v : Fin N.shape.vertices) :
    (N.computedSpanning root hc).depth v ≤ N.shape.vertices :=
  N.incidenceGraph.connectedSpanning_depth_le root hc v

variable [CommSemiring K]

/-- Executable connected-tree program from actual incidence alone. -/
def computedTreeProgram (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root) :
    Arithmetic K K :=
  (N.executableTree (N.computedSpanning root hc) N.shape.vertices).closedProgram

theorem computedTreeProgram_spec (root : Fin N.shape.vertices)
    (hc : N.incidenceGraph.Connected root)
    (ht : N.shape.edges + 1 = N.shape.vertices)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.computedTreeProgram root hc).run =
      (N.denote Fin.elim0, 3 * N.shape.vertices + 5 * N.shape.edges - 1) :=
  N.executableTree_program_spec (N.computedSpanning root hc) N.shape.vertices
    (N.computedSpanning_depth_le root hc) ht hf hX

end Holant.Network

namespace Holant.Network

open OneHot.Computable OneHot.Decomposition

variable {K : Type*} (N : Network K 0)

/-- The executed finite search uses precisely the network's actual endpoints. -/
theorem incidenceGraph_reach_iff (root v : Fin N.shape.vertices) :
    v ∈ N.incidenceGraph.reach root N.shape.vertices ↔ N.shape.Reachable root v := by
  have hl : Link N.incidenceGraph.endpoint = Link N.shape.endpoint := by
    funext u v
    apply propext
    constructor
    · rintro ⟨e, h₁, h₂⟩
      exact ⟨N.incidenceGraphEdgeEquiv e,
        (N.incidenceGraph_endpoint e false).symm.trans h₁,
        (N.incidenceGraph_endpoint e true).symm.trans h₂⟩
    · rintro ⟨e, h₁, h₂⟩
      refine ⟨N.incidenceGraphEdgeEquiv.symm e, ?_, ?_⟩
      · simpa using (N.incidenceGraph_endpoint (N.incidenceGraphEdgeEquiv.symm e) false).trans h₁
      · simpa using (N.incidenceGraph_endpoint (N.incidenceGraphEdgeEquiv.symm e) true).trans h₂
  exact (N.incidenceGraph.reach_iff root v).trans (by rw [hl]; rfl)

end Holant.Network

namespace Holant.FiniteNetwork

open OneHot OneHot.Decomposition

variable {K V E : Type*}

/-- Both oriented endpoints are preserved by the executable finite relabeling. -/
theorem enumerate_endpoint {v e : ℕ} (N : FiniteNetwork K V E 0)
    (vs : V ≃ Fin v) (es : E ≃ Fin e) (d : E) (z : Bool) :
    (N.enumerate vs es).shape.endpoint (es d) z = vs (N.endpoint d z) := by
  simp [NetworkShape.endpoint, NetworkShape.closedPorts, FiniteNetwork.endpoint,
    FiniteNetwork.closedPorts, enumerate, Equiv.emptySum]
  rfl

variable [Fintype V] [Fintype E] [LinearOrder V] [LinearOrder E]

/-- Increasing enumeration transports the actual original paths. -/
theorem orderedNetwork_connected (N : FiniteNetwork K V E 0) (root : V)
    (hc : ∀ v, Relation.EqvGen (Link N.endpoint) root v) :
    N.orderedNetwork.incidenceGraph.Connected
      ((Fintype.orderIsoFinOfCardEq V rfl).symm root) := by
  intro w
  apply (N.orderedNetwork.incidenceGraph_reach_iff _ _).mpr
  have h := reachable_map (Fintype.orderIsoFinOfCardEq V rfl).symm.toEquiv
    (Fintype.orderIsoFinOfCardEq E rfl).symm.toEquiv
    (N.enumerate_endpoint _ _) (hc (Fintype.orderIsoFinOfCardEq V rfl w))
  exact (Fintype.orderIsoFinOfCardEq V rfl).symm_apply_apply w ▸ h

variable [CommSemiring K]

/-- Build the actual tree after deterministic original-index enumeration. -/
def computedTreeProgram (N : FiniteNetwork K V E 0) (root : V)
    (hc : ∀ v, Relation.EqvGen (Link N.endpoint) root v) : Arithmetic K K :=
  N.orderedNetwork.computedTreeProgram ((Fintype.orderIsoFinOfCardEq V rfl).symm root)
    (N.orderedNetwork_connected root hc)

theorem computedTreeProgram_spec (N : FiniteNetwork K V E 0) (root : V)
    (hc : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (ht : Fintype.card E + 1 = Fintype.card V)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.computedTreeProgram root hc).run =
      (N.denote Fin.elim0, 3 * Fintype.card V + 5 * Fintype.card E - 1) := by
  have hn := N.orderedNetwork.computedTreeProgram_spec
    ((Fintype.orderIsoFinOfCardEq V rfl).symm root)
    (N.orderedNetwork_connected root hc) ht
    (fun v => hf (Fintype.orderIsoFinOfCardEq V rfl v))
    (fun e => hX (Fintype.orderIsoFinOfCardEq E rfl e))
  rw [N.denote_orderedNetwork] at hn
  exact hn

end Holant.FiniteNetwork
