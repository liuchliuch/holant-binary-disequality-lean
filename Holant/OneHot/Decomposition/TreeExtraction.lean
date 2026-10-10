import Holant.OneHot.Decomposition.UnfoldingIncidence
import Holant.OneHot.Decomposition.ClosedUnfolding
import Holant.OneHot.Decomposition.EndpointTransport
import Holant.OneHot.Decomposition.OriginalPorts

/-!
# Actual ordered-port tree extraction

Input coefficients are read at their literal original port occurrences. The
extracted recursive tree is closed using the genuine root construction. Vertex,
edge, endpoint, local-port and label transport are proved explicitly.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Decomposition

/-- Put the selected child end at false, preserving both original occurrences. -/
def orientFromChild (child : Bool) : Bool ≃ Bool where
  toFun z := if z then !child else child
  invFun z := if z then !child else child
  left_inv z := by cases child <;> cases z <;> rfl
  right_inv z := by cases child <;> cases z <;> rfl

@[simp] theorem orientFromChild_false (b : Bool) : orientFromChild b false = b := rfl
@[simp] theorem orientFromChild_true (b : Bool) : orientFromChild b true = !b := rfl

end Holant.OneHot.Decomposition

namespace Holant.Network

open OneHot OneHot.Decomposition

variable {K : Type*} [CommSemiring K] (N : Network K 0)
variable {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)

open scoped Classical

/-- Read a singleton coefficient at its literal original ordered occurrence. -/
def occurrenceCoefficient (p : Σ v : Fin N.shape.vertices, Fin (N.shape.arity v)) : K :=
  N.vertex p.1 (fun j => decide (j = p.2))

/-- The actual zero-word weight of each original vertex. -/
def treeZero (v : Fin N.shape.vertices) : K := N.vertex v (fun _ => false)

/-- The root's unused virtual-parent coefficient is zero; every actual parent
coefficient is read at its original child endpoint occurrence. -/
noncomputable def treeParent (v : Fin N.shape.vertices) : K :=
  if h : v = root then 0 else N.occurrenceCoefficient (N.shape.closedPorts.symm (t.parentEnd ⟨v, h⟩))

/-- The coefficient on the opposite occurrence of each original selected edge. -/
noncomputable def treeChild (u : {v : Fin N.shape.vertices // v ≠ root}) : K :=
  N.occurrenceCoefficient (N.shape.closedPorts.symm
    ((t.parentEnd u).1, !(t.parentEnd u).2))

/-- The genuine extracted recursive tree, with only original graph coefficients. -/
noncomputable def extractedTree : Tree K :=
  (t.unfold N.treeZero (N.treeParent t) (N.treeChild t) root).tree

/-- Every generated vertex is exactly one original input vertex. -/
noncomputable def extractedVertices : (N.extractedTree t).Vertex ≃ Fin N.shape.vertices :=
  t.unfoldVertices N.treeZero (N.treeParent t) (N.treeChild t)

/-- Every generated edge identifies its original non-root child. -/
noncomputable def extractedChildren : (N.extractedTree t).Edge ≃
    {v : Fin N.shape.vertices // v ≠ root} :=
  t.unfoldNonroot N.treeZero (N.treeParent t) (N.treeChild t)

/-- In the tree-count case every original edge is represented exactly once. -/
noncomputable def extractedEdges (h : Function.Surjective t.parentEdge) :
    (N.extractedTree t).Edge ≃ Fin N.shape.edges :=
  (N.extractedChildren t).trans (Equiv.ofBijective t.parentEdge ⟨t.parentEdge_injective, h⟩)

/-- Each generated edge retains its original false/true endpoint orientation. -/
noncomputable def extractedOrientations (e : (N.extractedTree t).Edge) : Bool ≃ Bool :=
  orientFromChild (t.parentEnd (N.extractedChildren t e)).2

/-- Actual endpoint-level transport from the closed extracted tree to the input. -/
noncomputable def extractedEndpointTransport (h : Function.Surjective t.parentEdge) :
    FiniteNetwork.EndpointTransport (N.extractedTree t).closedFiniteNetwork N.asFinite where
  vertices := N.extractedVertices t
  edges := N.extractedEdges t h
  orientations := N.extractedOrientations t
  endpoints e z := by
    let u := N.extractedChildren t e
    change N.shape.endpoint (t.parentEdge u) (orientFromChild (t.parentEnd u).2 z) = _
    change N.shape.endpoint (t.parentEdge u) (orientFromChild (t.parentEnd u).2 z) =
      N.extractedVertices t (((N.extractedTree t).closedFiniteNetwork.ports.symm (.inr (e, z))).1)
    rw [Tree.closed_ports_endpoint]
    cases z with
    | false =>
      rw [orientFromChild_false]
      exact (t.child_endpoint u).trans
        (t.unfoldNonroot_false_endpoint N.treeZero (N.treeParent t) (N.treeChild t) e)
    | true =>
      rw [orientFromChild_true]
      have hp : N.shape.endpoint (t.parentEdge u) (!(t.parentEnd u).2) = t.parent u.1 := by
        simp only [RootedSpanning.parent, dite_eq_right u.2, RootedSpanning.parentEdge]
      exact hp.trans
        (t.unfoldNonroot_true_endpoint N.treeZero (N.treeParent t) (N.treeChild t) e).symm

/-- Both retained singleton weights are the literal input endpoint coefficients. -/
theorem extracted_endpoint_coefficient (h : Function.Surjective t.parentEdge)
    (e : (N.extractedTree t).Edge) (z : Bool) :
    (N.extractedTree t).closedPortCoefficient
      (((N.extractedTree t).closedFiniteNetwork.closedPorts.symm (e, z)).1)
      (((N.extractedTree t).closedFiniteNetwork.closedPorts.symm (e, z)).2) =
      N.occurrenceCoefficient (N.shape.closedPorts.symm
        ((N.extractedEndpointTransport t h).ends (e, z))) := by
  change (N.extractedTree t).closedPortCoefficient
    (((N.extractedTree t).closedFiniteNetwork.ports.symm (.inr (e, z))).1)
    (((N.extractedTree t).closedFiniteNetwork.ports.symm (.inr (e, z))).2) = _
  rw [Tree.closedPortCoefficient_endpoint]
  cases z with
  | false =>
    refine (t.unfoldNonroot_false_coefficient N.treeZero (N.treeParent t) (N.treeChild t) e).trans ?_
    let u := N.extractedChildren t e
    change N.treeParent t u.1 = N.occurrenceCoefficient (N.shape.closedPorts.symm
      (t.parentEdge u, (t.parentEnd u).2))
    simp only [treeParent, dite_eq_right u.2, RootedSpanning.parentEdge]
  | true =>
    exact t.unfoldNonroot_true_coefficient N.treeZero (N.treeParent t) (N.treeChild t) e

/-- The derived local port bijection preserves every original singleton coefficient. -/
theorem extracted_port_coefficient (h : Function.Surjective t.parentEdge)
    (v : (N.extractedTree t).Vertex)
    (i : Fin ((N.extractedTree t).closedFiniteNetwork.arity v)) :
    (N.extractedTree t).closedPortCoefficient v i =
      N.vertex (N.extractedVertices t v)
        (fun j => decide (j = (N.extractedEndpointTransport t h).ports v i)) := by
  let p : Σ v, Fin ((N.extractedTree t).closedFiniteNetwork.arity v) := ⟨v, i⟩
  let q := (N.extractedTree t).closedFiniteNetwork.closedPorts p
  have hc := N.extracted_endpoint_coefficient t h q.1 q.2
  have hp := (N.extractedEndpointTransport t h).target_occurrence v i
  change (⟨N.extractedVertices t v, (N.extractedEndpointTransport t h).ports v i⟩ :
    Σ w, Fin (N.shape.arity w)) = N.shape.closedPorts.symm
      ((N.extractedEndpointTransport t h).ends q) at hp
  have hc' : (N.extractedTree t).closedPortCoefficient v i =
      N.occurrenceCoefficient (N.shape.closedPorts.symm
        ((N.extractedEndpointTransport t h).ends q)) := by
    let coeff := fun p : (Σ v, Fin ((N.extractedTree t).closedFiniteNetwork.arity v)) =>
      (N.extractedTree t).closedPortCoefficient p.1 p.2
    have hpL := (N.extractedTree t).closedFiniteNetwork.closedPorts.symm_apply_apply p
    exact (congrArg coeff hpL).symm.trans hc
  exact hc'.trans (congrArg N.occurrenceCoefficient hp.symm)

end Holant.Network
