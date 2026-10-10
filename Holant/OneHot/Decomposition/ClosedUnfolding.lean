import Holant.OneHot.Decomposition.Unfolding
import Holant.OneHot.Decomposition.AssemblyIncidence
import Holant.OneHot.ClosedTree

/-!
# Closing an unfolded tree at its genuine root

The auxiliary recursive parent slot is removed. No pin signature, extra vertex,
or artificial edge is added; the existing verified `Forest.closedNetwork` and
`Forest.closedProgram` are used verbatim.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Tree

variable {K : Type*} [CommSemiring K]

/-- Close the actual root by retaining exactly its child ports. -/
def closedFiniteNetwork : (t : Tree K) → FiniteNetwork K t.Vertex t.Edge 0
  | .node a _ ts => ts.closedFiniteNetwork a

/-- Actual closed graph with its root's virtual parent port removed. -/
noncomputable def closedNetwork (t : Tree K) : Network K 0 :=
  t.closedFiniteNetwork.toNetwork

/-- Run the existing closed-root arithmetic program. -/
def closedProgram : Tree K → Arithmetic K K
  | .node a _ ts => ts.closedProgram a

/-- The closed graph uses the unoccupied-parent subtree value at its root. -/
theorem denote_closedNetwork (t : Tree K) :
    t.closedNetwork.denote Fin.elim0 = t.denote false := by
  cases t with
  | node a b ts => exact ts.denote_closedNetwork a b

@[simp] theorem closedNetwork_vertices (t : Tree K) :
    t.closedNetwork.shape.vertices = t.vertices := by
  change Fintype.card t.Vertex = t.vertices
  exact t.card_vertex

@[simp] theorem closedNetwork_edges (t : Tree K) :
    t.closedNetwork.shape.edges = t.edges := t.card_edge

/-- Exact actual-network correctness and arithmetic instruction count. -/
theorem closedProgram_network_spec (t : Tree K) :
    t.closedProgram.run =
      (t.closedNetwork.denote Fin.elim0, 3 * t.vertices + 5 * t.edges - 1) := by
  cases t with
  | node a b ts =>
    have h := ts.closedProgram_network_spec a
    rw [ts.closedNetwork_vertices, ts.closedNetwork_edges] at h
    exact h

/-- Removing the virtual parent port changes no original internal endpoint vertex. -/
theorem closed_ports_endpoint (t : Tree K) (e : t.Edge) (z : Bool) :
    (t.closedFiniteNetwork.ports.symm (.inr (e, z))).1 =
      (t.portInv (.inr (e, z))).1 := by
  cases t with
  | node a b ts =>
    change ((ts.closedSlots.symm (ts.portInv (e, z))).1) = _
    cases h : ts.portInv (e, z) <;>
      simp [Tree.portInv, h, Forest.closedSlots]

/-- Literal singleton table at every closed node. -/
def closedPortCoefficient : (t : Tree K) →
    (v : t.Vertex) → Fin (t.closedFiniteNetwork.arity v) → K
  | .node _ _ ts, .inl _ => ts.coefficients
  | .node _ _ ts, .inr v => ts.portCoefficient v

theorem closedLabel_eq_table (t : Tree K) (v : t.Vertex) :
    t.closedFiniteNetwork.vertex v =
      table (t.zeroCoefficient v) (t.closedPortCoefficient v) := by
  cases t with
  | node a b ts =>
    cases v with
    | inl u => rfl
    | inr v => exact ts.label_eq_table v

/-- The zero-word coefficient at every original node is unchanged. -/
theorem closedLabel_zero (t : Tree K) (v : t.Vertex) :
    t.closedFiniteNetwork.vertex v (fun _ => false) = t.zeroCoefficient v := by
  rw [t.closedLabel_eq_table]
  exact table_zero _ _

/-- Every retained internal endpoint keeps exactly its original singleton weight. -/
theorem closedPortCoefficient_endpoint (t : Tree K) (e : t.Edge) (z : Bool) :
    t.closedPortCoefficient (t.closedFiniteNetwork.ports.symm (.inr (e, z))).1
      (t.closedFiniteNetwork.ports.symm (.inr (e, z))).2 =
      t.portCoefficient (t.portInv (.inr (e, z))).1 (t.portInv (.inr (e, z))).2 := by
  cases t with
  | node a b ts =>
    rw [Tree.portCoefficient_node_endpoint]
    change (Tree.node a b ts).closedPortCoefficient
      (ts.closedSlots.symm (ts.portInv (e, z))).1
      (ts.closedSlots.symm (ts.portInv (e, z))).2 = ts.slotCoefficient (ts.portInv (e, z))
    cases ts.portInv (e, z) <;> rfl

end Holant.OneHot.Tree
