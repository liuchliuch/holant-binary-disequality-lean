import Holant.Proofs.Traversal.ArityTwo.EdgeEnumeration
import Holant.OneHot.Decomposition.Factorization


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
open Holant Holant.Complexity PortWalk
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

/-- Proof-side indexing of an already computed duplicate-free list. -/
noncomputable def listFiberEquiv {X : Type*} (xs : List X) (hn : xs.Nodup)
    (P : X → Prop) (hm : ∀ x, x ∈ xs ↔ P x) : Fin xs.length ≃ {x // P x} :=
  Equiv.ofBijective (fun i => ⟨xs.get i,(hm _).mp (List.get_mem xs i)⟩) (by
    constructor
    · intro i j hij
      exact (List.nodup_iff_injective_get.mp hn) (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((hm x.val).mpr x.property)
      exact ⟨i,Subtype.ext hi⟩)

abbrev Comp (v : Fin r.vertices.length) := (r.shape h).componentOf v

theorem vertex_fiber (p : r.Ports arity) (v : Fin r.vertices.length) :
    (r.graph h).label v = (r.graph h).label p.1 ↔ (r.shape h).componentOf v = Comp r h p.1 :=
  r.graph_label_eq_iff h v p.1

theorem edge_fiber (p : r.Ports arity) (e : Fin r.edges.length) :
    (r.graph h).label (r.lookup h (e,false)).1 = (r.graph h).label p.1 ↔
      (r.shape h).edgeComponent e = Comp r h p.1 := by
  rw [r.graph_label_eq_iff h,r.lookup_vertex h]
  rfl

def pathVertices (p : r.Ports arity) : List (Fin r.vertices.length) :=
  (p::(walk r h (2*r.edges.length+1) [p] (cross r h p)).1).map Sigma.fst

def pathEdges (p : r.Ports arity) : List (Fin r.edges.length) :=
  (p::departures r (walk r h (2*r.edges.length+1) [p] (cross r h p)).1).map
    (fun q => (r.route h q).1)

def cycleVertices (p : r.Ports arity) : List (Fin r.vertices.length) :=
  ((walk r h (2*r.edges.length+1) [] p).1).map Sigma.fst

def cycleEdges (p : r.Ports arity) : List (Fin r.edges.length) :=
  (departures r (walk r h (2*r.edges.length+1) [] p).1).map (fun q => (r.route h q).1)

noncomputable def pathVertexEquiv (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    Fin (pathVertices r h p).length ≃ (r.shape h).ComponentVertex (Comp r h p.1) :=
  listFiberEquiv (pathVertices r h p) (path_completion r h hd p hp).2.2 _
    (fun v => (path_vertex_coverage r h hd p hp v).trans (vertex_fiber r h p v))

noncomputable def pathEdgeEquiv (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    Fin (pathEdges r h p).length ≃ (r.shape h).ComponentEdge (Comp r h p.1) :=
  listFiberEquiv (pathEdges r h p) (path_edge_ids_nodup r h hd p hp) _
    (fun e => (path_edge_exact r h hd p hp e).trans (edge_fiber r h p e))

noncomputable def cycleVertexEquiv (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1) :
    Fin (cycleVertices r h p).length ≃ (r.shape h).ComponentVertex (Comp r h p.1) :=
  listFiberEquiv (cycleVertices r h p) (cycle_completion r h hd p hp hu).2.2 _
    (fun v => (cycle_vertex_coverage r h hd p hp hu v).trans (vertex_fiber r h p v))

noncomputable def cycleEdgeEquiv (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1) :
    Fin (cycleEdges r h p).length ≃ (r.shape h).ComponentEdge (Comp r h p.1) :=
  listFiberEquiv (cycleEdges r h p) (cycle_edge_ids_nodup r h hd p hp hu) _
    (fun e => (cycle_edge_exact r h hd p hp hu e).trans (edge_fiber r h p e))

variable {K : Type*} [CommSemiring K]
variable (signatures : (i : Fin s) → Signature K (arity i.val)) (kernels : Fin b → Kernel K)

/-- The ordered expression still quantifies only the original component's
edge ends. Its local argument order is the original component port bijection. -/
noncomputable def indexedTerm (v : Fin r.vertices.length) {nv ne : ℕ}
    (vs : Fin nv ≃ (r.shape h).ComponentVertex (Comp r h v))
    (es : Fin ne ≃ (r.shape h).ComponentEdge (Comp r h v))
    (z : ((r.shape h).ComponentEdge (Comp r h v) × Bool) → Bool) : K :=
  (∏ i, signatures (r.signatureLabel h (vs i).1)
    (fun j => z ((r.shape h).componentClosedPorts (Comp r h v) ⟨vs i,j⟩))) *
    ∏ i, kernels (r.edgeLabel h (es i).1) (z (es i,false)) (z (es i,true))

theorem component_denote_indexed (v : Fin r.vertices.length) {nv ne : ℕ}
    (vs : Fin nv ≃ (r.shape h).ComponentVertex (Comp r h v))
    (es : Fin ne ≃ (r.shape h).ComponentEdge (Comp r h v)) :
    ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h v)).denote Fin.elim0 =
      ∑ z, indexedTerm r h signatures kernels v vs es z := by
  classical
  rw [Network.denote_componentFiniteNetwork]
  apply Finset.sum_congr rfl
  intro z _
  dsimp [Network.componentTerm,indexedTerm,RawClosedNetwork.realize]
  apply congrArg₂ (· * ·)
  · exact (vs.prod_comp _).symm
  · exact (es.prod_comp _).symm

/-- The actual computed path order supplies both bijections. -/
theorem path_denote_ordered (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h p.1)).denote Fin.elim0 =
      ∑ z, indexedTerm r h signatures kernels p.1
        (pathVertexEquiv r h hd p hp) (pathEdgeEquiv r h hd p hp) z :=
  component_denote_indexed r h signatures kernels _ _ _

theorem cycle_denote_ordered (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1) :
    ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h p.1)).denote Fin.elim0 =
      ∑ z, indexedTerm r h signatures kernels p.1
        (cycleVertexEquiv r h hd p hp hu) (cycleEdgeEquiv r h hd p hp hu) z :=
  component_denote_indexed r h signatures kernels _ _ _

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
