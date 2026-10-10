import Holant.OneHot.Decomposition.Unfolding
import Holant.OneHot.Decomposition.AssemblyIncidence

/-! The unfolded recursive tree retains the original selected-edge adjacency. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Decomposition

variable {K V : Type*}

/-- Map the assembled root and each child-tree address to their original vertices. -/
def assembledVertexMap {n : ℕ} (v : V) (b : Fin n → K) (ts : Fin n → Tree K)
    (f : (i : Fin n) → (ts i).Vertex → V) :
    (Unit ⊕ (Forest.ofFn b ts).Vertex) → V
  | .inl _ => v
  | .inr x => f ((Forest.ofFnVertex b ts) x).1 ((Forest.ofFnVertex b ts) x).2

/-- Compute both endpoint identities in an assembled node, without changing its
child order or any endpoint internal to a child tree. -/
theorem assembledVertexMap_endpoint {n : ℕ} (v : V) (a parent : K)
    (b : Fin n → K) (ts : Fin n → Tree K)
    (f : (i : Fin n) → (ts i).Vertex → V) (e : (Forest.ofFn b ts).Edge) (z : Bool) :
    assembledVertexMap v b ts f
      ((Tree.node a parent (Forest.ofFn b ts)).portInv (.inr (e, z))).1 =
      match (Forest.ofFnEdge b ts) e with
      | ⟨i, .inl _⟩ => if z then v else f i ((ts i).portInv (.inl 0)).1
      | ⟨i, .inr g⟩ => f i ((ts i).portInv (.inr (g, z))).1 := by
  let phi : (Unit ⊕ Σ i, (ts i).Vertex) → V :=
    Sum.elim (fun _ => v) (fun q => f q.1 q.2)
  calc
    _ = phi (Sum.map id (Forest.ofFnVertex b ts)
        ((Forest.ofFn b ts).endpointVertex e z)) := by
      unfold Forest.endpointVertex
      cases hp : (Forest.ofFn b ts).portInv (e, z) <;>
        simp [Tree.portInv, hp, assembledVertexMap, phi]
    _ = phi (match (Forest.ofFnEdge b ts) e with
      | ⟨i, .inl _⟩ => if z then .inl () else .inr ⟨i, ((ts i).portInv (.inl 0)).1⟩
      | ⟨i, .inr g⟩ => .inr ⟨i, ((ts i).portInv (.inr (g, z))).1⟩) :=
        congrArg phi (Forest.endpointVertex_ofFn b ts e z)
    _ = _ := by
      generalize (Forest.ofFnEdge b ts) e = q
      rcases q with ⟨i, u | g⟩
      · cases z <;> rfl
      · rfl

end Holant.OneHot.Decomposition

namespace Holant.OneHot.Decomposition.RootedSpanning

variable {V E K : Type*} {endpoint : E → Bool → V} {root : V}
variable (t : RootedSpanning endpoint root) [Fintype V]

open scoped Classical

/-- Every unfolded internal edge retains exactly its original child/parent
vertices. No claim about mere abstract tree counts substitutes for adjacency. -/
theorem unfold_parent_endpoints (a b : V → K) (port : {v : V // v ≠ root} → K)
    (v : V) : ∀ e : (t.unfold a b port v).tree.Edge,
    t.parent (((t.unfold a b port v).vertices
      (((t.unfold a b port v).tree.portInv (.inr (e, false))).1)).1) =
      (((t.unfold a b port v).vertices
        (((t.unfold a b port v).tree.portInv (.inr (e, true))).1)).1) := by
  induction v using (measure (fun v => Fintype.card (t.Descendant v))).wf.induction with
  | h v ih =>
    rw [unfold]
    intro e
    let en := (Fintype.equivFin (t.Child v)).symm
    let ts (i : Fin (Fintype.card (t.Child v))) := (t.unfold a b port (en i).1).tree
    let cs (i : Fin (Fintype.card (t.Child v))) := port ⟨(en i).1, (en i).2.1⟩
    let maps (i : Fin (Fintype.card (t.Child v))) (x : (ts i).Vertex) :=
      ((t.unfold a b port (en i).1).vertices x).1
    let ev : (Unit ⊕ (Forest.ofFn cs ts).Vertex) ≃ t.Descendant v :=
      (Equiv.sumCongr (Equiv.refl Unit)
        ((Forest.ofFnVertex cs ts).trans
          ((Equiv.sigmaCongrRight (fun i => (t.unfold a b port (en i).1).vertices)).trans
            (Equiv.sigmaCongrLeft (β := fun u : t.Child v => t.Descendant u.1) en)))).trans
        (t.descendantSplit v)
    have hm (x : Unit ⊕ (Forest.ofFn cs ts).Vertex) :
        (ev x).1 = assembledVertexMap v cs ts maps x := by
      cases x with
      | inl u => cases u; rfl
      | inr x => rfl
    change t.parent (ev
        ((Tree.node (a v) (b v) (Forest.ofFn cs ts)).portInv (.inr (e, false))).1).1 =
      (ev ((Tree.node (a v) (b v) (Forest.ofFn cs ts)).portInv (.inr (e, true))).1).1
    rw [hm, hm]
    rw [assembledVertexMap_endpoint, assembledVertexMap_endpoint]
    generalize he : Forest.ofFnEdge cs ts e = q
    rcases q with ⟨i, u | g⟩
    · change t.parent (maps i ((ts i).portInv (.inl 0)).1) = v
      have hr : ((ts i).portInv (.inl 0)).1 = (ts i).rootVertex := by cases ts i; rfl
      rw [hr]
      change t.parent (((t.unfold a b port (en i).1).vertices
        (t.unfold a b port (en i).1).tree.rootVertex).1) = v
      rw [(t.unfold a b port (en i).1).root_vertex]
      exact (en i).2.2
    · exact ih (en i).1 (t.descendant_card_child_lt v (en i)) g

/-- The child identity and its parent-side singleton weight are retained together
for every actual unfolded edge, including deep descendant edges. -/
theorem unfold_edge_coefficient (a b : V → K) (port : {v : V // v ≠ root} → K)
    (v : V) : ∀ e : (t.unfold a b port v).tree.Edge,
    ∃ u : {v : V // v ≠ root},
      (((t.unfold a b port v).vertices
        (((t.unfold a b port v).tree.portInv (.inr (e, false))).1)).1) = u.1 ∧
      (t.unfold a b port v).tree.portCoefficient
        (((t.unfold a b port v).tree.portInv (.inr (e, true))).1)
        (((t.unfold a b port v).tree.portInv (.inr (e, true))).2) = port u := by
  induction v using (measure (fun v => Fintype.card (t.Descendant v))).wf.induction with
  | h v ih =>
    rw [unfold]
    intro e
    let en := (Fintype.equivFin (t.Child v)).symm
    let ts (i : Fin (Fintype.card (t.Child v))) := (t.unfold a b port (en i).1).tree
    let cs (i : Fin (Fintype.card (t.Child v))) := port ⟨(en i).1, (en i).2.1⟩
    let maps (i : Fin (Fintype.card (t.Child v))) (x : (ts i).Vertex) :=
      ((t.unfold a b port (en i).1).vertices x).1
    let ev : (Unit ⊕ (Forest.ofFn cs ts).Vertex) ≃ t.Descendant v :=
      (Equiv.sumCongr (Equiv.refl Unit)
        ((Forest.ofFnVertex cs ts).trans
          ((Equiv.sigmaCongrRight (fun i => (t.unfold a b port (en i).1).vertices)).trans
            (Equiv.sigmaCongrLeft (β := fun u : t.Child v => t.Descendant u.1) en)))).trans
        (t.descendantSplit v)
    have hm (x : Unit ⊕ (Forest.ofFn cs ts).Vertex) :
        (ev x).1 = assembledVertexMap v cs ts maps x := by
      cases x with
      | inl u => cases u; rfl
      | inr x => rfl
    change ∃ u : {v : V // v ≠ root},
      (ev ((Tree.node (a v) (b v) (Forest.ofFn cs ts)).portInv (.inr (e, false))).1).1 = u.1 ∧
      (Tree.node (a v) (b v) (Forest.ofFn cs ts)).portCoefficient
        ((Tree.node (a v) (b v) (Forest.ofFn cs ts)).portInv (.inr (e, true))).1
        ((Tree.node (a v) (b v) (Forest.ofFn cs ts)).portInv (.inr (e, true))).2 = port u
    rw [hm, assembledVertexMap_endpoint, Tree.portCoefficient_node_endpoint,
      Forest.slotCoefficient_ofFn_true]
    generalize he : Forest.ofFnEdge cs ts e = q
    rcases q with ⟨i, u | g⟩
    · refine ⟨⟨(en i).1, (en i).2.1⟩, ?_, rfl⟩
      change maps i ((ts i).portInv (.inl 0)).1 = (en i).1
      have hr : ((ts i).portInv (.inl 0)).1 = (ts i).rootVertex := by cases ts i; rfl
      rw [hr]
      exact (t.unfold a b port (en i).1).root_vertex
    · exact ih (en i).1 (t.descendant_card_child_lt v (en i)) g

/-- Generated child edges biject with every original non-root vertex. -/
noncomputable def unfoldNonroot (a b : V → K) (port : {v : V // v ≠ root} → K) :
    (t.unfold a b port root).tree.Edge ≃ {v : V // v ≠ root} :=
  (t.unfold a b port root).tree.edgeNonrootEquiv.trans
    (Equiv.subtypeEquiv (t.unfoldVertices a b port) (fun x => by
      simpa only [t.unfoldVertices_root a b port] using
        ((t.unfoldVertices a b port).injective.ne_iff
          (x := x) (y := (t.unfold a b port root).tree.rootVertex)).symm))

/-- The original child identity is read from the actual false endpoint. -/
theorem unfoldNonroot_false_endpoint (a b : V → K) (port : {v : V // v ≠ root} → K)
    (e : (t.unfold a b port root).tree.Edge) :
    (t.unfoldNonroot a b port e).1 = t.unfoldVertices a b port
      (((t.unfold a b port root).tree.portInv (.inr (e, false))).1) := by
  rw [Tree.false_endpoint_eq]
  rfl

/-- The other actual endpoint maps to the genuine original parent vertex. -/
theorem unfoldNonroot_true_endpoint (a b : V → K) (port : {v : V // v ≠ root} → K)
    (e : (t.unfold a b port root).tree.Edge) :
    t.unfoldVertices a b port (((t.unfold a b port root).tree.portInv (.inr (e, true))).1) =
      t.parent (t.unfoldNonroot a b port e).1 := by
  rw [t.unfoldNonroot_false_endpoint]
  exact (t.unfold_parent_endpoints a b port root e).symm

/-- Every generated true endpoint carries its actual original parent-side weight. -/
theorem unfoldNonroot_true_coefficient (a b : V → K) (port : {v : V // v ≠ root} → K)
    (e : (t.unfold a b port root).tree.Edge) :
    (t.unfold a b port root).tree.portCoefficient
      (((t.unfold a b port root).tree.portInv (.inr (e, true))).1)
      (((t.unfold a b port root).tree.portInv (.inr (e, true))).2) =
      port (t.unfoldNonroot a b port e) := by
  obtain ⟨u, hu, hc⟩ := t.unfold_edge_coefficient a b port root e
  have he : t.unfoldNonroot a b port e = u := by
    apply Subtype.ext
    exact (t.unfoldNonroot_false_endpoint a b port e).trans hu
  rw [he]
  exact hc

/-- Every generated false endpoint carries its actual original child-side weight. -/
theorem unfoldNonroot_false_coefficient (a b : V → K) (port : {v : V // v ≠ root} → K)
    (e : (t.unfold a b port root).tree.Edge) :
    (t.unfold a b port root).tree.portCoefficient
      (((t.unfold a b port root).tree.portInv (.inr (e, false))).1)
      (((t.unfold a b port root).tree.portInv (.inr (e, false))).2) =
      b (t.unfoldNonroot a b port e).1 := by
  rw [Tree.portInv_false, t.unfold_portCoefficient]
  change b (((t.unfold a b port root).vertices
    ((t.unfold a b port root).tree.edgeRootEquiv (.inr e))).1) = _
  have he (s : Tree K) (f : s.Edge) :
      s.edgeRootEquiv (.inr f) = (s.edgeNonrootEquiv f).1 := by cases s; rfl
  rw [he]
  rfl

end Holant.OneHot.Decomposition.RootedSpanning
