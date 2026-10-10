import Holant.Proofs.Traversal.ArityTwo.TraceWeights


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
open Holant Holant.Complexity PortWalk
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

noncomputable def liftAssignment (root : Fin r.vertices.length)
    (z : ((r.shape h).ComponentEdge (Comp r h root) × Bool) → Bool) (p : r.Ports arity) : Bool :=
  if hp : (r.shape h).componentOf p.1 = Comp r h root then
    z (componentPortEquiv r h root ⟨p,hp⟩) else false

theorem lift_vertex (root : Fin r.vertices.length)
    (z : ((r.shape h).ComponentEdge (Comp r h root) × Bool) → Bool)
    (v : (r.shape h).ComponentVertex (Comp r h root)) (j : Fin ((r.shape h).arity v.val)) :
    liftAssignment r h root z ⟨v.val,j⟩ = z ((r.shape h).componentClosedPorts (Comp r h root) ⟨v,j⟩) := by
  simp only [liftAssignment,dif_pos v.property]
  rfl

theorem lift_edge (root : Fin r.vertices.length)
    (z : ((r.shape h).ComponentEdge (Comp r h root) × Bool) → Bool)
    (e : (r.shape h).ComponentEdge (Comp r h root)) (side : Bool) :
    liftAssignment r h root z (r.lookup h (e.val,side)) = z (e,side) := by
  have hp : (r.shape h).componentOf (r.lookup h (e.val,side)).1 = Comp r h root := by
    rw [r.lookup_vertex h,(r.shape h).componentOf_endpoint]
    exact e.property
  rw [liftAssignment,dif_pos hp]
  apply congrArg z
  apply Prod.ext
  · apply Subtype.ext
    change (r.route h (r.lookup h (e.val,side))).1 = e.val
    simp
  · change (r.route h (r.lookup h (e.val,side))).2 = side
    simp

theorem prod_get {X K : Type*} [CommMonoid K] (xs : List X) (f : X → K) :
    (∏ i : Fin xs.length, f (xs.get i)) = (xs.map f).prod := by
  rw [← List.prod_ofFn]
  change (List.ofFn (f ∘ xs.get)).prod = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem prod_listFiber {X K : Type*} [Fintype X] [CommMonoid K]
    (xs : List X) (hn : xs.Nodup) (P : X → Prop) [DecidablePred P]
    (hm : ∀ x, x ∈ xs ↔ P x) (f : X → K) :
    (∏ x : {x // P x}, f x.val) = (xs.map f).prod := by
  rw [← (listFiberEquiv xs hn P hm).prod_comp (fun x => f x.val)]
  exact prod_get xs f

variable {K : Type} [CommSemiring K]
variable (signatures : (i : Fin s) → Signature K (arity i.val)) (kernels : Fin b → Kernel K)

def occurrenceVertex (v : Fin r.vertices.length) := signatures (r.signatureLabel h v)
def occurrenceEdge (e : Fin r.edges.length) := kernels (r.edgeLabel h e)

noncomputable def listTerm (root : Fin r.vertices.length)
    (xs outs : List (r.Ports arity))
    (z : ((r.shape h).ComponentEdge (Comp r h root) × Bool) → Bool) : K :=
  (xs.map (vertexWeight r (occurrenceVertex r h signatures) id (liftAssignment r h root z))).prod *
    (outs.map (edgeWeight r h (occurrenceEdge r h kernels) id (liftAssignment r h root z))).prod

theorem component_sum_lists (root : Fin r.vertices.length) (xs outs : List (r.Ports arity))
    (hv : (xs.map Sigma.fst).Nodup)
    (hvm : ∀ v, v ∈ xs.map Sigma.fst ↔ (r.shape h).componentOf v = Comp r h root)
    (he : (outs.map (fun p => (r.route h p).1)).Nodup)
    (hem : ∀ e, e ∈ outs.map (fun p => (r.route h p).1) ↔ (r.shape h).edgeComponent e = Comp r h root) :
    ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h root)).denote Fin.elim0 =
      ∑ z, listTerm r h signatures kernels root xs outs z := by
  classical
  rw [Network.denote_componentFiniteNetwork]
  apply Finset.sum_congr rfl
  intro z _
  unfold Network.componentTerm listTerm
  apply congrArg₂ (· * ·)
  · calc
      _ = ∏ v : (r.shape h).ComponentVertex (Comp r h root),
          signatures (r.signatureLabel h v.val) (fun j => liftAssignment r h root z ⟨v.val,j⟩) := by
            apply Finset.prod_congr rfl
            intro v _
            congr 1
            funext j
            exact (lift_vertex r h root z v j).symm
      _ = _ := by
        have heq := prod_listFiber (xs.map Sigma.fst) hv _ hvm
          (fun v => signatures (r.signatureLabel h v) (fun j => liftAssignment r h root z ⟨v,j⟩))
        simp only [List.map_map,Function.comp_def] at heq
        convert heq using 1 <;> rfl
  · calc
      _ = ∏ e : (r.shape h).ComponentEdge (Comp r h root),
          kernels (r.edgeLabel h e.val)
            (liftAssignment r h root z (r.lookup h (e.val,false)))
            (liftAssignment r h root z (r.lookup h (e.val,true))) := by
            apply Finset.prod_congr rfl
            intro e _
            rw [lift_edge,lift_edge]
            rfl
      _ = _ := by
        have heq := prod_listFiber (outs.map (fun p => (r.route h p).1)) he _ hem
          (fun e => kernels (r.edgeLabel h e)
            (liftAssignment r h root z (r.lookup h (e,false)))
            (liftAssignment r h root z (r.lookup h (e,true))))
        simp only [List.map_map,Function.comp_def] at heq
        convert heq using 1 <;> rfl

theorem path_component_sum (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    let xs := (walk r h (2*r.edges.length+1) [p] (cross r h p)).1
    ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h p.1)).denote Fin.elim0 =
      ∑ z, listTerm r h signatures kernels p.1 (p::xs) (p::departures r xs) z :=
  component_sum_lists r h signatures kernels p.1 _ _ (path_completion r h hd p hp).2.2
    (fun v => (path_vertex_coverage r h hd p hp v).trans (vertex_fiber r h p v))
    (path_edge_ids_nodup r h hd p hp)
    (fun e => (path_edge_exact r h hd p hp e).trans (edge_fiber r h p e))

theorem cycle_component_sum (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1) :
    let xs := (walk r h (2*r.edges.length+1) [] p).1
    ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h p.1)).denote Fin.elim0 =
      ∑ z, walkWeight r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels) id
        (liftAssignment r h p.1 z) xs :=
  component_sum_lists r h signatures kernels p.1 _ _ (cycle_completion r h hd p hp hu).2.2
    (fun v => (cycle_vertex_coverage r h hd p hp hu v).trans (vertex_fiber r h p v))
    (cycle_edge_ids_nodup r h hd p hp hu)
    (fun e => (cycle_edge_exact r h hd p hp hu e).trans (edge_fiber r h p e))

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
