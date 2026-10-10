import Holant.Holographic

/-! Open-port extension of the frozen finite-assignment holographic algebra.
The actual port bijection splits transformed assignments into boundary and
internal-edge choices. Internal cancellations reuse Network.sum_edge_action;
free ports retain the literal ordered tensor action instead of scalar invariance.
No gadget availability, compiler, simplicity or nonzero assumption is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.OpenHolographic
open Holant

variable {K : Type} [CommSemiring K] {n : ℕ}

/-- Same incidence and actual ordered labels as the closed frozen transform. -/
def transform (G : Network K n) (M N : Kernel K) : Network K n where
  shape := G.shape
  vertex := fun v => Signature.coordinateAction (fun _ => N) (G.vertex v)
  edge := fun e => Kernel.pullback (G.edge e) M

/-- Every local assignment is exactly one boundary choice and one choice at
each ordered internal edge occurrence, transported through the real ports. -/
def assignments (s : NetworkShape n) :
    ((Fin n → Bool) × ((Fin s.edges × Bool) → Bool)) ≃
      ((v : Fin s.vertices) → Fin (s.arity v) → Bool) :=
  (Equiv.sumArrowEquivProdArrow (Fin n) (Fin s.edges × Bool) Bool).symm.trans
    ((Equiv.arrowCongr s.ports.symm (Equiv.refl Bool)).trans
      (Equiv.piCurry fun (v : Fin s.vertices) (_ : Fin (s.arity v)) => Bool))

@[simp] theorem assignments_apply (s : NetworkShape n)
    (y : Fin n → Bool) (w : (Fin s.edges × Bool) → Bool)
    (v : Fin s.vertices) (i : Fin (s.arity v)) :
    assignments s (y,w) v i = s.assignment y w v i := rfl

/-- Actual local vertex action expansion with ordered FREE ports preserved. -/
theorem prod_vertex_action (s : NetworkShape n)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) (N : Kernel K)
    (x : Fin n → Bool) (z : (Fin s.edges × Bool) → Bool) :
    (∏ v : Fin s.vertices,
      Signature.coordinateAction (fun _ => N) (f v) (s.assignment x z v)) =
    ∑ y : Fin n → Bool, ∑ w : (Fin s.edges × Bool) → Bool,
      ((∏ i : Fin n, N (x i) (y i)) *
        (∏ q : Fin s.edges × Bool, N (z q) (w q))) *
          ∏ v : Fin s.vertices, f v (s.assignment y w v) := by
  classical
  simp only [Signature.coordinateAction]
  rw [Fintype.prod_sum,←(assignments s).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.prod_mul_distrib]
  congr 1
  · change (∏ v : Fin s.vertices, ∏ i : Fin (s.arity v),
      N (s.assignment x z v i) (s.assignment y w v i)) = _
    rw [←Fintype.prod_sigma (fun p : Σ v : Fin s.vertices, Fin (s.arity v) =>
      N (s.assignment x z p.1 p.2) (s.assignment y w p.1 p.2))]
    rw [←s.ports.symm.prod_comp]
    simp only [NetworkShape.assignment,Sigma.eta,Equiv.apply_symm_apply,Fintype.prod_sum_type,
      Sum.elim_inl,Sum.elim_inr]

/-- Exact open-network tensor action: internal edges cancel, but every free
port keeps N. Loops, parallel edges, nullary vertices and scalar components
are all represented by the same incidence shape and actual assignment sum. -/
theorem denote_transform (G : Network K n) (M N : Kernel K)
    (hMN : Kernel.mul M N = Signature.equality) :
    (transform G M N).denote = Signature.coordinateAction (fun _ => N) G.denote := by
  classical
  funext x
  simp only [Network.denote,transform]
  simp_rw [prod_vertex_action]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  calc
    _ = (∏ i : Fin n, N (x i) (y i)) *
        ∑ w : (Fin G.shape.edges × Bool) → Bool,
          (∏ v : Fin G.shape.vertices, G.vertex v (G.shape.assignment y w v)) *
            ∑ z : (Fin G.shape.edges × Bool) → Bool,
              (∏ q : Fin G.shape.edges × Bool, N (z q) (w q)) *
                ∏ e : Fin G.shape.edges,
                  Kernel.pullback (G.edge e) M (z (e,false)) (z (e,true)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ac_rfl
    _ = _ := by
      simp_rw [Network.sum_edge_action G.shape.edges G.edge M N hMN]
      rfl

/-- At n=0 this really is the frozen transform, without an open-domain cast. -/
@[simp] theorem transform_closed (G : Network K 0) (M N : Kernel K) :
    transform G M N = Network.holographicTransform G M N := rfl
end Holant.LocalDrafts.RemoteWork.StableClosureV2.OpenHolographic
