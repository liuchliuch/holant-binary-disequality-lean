import Holant.NetworkGluing.Finite
import Holant.Holographic
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalAlgebra

/-! Exact analytic transport for an open finite network. This file makes no
claim that its change-of-coordinate matrices are available gadget resources. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTransport
variable {V E : Type*} [Fintype V] [Fintype E] {n : ℕ}

def assignments (N : FiniteNetwork ℂ V E n) :
    ((Fin n → Bool) × ((E × Bool) → Bool)) ≃
      ((v : V) → Fin (N.arity v) → Bool) :=
  (Equiv.sumArrowEquivProdArrow (Fin n) (E × Bool) Bool).symm.trans
    ((Equiv.arrowCongr N.ports.symm (Equiv.refl Bool)).trans
      (Equiv.piCurry fun (v : V) (_ : Fin (N.arity v)) => Bool))

omit [Fintype V] [Fintype E] in
theorem assignments_apply (N : FiniteNetwork ℂ V E n)
    (x : Fin n → Bool) (z : E × Bool → Bool) (v : V) (i : Fin (N.arity v)) :
    assignments N (x,z) v i = Sum.elim x z (N.ports ⟨v,i⟩) := rfl

theorem port_product (N : FiniteNetwork ℂ V E n)
    (f : Fin n ⊕ (E × Bool) → ℂ) :
    (∏ v, ∏ i, f (N.ports ⟨v,i⟩)) = (∏ j, f (.inl j)) * ∏ e, f (.inr e) := by
  rw [← Fintype.prod_sigma (fun p => f (N.ports p)), N.ports.prod_comp,
    Fintype.prod_sum_type]

theorem product_action (N : FiniteNetwork ℂ V E n) (M : Kernel ℂ)
    (x : Fin n → Bool) (z : E × Bool → Bool) :
    (∏ v, Signature.coordinateAction (fun _ => M) (N.vertex v)
      (fun i => Sum.elim x z (N.ports ⟨v,i⟩))) =
    ∑ y : Fin n → Bool, ∑ t : E × Bool → Bool,
      (∏ j, M (x j) (y j)) * (∏ e, M (z e) (t e)) *
        ∏ v, N.vertex v (fun i => Sum.elim y t (N.ports ⟨v,i⟩)) := by
  classical
  simp only [Signature.coordinateAction]
  rw [Fintype.prod_sum, ← (assignments N).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib]
  simp only [assignments_apply]
  congr 1
  exact port_product N (fun p => M (Sum.elim x z p) (Sum.elim y t p))

theorem sum_halfEdge_products [DecidableEq (E × Bool)] (f : E → Bool → Bool → ℂ) :
    (∑ z : E × Bool → Bool, ∏ e, f e (z (e,false)) (z (e,true))) =
      ∏ e, ∑ a : Bool, ∑ b : Bool, f e a b := by
  classical
  rw [← (Equiv.curry E Bool Bool).symm.sum_comp]
  change (∑ z : E → Bool → Bool, ∏ e, f e (z e false) (z e true)) = _
  rw [← Fintype.prod_sum (fun e (w : Bool → Bool) => f e (w false) (w true))]
  apply Finset.prod_congr rfl
  intro e _
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_edge_pullback (E' : E → Kernel ℂ) (M : Kernel ℂ) (t : E × Bool → Bool) :
    (∑ z : E × Bool → Bool,
      (∏ e, M (z e) (t e)) * ∏ e, E' e (z (e,false)) (z (e,true))) =
      ∏ e, Kernel.pullback (E' e) M (t (e,false)) (t (e,true)) := by
  simp only [Fintype.prod_prod_type, Fintype.prod_bool]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_halfEdge_products (fun e a b => M b (t (e,true)) * M a (t (e,false)) * E' e a b)]
  apply Finset.prod_congr rfl
  intro e _
  simp [Kernel.pullback,Kernel.mul,Kernel.transpose]
  ring

/-- Transport every actual vertex label, leaving the boundary action explicit. -/
theorem denote_action (N : FiniteNetwork ℂ V E n) (M : Kernel ℂ) :
    ({ N with vertex := fun v => Signature.coordinateAction (fun _ => M) (N.vertex v) }).denote =
      Signature.coordinateAction (fun _ => M)
        ({ N with edge := fun e => Kernel.pullback (N.edge e) M }).denote := by
  classical
  funext x
  simp only [FiniteNetwork.denote]
  simp_rw [product_action]
  simp only [Signature.coordinateAction,FiniteNetwork.denote]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _ = (∏ j, M (x j) (y j)) *
        (∏ v, N.vertex v (fun i => Sum.elim y t (N.ports ⟨v,i⟩))) *
        (∑ z : E × Bool → Bool,
          (∏ e, M (z e) (t e)) * ∏ e, N.edge e (z (e,false)) (z (e,true))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [sum_edge_pullback]; ring

end ExceptionalTransport
end Holant.ReedMuller.WeightTwoIntegration
