import Holant.Proofs.Traversal.ArityTwo.DescriptorTotal
import Holant.Proofs.Traversal.ArityTwo.RawDenote


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.Descriptors
open Holant Holant.Complexity PortWalk
variable {s b : ℕ} {arity : ℕ → ℕ} {A K : Type} [CommSemiring K]
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (vertex : ∀ v : Fin r.vertices.length, (Fin (degree (arity := arity) r v) → Bool) → A)
variable (edge : Fin r.edges.length → Kernel A) (coeff : A → K)

theorem binaryTable_at_assignment (z : r.Ports arity → Bool) (p out : r.Ports arity)
    (ho : other r p = some out) :
    realizeMatrix coeff (binaryTable r vertex p) (z p) (z out) =
      coeff (vertex p.1 (fun j => z ⟨p.1,j⟩)) := by
  unfold realizeMatrix binaryTable
  congr 1
  congr 1
  funext j
  by_cases hj : j.val = p.2.val
  · have he : (⟨p.1,j⟩ : r.Ports arity) = p := by
      obtain ⟨v,i⟩ := p
      exact congrArg (Sigma.mk v) (Fin.ext hj)
    simp [hj,he]
  · have he : (⟨p.1,j⟩ : r.Ports arity) = out := by
      rcases binary_ports r p out ⟨p.1,j⟩ ho rfl with he | he
      · exact (hj (congrArg (fun q : r.Ports arity => q.2.val) he)).elim
      · exact he
    simp [hj,he]

theorem unaryTable_at_assignment (z : r.Ports arity → Bool) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    coeff (unaryTable r vertex p.1 (z p)) = coeff (vertex p.1 (fun j => z ⟨p.1,j⟩)) := by
  unfold unaryTable
  congr 1
  congr 1
  funext j
  exact congrArg z (same_unary_vertex r p ⟨p.1,j⟩ hp rfl).symm

theorem edgeTable_at_assignment (z : r.Ports arity → Bool) (p : r.Ports arity) :
    realizeMatrix coeff (edgeTable r h edge p) (z p) (z (cross r h p)) =
      coeff (edge (r.route h p).1
        (z (r.lookup h ((r.route h p).1,false))) (z (r.lookup h ((r.route h p).1,true)))) := by
  cases hb : (r.route h p).2 with
  | false =>
    have hp : r.lookup h ((r.route h p).1,false) = p := by
      have he : r.route h p = ((r.route h p).1, false) := Prod.ext rfl hb
      rw [← he]
      exact r.lookup_route h p
    have hc : cross r h p = r.lookup h ((r.route h p).1,true) := by simp [cross,hb]
    simp [realizeMatrix,edgeTable,orient,hb,hp,hc]
  | true =>
    have hp : r.lookup h ((r.route h p).1,true) = p := by
      have he : r.route h p = ((r.route h p).1, true) := Prod.ext rfl hb
      rw [← he]
      exact r.lookup_route h p
    have hc : cross r h p = r.lookup h ((r.route h p).1,false) := by simp [cross,hb]
    simp [realizeMatrix,edgeTable,orient,hb,Kernel.transpose,hp,hc]

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.Descriptors

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
open Holant Holant.Complexity
open scoped BigOperators
variable {s b : ℕ} {arity : ℕ → ℕ} {K : Type*} [CommSemiring K]
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (signatures : (i : Fin s) → Signature K (arity i.val)) (kernels : Fin b → Kernel K)

/-- All original local-port bits are independent variables of the defining
sum. This is the actual inverse incidence permutation, not an endpoint oracle. -/
theorem raw_denote_port_sum :
    (r.realize h signatures kernels).denote Fin.elim0 =
      ∑ z : r.Ports arity → Bool,
        (∏ v, signatures (r.signatureLabel h v) (fun j => z ⟨v,j⟩)) *
        ∏ e, kernels (r.edgeLabel h e) (z (r.lookup h (e,false))) (z (r.lookup h (e,true))) := by
  classical
  unfold Network.denote
  apply Fintype.sum_equiv (Equiv.arrowCongr (r.incidenceEquiv h).symm (Equiv.refl Bool))
  intro z
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    congr 1
  · apply Finset.prod_congr rfl
    intro e _
    simp [RawClosedNetwork.realize,Equiv.arrowCongr,RawClosedNetwork.incidenceEquiv]
    rfl

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
