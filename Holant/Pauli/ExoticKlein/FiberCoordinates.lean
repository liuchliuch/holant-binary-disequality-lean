import Holant.Pauli.ExoticKlein.RulingCoordinates
import Holant.Pauli.ExoticKlein.FiberSupport

/-! Literal tomographic fibers on one complete original-port matching. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
open Holant.Dihedral.CompatibleCoefficientLine (pair tail)

namespace Matching
variable {n r : ℕ}

def prependPorts (M : Matching (Fin n) r) : (Fin (r+1) × Bool) ≃ Fin (n+2) where
  toFun eb := Fin.cases (if eb.2 then 1 else 0) (fun e => (M.ports (e,eb.2)).succ.succ) eb.1
  invFun i := Fin.cases (0,false) (fun j => Fin.cases (0,true)
    (fun k => ((M.ports.symm k).1.succ,(M.ports.symm k).2)) j) i
  left_inv eb := by
    rcases eb with ⟨e,b⟩
    refine Fin.cases ?_ (fun j => ?_) e
    · cases b <;> rfl
    · simp only [Fin.cases_succ,Equiv.symm_apply_apply]
  right_inv i := by
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · simp only [Fin.cases_succ,Prod.mk.eta,Equiv.apply_symm_apply]

def prepend (M : Matching (Fin n) r) : Matching (Fin (n+2)) (r+1) := ⟨prependPorts M⟩

@[simp] theorem prepend_tensor (M : Matching (Fin n) r) (a : Label) (labels : Fin r → Label)
    (x : Fin (n+2) → Bool) :
    M.prepend.tensor (Fin.cons a labels) x = E a (x 0) (x 1)*M.tensor labels (tail x) := by
  simp only [tensor,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,prepend,prependPorts,
    Equiv.coe_fn_mk,Fin.cases_zero,Fin.cases_succ,Bool.false_eq_true,ite_false,ite_true,tail]

end Matching

namespace MatchingCard

theorem common_full_fiber (r : ℕ) (hr : 0 < r) (f : Signature ℂ (2*r+6))
    (hf : f ≠ 0) (hs : OrderedPairSafe f) :
    ∃ s : ℕ, ∃ M : Matching (Fin (2*r+6)) (s+1),
      ∃ weight : Label → ℂ, ∃ labels : Label → Fin (s+1) → Label,
        (∀ a, labels a 0 = a) ∧ f = Fiber.tensor M weight labels ∧
        (∀ a, weight a = 0 ↔ Signature.contract (dual a) f = 0) ∧ 3 ≤ s := by
  obtain ⟨s,M,weight,labels,he,hz⟩ := common_card_coordinates r hr f hf hs
  have hcard := M.port_card
  simp only [Fintype.card_fin] at hcard
  refine ⟨s,M.prepend,weight,(fun a => Fin.cons a (labels a)),fun _ => rfl,?_,hz,by omega⟩
  funext x
  have hx : pair (x 0) (x 1) (tail x) = x := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  have hh := front_reconstruction f (x 0) (x 1) (tail x)
  rw [hx] at hh
  rw [←hh]
  simp only [Fiber.tensor,Matching.prepend_tensor,he]
  apply Finset.sum_congr rfl
  intro a ha
  ring

end MatchingCard
end
end Holant.Pauli.ExoticKlein
