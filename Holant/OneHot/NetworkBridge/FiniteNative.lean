import Holant.NetworkGluing.Finite
import Holant.NativeNetwork

/-! Native-X compression for finite-index networks. Each edge contributes one
choice bit, with opposite values at its false and true endpoints. -/

namespace Holant.FiniteNetwork

variable {K V E : Type*} {n : ℕ}

/-- A choice bit gives the true endpoint's value; the false endpoint is opposite. -/
def endpointChoiceAssignment (c : E → Bool) : (E × Bool) → Bool :=
  fun q => if q.2 then c q.1 else !(c q.1)

/-- The one-choice-per-edge sum for a finite-index native-X network. -/
noncomputable def endpointChoiceDenote [Fintype V] [Fintype E] [CommSemiring K]
    (arity : V → ℕ)
    (ports : (Σ v : V, Fin (arity v)) ≃ (Fin n ⊕ (E × Bool)))
    (f : (v : V) → Signature K (arity v)) : Signature K n := by
  classical
  exact fun x => ∑ c : E → Bool,
    ∏ v, f v (fun i => Sum.elim x (endpointChoiceAssignment c) (ports ⟨v, i⟩))

private def halfEdgeAssignmentsEquiv :
    ((E × Bool) → Bool) ≃ ((E → Bool) × (E → Bool)) where
  toFun := fun z => (fun e => z (e, false), fun e => z (e, true))
  invFun := fun p q => if q.2 then p.2 q.1 else p.1 q.1
  left_inv := fun z => by
    funext q
    cases q with
    | mk e b => cases b <;> rfl
  right_inv := fun _ => rfl

private theorem prod_disequality [Fintype E] [CommSemiring K] (x y : E → Bool) :
    (∏ e, Signature.disequality (K := K) (x e) (y e)) =
      if x = (fun e => !(y e)) then 1 else 0 := by
  classical
  simp only [Signature.disequality_eq_equality_compl, Signature.equality,
    Fintype.prod_boole, ← funext_iff]

set_option backward.isDefEq.respectTransparency false in
/-- Compress the actual half-edge denotation of a finite native-X network to
one endpoint choice per edge. No restriction excludes loops or parallel edges. -/
theorem denote_disequality [Fintype V] [Fintype E] [CommSemiring K]
    (arity : V → ℕ)
    (ports : (Σ v : V, Fin (arity v)) ≃ (Fin n ⊕ (E × Bool)))
    (f : (v : V) → Signature K (arity v)) :
    (FiniteNetwork.mk arity ports f (fun _ => Signature.disequality)).denote =
      endpointChoiceDenote arity ports f := by
  classical
  funext x
  unfold denote endpointChoiceDenote
  dsimp only
  rw [← (halfEdgeAssignmentsEquiv (E := E)).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [halfEdgeAssignmentsEquiv, Equiv.coe_fn_symm_mk, Bool.false_eq_true,
    ↓reduceIte, prod_disequality]
  simp
  rfl

open scoped Classical in
/-- Pointwise form exposing the endpoint-choice summand. -/
theorem denote_disequality_apply [Fintype V] [Fintype E] [CommSemiring K]
    (arity : V → ℕ)
    (ports : (Σ v : V, Fin (arity v)) ≃ (Fin n ⊕ (E × Bool)))
    (f : (v : V) → Signature K (arity v)) (x : Fin n → Bool) :
    (FiniteNetwork.mk arity ports f (fun _ => Signature.disequality)).denote x =
      ∑ c : E → Bool, ∏ v,
        f v (fun i => Sum.elim x
          (fun q : E × Bool => if q.2 then c q.1 else !(c q.1)) (ports ⟨v, i⟩)) := by
  classical
  rw [denote_disequality]
  rfl

end Holant.FiniteNetwork
