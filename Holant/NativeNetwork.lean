import Holant.OrdinaryNetwork

/-!
Native-X edge compression retains opposite endpoint bits. A choice bit records
which endpoint is occupied, so loops still have two distinct available choices.
This is the endpoint-choice sum used in the proof of manuscript Lemma 2.18.
-/

namespace Holant.Signature

variable {K : Type*} [CommSemiring K] {n : ℕ}

theorem disequality_eq_equality_compl (a b : Bool) :
    disequality (K := K) a b = equality a (!b) := by
  cases a <;> cases b <;> rfl

theorem prod_disequality (x y : Fin n → Bool) :
    (∏ j : Fin n, disequality (K := K) (x j) (y j)) =
      if x = (fun j => !(y j)) then 1 else 0 := by
  simp only [disequality_eq_equality_compl, prod_equality]

end Holant.Signature

namespace Holant.Network

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- A true choice occupies the true endpoint; a false choice occupies the false endpoint. -/
def endpointChoiceAssignment {m : ℕ} (c : Fin m → Bool) : (Fin m × Bool) → Bool :=
  fun q => if q.2 then c q.1 else !(c q.1)

/-- Exactly one occupied half-edge per native-X edge, including loop edges. -/
def endpointChoiceDenote (s : NetworkShape n)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) : Signature K n :=
  fun x => ∑ c : Fin s.edges → Bool,
    ∏ v : Fin s.vertices, f v (s.assignment x (endpointChoiceAssignment c) v)

set_option backward.isDefEq.respectTransparency false in
/-- The actual native half-edge sum equals its endpoint-choice enumeration.
This is not the ordinary equality-wire one-bit compression. -/
theorem denote_disequality (s : NetworkShape n)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) :
    (Network.mk s f (fun _ => Signature.disequality)).denote = endpointChoiceDenote s f := by
  funext x
  unfold denote endpointChoiceDenote
  dsimp only
  rw [← (halfEdgeAssignmentsEquiv s.edges).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [halfEdgeAssignmentsEquiv, Equiv.coe_fn_symm_mk, Bool.false_eq_true,
    ↓reduceIte, Signature.prod_disequality]
  simp
  rfl

end Holant.Network
