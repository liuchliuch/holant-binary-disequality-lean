import Holant.Network
import Holant.BoundaryAction

/-! Compression of equality-wired half-edge networks to one bit per edge. -/

namespace Holant

/-- Split independent endpoint bits into the false-end and true-end assignments. -/
def halfEdgeAssignmentsEquiv (m : ℕ) :
    ((Fin m × Bool) → Bool) ≃ ((Fin m → Bool) × (Fin m → Bool)) where
  toFun := fun z => (fun e => z (e, false), fun e => z (e, true))
  invFun := fun p q => if q.2 then p.2 q.1 else p.1 q.1
  left_inv := fun z => by
    funext q
    cases q with
    | mk e b => cases b <;> rfl
  right_inv := fun _ => rfl

namespace Network

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- The ordinary one-bit-per-edge sum, valid even for loops and parallel edges. -/
def ordinaryDenote (s : NetworkShape n)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) : Signature K n :=
  fun x => ∑ a : Fin s.edges → Bool,
    ∏ v : Fin s.vertices, f v (s.assignment x (fun q => a q.1) v)

set_option backward.isDefEq.respectTransparency false in
/-- Equality kernels force both endpoint bits to agree and recover the usual Holant sum. -/
theorem denote_equality (s : NetworkShape n)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) :
    (Network.mk s f (fun _ => Signature.equality)).denote = ordinaryDenote s f := by
  funext x
  unfold denote ordinaryDenote
  dsimp only
  rw [← (halfEdgeAssignmentsEquiv s.edges).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [halfEdgeAssignmentsEquiv, Equiv.coe_fn_symm_mk, Bool.false_eq_true,
    ↓reduceIte]
  simp only [Signature.prod_equality]
  simp

end Network
end Holant
