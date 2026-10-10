import Holant.BoundaryAction

/-! Exact two-port enumeration, with coordinate zero preceding coordinate one. -/

namespace Holant.Signature

/-- Finite coordinate words are put in the explicit `(port 0, port 1)` order. -/
def twoBitsEquiv : (Fin 2 → Bool) ≃ (Bool × Bool) where
  toFun := fun x => (x 0, x 1)
  invFun := fun p => Fin.cons p.1 (Fin.cons p.2 Fin.elim0)
  left_inv := fun x => by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  right_inv := fun _ => rfl

theorem sum_two_assignments {K : Type*} [AddCommMonoid K] (f : Signature K 2) :
    (∑ x : Fin 2 → Bool, f x) =
      ∑ a : Bool, ∑ b : Bool, f (Fin.cons a (Fin.cons b Fin.elim0)) := by
  rw [← twoBitsEquiv.symm.sum_comp f, Fintype.sum_prod_type]
  rfl

theorem coordinateAction_two {K : Type*} [CommSemiring K]
    (A : Fin 2 → Bool → Bool → K) (f : Signature K 2) (x : Fin 2 → Bool) :
    coordinateAction A f x =
      ∑ a : Bool, ∑ b : Bool,
        (A 0 (x 0) a * A 1 (x 1) b) * f (Fin.cons a (Fin.cons b Fin.elim0)) := by
  simp only [coordinateAction, sum_two_assignments, Fin.prod_univ_two,
    Fin.cons_zero, Fin.cons_one]

end Holant.Signature
