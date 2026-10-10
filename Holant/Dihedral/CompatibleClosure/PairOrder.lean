import Holant.Signature
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred

/-! Explicit common port order for contracting any two distinct original ports.
The same permutation is used for both sampled products. -/
namespace Holant.Dihedral.CompatibleClosure

variable {n : ℕ}

def pairOrder (u v : Fin (n+2)) : Equiv.Perm (Fin (n+2)) :=
  (Equiv.swap 1 ((Equiv.swap 0 u).symm v)).trans (Equiv.swap 0 u)

theorem pairOrder_first (u v : Fin (n+2)) (huv : u ≠ v) : pairOrder u v 0 = u := by
  have h0 : (Equiv.swap 0 u).symm v ≠ 0 := by
    intro he
    have hh := congrArg (Equiv.swap 0 u) he
    simp only [Equiv.apply_symm_apply,Equiv.swap_apply_left] at hh
    exact huv hh.symm
  simp only [pairOrder,Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne (Fin.zero_ne_one) (Ne.symm h0),Equiv.swap_apply_left]

theorem pairOrder_second (u v : Fin (n+2)) : pairOrder u v 1 = v := by
  simp only [pairOrder,Equiv.trans_apply,Equiv.swap_apply_left,Equiv.apply_symm_apply]

end Holant.Dihedral.CompatibleClosure
