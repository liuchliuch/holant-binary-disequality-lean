import Holant.Pauli.ExoticKlein.Matching
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! Actual matching involutions and their alternating permutation. The two
halves of each alternating cycle are distinct permutation orbits; fixed points
of the alternating permutation cover common matching edges. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open Equiv
namespace Matching
variable {P : Type*} {r : ℕ}

private def flip : Equiv.Perm (Fin r × Bool) where
  toFun q := (q.1,!q.2)
  invFun q := (q.1,!q.2)
  left_inv q := by cases q with | mk e b => cases b <;> rfl
  right_inv q := by cases q with | mk e b => cases b <;> rfl

def mate (M : Matching P r) : Equiv.Perm P := M.ports.symm.trans (flip.trans M.ports)

@[simp] theorem mate_port (M : Matching P r) (e : Fin r) (b : Bool) :
    M.mate (M.ports (e,b)) = M.ports (e,!b) := by simp [mate,flip]

@[simp] theorem mate_mate (M : Matching P r) (p : P) : M.mate (M.mate p) = p := by
  obtain ⟨⟨e,b⟩,rfl⟩ := M.ports.surjective p
  simp

theorem mate_ne_self (M : Matching P r) (p : P) : M.mate p ≠ p := by
  obtain ⟨⟨e,b⟩,rfl⟩ := M.ports.surjective p
  rw [mate_port]
  intro h
  have hh := congrArg Prod.snd (M.ports.injective h)
  cases b <;> contradiction

@[simp] theorem mate_square (M : Matching P r) : M.mate*M.mate = 1 := by
  ext p
  exact M.mate_mate p

@[simp] theorem mate_inv (M : Matching P r) : M.mate⁻¹ = M.mate := by
  have h := M.mate_square
  exact inv_eq_of_mul_eq_one_left h

/-- First traverse the M-edge, then the N-edge. -/
def alternating (M N : Matching P r) : Equiv.Perm P := N.mate*M.mate

theorem alternating_mate_alternating (M N : Matching P r) :
    M.alternating N*M.mate*M.alternating N = M.mate := by
  unfold alternating
  calc
    (N.mate*M.mate)*M.mate*(N.mate*M.mate) = N.mate*(M.mate*M.mate)*N.mate*M.mate := by simp only [mul_assoc]
    _ = M.mate := by rw [mate_square,mul_one,mate_square,one_mul]

/-- A finite alternating walk cannot reach its starting point's M-mate on an
even number of edges. This follows only from both matchings having no fixed port. -/
theorem mate_ne_alternating_pow (M N : Matching P r) :
    ∀ k : ℕ, ∀ p : P, M.mate p ≠ ((M.alternating N)^k) p := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro p hp
    cases k with
    | zero => exact M.mate_ne_self p hp
    | succ k =>
      cases k with
      | zero =>
        have hh : N.mate (M.mate p) = M.mate p := by simpa [alternating] using hp.symm
        exact N.mate_ne_self (M.mate p) hh
      | succ k =>
        let R := M.alternating N
        have hsmall : M.mate (R p) = (R^k) (R p) := by
          apply R.injective
          calc
            R (M.mate (R p)) = M.mate p := congrArg (fun f : Equiv.Perm P => f p) (M.alternating_mate_alternating N)
            _ = (R^(k+2)) p := hp
            _ = R ((R^k) (R p)) := by rw [pow_succ',pow_succ]; rfl
        exact ih k (by omega) (R p) hsmall

variable [Fintype P] [DecidableEq P]

theorem mate_not_sameCycle (M N : Matching P r) (p : P) :
    ¬(M.alternating N).SameCycle p (M.mate p) := by
  intro h
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  exact M.mate_ne_alternating_pow N k p hk.symm

theorem mate_conjugate_alternating (M N : Matching P r) :
    M.mate*M.alternating N*M.mate⁻¹ = (M.alternating N)⁻¹ := by
  simp only [alternating,mul_inv_rev,mate_inv]
  calc
    M.mate*(N.mate*M.mate)*M.mate = M.mate*N.mate*(M.mate*M.mate) := by simp only [mul_assoc]
    _ = M.mate*N.mate := by rw [mate_square,mul_one]

theorem sameCycle_mate_iff (M N : Matching P r) (p q : P) :
    (M.alternating N).SameCycle (M.mate p) (M.mate q) ↔ (M.alternating N).SameCycle p q := by
  have h := Equiv.Perm.sameCycle_conj (f := M.alternating N) (g := M.mate)
    (x := M.mate p) (y := M.mate q)
  rw [M.mate_conjugate_alternating N] at h
  simpa only [Equiv.Perm.sameCycle_inv,mate_inv,mate_mate] using h

end Matching
end
end Holant.Pauli.ExoticKlein
