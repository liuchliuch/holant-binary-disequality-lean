import Holant.Marked.SupportAtlas.MarkedDeck

/-! Exact source reversal formula for the off-diagonal effective kernel.
The label permutation and its nonzero multiplier are both retained. -/
noncomputable section
namespace Holant.Marked.SupportAtlas

theorem effectiveKernel_even_transpose (d t : ℂ) :
    Kernel.transpose (effectiveKernel d false t) = effectiveKernel d false t := by
  funext a b; cases a <;> cases b <;> rfl

/-- Equation `marked-A-card-reversal`, including the B case delta=1. -/
theorem effectiveKernel_off_transpose (d t : ℂ) (hd : d ≠ 0) (ht : t ≠ 0) :
    Kernel.transpose (effectiveKernel d true t) =
      (t/d) • effectiveKernel d true (d^2/t) := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.transpose, effectiveKernel] <;> field_simp

theorem reversed_phase_root {m : ℕ} (d t : ℂ) (hd : (d^2)^m=1) (ht : t^m=1) :
    (d^2/t)^m=1 := by rw [div_pow, hd, ht, one_div_one]

theorem reversal_multiplier_ne_zero {m : ℕ} (hm : 0 < m) (d t : ℂ)
    (hd : d ≠ 0) (ht : t^m=1) : t/d ≠ 0 := by
  apply div_ne_zero _ hd
  intro hz
  simp [hz, Nat.ne_of_gt hm] at ht

/-- The reversed first two original ports are an explicit permutation, leaving residual order fixed. -/
def reverseDeleted (e : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 1).trans e

theorem join_reverseDeleted (e : Equiv.Perm (Fin 4)) (a b u v : Bool) :
    join (reverseDeleted e) a b u v = join e b a u v := by
  funext i
  obtain ⟨j,rfl⟩ := e.surjective i
  fin_cases j <;> simp [Holant.Marked.SupportAtlas.join, reverseDeleted, Equiv.swap_apply_def]

/-- Reversal of the actual ordered card agrees with the root relabeling and known scalar. -/
theorem weightedCard_off_reversal (d t : ℂ) (hd : d ≠ 0) (ht : t ≠ 0)
    (q : Signature ℂ 4) (e : Equiv.Perm (Fin 4)) :
    weightedCard d q (reverseDeleted e) true t =
      (t/d) • weightedCard d q e true (d^2/t) := by
  funext u v
  simp [weightedCard, effectiveKernel, join_reverseDeleted]
  field_simp
  ring

end Holant.Marked.SupportAtlas
