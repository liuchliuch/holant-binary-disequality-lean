import Holant.Dihedral.PolarizedDeterminant.Cards

/-! The padded phase notation is exactly the remaining-coordinate cube, with no
additional phase tests at the two exposed coordinates. -/
noncomputable section
namespace Holant.Dihedral.PolarizedDeterminant
open scoped BigOperators

abbrev Remaining {s : ℕ} (i k : Fin s) := {j : Fin s // j ≠ i ∧ j ≠ k}

/-- A canonical identification of the source's remaining cube with the zero-extended words. -/
def remainingEquiv {s : ℕ} (i k : Fin s) :
    {z : Cube s // z i = false ∧ z k = false} ≃ (Remaining i k → Bool) where
  toFun z j := z.val j.val
  invFun z := ⟨fun j => if h : j = i ∨ j = k then false else
    z ⟨j, by simpa only [not_or] using h⟩, by simp⟩
  left_inv z := by
    apply Subtype.ext
    funext j
    by_cases h : j = i ∨ j = k
    · rcases h with rfl | rfl <;> simp [z.property.1, z.property.2]
    · simp [h]
  right_inv z := by
    funext j
    simp [j.property.1, j.property.2]

/-- The exposed coordinates never affect a card's value, since their exponents are zero. -/
theorem card_phase_congr {s : ℕ} (w : Cube s → ℂ) (i k : Fin s)
    (lam mu : Fin s → ℂ) (h : ∀ j, j ≠ i → j ≠ k → lam j = mu j)
    (a b xi : Bool) : card w i k lam a b xi = card w i k mu a b xi := by
  apply Finset.sum_congr rfl
  intro z hz
  have hz' := (mem_sliceWords i k z).mp hz
  have he : phaseMonomial lam z = phaseMonomial mu z := by
    apply Finset.prod_congr rfl
    intro j hj
    cases hjz : z j
    · simp
    · have hji : j ≠ i := by intro he; subst j; simp [hz'.1] at hjz
      have hjk : j ≠ k := by intro he; subst j; simp [hz'.2] at hjz
      simp [h j hji hjk]
  rw [he]

end Holant.Dihedral.PolarizedDeterminant
