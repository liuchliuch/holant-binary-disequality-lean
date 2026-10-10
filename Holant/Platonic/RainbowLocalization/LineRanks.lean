import Holant.Platonic.RainbowLocalization.MatchingRank

/-! Rank inequalities obtained from a literal tensor-line equation. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant Holant.Pauli.ExoticKlein
open Holant.Certificates.MatchingContractionClosure

theorem matrix_rank_add_le {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem matrix_rank_smul_le {I J : Type*} [Fintype I] [Fintype J]
    (a : ℂ) (A : Matrix I J ℂ) : (a • A).rank ≤ A.rank := by
  by_cases ha : a = 0
  · simp [ha]
  · exact le_of_eq (Matrix.rank_smul_of_mem_nonZeroDivisors A
      (mem_nonZeroDivisors_of_ne_zero ha))

theorem matrix_rank_linear_combination_le {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℂ) (a b : ℂ) : (a • A + b • B).rank ≤ A.rank + B.rank :=
  (matrix_rank_add_le _ _).trans (Nat.add_le_add (matrix_rank_smul_le a A)
    (matrix_rank_smul_le b B))

namespace MatchingCut
variable {P : Type*} [Fintype P] [DecidableEq P]

@[simp] theorem flatten_add (s : P → Bool) (F H : Tensor ℂ P) :
    flatten s (F + H) = flatten s F + flatten s H := rfl

@[simp] theorem flatten_smul (s : P → Bool) (a : ℂ) (F : Tensor ℂ P) :
    flatten s (a • F) = a • flatten s F := rfl

/-- Each actual tensor-line equation gives the cut rank triangle inequality. -/
theorem flatten_rank_le_of_line (s : P → Bool) (F₀ F₁ F₂ : Tensor ℂ P) (a b : ℂ)
    (hline : F₂ = a • F₀ + b • F₁) :
    (flatten s F₂).rank ≤ (flatten s F₀).rank + (flatten s F₁).rank := by
  rw [hline, flatten_add, flatten_smul, flatten_smul]
  exact matrix_rank_linear_combination_le _ _ _ _

/-- The source rank inequality with every exponent computed from the given
literal matching and cut; no flattening rank is supplied as an assumption. -/
theorem crossing_pow_le_of_line {r₀ r₁ r₂ : ℕ}
    (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (A₀ : Fin r₀ → Matrix Bool Bool ℂ) (A₁ : Fin r₁ → Matrix Bool Bool ℂ)
    (A₂ : Fin r₂ → Matrix Bool Bool ℂ) (c₀ c₁ c₂ a b : ℂ)
    (h₀ : ∀ e, (A₀ e).det ≠ 0) (h₁ : ∀ e, (A₁ e).det ≠ 0)
    (h₂ : ∀ e, (A₂ e).det ≠ 0) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hline : productValue M₂.ports A₂ c₂ =
      a • productValue M₀.ports A₀ c₀ + b • productValue M₁.ports A₁ c₁)
    (s : P → Bool) :
    2 ^ Fintype.card (Crossing M₂ s) ≤
      2 ^ Fintype.card (Crossing M₀ s) + 2 ^ Fintype.card (Crossing M₁ s) := by
  have hh := flatten_rank_le_of_line s _ _ _ a b hline
  simpa only [flatten_product_rank M₀ s A₀ c₀ h₀ hc₀,
    flatten_product_rank M₁ s A₁ c₁ h₁ hc₁,
    flatten_product_rank M₂ s A₂ c₂ h₂ hc₂] using hh

end MatchingCut
end Holant.Platonic.RainbowLocalization
