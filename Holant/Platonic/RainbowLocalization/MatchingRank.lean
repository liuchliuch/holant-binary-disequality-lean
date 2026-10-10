import Holant.Platonic.RainbowLocalization.CutCoordinates
import Holant.Platonic.RainbowLocalization.CutRankAlgebra

/-! Exact cut ranks of literal nonsingular matching products. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant Holant.Pauli.ExoticKlein
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
variable {P : Type*} {r : ℕ}

namespace MatchingCut

def internalFactor (M : Matching P r) (s : P → Bool) (b : Bool)
    (A : Fin r → Matrix Bool Bool ℂ) (c : ℂ) :
    ((Internal M s b × Bool) → Bool) → ℂ :=
  fun x => c * ∏ e : Internal M s b, A e.val (x (e,false)) (x (e,true))

theorem internalFactor_nonzero (M : Matching P r) (s : P → Bool) (b : Bool)
    (A : Fin r → Matrix Bool Bool ℂ) (c : ℂ) (hc : c ≠ 0)
    (hA : ∀ e, (A e).det ≠ 0) : ∃ x, internalFactor M s b A c x ≠ 0 := by
  have hn := productValue_nonzero (Equiv.refl (Internal M s b × Bool))
    (fun e : Internal M s b => A e.val) c (fun e => hA e.val) hc
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hn
  exact ⟨x,hx⟩

theorem crossingMatrix_det (M : Matching P r) (s : P → Bool)
    (A : Fin r → Matrix Bool Bool ℂ) (hA : ∀ e, (A e).det ≠ 0)
    (e : Crossing M s) : (crossingMatrix M s A e).det ≠ 0 := by
  cases h : s (M.ports (e.val,false)) <;> simp [crossingMatrix,h,hA]

/-- The cut matrix is obtained from the separated tensor-product matrix by
the explicit original-port row and column bijections. -/
theorem flatten_product_coordinates (M : Matching P r) (s : P → Bool)
    (A : Fin r → Matrix Bool Bool ℂ) (c : ℂ) :
    (flatten s (productValue M.ports A c)).submatrix
      (sideAssignments M s true).symm (sideAssignments M s false).symm =
      separatedMatrix (internalFactor M s true A c) (internalFactor M s false A 1)
        (binaryProductMatrix (crossingMatrix M s A)) := by
  ext x y
  have he := product_assignment M s A c x y
  simpa only [Matrix.submatrix_apply, flatten, assignment, separatedMatrix,
    internalFactor, binaryProductMatrix, one_mul] using he

/-- Flattening rank recovers the number of crossing edges for every actual
cut, every orientation, and arbitrary nonsingular binary factors. -/
theorem flatten_product_rank [Fintype P] [DecidableEq P]
    (M : Matching P r) (s : P → Bool) (A : Fin r → Matrix Bool Bool ℂ) (c : ℂ)
    (hA : ∀ e, (A e).det ≠ 0) (hc : c ≠ 0) :
    (flatten s (productValue M.ports A c)).rank = 2 ^ Fintype.card (Crossing M s) := by
  rw [← Matrix.rank_submatrix (flatten s (productValue M.ports A c))
    (sideAssignments M s true).symm (sideAssignments M s false).symm,
    flatten_product_coordinates]
  exact separated_binary_product_det_rank _ _ _
    (internalFactor_nonzero M s true A c hc hA)
    (internalFactor_nonzero M s false A 1 one_ne_zero hA)
    (crossingMatrix_det M s A hA)

end MatchingCut
end Holant.Platonic.RainbowLocalization
