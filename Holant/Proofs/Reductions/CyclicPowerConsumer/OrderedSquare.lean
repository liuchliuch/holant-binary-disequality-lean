import Holant.Proofs.Algorithms.CyclicBoundary.DoubledDescent
import Holant.Proofs.Reductions.GeneralExtraction.GeneralPowerExposure


noncomputable section
namespace Holant.LocalDrafts.Hardness.CyclicPowerConsumer
open Holant.Tractable
open scoped BigOperators
open Holant.LocalDrafts.MainChain.CyclicBoundary
open GeneralExtraction

theorem first_block_port (i : Fin 2) :
    (finProdFinEquiv ((0 : Fin 2), i) : Fin (2 * 2)) =
      Fin.cast (show 2 + 2 = 2 * 2 from rfl) (Fin.castAdd 2 i) := by
  fin_cases i <;> rfl

theorem second_block_port (i : Fin 2) :
    (finProdFinEquiv ((1 : Fin 2), i) : Fin (2 * 2)) =
      Fin.cast (show 2 + 2 = 2 * 2 from rfl) (Fin.natAdd 2 i) := by
  fin_cases i <;> rfl

theorem ordered_square_blockPower (b : Signature AlgebraicComplex 2) :
    DoubledDescent.square b = Carrier.blockPower b 2 := by
  rw [DoubledDescent.square_ordered]
  funext x
  simp only [Signature.tensor_apply, Carrier.blockPower, Fin.prod_univ_two]
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem blockPower_two_nonzero (b : Signature AlgebraicComplex 2) (hb : b ≠ 0) :
    ∃ x : Fin (2 * 2) → Bool, Carrier.blockPower b 2 x ≠ 0 := by
  have he : ∃ y, b y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hb (funext h)
  obtain ⟨y,hy⟩ := he
  exact ⟨Carrier.blockPivot y 2, Carrier.blockPower_pivot_nonzero b y hy⟩

end Holant.LocalDrafts.Hardness.CyclicPowerConsumer
