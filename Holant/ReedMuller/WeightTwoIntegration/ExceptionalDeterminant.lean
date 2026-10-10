import Holant.ReedMuller.WeightTwoIntegration.ExceptionalAlgebra

noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration

/-- Original logical coordinate closed; remaining coordinates retain their order. -/
def exceptionalSamePairCard (r : Fin 3 → ℂ) (k : ℂ) (i : Fin 3)
    (minus x y : Bool) : ℂ :=
  let s : ℂ := if minus then -1 else 1
  if i = 0 then exceptionalH r k false x y + s * exceptionalH r k true x y
  else if i = 1 then exceptionalH r k x false y + s * exceptionalH r k x true y
  else exceptionalH r k x y false + s * exceptionalH r k x y true

def exceptionalRemainingLeft : Fin 3 → Fin 3 := ![1,0,0]
def exceptionalRemainingRight : Fin 3 → Fin 3 := ![2,2,1]

theorem exceptional_samePair_determinant (r : Fin 3 → ℂ) (k : ℂ)
    (i : Fin 3) (minus : Bool) :
    exceptionalSamePairCard r k i minus false false *
        exceptionalSamePairCard r k i minus true true -
      exceptionalSamePairCard r k i minus false true *
        exceptionalSamePairCard r k i minus true false =
    r (exceptionalRemainingLeft i) * r (exceptionalRemainingRight i) *
      (k - 1) * (1 - k * r i ^ 2) := by
  fin_cases i <;> cases minus <;>
    norm_num [exceptionalSamePairCard,exceptionalH,
      exceptionalRemainingLeft,exceptionalRemainingRight] <;> ring

theorem exceptional_square_of_samePair_rank_one (r : Fin 3 → ℂ) (k : ℂ)
    (hr : ∀ i, r i ≠ 0) (hk : k ≠ 1) (i : Fin 3) (minus : Bool)
    (hdet : exceptionalSamePairCard r k i minus false false *
        exceptionalSamePairCard r k i minus true true -
      exceptionalSamePairCard r k i minus false true *
        exceptionalSamePairCard r k i minus true false = 0) :
    k * r i ^ 2 = 1 := by
  rw [exceptional_samePair_determinant] at hdet
  have hn : r (exceptionalRemainingLeft i) * r (exceptionalRemainingRight i) *
      (k - 1) ≠ 0 := mul_ne_zero (mul_ne_zero (hr _) (hr _)) (sub_ne_zero.mpr hk)
  have hz := (mul_eq_zero.mp hdet).resolve_left hn
  exact (sub_eq_zero.mp hz).symm

end Holant.ReedMuller.WeightTwoIntegration
