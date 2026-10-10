import Holant.Certificates.MatchingProductBridge.Flattenings

/-! A reusable rank-two certificate using an actual two-column factorization
and an actual nonzero two-by-two minor. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant.Certificates.MatchingProductBridge
noncomputable section

abbrev PairIndex := Bool × Bool

def pivotMinor (M : PairMatrix) (r c : Bool → PairIndex) : ℂ :=
  M (r false) (c false)*M (r true) (c true)-M (r false) (c true)*M (r true) (c false)

def rankLeft (M : PairMatrix) (r c : Bool → PairIndex) : Matrix PairIndex Bool ℂ := fun i b =>
  if b then (M (r false) (c false)*M i (c true)-M (r false) (c true)*M i (c false))/pivotMinor M r c
  else (M i (c false)*M (r true) (c true)-M i (c true)*M (r true) (c false))/pivotMinor M r c

def rankRight (M : PairMatrix) (r : Bool → PairIndex) : Matrix Bool PairIndex ℂ := fun b j => M (r b) j

theorem rank_two_of_certificate (M : PairMatrix) (r c : Bool → PairIndex)
    (hn : pivotMinor M r c ≠ 0) (hf : M = rankLeft M r c * rankRight M r) : M.rank = 2 := by
  have hu : M.rank ≤ 2 := by
    rw [hf]
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (rankLeft M r c))
  have hl : ¬ M.rank ≤ 1 := by
    intro h
    exact hn (minor_two_eq_zero_of_rank_le_one M h (r false) (r true) (c false) (c true))
  omega

end
end Holant.Certificates.TetrahedralOrientation
