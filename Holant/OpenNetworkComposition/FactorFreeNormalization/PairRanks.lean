import Holant.OpenNetworkComposition.FactorFreeNormalization.Factors
import Holant.Platonic.RainbowLocalization.CutCoordinates
import Mathlib.LinearAlgebra.Matrix.Rank

/-! An isolated X factor has rank at most one in the pair-versus-complement
flattening. All-pair rank at least two therefore supplies the no-new-resource
ordinary normalization criterion, at arbitrary boundary arity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.FactorFreeNormalization
open Holant.Platonic.RainbowLocalization
variable {K : Type*} [Field K] {n : ℕ}

/-- A chosen pair is the row side of the original-coordinate flattening. -/
def pairSide (i j : Fin n) (k : Fin n) : Bool := decide (k=i ∨ k=j)

/-- Exact free/free factorization gives an outer-product matrix, including
when its residual tensor is zero or has nonunit scalar factors. -/
theorem pair_flatten_rank_le_one (h : Signature K n) (i j : Fin n)
    (g : Tensor K (OtherPorts i j))
    (hg : ∀x,h x=Signature.disequality (x i) (x j)*g (fun k => x k.val)) :
    (MatchingCut.flatten (pairSide i j) h).rank≤1 := by
  classical
  let row : (MatchingCut.Side (pairSide i j) true → Bool) → K :=
    fun x => Signature.disequality (x ⟨i,by simp [pairSide]⟩) (x ⟨j,by simp [pairSide]⟩)
  let col : (MatchingCut.Side (pairSide i j) false → Bool) → K :=
    fun y => g (fun k => y ⟨k.val,by simp [pairSide,k.property.1,k.property.2]⟩)
  have he : MatchingCut.flatten (pairSide i j) h=Matrix.vecMulVec row col := by
    ext x y
    rw [MatchingCut.flatten,hg]
    change Signature.disequality
      (MatchingCut.joinAssignment (pairSide i j) x y i)
      (MatchingCut.joinAssignment (pairSide i j) x y j)*
      g (fun k => MatchingCut.joinAssignment (pairSide i j) x y k.val)=row x*col y
    dsimp only [row,col]
    have hi : MatchingCut.joinAssignment (pairSide i j) x y i=x ⟨i,by simp [pairSide]⟩ :=
      MatchingCut.joinAssignment_true _ _ _ ⟨i,by simp [pairSide]⟩
    have hj : MatchingCut.joinAssignment (pairSide i j) x y j=x ⟨j,by simp [pairSide]⟩ :=
      MatchingCut.joinAssignment_true _ _ _ ⟨j,by simp [pairSide]⟩
    rw [hi,hj]
    congr 1
    congr 1
    funext k
    exact MatchingCut.joinAssignment_false _ _ _
      ⟨k.val,by simp [pairSide,k.property.1,k.property.2]⟩
  rw [he]
  exact Matrix.rank_vecMulVec_le row col

/-- Every pair cut of rank at least two excludes the exact native-X factor. -/
theorem noXFactor_of_pairRanks (h : Signature K n)
    (hr : ∀i j : Fin n,i≠j →
      2≤(MatchingCut.flatten (fun k => decide (k=i ∨ k=j)) h).rank) :
    NoXFactor h := by
  rintro ⟨i,j,hij,g,hg⟩
  have hu := pair_flatten_rank_le_one h i j g hg
  have hl := hr i j hij
  change 2≤(MatchingCut.flatten (pairSide i j) h).rank at hl
  omega

end Holant.OpenNetworkComposition.FactorFreeNormalization
