import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSquares
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! The easy selection alternative is physical and independent of an anti
resource: any nonaffine pointwise square is already an actual even block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionSquares
open Holant Holant.Tractable
namespace S
export NoXWeightedAntiSquares (blocks balanced row row_nonaffine AllSquaresAffine)
end S
namespace B
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'

theorem evenBad (j : Fin src.size) (bad : ¬Affine (fun x=>(src.H j x : AlgebraicComplex)^2)) :
    B.EvenBad src.H := by
  refine ⟨src.b j.val,⟨0,S.blocks G src j,S.balanced G src j⟩,?_⟩
  exact S.row_nonaffine G src j bad

theorem evenBad_or_squares : B.EvenBad src.H ∨ S.AllSquaresAffine G src := by
  classical
  by_cases squares : S.AllSquaresAffine G src
  · exact Or.inr squares
  · left
    obtain ⟨j,hj⟩ := not_forall.mp squares
    exact evenBad G src j hj

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionSquares
end
