import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoUniformOpposite
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralRankTwoSupply
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Both rank-two class witnesses now terminate at actual typed resources.
All former separately-odd residuals are physically retained and consumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryRankTwoDispatch
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeSparseRankDescent
open NoXGeneralMixingResources
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
variable (j : Fin src.size) (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
variable (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G)
include negative square noHard in
theorem ordinary (W : OrdinaryNegativeSparseMinimalRank.PinWitness (src.H j) 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z)) :
    OrdinarySupply src.H := by
  rcases NoIOrdinaryRaw.NoXGeneralRankTwoSupply.ordinary G src j square negative W minimal with hard|bad|standard|both
  · exact False.elim (noHard hard)
  · exact False.elim (noHard (NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative bad))
  · exact Or.inl ⟨.three,standard⟩
  · exact Or.inr ⟨.three,⟨NoXGeneralRankTwoOppositeSupply.ordinary src.H j (src.p false) (src.p true)
      (src.hp false) (src.hp true) W both.1 square minimal⟩⟩
include negative square noHard in
theorem uniform (W : OrdinaryNegativeSparseUniformMinimal.UniformPinWitness (src.H j) 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,
      Affine (OrdinaryNegativeAffineRankOne.uniform (minor W.chart S z))) :
    UniformSupply src.H := by
  rcases NoIOrdinaryRaw.NoXGeneralRankTwoSupply.uniform G src j square negative W minimal with hard|bad|standard|both
  · exact False.elim (noHard hard)
  · exact False.elim (noHard (NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative bad))
  · exact Or.inl ⟨.three,standard⟩
  · exact Or.inr ⟨.three,⟨NoXGeneralRankTwoUniformOpposite.resource src.H j (src.p false) (src.p true)
      (src.hp false) (src.hp true) W both square minimal⟩⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryRankTwoDispatch
end
