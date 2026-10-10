import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoUniformOpposite
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenHardness

/-! Both rank-two class witnesses now terminate at actual typed resources.
All former separately-odd residuals are physically retained and consumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoDispatch
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeSparseRankDescent
open NoXGeneralMixingResources
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (zLabel : Fin src.size)
variable (zLiteral : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))
variable (j : Fin src.size) (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
variable (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G)
include zLiteral negative square noHard in
theorem ordinary (W : OrdinaryNegativeSparseMinimalRank.PinWitness (src.H j) 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z)) :
    OrdinarySupply src.H := by
  rcases NoXGeneralRankTwoSupply.ordinary G src j square negative W minimal with hard|bad|standard|both
  · exact False.elim (noHard hard)
  · exact False.elim (noHard (NoXGeneralEvenHardness.countingHard G src zLabel zLiteral negative bad))
  · exact Or.inl ⟨.three,standard⟩
  · exact Or.inr ⟨.three,⟨NoXGeneralRankTwoOppositeSupply.ordinary src.H j (src.p false) (src.p true)
      (src.hp false) (src.hp true) W both.1 square minimal⟩⟩
include zLiteral negative square noHard in
theorem uniform (W : OrdinaryNegativeSparseUniformMinimal.UniformPinWitness (src.H j) 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,
      Affine (OrdinaryNegativeAffineRankOne.uniform (minor W.chart S z))) :
    UniformSupply src.H := by
  rcases NoXGeneralRankTwoSupply.uniform G src j square negative W minimal with hard|bad|standard|both
  · exact False.elim (noHard hard)
  · exact False.elim (noHard (NoXGeneralEvenHardness.countingHard G src zLabel zLiteral negative bad))
  · exact Or.inl ⟨.three,standard⟩
  · exact Or.inr ⟨.three,⟨NoXGeneralRankTwoUniformOpposite.resource src.H j (src.p false) (src.p true)
      (src.hp false) (src.hp true) W both square minimal⟩⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoDispatch
end
