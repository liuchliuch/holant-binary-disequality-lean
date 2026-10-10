import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSupplierSelection
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankOneDispatch
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoDispatch
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankThreeDispatch
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalMixingOriginal

/-! Universal negative ordinary Eq4/both-pins/Z source. Every class witness,
least rank, physical sign correction, local obstruction resource, and finite
mixer is selected internally. The final counting oracle is the unchanged G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralComplete
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
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
variable (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G)
include zLiteral negative noHard in
theorem ordinary : OrdinarySupply src.H := by
  obtain ⟨j,r,lower,upper,W,minimal⟩:=NoXGeneralSupplierSelection.ordinary G src zLabel zLiteral negative noHard
  have square:=NoXGeneralSupplierSelection.square G src zLabel zLiteral negative noHard j
  have cases_r : r=1 ∨ r=2 ∨ r=3:=by omega
  rcases cases_r with rfl|rfl|rfl
  · exact NoXGeneralRankOneDispatch.ordinary G src zLabel zLiteral negative j square noHard W
  · exact NoXGeneralRankTwoDispatch.ordinary G src zLabel zLiteral negative j square noHard W minimal
  · exact NoXGeneralRankThreeDispatch.ordinary G src zLabel zLiteral negative j square noHard W minimal
include zLiteral negative noHard in
theorem uniform : UniformSupply src.H := by
  obtain ⟨j,r,lower,upper,W,minimal⟩:=NoXGeneralSupplierSelection.uniform G src zLabel zLiteral negative noHard
  have square:=NoXGeneralSupplierSelection.square G src zLabel zLiteral negative noHard j
  have cases_r : r=1 ∨ r=2 ∨ r=3:=by omega
  rcases cases_r with rfl|rfl|rfl
  · exact NoXGeneralRankOneDispatch.uniform G src zLabel zLiteral negative j square noHard W
  · exact NoXGeneralRankTwoDispatch.uniform G src zLabel zLiteral negative j square noHard W minimal
  · exact NoXGeneralRankThreeDispatch.uniform G src zLabel zLiteral negative j square noHard W minimal
include zLiteral negative in
theorem countingHard : NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_contra noHard
  exact noHard (NoXGeneralLocalMixingOriginal.countingHard G src zLabel zLiteral negative
    (ordinary G src zLabel zLiteral negative noHard) (uniform G src zLabel zLiteral negative noHard))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralComplete
end
