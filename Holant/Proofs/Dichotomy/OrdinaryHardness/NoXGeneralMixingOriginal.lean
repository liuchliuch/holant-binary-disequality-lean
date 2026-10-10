import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixingResources
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenHardness

/-! The exact finite actual-resource mixer feeds the proved original-G
hardness programme. Resource selection is handled by separate producers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralMixingOriginal
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open NoXGeneralMixingResources
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (zLabel : Fin src.size)
variable (zLiteral : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))
include zLiteral negative in
theorem countingHard (ordinary : OrdinarySupply src.H) (uniform : UniformSupply src.H)
    (localSupply : LocalSupply src.H) : NoXWeightedAntiResourcesOriginal.Hard G :=
  NoXGeneralEvenHardness.countingHard G src zLabel zLiteral negative
    (NoXGeneralMixingResources.evenBad src.H ordinary uniform localSupply)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralMixingOriginal
end
