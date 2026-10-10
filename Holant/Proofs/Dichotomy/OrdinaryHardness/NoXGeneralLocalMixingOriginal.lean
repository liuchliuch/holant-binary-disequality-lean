import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalFiniteSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixingRelabel
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixingOriginal

/-! The whole-family local obstruction is selected internally, in an actual
same-field graph extension. Earlier ordinary/uniform resources and literal Z
are transported unchanged before the proved original-G mixer is invoked. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalMixingOriginal
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open NoXGeneralMixingResources
namespace C
export NoXReciprocalSelectionClosure (extension output obstruction)
end C
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
include zLiteral negative in
theorem countingHard (ordinary : OrdinarySupply src.H) (uniform : UniformSupply src.H) :
    NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_contra noHard
  obtain ⟨n,N,localSupply⟩:=NoXGeneralLocalFiniteSupply.choose G src zLabel zLiteral negative noHard
  let dst:=C.extension G src N
  have literal (i : Fin src.size) :
      (⟨dst.b (NoXOrdinaryGraphAdjoin.old src.H i).val,dst.H (NoXOrdinaryGraphAdjoin.old src.H i)⟩ : AnySignature src.K)=
      ⟨src.b i.val,src.H i⟩ := NoXOrdinaryGraphSource.old_literal G src (C.output G src N) i
  have ordinary':=NoXGeneralMixingRelabel.ordinary src.H dst.H (NoXOrdinaryGraphAdjoin.old src.H) literal ordinary
  have uniform':=NoXGeneralMixingRelabel.uniform src.H dst.H (NoXOrdinaryGraphAdjoin.old src.H) literal uniform
  exact noHard (NoXGeneralMixingOriginal.countingHard G dst (NoXOrdinaryGraphAdjoin.old src.H zLabel)
    ((literal zLabel).trans zLiteral) (C.obstruction G src N negative) ordinary' uniform' localSupply)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalMixingOriginal
end
