import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalFiniteSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixingRelabel
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryMixingOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinarySelectionClosure
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! The whole-family local obstruction is selected internally, in an actual
same-field graph extension. Earlier ordinary/uniform resources are transported unchanged before the proved original-G mixer is invoked. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalMixingOriginal
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open NoXGeneralMixingResources
namespace C
export NoIOrdinaryRaw.NoIOrdinarySelectionClosure (extension output obstruction)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
include negative in
theorem countingHard (ordinary : OrdinarySupply src.H) (uniform : UniformSupply src.H) :
    NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_contra noHard
  obtain ⟨n,N,localSupply⟩:=NoIOrdinaryRaw.NoIOrdinaryLocalFiniteSupply.choose G src negative noHard
  let dst:=C.extension G src N
  have literal (i : Fin src.size) :
      (⟨dst.b (NoXOrdinaryGraphAdjoin.old src.H i).val,dst.H (NoXOrdinaryGraphAdjoin.old src.H i)⟩ : AnySignature src.K)=
      ⟨src.b i.val,src.H i⟩ := NoIOrdinaryRaw.NoXOrdinaryGraphSource.old_literal G src (C.output G src N) i
  have ordinary':=NoXGeneralMixingRelabel.ordinary src.H dst.H (NoXOrdinaryGraphAdjoin.old src.H) literal ordinary
  have uniform':=NoXGeneralMixingRelabel.uniform src.H dst.H (NoXOrdinaryGraphAdjoin.old src.H) literal uniform
  exact noHard (NoIOrdinaryRaw.NoIOrdinaryMixingOriginal.countingHard G dst (C.obstruction G src N negative) ordinary' uniform' localSupply)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalMixingOriginal
end
