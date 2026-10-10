import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXMinimalWitnesses
import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Every internally supplied even nonaffine block immediately reaches the
unchanged original counting problem, using the independently selected actual
non-Product resource. No support-closure test or resource oracle is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXUniversalBase
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeXUniversalResource
namespace E
export GenericLiteralXSource (count arity table family)
export GenericLiteralXSource (field)
end E
namespace N
export OrdinaryNegativeGenericXNonproduct (blocks balanced row_nonproduct)
end N
namespace F
export OrdinaryNegativeGenericXFourthCompatibilitySource (Hard)
end F
namespace R
export OrdinaryNegativeGenericXMixedBlockResourcesXOriginal (countingHard)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))

include negative in
theorem hard_of_even (bad : EvenBad (E.table G src)) : F.Hard G := by
  obtain ⟨n,B,hbad⟩ := bad
  exact R.countingHard G src B.rows (N.blocks G src negative) hbad
    (N.row_nonproduct G src negative) B.balanced (N.balanced G src negative)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXUniversalBase
end
