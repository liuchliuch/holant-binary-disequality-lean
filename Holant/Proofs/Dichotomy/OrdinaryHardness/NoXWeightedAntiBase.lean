import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXNonproduct
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! An actual even non-Affine resource is discharged to the unchanged original
counting problem. Its complementary non-Product resource is selected from the
exact ordinary obstruction, with no caller-supplied hardness hypothesis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiBase
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GenericOrdinarySource (field count arity table family)
end E
namespace N
export NoXNonproduct (blocks balanced row_nonproduct)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))
variable (antiLabel : Fin (E.count G src)) (v w : E.field G src)
variable (hv : v≠0) (hw : w≠0)
variable (ha_lit : (⟨E.arity G src antiLabel.val,E.table G src antiLabel⟩ : AnySignature (E.field G src))=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)

include negative hv hw ha_lit in
theorem hard_of_even (bad : OrdinaryNegativeXUniversalResource.EvenBad (E.table G src)) :
    NoXWeightedAntiResourcesOriginal.Hard G := by
  obtain ⟨n,B,hbad⟩ := bad
  exact NoXWeightedAntiResourcesOriginal.countingHard G src antiLabel v w hv hw ha_lit
    B.rows (N.blocks G src negative) hbad (N.row_nonproduct G src negative)
    B.balanced (N.balanced G src negative)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiBase
end
