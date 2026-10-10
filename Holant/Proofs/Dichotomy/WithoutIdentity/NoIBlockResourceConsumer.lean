import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationBlocks
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIDiagonalProductSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoISuppliedIdentityConsumer

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIBlockResourceConsumer
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)

theorem diagonal (D : GlobalCloseCompletionComplementQ4ClassificationBlocks.DiagonalProduct H) :
    Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L H)) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard := by
  exact NoISuppliedIdentityConsumer.tract_or_hard L H F
    (NoIDiagonalProductSource.produce L H F D.graph D.scale 1 D.ratio 1 D.ratio
      D.scale_ne one_ne_zero D.ratio_ne one_ne_zero D.ratio_ne D.value)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIBlockResourceConsumer
end
