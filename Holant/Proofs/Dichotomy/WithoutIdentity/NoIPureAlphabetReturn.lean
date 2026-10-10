import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureAlphabetData
import Holant.Tractable.Downward

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureAlphabetReturn
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
variable (D : NoIPureAlphabetData.Data L H F)
namespace A
export GlobalCloseCompletionUnaryDescentSource (ambient)
end A
local instance : Algebra ℚ D.K:=D.K.algebra'

theorem positive (h : Tract (familyAction sourceKBasis (A.ambient D.K D.table))) :
    Tract (familyAction sourceKBasis (A.ambient L H)) :=
  h.mono_family (Set.image_mono D.retained)

theorem hard (h : (NoISuppliedIdentityConsumer.target D.K D.table D.presentation).Hard) :
    (NoISuppliedIdentityConsumer.target L H F).Hard :=
  NoIOrdinaryRaw.Target.Hard.compose (S:=NoISuppliedIdentityConsumer.target D.K D.table D.presentation)
    (T:=NoISuppliedIdentityConsumer.target L H F) h D.source

theorem classified (h : Tract (familyAction sourceKBasis (A.ambient D.K D.table)) ∨
    (NoISuppliedIdentityConsumer.target D.K D.table D.presentation).Hard) :
    Tract (familyAction sourceKBasis (A.ambient L H)) ∨
    (NoISuppliedIdentityConsumer.target L H F).Hard :=
  h.imp (positive L H F D) (hard L H F D)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureAlphabetReturn
end
