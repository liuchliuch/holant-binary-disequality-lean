import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseWholeFamily
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseWholeFamilyCriterion
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeFamily

/-! Positive whole-family consumers use one common chart on one actual
nonzero-row tensor. This interface does not assume independently chosen
charts for individual graphs or rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyConsumer
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace W
export NoIPurePhaseWholeFamily (twist row wholeValue all_rows common_chart)
end W
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'

theorem phase (r : AlgebraicComplex) (nonzero : r≠0)
    (good : Affine (W.twist r (W.wholeValue target D))) :
    TractX (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient D.K D.table)) :=
  NoIPurePhaseWholeFamilyCriterion.phase D.K D.table r nonzero good

theorem product (good : Product (W.wholeValue target D)) :
    TractX (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient D.K D.table)) :=
  NoIPurePhaseWholeFamilyCriterion.product D.K D.table good

/-- The arbitrary phase family is selected once on the literal bundle. -/
theorem classified {α : Type} (phaseValues : α→AlgebraicComplex)
    (nonzero : ∀i,phaseValues i≠0)
    (good : (∃i,Affine (W.twist (phaseValues i) (W.wholeValue target D))) ∨
      Product (W.wholeValue target D)) :
    TractX (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient D.K D.table)) := by
  rcases good with ⟨i,hi⟩|hp
  · exact phase target D (phaseValues i) (nonzero i) hi
  · exact product target D hp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyConsumer
end
