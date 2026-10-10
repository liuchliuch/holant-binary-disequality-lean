import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseClassification
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseWholeFamilyConsumerCore

/-! Apply the proved phase selector once to the actual tensor of all nonzero
original rows. That same selected phase supplies the native family criterion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyClassification
open Holant Holant.Tractable Holant.Algebraic
namespace W
export NoIPurePhaseWholeFamily (whole wholeValue row twist common_chart)
end W
namespace R
export NoIPurePhaseRankTwoScalar (rho rho_nonzero)
end R
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'
variable (closed : NoIPureClosedMinimal.C.Closed (W.wholeValue target D))
variable (uniform : NoIPureChargeTwoFamily.UniformFour (W.wholeValue target D))
variable (legal : NoIPurePhaseLegalAffine.LegalAffine (W.wholeValue target D))
include closed uniform legal

/-- Exactly one phase index is chosen on the original physical bundle. -/
theorem phase_index : ∃k : Fin 4,
    Affine (W.twist (R.rho^k.val) (W.wholeValue target D)) :=
  NoIPurePhaseClassification.classified (W.whole target D).2.network.denote
    closed uniform legal

/-- This same index corrects every original row, including zero rows. -/
theorem all_rows : ∃k : Fin 4,∀j,
    Affine (W.twist (R.rho^k.val) (W.row target D j)) :=
  W.common_chart target D (fun k : Fin 4=>R.rho^k.val)
    (fun k=>pow_ne_zero k.val R.rho_nonzero) (phase_index target D closed uniform legal)

theorem positive : TractX (familyAction sourceKBasis
    (GlobalCloseCompletionUnaryDescentSource.ambient D.K D.table)) :=
  NoIPurePhaseWholeFamilyConsumer.classified target D
    (fun k : Fin 4=>R.rho^k.val) (fun k=>pow_ne_zero k.val R.rho_nonzero)
    (Or.inl (phase_index target D closed uniform legal))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyClassification
end
