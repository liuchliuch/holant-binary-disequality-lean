import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureRecipeAffine
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLegalAffine

/-! The legal-product closure used in phase classification is derived from
actual native graph sources and paired EO hardness, never assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureLegalAffineSource
open Holant Holant.Tractable Holant.Algebraic
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K := D.K.algebra'
variable (badP : ¬NoIPureProductPositive.WholeProduct target D)
variable (uniform : NoIPureSquareFour.GraphFour target D) (noHard : ¬target.Hard)

include badP uniform noHard in
theorem graph {n : ℕ} (N : NativeAntiTargetSource.Output D.table n) :
    NoIPurePhaseLegalAffine.LegalAffine (fun z => (N.network.denote z : AlgebraicComplex)) := by
  intro m k ps legal
  exact NoIPureRecipeAffine.affine target D badP uniform noHard (fun _ : Fin k => N) ps legal

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureLegalAffineSource
end
