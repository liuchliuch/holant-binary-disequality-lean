import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareDataCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeFamily
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeProductCriterion

/-! The literal whole Product alternative supplies the native criterion,
including the actual X edge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductPositive
open Holant Holant.Tractable Holant.Algebraic
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'

def WholeProduct : Prop:=∀i,Product (fun z=>(D.table i z : AlgebraicComplex))

theorem positive (all : WholeProduct target D) :
    TractX (familyAction sourceKBasis
      (GlobalCloseCompletionUnaryDescentSource.ambient D.K D.table)) := by
  apply NoINativeProductCriterion.criterion
  · exact Set.finite_range _
  · rintro f ⟨i,rfl⟩
    exact all i

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductPositive
end
