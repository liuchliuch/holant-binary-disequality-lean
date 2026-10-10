import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureGraphGuards
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseWholeFamilyClassification
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseWholeFamilyConsumer
import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementComplete
import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementReturn

/-! Unconditional source-preserving classification of the remaining pure
weighted Eq4 event. All support, charge, recipe and common-phase producers
are invoked internally, and the original target is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureComplete
open Holant Holant.Tractable Holant.Algebraic
namespace W
export NoIPurePhaseWholeFamily (whole wholeValue twist)
end W
namespace R
export NoIPurePhaseRankTwoScalar (rho rho_nonzero)
end R
namespace A
export GlobalCloseCompletionUnaryDescentSource (ambient)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false

theorem alphabet (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target) :
    Tract (familyAction sourceKBasis (A.ambient D.K D.table)) ∨ target.Hard := by
  classical
  letI : Algebra ℚ D.K := D.K.algebra'
  by_cases positive : Tract (familyAction sourceKBasis (A.ambient D.K D.table))
  · exact Or.inl positive
  by_cases hard : target.Hard
  · exact Or.inr hard
  let N := (W.whole target D).2
  have guards := NoIPureGraphGuards.graph target D hard positive N
  have common := NoIPurePhaseWholeFamilyClassification.positive target D
    guards.1 guards.2.1 guards.2.2
  exact False.elim (positive common.tract)

variable {s degree : ℕ} {a : ℕ → ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (H : (i : Fin s) → Signature L (a i.val)) (F : FixedField L degree)

theorem classified (pure : GlobalCloseCompletionComplementQ4ClassificationBlocks.Pure H) :
    Tract (familyAction sourceKBasis (A.ambient L H)) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard := by
  let D := NoIPureAlphabetSource.produce L H F pure
  rcases alphabet (NoISuppliedIdentityConsumer.target L H F)
    (NoIPureSquareAlphabet.ofAlphabet L H F D) with good|hard
  · exact Or.inl (NoIPureAlphabetReturn.positive L H F D good)
  · exact Or.inr hard

theorem event (D : NoISparseComplementComplete.PureData L H F) :
    Tract (familyAction sourceKBasis (A.ambient L H)) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard := by
  letI : Algebra ℚ D.source.K := D.source.K.algebra'
  exact NoISparseComplementReturn.classified L H F D.source
    (classified D.source.K D.source.table D.source.presentation D.pure)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureComplete
end
