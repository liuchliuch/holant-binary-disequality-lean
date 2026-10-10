import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseWholeFamilyConsumerCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureAlphabetReturn
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareAlphabet

/-! Retention returns one whole-family chart to every exact original label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyConsumer
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
section Original
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
variable (A : NoIPureAlphabetData.Data L H F)

/-- Retention returns the common-chart result to all original labels. -/
theorem original {α : Type} (phaseValues : α→AlgebraicComplex)
    (nonzero : ∀i,phaseValues i≠0)
    (good : (∃i,Affine (W.twist (phaseValues i) (W.wholeValue
      (NoISuppliedIdentityConsumer.target L H F) (NoIPureSquareAlphabet.ofAlphabet L H F A)))) ∨
      Product (W.wholeValue (NoISuppliedIdentityConsumer.target L H F)
        (NoIPureSquareAlphabet.ofAlphabet L H F A))) :
    Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L H)) := by
  apply NoIPureAlphabetReturn.positive L H F A
  exact (classified (NoISuppliedIdentityConsumer.target L H F)
    (NoIPureSquareAlphabet.ofAlphabet L H F A) phaseValues nonzero good).tract
/-- Failure of the original whole-family criterion excludes every proposed
common chart on this same single physical bundle. -/
theorem original_obstruction {α : Type} (phaseValues : α→AlgebraicComplex)
    (nonzero : ∀i,phaseValues i≠0)
    (negative : ¬Tract (familyAction sourceKBasis
      (GlobalCloseCompletionUnaryDescentSource.ambient L H))) :
    (∀i,¬Affine (W.twist (phaseValues i) (W.wholeValue
      (NoISuppliedIdentityConsumer.target L H F) (NoIPureSquareAlphabet.ofAlphabet L H F A)))) ∧
    ¬Product (W.wholeValue (NoISuppliedIdentityConsumer.target L H F)
      (NoIPureSquareAlphabet.ofAlphabet L H F A)) := by
  constructor
  · intro i hi
    exact negative (original L H F A phaseValues nonzero (Or.inl ⟨i,hi⟩))
  · intro hp
    exact negative (original L H F A phaseValues nonzero (Or.inr hp))
end Original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyConsumer
end
