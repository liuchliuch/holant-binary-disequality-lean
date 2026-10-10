import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementSelect
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationBlockSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIBlockResourceConsumer

/-! The single-middle branch is consumed with its actual original native
source. Its sole remaining structural output is a literal scalar Eq4 graph;
all diagonal products and Ising branches return whole-family results. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementSingle
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
namespace B
export GlobalCloseCompletionComplementQ4ClassificationBlocks (Pure)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)

abbrev Outcome := Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L H)) ∨
  (NoISuppliedIdentityConsumer.target L H F).Hard ∨ B.Pure H

theorem source (N : NoISparseComplementSelect.Single H) : Outcome L H F := by
  rcases GlobalCloseCompletionComplementQ4ClassificationBlockSource.nonzero_left H F
    ((algebraicClosure ℚ ℂ).subtype.comp L.subtype) N.graph N.a N.b N.form N.first with pure|product|hard
  · exact Or.inr (Or.inr pure)
  · obtain ⟨product⟩:=product
    rcases NoIBlockResourceConsumer.diagonal L H F product with tract|hard
    · exact Or.inl tract
    · exact Or.inr (Or.inl hard)
  · exact Or.inr (Or.inl hard)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementSingle
end
