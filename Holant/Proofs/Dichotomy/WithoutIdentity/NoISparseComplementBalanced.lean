import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementSingle
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationDense

/-! Every actual balanced complementary q4, with arbitrary middle zeros,
now reaches a whole-family result or one explicit actual scalar Eq4 resource.
All calls keep the same finite native dictionary and exact answer field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementBalanced
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
namespace S
export GlobalCloseCompletionComplementQ4Series (row)
end S
namespace B
export GlobalCloseCompletionComplementQ4ClassificationBlocks (Pure pure_of_zero)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (arity i.val)) (F : FixedField L degree)

theorem source (N : NativeAntiTargetSource.Output H 4) (a b c d : L)
    (form : N.network.denote=S.row a b c d) (first : a≠0) : NoISparseComplementSingle.Outcome L H F := by
  cases NoISparseComplementSelect.produce H N a b c d form first with
  | pure graph p live value=>exact Or.inr (Or.inr (B.pure_of_zero H graph p live value))
  | single result=>exact NoISparseComplementSingle.source L H F result
  | dense result=>
    rcases GlobalCloseCompletionComplementQ4ClassificationDense.classified L H F
      result.graph result.a result.b result.c result.d result.form
      result.first result.second result.third result.fourth with tract|pure|product|hard
    · exact Or.inl tract
    · exact Or.inr (Or.inr pure)
    · obtain ⟨product⟩:=product
      rcases NoIBlockResourceConsumer.diagonal L H F product with tract|hard
      · exact Or.inl tract
      · exact Or.inr (Or.inl hard)
    · exact Or.inr (Or.inl hard)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementBalanced
end
