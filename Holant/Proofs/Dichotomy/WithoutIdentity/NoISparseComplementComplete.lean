import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementBalanced
import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementReturn

/-! Complete complementary-q4 source continuation on the unchanged old
native family. Its sole unconsumed structure is an actual scalar Eq4 over a
fully retained native table with the exact common-frame back source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementComplete
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)

structure PureData : Type 1 where
  source : NoISparseComplementData.Data L H F
  pure : letI : Algebra ℚ source.K:=source.K.algebra';
    GlobalCloseCompletionComplementQ4ClassificationBlocks.Pure source.table

abbrev Outcome :=
  Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L H)) ∨
    (NoISuppliedIdentityConsumer.target L H F).Hard ∨ Nonempty (PureData L H F)

theorem source (q : Signature L 4) (even : EvenSupport q)
    (first : (entries q).a≠0) (last : (entries q).x≠0)
    (comp : PaperTerminalBridgeComplementSign.Complement q)
    (actual : Gadget.RealizesUpTo (PaperTerminalBridgeDenseSemantic.family H) .disequality q) : Outcome L H F := by
  let D:=NoISparseComplementSource.produce L H F q even first last comp actual
  letI : Algebra ℚ D.K:=D.K.algebra'
  rcases NoISparseComplementBalanced.source D.K D.table D.presentation D.graph
    (D.coeff 0) (D.coeff 1) (D.coeff 2) (D.coeff 3) D.form D.first with tract|hard|pure
  · exact Or.inl (NoISparseComplementReturn.positive L H F D tract)
  · exact Or.inr (Or.inl (NoISparseComplementReturn.hard L H F D hard))
  · exact Or.inr (Or.inr ⟨⟨D,pure⟩⟩)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementComplete
end
