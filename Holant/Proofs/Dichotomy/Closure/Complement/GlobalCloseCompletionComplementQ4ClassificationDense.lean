import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationResources
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4PairedConsumer

/-! Exhaustive dense complementary-row classification on the exact native
source. Whole-family tractability is returned only by the proved anchor
consumer; finite physical resources remain explicit for their own consumers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationDense
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GlobalCloseCompletionComplementQ4Series (row)
end S
namespace R
export GlobalCloseCompletionComplementQ4ClassificationReduction (alternatives)
end R
namespace P
export GlobalCloseCompletionComplementQ4PairedSource (produce)
export GlobalCloseCompletionComplementQ4ClassificationPaired (fourth_split)
end P
namespace B
export GlobalCloseCompletionComplementQ4ClassificationBlocks (Pure DiagonalProduct)
end B
namespace A
export GlobalCloseCompletionUnaryDescentSource (ambient)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {size degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin size)→Signature L (arity i.val)) (F : FixedField L degree)

theorem classified (N : NativeAntiTargetSource.Output H 4) (a b c d : L)
    (form : N.network.denote=S.row a b c d) (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    Tract (familyAction sourceKBasis (A.ambient L H)) ∨ B.Pure H ∨ Nonempty (B.DiagonalProduct H) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard := by
  let phi : L→+*ℂ:=(algebraicClosure ℚ ℂ).subtype.comp L.subtype
  rcases R.alternatives H N a b c d form ha hb hd with paired|outputs
  · let normal:=P.produce H N a b c d form ha hb hc hd paired
    rcases P.fourth_split normal.r normal.fourth with real|imaginary
    · rcases GlobalCloseCompletionComplementQ4PairedConsumer.real_classified L H F normal ha real with positive|hard
      · exact Or.inl positive.tract
      · exact Or.inr (Or.inr (Or.inr hard))
    · exact Or.inr (GlobalCloseCompletionComplementQ4ClassificationResources.imaginary H F phi
        normal.graph a normal.r normal.s normal.t normal.value ha imaginary normal.sign)
  · exact Or.inr (GlobalCloseCompletionComplementQ4ClassificationResources.redundant H F phi N a b c d form ha (Classical.choice outputs))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationDense
end
