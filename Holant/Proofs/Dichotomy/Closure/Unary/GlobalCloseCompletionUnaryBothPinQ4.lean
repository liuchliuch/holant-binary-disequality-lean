import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinOrdering
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinHighBinary
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinCapTrees
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinQuaternary
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinSignedRecover
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternarySmallForm

/-! A minimal actual quaternary prime has both-sided small cap trees. Their
cubic equations give the paired normal form at its chosen support pivot;
the exact signed physical conversion then supplies an unsigned paired graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinQ4
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain OrdinaryNegativeCubicGadgets
namespace D
export GlobalCloseCompletionUnaryBothPinNormalized (Data)
end D
namespace M
export GlobalCloseCompletionUnaryBothPinMinimal (arity)
end M
namespace C
export GlobalCloseCompletionUnaryBothPinHighBinary (caps_small)
export GlobalCloseCompletionUnaryBothPinCapTrees (cubic)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature L (b i.val))
variable (pins : Bool→NoXOrdinaryGraphAdjoin.Output H 1)
variable (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
variable (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H))
variable (N : D.Data H 4) (size : 4=M.arity L H pins pinsForm negative)

include pinsForm negative N size in
theorem exists_output : Nonempty (GlobalCloseCompletionUnarySignedPairConversion.Output (H:=H)) := by
  obtain ⟨V,order⟩:=GlobalCloseCompletionUnaryBothPinOrdering.exists_order H N
  have bound : 3<M.arity L H pins pinsForm negative := by omega
  have tiny:=C.caps_small L H pins pinsForm negative (by decide : 0<3) V bound
  have cross : GlobalCloseCompletionUnaryProductInteraction.minor V.value 0 2=0 ∧
      GlobalCloseCompletionUnaryProductInteraction.minor V.value 0 3=0 ∧
      GlobalCloseCompletionUnaryProductInteraction.minor V.value 1 2=0 ∧
      GlobalCloseCompletionUnaryProductInteraction.minor V.value 1 3=0 := by
    rcases order with none|edge
    · exact ⟨none 0 2 (by decide),none 0 3 (by decide),none 1 2 (by decide),none 1 3 (by decide)⟩
    · exact GlobalCloseCompletionUnaryQuaternarySmallForm.cross V.value (fun i=>tiny i false) edge
  have origin : V.value ![false,false,false,false]≠0 := by
    simpa only [show (![false,false,false,false] : Fin 4→Bool)=(fun _=>false) by
      funext i;fin_cases i <;>rfl] using V.origin
  have cubes : ∀i bit,GlobalCloseCompletionUnaryTernarySmallCubic.cubic
      (GlobalCloseCompletionUnaryBothPinQuaternary.cap bit V.value i)=0 :=
    C.cubic L H pins pinsForm negative V.actual bound V.mask
  obtain ⟨support,det⟩:=GlobalCloseCompletionUnaryBothPinQuaternary.paired_nonsingular
    V.value V.value_prime origin cross.1 cross.2.1 cross.2.2.1 cross.2.2.2 cubes
  exact ⟨GlobalCloseCompletionUnaryBothPinSignedRecover.produce H V support det
    (fun v=>show Macro H 1 from ⟨(pins v).network,(pins v).labels,(pins v).exact,(pins v).ordinary⟩) pinsForm⟩

def produce : GlobalCloseCompletionUnarySignedPairConversion.Output (H:=H) :=
  Classical.choice (exists_output L H pins pinsForm negative N size)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinQ4
end
