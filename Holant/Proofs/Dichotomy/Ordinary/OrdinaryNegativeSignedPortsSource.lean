import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedPortsIncidence
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingOriginal

/-! Actual-label physical sources for arbitrary even signed bundles. The
unique private assignment theorem supplies the exact unsquared signature;
all original normalization coefficients remain in the same fixed field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedPortsSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open OrdinaryNegativeMixedBlockData OrdinaryNegativeSignedPortsCore
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe even_recipe coefficient_eq)
end R
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s n m : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val))
variable (labels : Fin 4→Fin s) (f : Signature K n)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity n i.val,table f i⟩)
variable (p : Fin n→Port m) (even : ∀j,Even (OrdinaryNegativeSignedPortsIncidence.bundleSize p j))

def block : B.Block (s:=s) (b:=b) m where
  privateCount := n
  rows := R.exactRecipe labels (table f) H literal (recipe p)
  balanced := R.even_recipe labels (fun j=>congrArg Sigma.fst (literal j)) _
    (OrdinaryNegativeSignedPortsIncidence.even_recipe p even)

theorem block_value (z : Fin m→Bool) :
    (block H labels f literal p even).signature H z=f (word p z) := by
  unfold OrdinaryNegativeSparseMixingSource.Block.signature block M.trace
  simp_rw [R.coefficient_eq]
  exact trace_value f p z

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedPortsSource
end
