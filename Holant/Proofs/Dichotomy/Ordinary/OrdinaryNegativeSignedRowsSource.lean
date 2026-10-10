import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsCore

/-! Fixed-field actual-label source for a whole signed-row product. Only the
sum of original bundle incidences must be even: each factor may be odd. All
private bits are disjoint and every tensor shorthand has been expanded. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsSource
open Holant Holant.Algebraic
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
namespace S
export OrdinaryNegativeSignedRowsCore (recipe even_recipe trace_value)
end S
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K] {s n m r : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s) (f : Signature K n)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity n i.val,table f i⟩)
variable (p : Fin r→Fin n→Port m) (even : ∀j,Even (∑i,I.bundleSize (p i) j))

def block : B.Block (s:=s) (b:=b) m where
  privateCount := r*n
  rows := R.exactRecipe labels (table f) H literal (S.recipe p)
  balanced := R.even_recipe labels (fun j=>congrArg Sigma.fst (literal j)) _ (S.even_recipe p even)

theorem block_value (z : Fin m→Bool) :
    (block H labels f literal p even).signature H z=∏i,f (word (p i) z) := by
  unfold OrdinaryNegativeSparseMixingSource.Block.signature block M.trace
  simp_rw [R.coefficient_eq]
  exact S.trace_value f p z

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsSource
end
