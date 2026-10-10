import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockRelabel
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Exact old-block transport through a finite-table embedding. Private
sums, all physical incidences, and nonaffinity witnesses are unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRelabel
open Holant Holant.Tractable
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe coefficient_eq even_recipe)
end R
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s t : ℕ} {a b : ℕ→ℕ}
variable (F : (i : Fin s)→Signature K (a i.val)) (H : (i : Fin t)→Signature K (b i.val))
variable (labels : Fin s→Fin t)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨a i.val,F i⟩)
variable {n : ℕ} (row : B.Block (s:=s) (b:=a) n)
def block : B.Block (s:=t) (b:=b) n where
  privateCount := row.privateCount
  rows := R.exactRecipe labels F H literal row.rows
  balanced := R.even_recipe labels (fun i=>congrArg Sigma.fst (literal i)) row.rows row.balanced

theorem value : (block F H labels literal row).signature H=row.signature F := by
  funext x
  unfold OrdinaryNegativeSparseMixingSource.Block.signature OrdinaryNegativeMixedBlockSource.trace
  apply Finset.sum_congr rfl
  intro q _
  exact R.coefficient_eq labels F H literal row.rows 0 _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRelabel
end
