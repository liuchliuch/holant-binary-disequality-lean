import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockRelabel
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Actual odd resources retain every port and private variable under a
literal finite-table inclusion. No normalization or new gadget is inserted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddRelabel
open Holant Holant.Tractable
open OrdinaryNegativeXUniversalResource
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe ports_eq coefficient_eq)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s t n : ℕ} {a b : ℕ→ℕ}
variable (F : (i : Fin s)→Signature K (a i.val)) (H : (i : Fin t)→Signature K (b i.val))
variable (labels : Fin s→Fin t)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨a i.val,F i⟩)
variable (row : OddResource (s:=s) a n)

def resource : OddResource (s:=t) b n where
  privateCount:=row.privateCount
  rows:=R.exactRecipe labels F H literal row.rows
  constant_even q:=by
    change Even ((OrdinaryNegativeMixedBlockData.ports (R.exactRecipe labels F H literal row.rows) 0).count (.inl q))
    rw [OrdinaryNegativeMixedBlockRelabel.exactRecipe,R.ports_eq]
    exact row.constant_even q
  boundary_odd i:=by
    change Odd ((OrdinaryNegativeMixedBlockData.ports (R.exactRecipe labels F H literal row.rows) 0).count (.inr (Fin.castAdd row.privateCount i)))
    rw [OrdinaryNegativeMixedBlockRelabel.exactRecipe,R.ports_eq]
    exact row.boundary_odd i
  private_even i:=by
    change Even ((OrdinaryNegativeMixedBlockData.ports (R.exactRecipe labels F H literal row.rows) 0).count (.inr (Fin.natAdd n i)))
    rw [OrdinaryNegativeMixedBlockRelabel.exactRecipe,R.ports_eq]
    exact row.private_even i

theorem signature : (resource F H labels literal row).signature H=row.signature F := by
  funext x
  unfold OddResource.signature OrdinaryNegativeMixedBlockSource.trace
  apply Finset.sum_congr rfl
  intro y _
  exact R.coefficient_eq labels F H literal row.rows 0 _

theorem ambient : (resource F H labels literal row).ambient H=row.ambient F := by
  funext x
  change ((resource F H labels literal row).signature H x : AlgebraicComplex)=(row.signature F x : AlgebraicComplex)
  rw [signature]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddRelabel
end
