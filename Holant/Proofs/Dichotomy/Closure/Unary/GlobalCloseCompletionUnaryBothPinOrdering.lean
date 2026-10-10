import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinNormalized
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryNoInteractions
import Holant.Dihedral.CompatibleClosure.PairOrder

/-! The actual supported-word prime chooses its own interaction order. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinOrdering
open Holant
namespace D
export GlobalCloseCompletionUnaryBothPinNormalized (Data)
end D
namespace I
export GlobalCloseCompletionUnaryNoInteractions (NoInteractions)
export GlobalCloseCompletionUnaryProductInteraction (minor)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (a i.val))

theorem exists_order (N : D.Data H (n+2)) : ∃V : D.Data H (n+2),
    I.NoInteractions V.value ∨ I.minor V.value 0 1≠0 := by
  classical
  by_cases none : I.NoInteractions N.value
  · exact ⟨N,Or.inl none⟩
  · unfold I.NoInteractions at none
    push Not at none
    obtain ⟨i,j,different,edge⟩:=none
    let e:=Holant.Dihedral.CompatibleClosure.pairOrder i j
    refine ⟨N.reindex e,Or.inr ?_⟩
    rw [GlobalCloseCompletionUnaryBothPinNormalized.Data.reindex_minor,
      Holant.Dihedral.CompatibleClosure.pairOrder_first i j different,
      Holant.Dihedral.CompatibleClosure.pairOrder_second]
    exact edge

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinOrdering
end
