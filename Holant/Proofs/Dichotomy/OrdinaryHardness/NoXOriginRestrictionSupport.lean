import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalPairSupport
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalPermutation

/-! Rank decrease for literal restrictions of independent original ports.
The arbitrary selected information coordinates are only relabelled in the
chart; no compressed row is inserted into the source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginRestrictionSupport
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n r : ℕ} {f : Signature AlgebraicComplex n}

theorem rank_le (D : SystematicSupport f r) : r≤n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective D.ports D.injective

theorem pin_chart (D : SystematicSupport f (r+1)) (i : Fin (r+1)) (bit : Bool) :
    Nonempty (SystematicSupport (pinMask f (D.ports i) bit) r) := by
  let E:=NoXLocalPermutation.logical D (Equiv.swap 0 i)
  have first : E.ports 0=D.ports i := by simp [E,NoXLocalPermutation.logical]
  have chart:=E.pinFirst bit
  rw [first] at chart
  exact ⟨chart⟩

theorem equal_chart (D : SystematicSupport f (r+2)) (i j : Fin (r+2)) (ne : i≠j) :
    Nonempty (SystematicSupport (NoXLocalPairSupport.equalMask f (D.ports i) (D.ports j)) (r+1)) := by
  obtain ⟨e,he0,he1⟩ := NoXLocalPermutation.pair_permutation (0 : Fin (r+2)) 1 i j (by intro he;have hv:=congrArg Fin.val he;change 0=1 at hv;omega) ne
  let E:=NoXLocalPermutation.logical D e
  have first : E.ports 0=D.ports i := by simp only [E,NoXLocalPermutation.logical,he0]
  have second : E.ports (Fin.succ 0)=D.ports j := by
    change D.ports (e 1)=D.ports j
    rw [he1]
  have chart:=NoXLocalPairSupport.equalChart E
  rw [first,second] at chart
  exact ⟨chart⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginRestrictionSupport
end
