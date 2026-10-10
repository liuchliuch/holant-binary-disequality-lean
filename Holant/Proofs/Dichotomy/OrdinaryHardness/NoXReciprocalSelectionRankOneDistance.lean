import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneParity

/-! The two unsigned orientation counts exhaust the physical Hamming distance. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneDistance
open Holant
namespace P
export NoXReciprocalSelectionRankOne (ports)
export NoXSeparateSignedProjection (signedCount)
end P
namespace D
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end D
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
theorem counts (x y : Fin n→Bool) :
    D.distance x y=P.signedCount (P.ports x y) 0 false+P.signedCount (P.ports x y) 0 true := by
  unfold D.distance P.signedCount
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hx:x i <;> cases hy:y i <;> simp [P.ports,hx,hy]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneDistance
end
