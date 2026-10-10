import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalEvenCharacterPhase

/-! Separately even positive/negative occurrence counts imply even total
incidence of the complete finite original-row bundle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateParity
open Holant
open OrdinaryNegativeSignedPortsCore (Port)
open scoped BigOperators
namespace P
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
variable {m k : ℕ} {n : Fin m→ℕ} (ps : (i : Fin m)→Fin (n i)→Port k)
variable (even : ∀q bit,Even (∑i,P.signedCount (ps i) q bit))
include even in
theorem total_even (q : Fin k) : Even (∑i,P.bundleSize (ps i) q) := by
  have h (i : Fin m) : P.bundleSize (ps i) q=P.signedCount (ps i) q true+P.signedCount (ps i) q false := by
    rw [←NoXLocalEvenCharacterPhase.totalCount,Fintype.sum_bool]
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  exact (even q true).add (even q false)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateParity
end
