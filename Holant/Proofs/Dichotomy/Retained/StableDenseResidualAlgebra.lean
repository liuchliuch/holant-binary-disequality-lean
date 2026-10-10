import Holant.Proofs.Dichotomy.Retained.StableDenseParitySource

/-! The dense complete-pencil locus, kept as an explicit exceptional family.
The existing cancellation and weighted-cap tests cannot escape this locus:
their mandatory outer coefficient vanishes as soon as cancellation holds. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualAlgebra
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
variable {K : Type} [Field K]

/-- Equality of the four literal complementary products; neither corner is
normalized and no complexity conclusion is included in the definition. -/
def Products (M : Signature K 4) : Prop :=
  (entries M).a * (entries M).x = (entries M).b * (entries M).y ∧
  (entries M).a * (entries M).x = (entries M).c * (entries M).z ∧
  (entries M).a * (entries M).x = (entries M).d * (entries M).w

theorem cancellation_outer_zero (M : Signature K 4) (h : Products M)
    (cancel : (entries M).b + (entries M).y = 0) :
    (entries M).a * (entries M).x + (entries M).b ^ 2 = 0 := by
  linear_combination h.1 + (entries M).b * cancel

/-- This identity is valid even for zero cap weights. It retains the
actual weights instead of inserting a freely chosen root or phase. -/
theorem cap_outer_zero (M : Signature K 4) (h : Products M)
    (k : GeneralCancellationCapPin.Choice)
    (cancel : EightVertexCapLocal.p M k * (entries M).b +
      EightVertexCapLocal.q M k * (entries M).y = 0) :
    (EightVertexCapLocal.p M k * (entries M).a) *
      (EightVertexCapLocal.q M k * (entries M).x) +
      (EightVertexCapLocal.p M k * (entries M).b) ^ 2 = 0 := by
  linear_combination EightVertexCapLocal.p M k * EightVertexCapLocal.q M k * h.1 +
    (EightVertexCapLocal.p M k * (entries M).b) * cancel

theorem avoids_region (M : Signature K 4) (h : Products M) :
    ¬ StableDenseParitySource.Region M := by
  rintro (region | ⟨k,region⟩)
  · exact region.outer (cancellation_outer_zero M h region.cancel)
  · exact region.outer (cap_outer_zero M h k region.cancel)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualAlgebra
end
