import Holant.Proofs.Dichotomy.Retained.StableDenseParityAlgebra

/-! Faithful coefficient transport of the literal cancellation/cap tests.
The map acts only on coefficients; the cap index and orientation are unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseParityMap
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (M : Signature K 4)

def mapped : Signature L 4 := fun x => φ (M x)

theorem even (he : EvenSupport M) : EvenSupport (mapped φ M) := by
  intro x hx
  change φ (M x) = 0
  rw [he x hx,map_zero]

theorem cancellation (h : EightVertexCancellationLocal.Applicable M) :
    EightVertexCancellationLocal.Applicable (mapped φ M) := by
  refine ⟨even φ M h.even,?_,?_,?_,?_,?_,?_⟩
  · simpa [mapped,entries] using congrArg φ h.cancel
  · simpa [mapped,entries] using (map_ne_zero φ).mpr h.outer
  · exact (map_ne_zero φ).mpr h.c
  · exact (map_ne_zero φ).mpr h.z
  · simpa [mapped,entries] using (map_ne_zero φ).mpr h.sum
  · rcases h.additional with first | second
    · left
      simpa [mapped,entries] using (map_ne_zero φ).mpr first
    · right
      simpa [mapped,entries] using (map_ne_zero φ).mpr second

theorem oriented (k : GeneralCancellationCapPin.Choice) :
    GeneralCancellationCapPin.oriented (mapped φ M) k =
      (φ (GeneralCancellationCapPin.oriented M k).1,
       φ (GeneralCancellationCapPin.oriented M k).2) := by
  rcases k with ⟨c,rev⟩
  fin_cases c <;> cases rev <;>
    simp [GeneralCancellationCapPin.oriented,GeneralCancellationCapPin.coefficients,
      mapped,entries,map_add]

@[simp] theorem p (k : GeneralCancellationCapPin.Choice) :
    EightVertexCapLocal.p (mapped φ M) k = φ (EightVertexCapLocal.p M k) :=
  congrArg Prod.fst (oriented φ M k)

@[simp] theorem q (k : GeneralCancellationCapPin.Choice) :
    EightVertexCapLocal.q (mapped φ M) k = φ (EightVertexCapLocal.q M k) :=
  congrArg Prod.snd (oriented φ M k)

theorem cap_coefficients (k : GeneralCancellationCapPin.Choice)
    (h : EightVertexCapLocal.Coefficients M k) :
    EightVertexCapLocal.Coefficients (mapped φ M) k := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [mapped,entries] using congrArg φ h.cancel
  · simpa [mapped,entries] using (map_ne_zero φ).mpr h.outer
  · simpa [mapped,entries] using (map_ne_zero φ).mpr h.c
  · simpa [mapped,entries] using (map_ne_zero φ).mpr h.z
  · simpa [mapped,entries] using (map_ne_zero φ).mpr h.sum
  · rcases h.additional with first | second
    · left
      simpa [mapped,entries] using (map_ne_zero φ).mpr first
    · right
      simpa [mapped,entries] using (map_ne_zero φ).mpr second

theorem cap (h : EightVertexCapLocal.Applicable M) :
    EightVertexCapLocal.Applicable (mapped φ M) := by
  obtain ⟨he,k,hk⟩ := h
  exact ⟨even φ M he,k,cap_coefficients φ M k hk⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseParityMap
end
