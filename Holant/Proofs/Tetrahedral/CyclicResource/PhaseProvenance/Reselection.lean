import Holant.Proofs.Tetrahedral.CyclicResource.PhaseProvenance.FrozenSources


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open CyclicBoundary CyclicBoundary.PhysicalAttachments CyclicBoundary.ZeroEndpointDressing
open RingHomRealization
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rescale_action (A B : Kernel ℂ) (c κ s : ℂ) (hc : c ≠ 0)
    (he : B = c • A)
    (hB : Kernel.mul (Kernel.mul B Signature.disequality) hadamard =
      Kernel.mul hadamard ((2*κ) • phase s)) :
    Kernel.mul (Kernel.mul A Signature.disequality) hadamard =
      Kernel.mul hadamard ((2*(c⁻¹*κ)) • phase s) := by
  have ha : A = c⁻¹ • B := by rw [he,smul_smul,inv_mul_cancel₀ hc,one_smul]
  rw [ha]
  funext u v
  have h := congrArg (fun z : ℂ => c⁻¹*z) (congrFun (congrFun hB u) v)
  simp only [Kernel.mul,Fintype.sum_bool,Pi.smul_apply,smul_eq_mul] at h ⊢
  convert h using 1 <;> ring

variable {L : Type*} [Field L] [NumberField L]
variable (φ : L →+* ℂ) (F₀ : SignatureFamily L) (h₀ : ResidualTorsion F₀)
variable (q₀ : Signature L 4)
variable (hΛ : ResidualTorsion (fullRetainedDeck F₀ h₀ q₀))
variable (hgroup : completeGroup (fullRetainedDeck F₀ h₀ q₀) hΛ = completeGroup F₀ h₀)
variable {N : ℕ} (R : Representatives (mapFamily φ (fullRetainedDeck F₀ h₀ q₀)) N)
variable (hN : 0 < N)

def frozenIndex (s : {s : ℂ // s^N=1}) : completeGroup F₀ h₀ :=
  (phase_has_frozen_source φ F₀ h₀ q₀ hΛ hgroup R hN s).choose

def frozenRatio (s : {s : ℂ // s^N=1}) : L :=
  (phase_has_frozen_source φ F₀ h₀ q₀ hΛ hgroup R hN s).choose_spec.choose

theorem frozenRatio_ne_zero (s : {s : ℂ // s^N=1}) :
    frozenRatio φ F₀ h₀ q₀ hΛ hgroup R hN s ≠ 0 :=
  (phase_has_frozen_source φ F₀ h₀ q₀ hΛ hgroup R hN s).choose_spec.choose_spec.1

theorem frozen_equation (s : {s : ℂ // s^N=1}) :
    R.matrix s = φ (frozenRatio φ F₀ h₀ q₀ hΛ hgroup R hN s) •
      mapMatrix φ (actualRepresentative F₀ h₀ (frozenIndex φ F₀ h₀ q₀ hΛ hgroup R hN s)) :=
  (phase_has_frozen_source φ F₀ h₀ q₀ hΛ hgroup R hN s).choose_spec.choose_spec.2.1

/-- This is a derived representative system. Literal membership is proved
from fullRetainedDeck_representative, not supplied to the constructor. -/
def reselected : Representatives (mapFamily φ (fullRetainedDeck F₀ h₀ q₀)) N where
  matrix s := mapMatrix φ (actualRepresentative F₀ h₀
    (frozenIndex φ F₀ h₀ q₀ hΛ hgroup R hN s))
  scalar s := (φ (frozenRatio φ F₀ h₀ q₀ hΛ hgroup R hN s))⁻¹ * R.scalar s
  scalar_ne_zero s := mul_ne_zero (inv_ne_zero ((map_ne_zero φ).mpr
    (frozenRatio_ne_zero φ F₀ h₀ q₀ hΛ hgroup R hN s))) (R.scalar_ne_zero s)
  actual s := Gadget.realizes_of_mem _ .disequality _
    ⟨⟨2,binarySignature (actualRepresentative F₀ h₀
      (frozenIndex φ F₀ h₀ q₀ hΛ hgroup R hN s))⟩,
      fullRetainedDeck_representative F₀ h₀ q₀ _,rfl⟩
  action s := rescale_action _ _ _ _ _
    ((map_ne_zero φ).mpr (frozenRatio_ne_zero φ F₀ h₀ q₀ hΛ hgroup R hN s))
    (frozen_equation φ F₀ h₀ q₀ hΛ hgroup R hN s) (R.action s)

theorem reselected_literal (s : {s : ℂ // s^N=1}) :
    (⟨2,PhysicalAttachments.binary ((reselected φ F₀ h₀ q₀ hΛ hgroup R hN).matrix s)⟩ :
      AnySignature ℂ) ∈ mapFamily φ (fullRetainedDeck F₀ h₀ q₀) :=
  ⟨⟨2,binarySignature (actualRepresentative F₀ h₀
    (frozenIndex φ F₀ h₀ q₀ hΛ hgroup R hN s))⟩,
    fullRetainedDeck_representative F₀ h₀ q₀ _,rfl⟩

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
