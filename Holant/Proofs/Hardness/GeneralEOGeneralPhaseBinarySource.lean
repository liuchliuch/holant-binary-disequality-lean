import Holant.Proofs.Hardness.GeneralEOGeneralPhaseBinaryPins
import Holant.Proofs.Hardness.GeneralEOBinaryARS

/-! A genuinely non-ARS actual central binary supplies full literal pin
elimination over the unchanged original family. The binary-only equivalence
with unequal norms is proved, rather than assumed at arbitrary arity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOGeneralPhaseBinarySource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace S
export GeneralEOPhaseExtractionSource (inclusion)
end S
namespace P
export GeneralEOGeneralPhaseBinaryPins (zero_sided nonresonant exponent)
end P
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (B : Network AlgebraicComplex 2) (BL : Labelling B.shape s 1 a)
variable (hL : LabelledNetwork.Exact G B BL) (hN : ∀e,B.edge e=Signature.disequality)
variable (hE : Signature.CentralSupport B.denote)

include hL hN hE in
/-- This applies to the actual graph's two complex coefficients. -/
theorem unequal_norms
    (hn : ‖S.inclusion (B.denote ![false,true])‖≠
      ‖S.inclusion (B.denote ![true,false])‖) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) := by
  classical
  by_cases hp : B.denote ![false,true]=0
  · have hq : B.denote ![true,false]≠0 := by
      intro hq
      exact hn (by simp [hp,hq])
    exact P.zero_sided G B BL hL hN hE ![true,false] hq (Or.inr ⟨hp,hq⟩)
  by_cases hq : B.denote ![true,false]=0
  · exact P.zero_sided G B BL hL hN hE ![false,true] hp (Or.inl ⟨hp,hq⟩)
  apply P.nonresonant G B BL hL hN hE hp hq
  intro he
  have he' := congrArg S.inclusion he
  simp only [map_pow] at he'
  have hq' : S.inclusion (B.denote ![true,false])≠0 := by
    exact fun hz => hq (S.inclusion.injective (by simpa using hz))
  apply GeneralGeometricCapLocal.infinite_of_unequal_norms _ _ hq' hn
    (P.exponent G B) (GeneralEONonARSPinningFiniteCap.exponent_pos _)
  rw [div_pow,he',div_self (pow_ne_zero _ hq')]

include hL hN hE in
/-- No hardness alternative is needed when the actual binary itself is non-ARS. -/
theorem nonars
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (B.map S.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) := by
  apply unequal_norms G B BL hL hN hE
  intro hn
  apply hA
  apply GeneralEOBinaryARS.ars_of_equal_norm _
    (GeneralEOPhaseExtractionFieldBridge.map_central S.inclusion B hE)
  simpa only [Network.denote_map] using hn


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOGeneralPhaseBinarySource
