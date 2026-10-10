import Holant.Proofs.Hardness.GeneralEOSkewPhaseSource

/-! Pull pin elimination through an actual native original-labelled binary.
Normalize at one nonzero coefficient; its complete table lies in the original
field, and the scalar-macro compiler removes every augmented occurrence. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOGeneralPhaseBinaryRemoval
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace S
export GeneralEOPhaseExtractionSource (Pinning)
end S
namespace P
export GeneralEOPinnedDescentPalette (pinnedValue)
end P
namespace F
export GeneralEONonARSPinningFieldBridge (lift denote_lift)
end F
namespace A
export GeneralEOAugmentedPinField (augmented source)
end A
namespace M
export GeneralEOSignedTensorRemovalMacro (source)
end M
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

/-- The converse identification of the two literal pin-source interfaces. -/
theorem pinning_of_elimination (h : Nonempty (GeneralEOPinEliminationCases.Elimination G)) :
    S.Pinning G := by
  obtain ⟨r⟩ := h
  have he : GeneralEOAffineNetworkOriginalSource.sourceValue G=P.pinnedValue G := by
    funext q
    rw [GeneralEOAffineNetworkOriginalSource.literal_source_value]
    rw [P.pinnedValue,GeneralEOPinnedDescentAccess.targetValue,
      ExactSignatureTables.evaluate_eq_decoded]
    simp only [GeneralEOPinnedDescentAccess.tables,LinearEquiv.apply_symm_apply]
    rw [GeneralEOSinglePinPaletteBridge.literal_family]
    rfl
  rw [S.Pinning,he]
  exact ⟨r⟩

variable (B : Network AlgebraicComplex 2) (BL : Labelling B.shape s 1 a)
variable (hL : LabelledNetwork.Exact G B BL) (hN : ∀e,B.edge e=Signature.disequality)
variable (u : Fin 2→Bool) (hu : B.denote u≠0)

def normalized : Signature AlgebraicComplex 2 := fun x => B.denote x/B.denote u

include hu in
theorem normalized_unit : normalized B u u=1 := div_self hu

include hL hN in
theorem normalized_mem (x : Fin 2→Bool) : normalized B u x∈O.originalField G := by
  unfold normalized
  rw [←F.denote_lift G B BL hL hN x,←F.denote_lift G B BL hL hN u]
  exact (O.originalField G).div_mem ((F.lift G B BL).denote x).property
    ((F.lift G B BL).denote u).property

include hu in
theorem normalized_value : B.denote=B.denote u • normalized B u := by
  funext x
  change B.denote x=B.denote u*(B.denote x/B.denote u)
  field_simp

include hL hN hu in
/-- Exact augmented-to-original removal, with both generated-field codecs. -/
def removal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) 1
      (GeneralEOTensorPowerRemovalRaw.sourceArity s 2 a))
    (O.originalPresentation (A.augmented G (normalized B u))).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (O.originalValue (A.augmented G (normalized B u))) (O.originalValue G) :=
  M.source G (normalized B u) (normalized_mem G B BL hL hN u)
    B BL hL hN (B.denote u) hu (normalized_value B u hu) u (normalized_unit B u hu)

include hL hN hu in
/-- A proved supplier over the normalized physical binary transfers back to G. -/
theorem pull_elimination
    (h : Nonempty (GeneralEOPinEliminationCases.Elimination (A.augmented G (normalized B u)))) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) := by
  obtain ⟨r⟩ := pinning_of_elimination (A.augmented G (normalized B u)) h
  apply GeneralEOSelfdualPhaseSource.elimination_of_pinning G
  exact ⟨C.composeControlled (A.source G (normalized B u))
    (C.composeControlled r (removal G B BL hL hN u hu))⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOGeneralPhaseBinaryRemoval
