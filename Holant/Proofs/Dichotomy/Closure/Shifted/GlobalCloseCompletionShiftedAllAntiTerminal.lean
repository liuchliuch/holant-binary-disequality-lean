import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedAntiSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiComplete

/-! Complete shifted ordinary obstruction hardness using the actual full
weighted-antidiagonal source. Every rotation order is covered. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAllAntiTerminal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace A
export GlobalCloseCompletionShiftedAntiSource
  (selected source row row_left_nonzero row_right_nonzero outside_four_bad_row)
end A
namespace E
export GlobalCloseCompletionShiftedExplicitAnchor (retained current finiteAnchor)
end E
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (native : GlobalCloseCompletionShiftedMarking.Native G P torsion)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)
abbrev Hard := NoXWeightedAntiSquares.Hard G
abbrev CurrentTract := TractX (familyAction sourceKBasis
  (CurrentFrontierClosure.currentFamily G (E.retained G P torsion q core literal)))

include P torsion native q core literal stable
theorem countingHard
    (negative : StableHigherCurrentOrdinaryTerminal.Obstruction
      (preprocess (GenericOrdinarySource.family G (A.source G P torsion native q core literal stable)))) : Hard G := by
  let t : Holant.Marked.SupportAtlas.Phase (A.selected G P torsion native).m :=
    ⟨1,by simp [Holant.Marked.Roots]⟩
  let R := A.row G P torsion native q core literal stable t
  exact NoXWeightedAntiComplete.countingHard G
    (A.source G P torsion native q core literal stable) R.label R.left R.right
    (A.row_left_nonzero G P torsion native q core literal stable t)
    (A.row_right_nonzero G P torsion native q core literal stable t) R.literal negative

theorem classified : CurrentTract G P torsion q core literal ∨ Hard G := by
  rcases StableHigherCurrentOrdinarySourceTerminal.classified G
    (E.retained G P torsion q core literal) (E.finiteAnchor G P torsion native q core literal stable) with
      ⟨_test,affine|product|localAffine⟩|negative
  · change CommonKPresentationInKCoordinates affineClass (UniversalPairReduction.FiniteFamily.family
      (E.current G P torsion q core literal)) at affine
    rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq G (E.retained G P torsion q core literal)] at affine
    exact Or.inl (ClosureNativePresentation.tractX_forward_affine affine)
  · change CommonKPresentationInKCoordinates productClass (UniversalPairReduction.FiniteFamily.family
      (E.current G P torsion q core literal)) at product
    rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq G (E.retained G P torsion q core literal)] at product
    exact Or.inl (ClosureNativePresentation.tractX_forward_product product)
  · change CommonKPresentationInKCoordinates localAffineClass (UniversalPairReduction.FiniteFamily.family
      (E.current G P torsion q core literal)) at localAffine
    rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq G (E.retained G P torsion q core literal)] at localAffine
    exact Or.inl (ClosureNativePresentation.tractX_forward_localAffine localAffine)
  · right
    apply countingHard G P torsion native q core literal stable
    change StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess
      (StableHigherCurrentOrdinarySourceTerminal.physicalFamily G
        (E.retained G P torsion q core literal) (E.finiteAnchor G P torsion native q core literal stable)))
    rw [preprocess_eq_self (StableHigherCurrentOrdinarySourceTerminal.physical_family_preprocessed G
      (E.retained G P torsion q core literal) (E.finiteAnchor G P torsion native q core literal stable))]
    exact negative

theorem inFP_or_countingHard :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ Hard G := by
  rcases classified G P torsion native q core literal stable with positive|negative
  · exact Or.inl (StablePaletteTractability.original_inFP G (E.retained G P torsion q core literal) positive)
  · exact Or.inr negative


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAllAntiTerminal
end
