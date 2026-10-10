import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedParity
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinarySourceTerminal
import Holant.Proofs.Dichotomy.Retained.StablePaletteTractability
import Holant.EightVertex.ProductAnchor.Source
import Holant.Proofs.Closure.ClosureNativePresentation

/-! The actual shifted parity graph supplies an ordinary Eq4/two-pin source
for the entire current palette, with its genuine fixed-field programme to G.
The positive common-basis branch closes; a no-X ordinary obstruction is kept
explicitly and is never mislabeled a literal-X hardness theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAnchor
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.EightVertex.ProductAnchor
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace Pn
export GlobalCloseCompletionShiftedParity (output complexScalar scalar scalar_value scalar_nonzero ambient_value evenTable direct)
end Pn
namespace M
export GlobalCloseCompletionShiftedMask (phi)
end M
namespace O
export StableHigherCurrentOrdinarySourceTerminal (physicalFamily Classified classified)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (native : GlobalCloseCompletionShiftedMarking.Native G P torsion)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

abbrev ambient := RingHomRealization.mapSignature (M.phi G) (Pn.output G P torsion native q core literal stable)

theorem dense : DenseForm (ambient G P torsion native q core literal stable) := by
  have hc : Pn.complexScalar G P torsion native q core literal stable≠0 := by
    rw [←Pn.scalar_value]
    exact (map_ne_zero (M.phi G)).mpr (Pn.scalar_nonzero G P torsion native q core literal stable)
  refine ⟨Pn.complexScalar G P torsion native q core literal stable,1,hc,one_ne_zero,(fun _=>false),?_⟩
  intro x
  have h := congrFun (Pn.ambient_value G P torsion native q core literal stable) x
  simpa [ambient,Pn.evenTable,bitSign,smul_eq_mul] using h

theorem ambient_actual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
    (ambient G P torsion native q core literal stable) :=
  RingHomRealization.realizes_map (M.phi G) (Pn.direct G P torsion native q core literal stable).realizes

def anchor : QuaternaryEqualityTerminal.AnchorStep (ClosureSourceRows.ambientFamily G P) :=
  QuaternaryEqualityTerminal.anchorStep (dense_realizing_family_anchor
    (ambient G P torsion native q core literal stable) (dense G P torsion native q core literal stable)
    (ClosureSourceRows.ambientFamily G P) (ambient_actual G P torsion native q core literal stable))

def finiteAnchor := StableHigherCurrentFamilyTransport.fromAmbient G P (anchor G P torsion native q core literal stable)
def ordinarySource := StableHigherCurrentAnchorPins.toOriginal G P (finiteAnchor G P torsion native q core literal stable)
def squareCSPSource := StableHigherCurrentEvenCSPSource.squareToOriginal G P (finiteAnchor G P torsion native q core literal stable)
abbrev family := O.physicalFamily G P (finiteAnchor G P torsion native q core literal stable)
abbrev CurrentTract := TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P))

theorem classified : CurrentTract G P ∨ StableHigherCurrentOrdinaryTerminal.Obstruction
    (family G P torsion native q core literal stable) := by
  rcases O.classified G P (finiteAnchor G P torsion native q core literal stable) with
    ⟨_test,affine|product|localAffine⟩|negative
  · change CommonKPresentationInKCoordinates affineClass (UniversalPairReduction.FiniteFamily.family
      (StableHigherCurrentPurePinsCore.mapped G P)) at affine
    rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq G P] at affine
    exact Or.inl (ClosureNativePresentation.tractX_forward_affine affine)
  · change CommonKPresentationInKCoordinates productClass (UniversalPairReduction.FiniteFamily.family
      (StableHigherCurrentPurePinsCore.mapped G P)) at product
    rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq G P] at product
    exact Or.inl (ClosureNativePresentation.tractX_forward_product product)
  · change CommonKPresentationInKCoordinates localAffineClass (UniversalPairReduction.FiniteFamily.family
      (StableHigherCurrentPurePinsCore.mapped G P)) at localAffine
    rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq G P] at localAffine
    exact Or.inl (ClosureNativePresentation.tractX_forward_localAffine localAffine)
  · exact Or.inr negative

theorem inFP_or_obstruction :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨
      StableHigherCurrentOrdinaryTerminal.Obstruction (family G P torsion native q core literal stable) := by
  rcases classified G P torsion native q core literal stable with positive|negative
  · exact Or.inl (StablePaletteTractability.original_inFP G P positive)
  · exact Or.inr negative


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAnchor
end
