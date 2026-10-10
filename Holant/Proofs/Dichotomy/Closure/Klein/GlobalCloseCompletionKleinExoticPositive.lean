import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinExoticPins
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0CommonBasis
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEq4Source

/-! The positive ordinary test for the actual exotic source returns one
common basis for the entire original current family. The retained Z/2 row
reconstructs the original native-X edge in that same accumulated basis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticPositive
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open FrontierCommonPresentation
namespace S
export GlobalCloseCompletionKleinExoticOrdinarySource (retained transformed_member mapped zLabel z_literal)
end S
namespace D
export GlobalCloseCompletionKleinExoticPins (input data old_included)
end D
namespace T
export GlobalCloseCompletionKleinOrdinaryHTransport (H)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (exotic : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.exotic)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

abbrev family := GenericOrdinarySource.family G (D.data G P torsion cardinal noncyclic exotic q core literal stable)
abbrev CurrentTract := GlobalCloseCompletionKleinEq4Source.CurrentTract G P

theorem current_retained : CurrentFrontierClosure.currentFamily G P⊆
    ClosureSourceRows.ambientFamily G (S.retained G P torsion q core literal) := by
  rintro f ⟨g,hg,rfl⟩
  refine ⟨g,?_,rfl⟩
  rw [ProgrammeRetained.palette_family]
  exact fullRetainedDeck_retains P.family torsion q hg

theorem normalized_included : familyAction T.H.symm (CurrentFrontierClosure.currentFamily G P)⊆
    family G P torsion cardinal noncyclic exotic q core literal stable := by
  rintro _ ⟨f,hf,rfl⟩
  obtain ⟨i,hi⟩ := S.transformed_member G P torsion q core literal f (current_retained G P torsion q core literal hf)
  exact D.old_included G P torsion cardinal noncyclic exotic q core literal stable ⟨i,hi⟩

theorem native_member : (⟨2,T.H.symm.action (kernelSignature Signature.disequality)⟩ : AnySignature AlgebraicComplex)∈
    preprocess (family G P torsion cardinal noncyclic exotic q core literal stable) := by
  refine ⟨?_,by decide,?_⟩
  · rw [GlobalCloseCompletionKleinBAlgebra.H_X]
    exact D.old_included G P torsion cardinal noncyclic exotic q core literal stable
      ⟨S.zLabel G P torsion q core literal,S.z_literal G P torsion q core literal⟩
  · intro zero
    have hx := congrFun zero (fun _=>false)
    rw [GlobalCloseCompletionKleinBAlgebra.H_X] at hx
    norm_num [GlobalCloseCompletionKleinTwistedAlgebra.Z] at hx

theorem common (target : TargetClass)
    (ordinary : CommonTransformable target.family (preprocess (family G P torsion cardinal noncyclic exotic q core literal stable))) :
    CommonKPresentationInKCoordinates target.family (CurrentFrontierClosure.currentFamily G P) := by
  obtain ⟨_,V,basis⟩ := ordinary
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,T.H.comp V,?_,?_⟩
  · exact GlobalCloseCompletionA0CommonBasis.native_edge target _ V
      (native_member G P torsion cardinal noncyclic exotic q core literal stable) basis
  · intro f hf
    have mem : (⟨f.1,T.H.symm.action f.2⟩ : AnySignature AlgebraicComplex)∈
        familyAction T.H.symm (CurrentFrontierClosure.currentFamily G P) := ⟨f,hf,rfl⟩
    have live := Conformal.preprocessed_familyAction T.H.symm
      (GlobalCloseCompletionEq4Classification.current_preprocessed G P) _ mem
    have h := basis.2 _ ⟨normalized_included G P torsion cardinal noncyclic exotic q core literal stable mem,live⟩
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action] using h

theorem tractX_of_tract
    (tract : Tract (family G P torsion cardinal noncyclic exotic q core literal stable)) : CurrentTract G P := by
  have eq4 := GenericOrdinarySource.family_eq4 G (D.data G P torsion cardinal noncyclic exotic q core literal stable)
  rcases (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis eq4).mp tract with affine|product|localAffine
  · exact ClosureNativePresentation.tractX_forward_affine
      (common G P torsion cardinal noncyclic exotic q core literal stable .affine affine)
  · exact ClosureNativePresentation.tractX_forward_product
      (common G P torsion cardinal noncyclic exotic q core literal stable .product product)
  · exact ClosureNativePresentation.tractX_forward_localAffine
      (common G P torsion cardinal noncyclic exotic q core literal stable .localAffine localAffine)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticPositive
end
