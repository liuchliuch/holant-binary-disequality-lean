import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Representatives
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0EqualityOriginal
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Family
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0CurrentNativeRow
import Holant.Proofs.Dichotomy.Closure.Dense.GlobalCloseCompletionDenseCanonicalCurrent
import Holant.Proofs.Dichotomy.Closure.Generic.GlobalCloseCompletionGenericDenseResolved
import Holant.Proofs.Dichotomy.Closure.Native.GlobalCloseCompletionNativeToOrdinaryBasis

/-! Dense charts of the actual A0 finite native source. A successful canonical
chart is consumed into original whole-current tractability or original-G
hardness. Failed finite charts retain an actual bad normalized binary; its
open-coordinate singularity backtransfer is a separate proved obligation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0DenseCanonical
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open FrontierCommonPresentation
namespace C
export GlobalCloseCompletionA0CurrentSource
  (retained family count arity mapped source normalized_member identity_member oldLabel old_mapped)
end C
namespace Q
export GlobalCloseCompletionA0Quaternary (normalized)
end Q
namespace W
export GlobalCloseCompletionA0Workfield (basis)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)

abbrev CurrentTract := GlobalCloseCompletionA0EqualityOriginal.CurrentTract G P
abbrev Hard := OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G

include N in
theorem fullParity_or_bad (p : Bool) (full : ∀x,Q.normalized G q x≠0 ↔ parity x=p) :
    Nonempty (GlobalCloseCompletionBDenseCanonical.Receipt (C.family G P torsion q core literal) N.selected.m) ∨
      EightVertexGaugeFamily.BadBinary (C.family G P torsion q core literal) N.selected.m := by
  apply GlobalCloseCompletionDenseCanonicalCurrent.fullParity_or_bad N.selected.range N.selected.omega
    N.selected.primitive (C.family G P torsion q core literal) (C.identity_member G P torsion q core literal)
    (GlobalCloseCompletionA0Representatives.produce G P torsion N q core literal)
    (Q.normalized G q) ?_ p full
  exact Gadget.realizes_of_mem _ .disequality _ (C.normalized_member G P torsion q core literal)

variable (chart : GlobalCloseCompletionBDenseCanonical.Canonical (C.family G P torsion q core literal))

def input : GlobalCloseCompletionGenericDenseLiteralX.Input G where
  count := C.count G P torsion q core literal
  arity := C.arity G P torsion q core literal
  table := C.mapped G P torsion q core literal
  identity := C.identity_member G P torsion q core literal
  canonical := chart
  source := C.source G P torsion N q core literal

theorem preprocessed : Preprocessed (C.family G P torsion q core literal) :=
  GlobalCloseCompletionA0Family.finite_preprocessed G (C.retained G P torsion q core literal)

theorem normalized_included : familyAction W.basis.symm (CurrentFrontierClosure.currentFamily G P)⊆
    C.family G P torsion q core literal := by
  rintro _ ⟨_,⟨_,⟨i,rfl⟩,rfl⟩,rfl⟩
  exact ⟨C.oldLabel G P torsion q core literal i,C.old_mapped G P torsion q core literal i⟩

theorem common (target : TargetClass)
    (h : CommonKPresentationInKCoordinates target.family (C.family G P torsion q core literal)) :
    CommonKPresentationInKCoordinates target.family (CurrentFrontierClosure.currentFamily G P) := by
  have ordinary := GlobalCloseCompletionNativeToOrdinaryBasis.common_ordinary_of_native target
    (C.family G P torsion q core literal) (C.identity_member G P torsion q core literal) h
  obtain ⟨_,V,hV⟩ := ordinary
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,W.basis.comp V,?_,?_⟩
  · exact GlobalCloseCompletionA0CommonBasis.native_edge target _ V
      (GlobalCloseCompletionA0CurrentNativeRow.member G P torsion q core literal) hV
  · intro f hf
    have member : (⟨f.1,W.basis.symm.action f.2⟩ : AnySignature AlgebraicComplex)∈
        C.family G P torsion q core literal := normalized_included G P torsion q core literal ⟨f,hf,rfl⟩
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action] using hV.2 _ member

include N chart in
theorem canonical_classified : CurrentTract G P ∨ Hard G := by
  rcases GlobalCloseCompletionGenericDenseResolved.classified G (input G P torsion N q core literal chart)
    (preprocessed G P torsion q core literal) with (affine|product|localAffine)|hard
  · exact Or.inl (ClosureNativePresentation.tractX_forward_affine (common G P torsion q core literal .affine affine))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_product (common G P torsion q core literal .product product))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_localAffine (common G P torsion q core literal .localAffine localAffine))
  · exact Or.inr hard

include N in
theorem fullParity_classified (p : Bool) (full : ∀x,Q.normalized G q x≠0 ↔ parity x=p) :
    CurrentTract G P ∨ Hard G ∨ EightVertexGaugeFamily.BadBinary (C.family G P torsion q core literal) N.selected.m := by
  cases fullParity_or_bad G P torsion N q core literal p full with
  | inl witness =>
      rcases canonical_classified G P torsion N q core literal (Classical.choice witness).canonical with tract|hard
      · exact Or.inl tract
      · exact Or.inr (Or.inl hard)
  | inr bad => exact Or.inr (Or.inr bad)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0DenseCanonical
end
