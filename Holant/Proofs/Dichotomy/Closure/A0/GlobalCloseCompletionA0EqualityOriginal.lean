import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityCSP
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0CurrentNativeRow
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification

/-! An actual A0 scalar-Eq4 graph supplies one literal Eq4/pins/X ordinary
source for the entire normalized current family. Its positive test reconstructs
the original current family in the accumulated Hadamard basis, including the
exact native edge 2Z and its inverse-resource factor four. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0EqualityOriginal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace C
export GlobalCloseCompletionA0CurrentSource (mapped count arity source family oldLabel old_mapped identityLabel identity_literal)
end C
namespace S
export GlobalCloseCompletionBEqualityCSP
  (family ordinarySource evenCSPSource squareCSPSource current_included family_eq4 family_pin family_x rejected_iff)
end S
namespace W
export GlobalCloseCompletionA0Workfield (basis)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (d : GlobalCloseCompletionBPrimeEq4.Output (C.mapped G P torsion q core literal))
local instance : NumberField (OI.K (C.mapped G P torsion q core literal)) :=
  OI.numberField (C.mapped G P torsion q core literal)

def ordinarySource := Programme.compose
  (S.ordinarySource (C.mapped G P torsion q core literal) d
    (C.identityLabel G P torsion q core literal) (C.identity_literal G P torsion q core literal))
  (C.source G P torsion N q core literal)
def evenCSPSource := Programme.compose
  (S.evenCSPSource (C.mapped G P torsion q core literal) d
    (C.identityLabel G P torsion q core literal) (C.identity_literal G P torsion q core literal))
  (C.source G P torsion N q core literal)
def squareCSPSource := Programme.compose
  (S.squareCSPSource (C.mapped G P torsion q core literal) d
    (C.identityLabel G P torsion q core literal) (C.identity_literal G P torsion q core literal))
  (C.source G P torsion N q core literal)

abbrev family := S.family (C.mapped G P torsion q core literal) d
abbrev current := CurrentFrontierClosure.currentFamily G P
abbrev CurrentTract := TractX (familyAction sourceKBasis (current G P))

theorem normalized_current_included : familyAction W.basis.symm (current G P)⊆family G P torsion q core literal d := by
  rintro _ ⟨_,⟨_,⟨i,rfl⟩,rfl⟩,rfl⟩
  apply S.current_included (C.mapped G P torsion q core literal) d
  exact ⟨C.oldLabel G P torsion q core literal i,C.old_mapped G P torsion q core literal i⟩

theorem normalized_preprocessed : Preprocessed (familyAction W.basis.symm (current G P)) :=
  Conformal.preprocessed_familyAction W.basis.symm (GlobalCloseCompletionEq4Classification.current_preprocessed G P)

theorem normalized_preprocess_included :
    familyAction W.basis.symm (current G P)⊆preprocess (family G P torsion q core literal d) := by
  intro f hf
  exact ⟨normalized_current_included G P torsion q core literal d hf,normalized_preprocessed G P f hf⟩

theorem edge_resource : (⟨2,W.basis.symm.action (kernelSignature Signature.disequality)⟩ :
    AnySignature AlgebraicComplex)∈preprocess (family G P torsion q core literal d) := by
  refine ⟨?_,by decide,GlobalCloseCompletionA0CurrentNativeRow.nonzero⟩
  exact S.current_included (C.mapped G P torsion q core literal) d
    (GlobalCloseCompletionA0CurrentNativeRow.member G P torsion q core literal)

theorem common (target : TargetClass)
    (h : CommonTransformable target.family (preprocess (family G P torsion q core literal d))) :
    CommonKPresentationInKCoordinates target.family (current G P) := by
  obtain ⟨_,B,hB⟩ := h
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,W.basis.comp B,?_,?_⟩
  · exact GlobalCloseCompletionA0CommonBasis.native_edge target _ B
      (edge_resource G P torsion q core literal d) hB
  · intro f hf
    have member : (⟨f.1,W.basis.symm.action f.2⟩ : AnySignature AlgebraicComplex)∈
        preprocess (family G P torsion q core literal d) :=
      normalized_preprocess_included G P torsion q core literal d ⟨f,hf,rfl⟩
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action] using hB.2 _ member

theorem tractX_of_tract (tract : Tract (family G P torsion q core literal d)) : CurrentTract G P := by
  rcases (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis
    (S.family_eq4 (C.mapped G P torsion q core literal) d)).mp tract with affine | product | localAffine
  · exact ClosureNativePresentation.tractX_forward_affine (common G P torsion q core literal d .affine affine)
  · exact ClosureNativePresentation.tractX_forward_product (common G P torsion q core literal d .product product)
  · exact ClosureNativePresentation.tractX_forward_localAffine (common G P torsion q core literal d .localAffine localAffine)

def originalComputes (tract : Tract (family G P torsion q core literal d)) :=
  StablePaletteTractability.originalComputes G P (tractX_of_tract G P torsion q core literal d tract)

theorem classified : CurrentTract G P ∨
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (family G P torsion q core literal d)) := by
  classical
  by_cases tract : Tract (family G P torsion q core literal d)
  · exact Or.inl (tractX_of_tract G P torsion q core literal d tract)
  · exact Or.inr ((S.rejected_iff (C.mapped G P torsion q core literal) d).mp tract)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0EqualityOriginal
end
