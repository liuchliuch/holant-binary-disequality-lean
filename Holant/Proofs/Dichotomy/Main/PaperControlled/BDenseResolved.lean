import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseEscape
import Holant.Proofs.Dichotomy.Main.PaperControlled.GenericDenseResolved
import Holant.Proofs.Dichotomy.Closure.Native.GlobalCloseCompletionNativeToOrdinaryBasis
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityOriginal

/-! Dense normalized B charts are actual old-family sources. Successful
canonical charts are consumed by literal-X hardness or one whole-current
basis with explicit B backtransfer. A failed chart retains its original-field
singular graph and the exact nonzero normalized coefficient. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.BDenseResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace R
export GlobalCloseCompletionBDenseRepresentatives
  (family family_eq family_finite_eq finiteCanonical fullParity_or_bad)
end R
namespace Generic
export GlobalCloseCompletionGenericDenseLiteralX (Input)
export PaperControlled.GenericDenseResolved (classified)
end Generic
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
abbrev CurrentTract := GlobalCloseCompletionEq4Classification.CurrentTract G P
abbrev Hard := PaperControlledHardness.Original G

abbrev finiteFamily := UniversalPairReduction.FiniteFamily.family (GlobalCloseCompletionBNativeCodec.mapped G P)

def input (C : GlobalCloseCompletionBDenseCanonical.Canonical (R.family G P)) : Generic.Input G where
  count := P.count+1
  arity := GlobalCloseCompletionBNativeSource.arity G P
  table := GlobalCloseCompletionBNativeCodec.mapped G P
  identity := by rw [←R.family_finite_eq]; exact GlobalCloseCompletionBCoordinateRealizes.identity _
  canonical := R.finiteCanonical G P C
  source := GlobalCloseCompletionBNativeCodec.source G P

theorem preprocessed : Preprocessed (finiteFamily G P) := by
  change Preprocessed (UniversalPairReduction.FiniteFamily.family (GlobalCloseCompletionBNativeCodec.mapped G P))
  rw [←R.family_finite_eq G P]
  rintro f (old|rfl)
  · exact Conformal.preprocessed_familyAction basisB.symm
      (GlobalCloseCompletionEq4Classification.current_preprocessed G P) f old
  · refine ⟨by decide,?_⟩
    intro zero
    have h := congrFun zero ![false,false]
    simp [kernelSignature,Signature.equality] at h

private theorem target_scale (target : TargetClass) : Conformal.ScaleClosed target.family := by
  cases target
  · exact Conformal.affineClass_scaleClosed
  · exact Conformal.productClass_scaleClosed
  · exact Conformal.localAffineClass_scaleClosed

theorem common (target : TargetClass)
    (h : CommonKPresentationInKCoordinates target.family (finiteFamily G P)) :
    CommonKPresentationInKCoordinates target.family (CurrentFrontierClosure.currentFamily G P) := by
  have ordinary := GlobalCloseCompletionNativeToOrdinaryBasis.common_ordinary_of_native target
    (finiteFamily G P) (GlobalCloseCompletionBQuaternary.identity_member G P) h
  obtain ⟨_,V,basis⟩ := ordinary
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,basisB.comp V,?_,?_⟩
  · change (⟨2,kernelSignature (Kernel.pullback Signature.disequality
      (Kernel.mul basisB.matrix V.matrix))⟩ : AnySignature AlgebraicComplex)∈target.family
    have edge : Kernel.pullback Signature.disequality basisB.matrix=scale (-2*imaginaryUnit) Signature.equality := edgeB
    rw [pullback_mul,edge]
    change (⟨2,kernelSignature (Kernel.pullback
      (fun b c=>(-2*imaginaryUnit)*Signature.equality b c) V.matrix)⟩ : AnySignature AlgebraicComplex)∈target.family
    rw [Conformal.pullback_scale]
    exact target_scale target 2 _ basis.1 (-2*imaginaryUnit)
  · intro f hf
    have member : (⟨f.1,basisB.symm.action f.2⟩ : AnySignature AlgebraicComplex)∈finiteFamily G P := by
      change (⟨f.1,basisB.symm.action f.2⟩ : AnySignature AlgebraicComplex)∈
        UniversalPairReduction.FiniteFamily.family (GlobalCloseCompletionBNativeCodec.mapped G P)
      rw [←R.family_finite_eq G P]
      exact Or.inl ⟨f,hf,rfl⟩
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action] using basis.2 _ member

variable (C : GlobalCloseCompletionBDenseCanonical.Canonical (R.family G P))
include C in
theorem canonical_classified : CurrentTract G P ∨ Hard G := by
  rcases Generic.classified G (input G P C) (preprocessed G P) with (affine|product|localAffine)|hard
  · exact Or.inl (ClosureNativePresentation.tractX_forward_affine (common G P .affine affine))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_product (common G P .product product))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_localAffine (common G P .localAffine localAffine))
  · exact Or.inr hard

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

include torsion N in
theorem fullParity_classified (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
    (literal : core.signature=⟨4,q⟩) (p : Bool)
    (full : ∀x,GlobalCloseCompletionBQuaternary.normalized G q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p) :
    CurrentTract G P ∨ Hard G ∨ Nonempty (GlobalCloseCompletionBDenseEscape.SingularReceipt G P) := by
  rcases R.fullParity_or_bad G P torsion N q core literal p full with canonical|bad
  · obtain ⟨receipt⟩ := canonical
    rcases canonical_classified G P receipt.canonical with tract|hard
    · exact Or.inl tract
    · exact Or.inr (Or.inl hard)
  · exact Or.inr (Or.inr (GlobalCloseCompletionBDenseEscape.bad_original_singular G P torsion N bad))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.BDenseResolved
end
