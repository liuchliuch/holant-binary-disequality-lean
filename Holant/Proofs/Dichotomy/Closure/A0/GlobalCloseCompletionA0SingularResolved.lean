import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0SingularPrepare
import Holant.Proofs.Dichotomy.Closure.Generic.GlobalCloseCompletionGenericSingularResolved

/-! The genuine A0 singular exit is consumed using an arbitrary finite
native source with its carried original scalar-X row. The enlarged palette
is never assigned a new A0 group. Its shared basis is transported through the
same Hadamard matrix and restricted to the entire original current family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0SingularResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FrontierCommonPresentation
namespace Pr
export GlobalCloseCompletionA0SingularPrepare (Prepared family normalized_member prepared_exists)
end Pr
namespace Generic
export GlobalCloseCompletionGenericSingularPack (Input)
export GlobalCloseCompletionGenericSingularResolved (classified)
end Generic
namespace W
export GlobalCloseCompletionA0Workfield (basis)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (d : Pr.Prepared G P)
abbrev CurrentTract := GlobalCloseCompletionA0EqualityOriginal.CurrentTract G P
abbrev Hard := OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G

def input : Generic.Input G where
  count := d.palette.count+1
  arity := GlobalCloseCompletionA0NativeSource.arity G d.palette
  table := GlobalCloseCompletionA0NativeCodec.mapped G d.palette
  anchor := d.anchor
  x := d.x
  y := d.y
  u := d.u
  v := d.v
  y_nonzero := d.y_nonzero
  nonsingular := d.nonsingular
  u_nonzero := d.u_nonzero
  square := d.square
  binary_member := ⟨⟨2,GlobalCloseCompletionA0NormalizedPin.normalized G d.binary⟩,
    Pr.normalized_member G d.palette d.binary d.binary_retained,
    congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex)) d.binary_exact⟩
  unary_member := ⟨⟨1,GlobalCloseCompletionA0NormalizedPin.normalized G d.unary⟩,
    Pr.normalized_member G d.palette d.unary d.unary_retained,
    congrArg (fun f : Signature AlgebraicComplex 1=>(⟨1,f⟩ : AnySignature AlgebraicComplex)) d.unary_exact⟩
  source := GlobalCloseCompletionA0NativeCodec.source G d.palette d.row

theorem normalized_native : (⟨2,W.basis.symm.action (kernelSignature Signature.disequality)⟩ :
    AnySignature AlgebraicComplex)∈Pr.family G d.palette := by
  have hx := Pr.normalized_member G d.palette (binarySignature (X : Binary (K:=OI.K G))) d.nativeX
  have hm : GlobalCloseCompletionA0NormalizedPin.normalized G (binarySignature (X : Binary (K:=OI.K G)))=
      W.basis.symm.action (kernelSignature Signature.disequality) := by
    apply congrArg W.basis.symm.action
    funext x
    change ClosureSourceRows.embedding G (Signature.disequality (x 0) (x 1))=
      Signature.disequality (x 0) (x 1)
    cases x 0 <;> cases x 1 <;> simp [Signature.disequality]
  rwa [hm] at hx

theorem common (target : TargetClass)
    (h : CommonKPresentationInKCoordinates target.family (Pr.family G d.palette)) :
    CommonKPresentationInKCoordinates target.family (CurrentFrontierClosure.currentFamily G P) := by
  have hi : RetainsIdentity (Pr.family G d.palette) := by
    change RetainsIdentity (GlobalCloseCompletionA0Family.finiteFamily G d.palette)
    rw [←GlobalCloseCompletionA0Family.family_eq]
    exact GlobalCloseCompletionA0Family.identity G d.palette
  obtain ⟨_,V,hV⟩ := GlobalCloseCompletionNativeToOrdinaryBasis.common_ordinary_of_native target
    (Pr.family G d.palette) hi h
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,W.basis.comp V,?_,?_⟩
  · exact GlobalCloseCompletionA0CommonBasis.native_edge target _ V (normalized_native G P d) hV
  · rintro f ⟨g,hg,rfl⟩
    have member := Pr.normalized_member G d.palette g.2 (d.old hg)
    have he : GlobalCloseCompletionA0NormalizedPin.normalized G g.2=
        W.basis.symm.action (FrontierCommonPresentation.embed G g).2 := by
      apply congrArg W.basis.symm.action
      funext x
      rfl
    have row := hV.2 _ member
    rw [he] at row
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action,FrontierCommonPresentation.embed] using row

include d in
theorem prepared_classified : CurrentTract G P ∨ Hard G := by
  rcases Generic.classified G (input G P d) (GlobalCloseCompletionA0Family.finite_preprocessed G d.palette)
      with (affine|product|localAffine)|hard
  · exact Or.inl (ClosureNativePresentation.tractX_forward_affine (common G P d .affine affine))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_product (common G P d .product product))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_localAffine (common G P d .localAffine localAffine))
  · exact Or.inr hard

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (r : GlobalCloseCompletionA0DenseEscape.SingularReceipt G P torsion q core literal)
variable (p : Bool)
variable (full : ∀x,GlobalCloseCompletionA0NormalizedPin.normalized G q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p)

include torsion N core literal r full in
theorem classified : CurrentTract G P ∨ Hard G := by
  obtain ⟨prepared⟩ := Pr.prepared_exists G P torsion N q core literal r p full
  exact prepared_classified G P prepared


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0SingularResolved
end
