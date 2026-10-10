import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBNonisotropicPrepare
import Holant.Proofs.Dichotomy.Closure.Generic.GlobalCloseCompletionGenericSingularResolved

/-! The genuine B singular exit is consumed through its actual normalized
pin/phase/cycle source. Its successful common basis is transported through
B and restricted to the whole old current palette; its negative source keeps
the unchanged original-G input and answer encoding. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBNonisotropicResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FrontierCommonPresentation
namespace Pr
export GlobalCloseCompletionBNonisotropicPrepare (Prepared family normalized_member prepared_exists)
end Pr
namespace Generic
export GlobalCloseCompletionGenericSingularPack (Input)
export GlobalCloseCompletionGenericSingularResolved (classified)
end Generic
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (d : Pr.Prepared G P)
abbrev CurrentTract := GlobalCloseCompletionEq4Classification.CurrentTract G P
abbrev Hard := OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G

def input : Generic.Input G where
  count := d.palette.count+1
  arity := GlobalCloseCompletionBNativeSource.arity G d.palette
  table := GlobalCloseCompletionBNativeCodec.mapped G d.palette
  anchor := d.anchor
  x := d.x
  y := d.y
  u := d.u
  v := d.v
  y_nonzero := d.y_nonzero
  nonsingular := d.nonsingular
  u_nonzero := d.u_nonzero
  square := d.square
  binary_member := ⟨⟨2,GlobalCloseCompletionBNormalizedPin.normalized G d.binary⟩,
    Pr.normalized_member G d.palette d.binary d.binary_retained,
    congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex)) d.binary_exact⟩
  unary_member := ⟨⟨1,GlobalCloseCompletionBNormalizedPin.normalized G d.unary⟩,
    Pr.normalized_member G d.palette d.unary d.unary_retained,
    congrArg (fun f : Signature AlgebraicComplex 1=>(⟨1,f⟩ : AnySignature AlgebraicComplex)) d.unary_exact⟩
  source := GlobalCloseCompletionBNativeCodec.source G d.palette

theorem common (target : TargetClass)
    (h : CommonKPresentationInKCoordinates target.family (Pr.family G d.palette)) :
    CommonKPresentationInKCoordinates target.family (CurrentFrontierClosure.currentFamily G P) := by
  obtain ⟨_finite,V,edge,rows⟩ := GlobalCloseCompletionBDenseResolved.common G d.palette target h
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,V,edge,?_⟩
  rintro f ⟨g,hg,rfl⟩
  exact rows _ ⟨g,d.old hg,rfl⟩

include d in
theorem prepared_classified : CurrentTract G P ∨ Hard G := by
  rcases Generic.classified G (input G P d) (GlobalCloseCompletionBDenseResolved.preprocessed G d.palette)
      with (affine|product|localAffine)|hard
  · exact Or.inl (ClosureNativePresentation.tractX_forward_affine (common G P d .affine affine))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_product (common G P d .product product))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_localAffine (common G P d .localAffine localAffine))
  · exact Or.inr hard

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (r : GlobalCloseCompletionBDenseEscape.SingularReceipt G P)
variable (q : Signature (OI.K G) 4) (p : Bool)
variable (retained : (⟨4,q⟩ : AnySignature (OI.K G))∈P.family)
variable (full : ∀x,GlobalCloseCompletionBNormalizedPin.normalized G q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p)

include torsion N r retained full in
theorem classified : CurrentTract G P ∨ Hard G := by
  obtain ⟨prepared⟩ := Pr.prepared_exists G P torsion N r q p retained full
  exact prepared_classified G P prepared


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBNonisotropicResolved
end
