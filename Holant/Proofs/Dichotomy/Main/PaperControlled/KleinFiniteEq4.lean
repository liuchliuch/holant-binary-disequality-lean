import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinRealizedEq4

/-! Generic finite native Eq4 consumer. The input is an actual controlled
native table source, retained identity, and an actual projective Eq4 graph.
The output classifies the entire finite alphabet in one native basis or gives
original-G counting hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinFiniteEq4
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open FrontierCommonPresentation
namespace E
export GlobalCloseCompletionBEqualityCSP (field presentation arity table eq4Label pinLabel xLabel
  eq4_literal pin_literal x_literal ordinarySource current_included)
end E
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

structure Input where
  count : ℕ
  arity : ℕ→ℕ
  table : (i : Fin count)→Signature AlgebraicComplex (arity i.val)
  identity : RetainsIdentity (UniversalPairReduction.FiniteFamily.family table)
  source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) (O.originalPresentation table).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (O.originalValue table) (OriginalForestSource.value G)

variable (D : Input G)
abbrev family := UniversalPairReduction.FiniteFamily.family D.table
abbrev Hard := PaperControlledHardness.Original G
abbrev Positive := CommonKPresentationInKCoordinates affineClass (family G D) ∨
  CommonKPresentationInKCoordinates productClass (family G D) ∨
  CommonKPresentationInKCoordinates localAffineClass (family G D)

include D in
theorem output (actual : Gadget.RealizesUpTo (family G D) .disequality
    (Holant.EightVertex.ProductAnchor.equalityFour (K:=AlgebraicComplex))) :
    Nonempty (GlobalCloseCompletionBPrimeEq4.Output D.table) := by
  obtain ⟨c,hc,actual⟩ := actual
  obtain ⟨N,uses,native,denote⟩ := Holant.OpenNetworkComposition.OrdinaryNormalization.realizes_exists_ordinary D.identity actual
  let labels : Labelling N.shape D.count 1 D.arity :=
    { vertex := fun v=>(uses v).choose
      vertex_arity := fun v=>congrArg Sigma.fst (uses v).choose_spec
      edge := fun _=>0 }
  exact ⟨⟨N,labels,fun v=>(uses v).choose_spec,native,c,hc,denote⟩⟩

variable (out : GlobalCloseCompletionBPrimeEq4.Output D.table)

def data : GenericLiteralXSource.Data G where
  K := E.field D.table out
  degree := _
  F := E.presentation D.table out
  size := _
  b := E.arity D.table out
  H := E.table D.table out
  e := E.eq4Label D.table
  p := E.pinLabel D.table
  x := E.xLabel D.table
  he := E.eq4_literal D.table out
  hp := E.pin_literal D.table out
  hx := E.x_literal D.table out
  toOriginal := Programme.compose
    (E.ordinarySource D.table out D.identity.choose D.identity.choose_spec) D.source

include D out in
theorem common (target : TargetClass) (preprocessed : Preprocessed (family G D))
    (h : CommonTransformable target.family (preprocess (GenericLiteralXSource.family G (data G D out)))) :
    CommonKPresentationInKCoordinates target.family (family G D) := by
  obtain ⟨_,V,basis⟩ := h
  have x : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈
      preprocess (GenericLiteralXSource.family G (data G D out)) := by
    refine ⟨GenericLiteralXSource.family_x G (data G D out),by decide,?_⟩
    intro zero
    have hz := congrFun zero ![false,true]
    simp [kernelSignature,Signature.disequality] at hz
  have native := GlobalCloseCompletionEq4CommonBasis.target_native_of_ordinary target _ V x basis
  refine ⟨Set.finite_range _,V,native.1,?_⟩
  intro f hf
  exact native.2 f ⟨E.current_included D.table out hf,preprocessed f hf⟩

include D out in
theorem classified_output (preprocessed : Preprocessed (family G D)) : Positive G D ∨ Hard G := by
  rcases PaperControlledOrdinary.literalX_classified G (data G D out) with tract|hard
  · left
    rcases (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis
      (GenericLiteralXSource.family_eq4 G (data G D out))).mp tract with affine|product|localAffine
    · exact Or.inl (common G D out .affine preprocessed affine)
    · exact Or.inr (Or.inl (common G D out .product preprocessed product))
    · exact Or.inr (Or.inr (common G D out .localAffine preprocessed localAffine))
  · exact Or.inr hard

include D in
theorem classified (preprocessed : Preprocessed (family G D))
    (actual : Gadget.RealizesUpTo (family G D) .disequality
      (Holant.EightVertex.ProductAnchor.equalityFour (K:=AlgebraicComplex))) : Positive G D ∨ Hard G := by
  obtain ⟨out⟩ := output G D actual
  exact classified_output G D out preprocessed

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinFiniteEq4
end
