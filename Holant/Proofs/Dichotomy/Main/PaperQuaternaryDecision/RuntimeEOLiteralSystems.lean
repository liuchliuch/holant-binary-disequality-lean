import Holant.Proofs.Recognition.RuntimeEOLiteralSystems
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOLiteralRows
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineRecognitionSource
import Holant.Proofs.Algorithms.TransformRecognition.RationalDisjunctionMachine

/-! Typed reification and exact disjunction semantics for the internally
emitted A/P template catalogues. Every physical candidate is accounted for;
every paper template has an emitted representative. Reification is proof-side
only and never substitutes a chosen factorization for serialized search data. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralSystems
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm (Parameter Edge Skeleton)
open UniformTensorWitnessBranch (Metadata)
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRows
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (complete : Bool) (k : ℕ) (m : Metadata)
    (hg : m∈RuntimeTensorCatalogue.catalogue (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)))
    (hv : RuntimeEOPairings.valid (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)) m=true)
local notation "p" => RuntimeEOPairings.pairing m hg hv

def code {count : ℕ} (c : EncodedTable.Data) (hc : c∈RawAffineEnumeration.templates count) : AffineNormalForm.Code count :=
  RawAffineCandidateSource.normalizeAt count c (RawAffineEnumerationValidity.generated_regular _ c hc).1

def edges {count : ℕ} (c : List RawProductEnumeration.RawEdge) (hc : c∈RawProductEnumeration.templates count) : List (Edge count) :=
  Classical.choose (RawProductEnumeration.reify c hc)

theorem edges_exact {count : ℕ} (c : List RawProductEnumeration.RawEdge) (hc : c∈RawProductEnumeration.templates count) :
    c=(edges c hc).map RationalProductTemplateSource.edgeCode :=
  Classical.choose_spec (RawProductEnumeration.reify c hc)

def affineSystem (scale : Fin v) (C : AffineNormalForm.Code (p).count) : List (Sparse.Poly v 1) :=
  (SparseTransform.allWords (p).count).map (typedAffineRow imaginary sqrt address complete k m hg hv scale C)
def productSystem (es : List (Edge (p).count)) (param : Parameter (p).count → Fin v) : List (Sparse.Poly v 1) :=
  (SparseTransform.allWords (p).count).map (typedProductRow imaginary sqrt address complete k m hg hv es param)

def affineBranches (scale : Fin v) : List (List (Sparse.Poly v 1)) :=
  (RawAffineEnumeration.templates (p).count).attach.map (fun c =>
    affineSystem imaginary sqrt address complete k m hg hv scale (code c.val c.property))
def productBranches (param : Parameter (p).count → Fin v) : List (List (Sparse.Poly v 1)) :=
  (RawProductEnumeration.templates (p).count).attach.map (fun c =>
    productSystem imaginary sqrt address complete k m hg hv (edges c.val c.property) param)

theorem affine_generated_wire (scale : Fin v) (c : EncodedTable.Data)
    (hc : c∈RawAffineEnumeration.templates (p).count) :
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRows.affineRows (sourceBase imaginary sqrt address complete k m,scale.val,c)=
      RationalInputMachine.bodyWire (affineSystem imaginary sqrt address complete k m hg hv scale (code c hc)) := by
  change (RationalTableMachine.words (p).count).map _=_
  simp only [RationalTableMachine.words_eq,List.map_map,Function.comp_def,RationalInputMachine.bodyWire,affineSystem]
  apply List.map_congr_left
  intro x _
  unfold affineRow sourceBase
  rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.value_wire imaginary sqrt address complete k m hg hv x,
    RationalSparseMachine.variable_wire,
    RawAffineCandidateSource.coefficient_at imaginary c (RawAffineEnumerationValidity.generated_regular _ c hc).1
      (RawAffineEnumerationValidity.generated_regular _ c hc).2 x,
    RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

theorem affineBranches_wire (scale : Fin v) :
    (RawAffineEnumeration.templates (p).count).map (fun c =>
      _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRows.affineRows (sourceBase imaginary sqrt address complete k m,scale.val,c))=
      (affineBranches imaginary sqrt address complete k m hg hv scale).map RationalInputMachine.bodyWire := by
  unfold affineBranches
  rw [List.map_map]
  rw [←List.attach_map_val (l:=RawAffineEnumeration.templates (p).count)]
  apply List.map_congr_left
  intro c _
  exact affine_generated_wire imaginary sqrt address complete k m hg hv scale c.val c.property

theorem productBranches_wire (param : Parameter (p).count → Fin v) :
    (RawProductEnumeration.templates (p).count).map (fun c =>
      _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRows.productRows (sourceBase imaginary sqrt address complete k m,c,(param none).val,
        List.ofFn (fun j => ((param (some (j,false))).val,(param (some (j,true))).val))))=
      (productBranches imaginary sqrt address complete k m hg hv param).map RationalInputMachine.bodyWire := by
  unfold productBranches
  rw [List.map_map]
  rw [←List.attach_map_val (l:=RawProductEnumeration.templates (p).count)]
  apply List.map_congr_left
  intro c _
  have he := productRows_wire imaginary sqrt address complete k m hg hv (edges c.val c.property) param
  rw [←edges_exact c.val c.property] at he
  exact he

theorem affine_complete (scale : Fin v) (C : AffineNormalForm.Code (p).count) :
    affineSystem imaginary sqrt address complete k m hg hv scale C ∈
      affineBranches imaginary sqrt address complete k m hg hv scale := by
  let c := RationalAffineTemplateSource.sourceCode C
  have hc : c∈RawAffineEnumeration.templates (p).count := RawAffineEnumeration.source_mem C
  have he : affineSystem imaginary sqrt address complete k m hg hv scale (code c hc)=
      affineSystem imaginary sqrt address complete k m hg hv scale C := by
    apply RawAffineRecognitionSource.bodyWire_injective
    rw [←affine_generated_wire imaginary sqrt address complete k m hg hv scale c hc]
    exact affineRows_wire imaginary sqrt address complete k m hg hv scale C
  rw [←he]
  exact List.mem_map.mpr ⟨⟨c,hc⟩,List.mem_attach _ _,rfl⟩

theorem product_complete (param : Parameter (p).count → Fin v) (S : Skeleton (p).count) :
    productSystem imaginary sqrt address complete k m hg hv S.toList param ∈
      productBranches imaginary sqrt address complete k m hg hv param := by
  let c := S.toList.map RationalProductTemplateSource.edgeCode
  have hc : c∈RawProductEnumeration.templates (p).count := RawProductEnumeration.skeleton_mem S
  have he : edges c hc=S.toList :=
    (List.map_injective_iff.mpr RawProductEnumeration.edgeCode_injective) (edges_exact c hc).symm
  unfold productBranches
  exact List.mem_map.mpr ⟨⟨c,hc⟩,List.mem_attach _ _,by rw [he]⟩

variable (f : Signature AlgebraicComplex n) (z : Fin v → ℂ)
    (hi : z imaginary=(imaginaryUnit : ℂ)) (hs : z sqrt=(sqrtTwo : ℂ))
    (hf : ∀y,z (address y)=(f y : ℂ))

include hi hs hf in
theorem affine_equations_iff (scale : Fin v) :
    (∀e∈FiniteSystemDisjunction.combine (affineBranches imaginary sqrt address complete k m hg hv scale),
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z e=0) ↔
    ∃C : AffineNormalForm.Code (p).count,∀x,
      (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.viewSignature f complete k ((p).word x) : ℂ)=z scale*(AffineNormalForm.formula C 1 x : ℂ) := by
  rw [FiniteSystemDisjunction.combine_zero_iff]
  constructor
  · rintro ⟨es,hes,he⟩
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hes
    refine ⟨code c.val c.property,?_⟩
    intro x
    have hx := he _ (List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩)
    rw [affineRow_eval imaginary sqrt address complete k m hg hv f z hi hs hf] at hx
    exact sub_eq_zero.mp hx
  · rintro ⟨C,hC⟩
    refine ⟨_,affine_complete imaginary sqrt address complete k m hg hv scale C,?_⟩
    intro e he
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
    rw [affineRow_eval imaginary sqrt address complete k m hg hv f z hi hs hf,hC x,sub_self]

include hi hs hf in
theorem product_equations_iff (param : Parameter (p).count → Fin v) :
    (∀e∈FiniteSystemDisjunction.combine (productBranches imaginary sqrt address complete k m hg hv param),
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z e=0) ↔
    ∃S : Skeleton (p).count,∀x,
      (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.viewSignature f complete k ((p).word x) : ℂ)=
        Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.evaluate S (fun t => z (param t)) x := by
  rw [FiniteSystemDisjunction.combine_zero_iff]
  constructor
  · rintro ⟨es,hes,he⟩
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hes
    refine ⟨(edges c.val c.property).toFinset,?_⟩
    intro x
    have hx := he _ (List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩)
    rw [productRow_eval imaginary sqrt address complete k m hg hv f z hi hs hf] at hx
    exact sub_eq_zero.mp hx
  · rintro ⟨S,hS⟩
    refine ⟨_,product_complete imaginary sqrt address complete k m hg hv param S,?_⟩
    intro e he
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
    rw [productRow_eval imaginary sqrt address complete k m hg hv f z hi hs hf,Finset.toList_toFinset,hS x,sub_self]

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralSystems
