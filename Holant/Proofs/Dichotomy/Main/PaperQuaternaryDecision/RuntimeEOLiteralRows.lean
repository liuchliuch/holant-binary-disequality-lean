import Holant.Proofs.Recognition.RuntimeEOLiteralRows
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOLiteralTable
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineEnumerationValidity
import Holant.Proofs.Algorithms.TransformRecognition.RawProductEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.RationalProductRowsMachine

/-! Physical literal affine/product row compilers on runtime EO pair views.
The sparse transformed table is generated from original coefficient addresses;
template support, phases, signed constraints and parameter addresses are read
and evaluated by their established physical programmes. Template enumeration
and original-root request assembly remain separate from this row stage. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRows
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm (Parameter Edge)
open CommonFieldMachine (Executes)
open RuntimeTensorRows (Word wordEncoding)
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable (Base baseEncoding)
open UniformTensorWitnessBranch (Metadata metadataEncoding natListEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev AffineTemplate := ℕ × EncodedTable.Data
abbrev affineTemplateEncoding := pairEncoding encodingNatBool EncodedTable.encoding
abbrev AffineInput := Base × AffineTemplate
abbrev affineEncoding := pairEncoding baseEncoding affineTemplateEncoding
abbrev ProductTemplate := RationalProductRowsMachine.Template
abbrev productTemplateEncoding := RationalProductRowsMachine.templateEncoding
abbrev ProductInput := Base × ProductTemplate
abbrev productEncoding := pairEncoding baseEncoding productTemplateEncoding

def affineRow (r : AffineInput) (x : Word) : RationalSparseMachine.Poly :=
  RationalSparseMachine.sub (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.value (r.1,x))
    (RationalSparseMachine.mul (RationalSparseMachine.variable r.1.1.1 r.2.1)
      (RationalAffineTemplateMachine.value (r.1.1.1,r.1.1.2.1,r.2.2,x)))
def affineRows (r : AffineInput) : List RationalSparseMachine.Poly :=
  (RationalTableMachine.words r.1.2.2.1.1.length).map (affineRow r)
def productRow (r : ProductInput) (x : Word) : RationalSparseMachine.Poly :=
  RationalSparseMachine.sub (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.value (r.1,x))
    (RationalProductTemplateMachine.value (r.1.1.1,r.2.1,r.2.2.1,r.2.2.2,x))
def productRows (r : ProductInput) : List RationalSparseMachine.Poly :=
  (RationalTableMachine.words r.1.2.2.1.1.length).map (productRow r)

def baseLayout := RuntimeTensorRows.fst _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.layoutEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.viewTailEncoding
def baseWidth := baseLayout.comp (RuntimeTensorRows.fst encodingNatBool (pairEncoding encodingNatBool encodingNatBool))
def baseConstants := baseLayout.comp (RuntimeTensorRows.snd encodingNatBool (pairEncoding encodingNatBool encodingNatBool))
def baseImaginary := baseConstants.comp (RuntimeTensorRows.fst encodingNatBool encodingNatBool)
def baseCount := (((RuntimeTensorRows.snd _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.layoutEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.viewTailEncoding).comp
  (RuntimeTensorRows.snd _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.pairTableEncoding)).comp
  (RuntimeTensorRows.fst metadataEncoding RationalTensorMachine.tableEncoding)).comp
  ((RuntimeTensorRows.fst natListEncoding RuntimeTensorRows.metadataTailEncoding).comp (RuntimeTensorRows.length encodingNatBool))

def affineCell : Executes (pairEncoding affineEncoding wordEncoding) RationalSparseMachine.encoding
    (fun p => affineRow p.1 p.2) := by
  let r := RuntimeTensorRows.fst affineEncoding wordEncoding
  let x := RuntimeTensorRows.snd affineEncoding wordEncoding
  let base := r.comp (RuntimeTensorRows.fst baseEncoding affineTemplateEncoding)
  let tpl := r.comp (RuntimeTensorRows.snd baseEncoding affineTemplateEncoding)
  let scalar := tpl.comp (RuntimeTensorRows.fst encodingNatBool EncodedTable.encoding)
  let template := tpl.comp (RuntimeTensorRows.snd encodingNatBool EncodedTable.encoding)
  let width := base.comp baseWidth
  let imaginary := base.comp baseImaginary
  let original := (base.pair x).comp _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.executes
  let scale := (width.pair scalar).comp RationalSparseMachine.variableExecutes
  let coeff := (width.pair (imaginary.pair (template.pair x))).comp RationalAffineTemplateMachine.executes
  exact (original.pair ((scale.pair coeff).comp RationalSparseMachine.mulExecutes)).comp
    (Executes.ofComputes RationalSparseMachine.subComputes)

def affineExecutes : Executes affineEncoding RationalSparseMachine.familyEncoding affineRows :=
  NegativeCertificateMachine.Lists.map affineEncoding wordEncoding RationalSparseMachine.encoding
    (((RuntimeTensorRows.fst baseEncoding affineTemplateEncoding).comp baseCount).comp RationalTableMachine.wordsExecutes)
    affineRow affineCell

def productCell : Executes (pairEncoding productEncoding wordEncoding) RationalSparseMachine.encoding
    (fun p => productRow p.1 p.2) := by
  let r := RuntimeTensorRows.fst productEncoding wordEncoding
  let x := RuntimeTensorRows.snd productEncoding wordEncoding
  let base := r.comp (RuntimeTensorRows.fst baseEncoding productTemplateEncoding)
  let tpl := r.comp (RuntimeTensorRows.snd baseEncoding productTemplateEncoding)
  let edges := tpl.comp (RuntimeTensorRows.fst RationalProductTemplateMachine.edgesEncoding RationalProductRowsMachine.templateTailEncoding)
  let tail := tpl.comp (RuntimeTensorRows.snd RationalProductTemplateMachine.edgesEncoding RationalProductRowsMachine.templateTailEncoding)
  let scale := tail.comp (RuntimeTensorRows.fst encodingNatBool RationalProductTemplateMachine.addressesEncoding)
  let unary := tail.comp (RuntimeTensorRows.snd encodingNatBool RationalProductTemplateMachine.addressesEncoding)
  let original := (base.pair x).comp _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.executes
  let value := ((base.comp baseWidth).pair (edges.pair (scale.pair (unary.pair x)))).comp RationalProductTemplateMachine.executes
  exact (original.pair value).comp (Executes.ofComputes RationalSparseMachine.subComputes)

def productExecutes : Executes productEncoding RationalSparseMachine.familyEncoding productRows :=
  NegativeCertificateMachine.Lists.map productEncoding wordEncoding RationalSparseMachine.encoding
    (((RuntimeTensorRows.fst baseEncoding productTemplateEncoding).comp baseCount).comp RationalTableMachine.wordsExecutes)
    productRow productCell

variable {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (complete : Bool) (k : ℕ) (m : Metadata)
    (hg : m∈RuntimeTensorCatalogue.catalogue (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)))
    (hv : RuntimeEOPairings.valid (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)) m=true)
local notation "p" => RuntimeEOPairings.pairing m hg hv

def sourceBase : Base := ((v,imaginary.val,sqrt.val),(n,complete,k),m,
  (SparseTransform.allWords n).map (fun y => _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.wireRow (y,address y)))

def typedAffineRow (scale : Fin v) (C : AffineNormalForm.Code (p).count) (x : Fin (p).count → Bool) : Sparse.Poly v 1 :=
  Sparse.sub (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.typedView imaginary sqrt address complete k ((p).word x))
    (Sparse.mul RationalCompiler.data (SparseTransform.variableCode RationalCompiler.data scale)
      (SymbolicPhaseCoefficients.affineCoefficient imaginary C x))

def typedProductRow (edges : List (Edge (p).count)) (param : Parameter (p).count → Fin v)
    (x : Fin (p).count → Bool) : Sparse.Poly v 1 :=
  Sparse.sub (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.typedView imaginary sqrt address complete k ((p).word x))
    (SparseProductTemplate.entry RationalCompiler.data edges param x)

theorem affineRow_wire (scale : Fin v) (C : AffineNormalForm.Code (p).count) (x : Fin (p).count → Bool) :
    affineRow (sourceBase imaginary sqrt address complete k m,scale.val,RationalAffineTemplateSource.sourceCode C) (List.ofFn x)=
      RationalInputMachine.rowWire (typedAffineRow imaginary sqrt address complete k m hg hv scale C x) := by
  unfold affineRow sourceBase
  rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.value_wire imaginary sqrt address complete k m hg hv x,
    RationalSparseMachine.variable_wire,RationalAffineTemplateSource.value_fromCode,
    RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

theorem affineRows_wire (scale : Fin v) (C : AffineNormalForm.Code (p).count) :
    affineRows (sourceBase imaginary sqrt address complete k m,scale.val,RationalAffineTemplateSource.sourceCode C)=
      ((SparseTransform.allWords (p).count).map
        (typedAffineRow imaginary sqrt address complete k m hg hv scale C)).map RationalInputMachine.rowWire := by
  change (RationalTableMachine.words (p).count).map _=_
  simp only [RationalTableMachine.words_eq,List.map_map,Function.comp_def,affineRow_wire]

theorem productRow_wire (edges : List (Edge (p).count)) (param : Parameter (p).count → Fin v)
    (x : Fin (p).count → Bool) :
    productRow (sourceBase imaginary sqrt address complete k m,
      edges.map RationalProductTemplateSource.edgeCode,(param none).val,
      List.ofFn (fun j => ((param (some (j,false))).val,(param (some (j,true))).val))) (List.ofFn x)=
      RationalInputMachine.rowWire (typedProductRow imaginary sqrt address complete k m hg hv edges param x) := by
  unfold productRow sourceBase
  rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.value_wire imaginary sqrt address complete k m hg hv x]
  change RationalSparseMachine.sub _ (RationalProductTemplateMachine.value (RationalProductTemplateSource.fromSource edges param x))=_
  rw [RationalProductTemplateSource.value_source,RationalSparseMachine.sub_wire]
  rfl

theorem productRows_wire (edges : List (Edge (p).count)) (param : Parameter (p).count → Fin v) :
    productRows (sourceBase imaginary sqrt address complete k m,
      edges.map RationalProductTemplateSource.edgeCode,(param none).val,
      List.ofFn (fun j => ((param (some (j,false))).val,(param (some (j,true))).val)))=
      ((SparseTransform.allWords (p).count).map
        (typedProductRow imaginary sqrt address complete k m hg hv edges param)).map RationalInputMachine.rowWire := by
  change (RationalTableMachine.words (p).count).map _=_
  simp only [RationalTableMachine.words_eq,List.map_map,Function.comp_def,productRow_wire]

variable (f : Signature AlgebraicComplex n) (z : Fin v → ℂ)
    (hi : z imaginary=(imaginaryUnit : ℂ)) (hs : z sqrt=(sqrtTwo : ℂ))
    (hf : ∀y,z (address y)=(f y : ℂ))

include hi hs hf in
theorem affineRow_eval (scale : Fin v) (C : AffineNormalForm.Code (p).count) (x : Fin (p).count → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (typedAffineRow imaginary sqrt address complete k m hg hv scale C x)=
      (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.viewSignature f complete k ((p).word x) : ℂ)-
        z scale*(AffineNormalForm.formula C 1 x : ℂ) := by
  unfold typedAffineRow
  rw [SparseEvaluation.sub_eval,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.compilerData,SparseEvaluation.mul_eval,
    SparseEvaluation.variable_eval,
    SymbolicPhaseCoefficients.affineCoefficient_eval imaginary C x z hi,
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.typedView_eval_map (algebraMap AlgebraicComplex ℂ) imaginary sqrt address f z hi hs hf]
  rfl

include hi hs hf in
theorem productRow_eval (edges : List (Edge (p).count)) (param : Parameter (p).count → Fin v)
    (x : Fin (p).count → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (typedProductRow imaginary sqrt address complete k m hg hv edges param x)=
      (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.viewSignature f complete k ((p).word x) : ℂ)-
        Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.evaluate edges.toFinset (fun t => z (param t)) x := by
  unfold typedProductRow
  rw [SparseEvaluation.sub_eval,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.compilerData,SparseProductTemplate.entry_eval,
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.typedView_eval_map (algebraMap AlgebraicComplex ℂ) imaginary sqrt address f z hi hs hf]
  rfl

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRows
