import Holant.Proofs.Recognition.RuntimeEOLiteralTable
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeKTable
import Holant.Proofs.Recognition.RuntimeEOPairWord
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOView

/-! The literal EO A/P table frontend. Runtime pairing metadata expands each
compressed word, the central/completed view computes its mask and original
word, and the prescribed K-inverse compiler emits its sparse polynomial.
No transformed coefficients or field arithmetic oracle are machine inputs.
This file is a table compiler; the template/search loop is a separate stage. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Hardness
open CommonFieldMachine (Executes)
open RuntimeTensorRows (Word wordEncoding)
open UniformTensorWitnessBranch (Metadata metadataEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev Base := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.Layout × (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.View × (Metadata × List RationalTensorMachine.Row))
abbrev pairTableEncoding := pairEncoding metadataEncoding RationalTensorMachine.tableEncoding
abbrev viewTailEncoding := pairEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewEncoding pairTableEncoding
abbrev baseEncoding := pairEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.layoutEncoding viewTailEncoding
abbrev Input := Base × Word
abbrev encoding := pairEncoding baseEncoding wordEncoding

def expanded (r : Input) : Word := RuntimeEOPairWord.word (r.1.2.2.1,r.2)
def selection (r : Input) : Bool × Word := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.selection (r.1.2.1,expanded r)
def value (r : Input) : RationalSparseMachine.Poly :=
  if (selection r).1 then _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.vertex (r.1.1,(selection r).2,r.1.2.2.2) else []

def base := RuntimeTensorRows.fst baseEncoding wordEncoding
def word := RuntimeTensorRows.snd baseEncoding wordEncoding
def layout := base.comp (RuntimeTensorRows.fst _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.layoutEncoding viewTailEncoding)
def rest := base.comp (RuntimeTensorRows.snd _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.layoutEncoding viewTailEncoding)
def view := rest.comp (RuntimeTensorRows.fst _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewEncoding pairTableEncoding)
def pairTable := rest.comp (RuntimeTensorRows.snd _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewEncoding pairTableEncoding)
def metadata := pairTable.comp (RuntimeTensorRows.fst metadataEncoding RationalTensorMachine.tableEncoding)
def table := pairTable.comp (RuntimeTensorRows.snd metadataEncoding RationalTensorMachine.tableEncoding)

def expandedExecutes : Executes encoding wordEncoding expanded := (metadata.pair word).comp RuntimeEOPairWord.executes
def selectionExecutes : Executes encoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.selectionEncoding selection :=
  (view.pair expandedExecutes).comp _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.executes

def executes : Executes encoding RationalSparseMachine.encoding value := by
  let mask := selectionExecutes.comp (RuntimeTensorRows.fst encodingBoolBool wordEncoding)
  let selected := selectionExecutes.comp (RuntimeTensorRows.snd encodingBoolBool wordEncoding)
  let poly := (layout.pair (selected.pair table)).comp _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.executes
  exact RuntimeTensorRows.choose _ _ mask poly (RuntimeTensorRows.const encoding RationalSparseMachine.encoding [])

def typedView {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (complete : Bool) (k : ℕ) : (Fin (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)) → Bool) → Sparse.Poly v 1 :=
  match complete with
  | false => fun x => if _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((n,false,k),List.ofFn x) then
      _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.typedVertex imaginary sqrt address x else []
  | true => fun x => if _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((n,true,k),List.ofFn x) then
      _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.typedVertex imaginary sqrt address (SingleWeightCompletion.restrict k x) else []

def viewSignature {n : ℕ} (f : Signature AlgebraicComplex n) (complete : Bool) (k : ℕ) :
    Signature AlgebraicComplex (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)) :=
  match complete with
  | false => Signature.centralRestriction (f)
  | true => SingleWeightCompletion.completed (f) k

theorem view_wire {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (complete : Bool) (k : ℕ) (x : Fin (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)) → Bool) :
    (if _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((n,complete,k),List.ofFn x) then
      _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.vertex ((v,imaginary.val,sqrt.val),_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.restricted ((n,complete,k),List.ofFn x),
        (SparseTransform.allWords n).map (fun y => _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.wireRow (y,address y))) else [])=
      RationalInputMachine.rowWire (typedView imaginary sqrt address complete k x) := by
  cases complete
  · change Fin n → Bool at x
    rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.restricted_central,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.vertex_wire]
    dsimp only [typedView]
    split_ifs <;> rfl
  · change Fin (n+SingleWeightCompletion.extra n k) → Bool at x
    rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.restricted_source,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.vertex_wire]
    dsimp only [typedView]
    split_ifs <;> rfl

theorem value_wire {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (complete : Bool) (k : ℕ) (m : Metadata)
    (hg : m∈RuntimeTensorCatalogue.catalogue (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)))
    (hv : RuntimeEOPairings.valid (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)) m=true)
    (z : Fin (RuntimeEOPairings.pairing m hg hv).count → Bool) :
    value (((v,imaginary.val,sqrt.val),(n,complete,k),m,
      (SparseTransform.allWords n).map (fun y => _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.wireRow (y,address y))),List.ofFn z)=
      RationalInputMachine.rowWire (typedView imaginary sqrt address complete k
        ((RuntimeEOPairings.pairing m hg hv).word z)) := by
  unfold value selection expanded
  rw [RuntimeEOPairWord.word_source m hg hv z]
  exact view_wire imaginary sqrt address complete k _

theorem typedView_eval_map {E : Type*} [Field E] [Algebra ℚ E] (ψ : AlgebraicComplex →+* E)
    {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (f : Signature AlgebraicComplex n) (z : Fin v → E)
    (hi : z imaginary=ψ imaginaryUnit) (hs : z sqrt=ψ sqrtTwo)
    (hf : ∀y,z (address y)=ψ (f y)) (complete : Bool) (k : ℕ)
    (x : Fin (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (n,complete,k)) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z
      (typedView imaginary sqrt address complete k x)=ψ (viewSignature f complete k x) := by
  cases complete
  · change Fin n → Bool at x
    change SparseEvaluation.evaluate _ _ z
      (if _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((n,false,k),List.ofFn x) then
        _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.typedVertex imaginary sqrt address x else [])=
      ψ (Signature.centralRestriction (f) x)
    have hm := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed_central k x
    by_cases h : 2*Holant.weight x=n
    · simp only [hm.mpr h,ite_true]
      rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.vertex_eval_map ψ imaginary sqrt address f z hi hs hf]
      simp [Signature.centralRestriction,h]
    · have hn : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((n,false,k),List.ofFn x)≠true := fun hb => h (hm.mp hb)
      simp only [hn]
      simp [Signature.centralRestriction,h,SparseEvaluation.evaluate]
  · change Fin (n+SingleWeightCompletion.extra n k) → Bool at x
    change SparseEvaluation.evaluate _ _ z
      (if _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((n,true,k),List.ofFn x) then
        _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.typedVertex imaginary sqrt address (SingleWeightCompletion.restrict k x) else [])=
      ψ (SingleWeightCompletion.completed (f) k x)
    rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.completed_value]
    split
    · rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable.vertex_eval_map ψ imaginary sqrt address f z hi hs hf]
    · simp [SparseEvaluation.evaluate]

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable
