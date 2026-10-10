import Holant.Proofs.Recognition.RuntimeKTable
import Holant.Proofs.Recognition.RuntimeEOPairWord
import Holant.Proofs.Recognition.RuntimeEOView

/-! The literal EO A/P table frontend. Runtime pairing metadata expands each
compressed word, the central/completed view computes its mask and original
word, and the prescribed K-inverse compiler emits its sparse polynomial.
No transformed coefficients or field arithmetic oracle are machine inputs.
This file is a table compiler; the template/search loop is a separate stage. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOLiteralTable
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

abbrev Base := RuntimeTensorBasis.Layout × (RuntimeEOView.View × (Metadata × List RationalTensorMachine.Row))
abbrev pairTableEncoding := pairEncoding metadataEncoding RationalTensorMachine.tableEncoding
abbrev viewTailEncoding := pairEncoding RuntimeEOView.viewEncoding pairTableEncoding
abbrev baseEncoding := pairEncoding RuntimeTensorBasis.layoutEncoding viewTailEncoding
abbrev Input := Base × Word
abbrev encoding := pairEncoding baseEncoding wordEncoding

def expanded (r : Input) : Word := RuntimeEOPairWord.word (r.1.2.2.1,r.2)
def selection (r : Input) : Bool × Word := RuntimeEOView.selection (r.1.2.1,expanded r)
def value (r : Input) : RationalSparseMachine.Poly :=
  if (selection r).1 then RuntimeKTable.vertex (r.1.1,(selection r).2,r.1.2.2.2) else []

def base := RuntimeTensorRows.fst baseEncoding wordEncoding
def word := RuntimeTensorRows.snd baseEncoding wordEncoding
def layout := base.comp (RuntimeTensorRows.fst RuntimeTensorBasis.layoutEncoding viewTailEncoding)
def rest := base.comp (RuntimeTensorRows.snd RuntimeTensorBasis.layoutEncoding viewTailEncoding)
def view := rest.comp (RuntimeTensorRows.fst RuntimeEOView.viewEncoding pairTableEncoding)
def pairTable := rest.comp (RuntimeTensorRows.snd RuntimeEOView.viewEncoding pairTableEncoding)
def metadata := pairTable.comp (RuntimeTensorRows.fst metadataEncoding RationalTensorMachine.tableEncoding)
def table := pairTable.comp (RuntimeTensorRows.snd metadataEncoding RationalTensorMachine.tableEncoding)

def expandedExecutes : Executes encoding wordEncoding expanded := (metadata.pair word).comp RuntimeEOPairWord.executes
def selectionExecutes : Executes encoding RuntimeEOView.selectionEncoding selection :=
  (view.pair expandedExecutes).comp RuntimeEOView.executes

def executes : Executes encoding RationalSparseMachine.encoding value := by
  let mask := selectionExecutes.comp (RuntimeTensorRows.fst encodingBoolBool wordEncoding)
  let selected := selectionExecutes.comp (RuntimeTensorRows.snd encodingBoolBool wordEncoding)
  let poly := (layout.pair (selected.pair table)).comp RuntimeKTable.executes
  exact RuntimeTensorRows.choose _ _ mask poly (RuntimeTensorRows.const encoding RationalSparseMachine.encoding [])

def typedView {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (complete : Bool) (k : ℕ) : (Fin (RuntimeEOView.arity (n,complete,k)) → Bool) → Sparse.Poly v 1 :=
  match complete with
  | false => fun x => if RuntimeEOView.allowed ((n,false,k),List.ofFn x) then
      RuntimeKTable.typedVertex imaginary sqrt address x else []
  | true => fun x => if RuntimeEOView.allowed ((n,true,k),List.ofFn x) then
      RuntimeKTable.typedVertex imaginary sqrt address (SingleWeightCompletion.restrict k x) else []

def viewSignature {n : ℕ} (f : Signature AlgebraicComplex n) (complete : Bool) (k : ℕ) :
    Signature AlgebraicComplex (RuntimeEOView.arity (n,complete,k)) :=
  match complete with
  | false => Signature.centralRestriction (sourceKBasis.symm.action f)
  | true => SingleWeightCompletion.completed (sourceKBasis.symm.action f) k

theorem view_wire {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (complete : Bool) (k : ℕ) (x : Fin (RuntimeEOView.arity (n,complete,k)) → Bool) :
    (if RuntimeEOView.allowed ((n,complete,k),List.ofFn x) then
      RuntimeKTable.vertex ((v,imaginary.val,sqrt.val),RuntimeEOView.restricted ((n,complete,k),List.ofFn x),
        (SparseTransform.allWords n).map (fun y => RuntimeKTable.wireRow (y,address y))) else [])=
      RationalInputMachine.rowWire (typedView imaginary sqrt address complete k x) := by
  cases complete
  · change Fin n → Bool at x
    rw [RuntimeEOView.restricted_central,RuntimeKTable.vertex_wire]
    dsimp only [typedView]
    split_ifs <;> rfl
  · change Fin (n+SingleWeightCompletion.extra n k) → Bool at x
    rw [RuntimeEOView.restricted_source,RuntimeKTable.vertex_wire]
    dsimp only [typedView]
    split_ifs <;> rfl

theorem value_wire {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (complete : Bool) (k : ℕ) (m : Metadata)
    (hg : m∈RuntimeTensorCatalogue.catalogue (RuntimeEOView.arity (n,complete,k)))
    (hv : RuntimeEOPairings.valid (RuntimeEOView.arity (n,complete,k)) m=true)
    (z : Fin (RuntimeEOPairings.pairing m hg hv).count → Bool) :
    value (((v,imaginary.val,sqrt.val),(n,complete,k),m,
      (SparseTransform.allWords n).map (fun y => RuntimeKTable.wireRow (y,address y))),List.ofFn z)=
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
    (x : Fin (RuntimeEOView.arity (n,complete,k)) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z
      (typedView imaginary sqrt address complete k x)=ψ (viewSignature f complete k x) := by
  cases complete
  · change Fin n → Bool at x
    change SparseEvaluation.evaluate _ _ z
      (if RuntimeEOView.allowed ((n,false,k),List.ofFn x) then
        RuntimeKTable.typedVertex imaginary sqrt address x else [])=
      ψ (Signature.centralRestriction (sourceKBasis.symm.action f) x)
    have hm := RuntimeEOView.allowed_central k x
    by_cases h : 2*Holant.weight x=n
    · simp only [hm.mpr h,ite_true]
      rw [RuntimeKTable.vertex_eval_map ψ imaginary sqrt address f z hi hs hf]
      simp [Signature.centralRestriction,h]
    · have hn : RuntimeEOView.allowed ((n,false,k),List.ofFn x)≠true := fun hb => h (hm.mp hb)
      simp only [hn]
      simp [Signature.centralRestriction,h,SparseEvaluation.evaluate]
  · change Fin (n+SingleWeightCompletion.extra n k) → Bool at x
    change SparseEvaluation.evaluate _ _ z
      (if RuntimeEOView.allowed ((n,true,k),List.ofFn x) then
        RuntimeKTable.typedVertex imaginary sqrt address (SingleWeightCompletion.restrict k x) else [])=
      ψ (SingleWeightCompletion.completed (sourceKBasis.symm.action f) k x)
    rw [RuntimeEOView.completed_value]
    split
    · rw [RuntimeKTable.vertex_eval_map ψ imaginary sqrt address f z hi hs hf]
    · simp [SparseEvaluation.evaluate]

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOLiteralTable
