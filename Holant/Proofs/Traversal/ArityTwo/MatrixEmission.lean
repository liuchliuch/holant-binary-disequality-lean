import Holant.Proofs.Traversal.ArityTwo.RawPortQuery
import Holant.Proofs.Traversal.ArityTwo.Descriptors
import Holant.Proofs.Tractability.ProductMachine.RawCompiler


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.MatrixEmission
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)

def word (code : Code A) := entries (opEncoding codec) code
def localMatrix (k : ℕ) (i : Fin s) : Kernel A :=
  fun a b => labels i (fun j => if j.val = k then a else b)

def vertexWord (k : ℕ) (x : Query s b arity) :=
  word codec (matrixStep (localMatrix s arity labels k (sourceLabel s b arity x)))

def vertexComputes (k : ℕ) : Computes (queryEncoding s b arity) Frame.wordEncoding
    (vertexWord s b arity labels codec k) :=
  labelRecodeComputes s b arity Frame.wordEncoding
    (fun i => word codec (matrixStep (localMatrix s arity labels k i)))

def vertexPortWord (x : RawPortQuery.Input s b arity) :=
  if RawPortQuery.first s b arity x then
    vertexWord s b arity labels codec 0 (RawPortQuery.vertexQuery s b arity x)
  else vertexWord s b arity labels codec 1 (RawPortQuery.vertexQuery s b arity x)

def vertexPortComputes : Computes (RawPortQuery.encoding s b arity) Frame.wordEncoding
    (vertexPortWord s b arity labels codec) :=
  ifComputes (RawPortQuery.firstComputes s b arity)
    ((RawPortQuery.vertexComputes s b arity).andThen (vertexComputes s b arity labels codec 0))
    ((RawPortQuery.vertexComputes s b arity).andThen (vertexComputes s b arity labels codec 1))

def unaryWord (x : Query s b arity) :=
  word codec [.literal (labels (sourceLabel s b arity x) (fun _ => true)),
    .literal (labels (sourceLabel s b arity x) (fun _ => false))]

def unaryComputes : Computes (queryEncoding s b arity) Frame.wordEncoding
    (unaryWord s b arity labels codec) :=
  labelRecodeComputes s b arity Frame.wordEncoding (fun i =>
    word codec [.literal (labels i (fun _ => true)),.literal (labels i (fun _ => false))])

def unaryPortComputes : Computes (RawPortQuery.encoding s b arity) Frame.wordEncoding
    (fun x => unaryWord s b arity labels codec (RawPortQuery.vertexQuery s b arity x)) :=
  (RawPortQuery.vertexComputes s b arity).andThen (unaryComputes s b arity labels codec)

def degreeComputes (n : ℕ) : Computes (RawPortQuery.encoding s b arity) encodingBoolBool
    (fun x => decide (PortWalk.degree (arity := arity) x.1.val (RawPortQuery.port s b arity x).1 = n)) :=
  (RawPortQuery.vertexComputes s b arity).andThen
    (labelRecodeComputes s b arity encodingBoolBool (fun i => decide (arity i.val = n)))

theorem vertexPort_exact (x : RawPortQuery.Input s b arity)
    (hd : PortWalk.degree (arity := arity) x.1.val (RawPortQuery.port s b arity x).1 = 2) :
    vertexPortWord s b arity labels codec x =
      word codec (matrixStep (Descriptors.binaryTable x.1.val
        (fun v => labels (x.1.val.signatureLabel x.1.property v))
        (RawPortQuery.port s b arity x))) := by
  have hp := (RawPortQuery.port s b arity x).2.isLt
  change (RawPortQuery.port s b arity x).2.val < PortWalk.degree (arity := arity) x.1.val _ at hp
  by_cases hzero : (RawPortQuery.port s b arity x).2.val = 0
  · have ht := (RawPortQuery.first_iff s b arity x).mpr hzero
    simp [vertexPortWord,ht,vertexWord,localMatrix,Descriptors.binaryTable,
      sourceLabel,RawPortQuery.vertexQuery,hzero,RawClosedNetwork.signatureLabel]
    congr 2
    funext a b
    unfold localMatrix Descriptors.binaryTable
    congr 1
    funext j
    simp [hzero]
  · have hone : (RawPortQuery.port s b arity x).2.val = 1 := by omega
    have ht : RawPortQuery.first s b arity x = false := by
      cases h : RawPortQuery.first s b arity x with
      | false => rfl
      | true => exact (hzero ((RawPortQuery.first_iff s b arity x).mp h)).elim
    simp [vertexPortWord,ht,vertexWord,localMatrix,Descriptors.binaryTable,
      sourceLabel,RawPortQuery.vertexQuery,hone,RawClosedNetwork.signatureLabel]
    congr 2
    funext a b
    unfold localMatrix Descriptors.binaryTable
    congr 1
    funext j
    simp [hone]

def scalarWord (x : Query s b arity) :=
  word codec [.literal (labels (sourceLabel s b arity x) (fun _ => false))]

def scalarComputes : Computes (queryEncoding s b arity) Frame.wordEncoding
    (scalarWord s b arity labels codec) :=
  labelRecodeComputes s b arity Frame.wordEncoding
    (fun i => word codec [.literal (labels i (fun _ => false))])

def edgeWord (side : Bool) (x : EdgeWord.Input s b arity) :=
  word codec (matrixStep (orient side (edges (x.1.val.edgeLabel x.1.property x.2))))

/-- Reuse only the raw edge-label query, not Product's specialized elimination
semantics: here the finite emitted table consists of arbitrary 2-by-2 matrices. -/
def edgeComputes (side : Bool) : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding
    (edgeWord s b arity edges codec side) :=
  (Holant.LocalDrafts.Tractability.ProductMachine.RawCompiler.labelComputes s b arity).andThen
    (FiniteRecode.computes (SignatureLabel.binaryFinEncoding b) Frame.wordEncoding
      (fun i => word codec (matrixStep (orient side (edges i)))) b.size
      (SignatureLabel.binaryFinEncoding_length_le b))

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.MatrixEmission
