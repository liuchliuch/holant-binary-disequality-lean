import Holant.Proofs.Algorithms.LocalAffine.EncodedReference
import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.Backend
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionContextInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface
import Holant.Proofs.Algorithms.OptionalValue


namespace Holant.LocalDrafts.MainChain.LocalAffineEvaluator
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing.OriginalCoefficient
open Holant.LocalDrafts.Tractability.LocalAffineMachine
open Holant.OneHot.StackProgram.GraphLabelEncoding
noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)

abbrev Input := ExactSignatureTables.Input s b arity
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s b arity
abbrev outputEncoding := (OriginalFamily.presentation D.signatures D.kernels).encoding

def selected (r : Input (s:=s) (b:=b) (arity:=arity)) :
    Option (Relabel.Graph.Input (s:=s) (b:=b) (arity:=arity)) :=
  (LocalAffineEncodedReference.value D r).map (fun w => (r,w))

def selectedComputes : Computes (inputEncoding (s:=s) (b:=b) (arity:=arity))
    (optionEncoding (Relabel.Compiler.inputEncoding (s:=s) (b:=b) (arity:=arity))) (selected D) :=
  (pairComputes (identityComputes inputEncoding) (LocalAffineEncodedReference.computes D)).andThen
    (OptionContext.computes inputEncoding Relabel.WordLookup.wordEncoding)

def optionalValue (r : Input (s:=s) (b:=b) (arity:=arity)) :=
  (selected D r).map (Relabel.Backend.recoveredValue D)

def optionalComputes : Computes (inputEncoding (s:=s) (b:=b) (arity:=arity))
    (optionEncoding (outputEncoding D)) (optionalValue D) :=
  (selectedComputes D).andThen (OptionMap.computes (Relabel.Backend.computes D))

def value (r : Input (s:=s) (b:=b) (arity:=arity)) := (optionalValue D r).getD 0

def rawComputes : Computes (inputEncoding (s:=s) (b:=b) (arity:=arity))
    (outputEncoding D) (value D) :=
  (optionalComputes D).andThen (OptionalValue.getDComputes (outputEncoding D) 0)

theorem selected_supported (r : Input (s:=s) (b:=b) (arity:=arity)) (w : List Bool)
    (h : LocalAffineEncodedReference.value D r=some w) :
    Relabel.Semantics.Supported D (r,w) := by
  have href : Relabel.Graph.reference (r,w)=LocalAffineEncodedReference.assignment r w := by
    funext e
    rfl
  change (LocalAffineLabels.network D r).assignmentTerm Fin.elim0 (Relabel.Graph.reference (r,w)) ≠ 0
  rw [href]
  exact LocalAffineEncodedReference.some_supported D r w h

/-- No converse from zero partition value to unsatisfiable support is used:
the Affine backend also handles cancellations on the some branch. -/
theorem value_exact (r : Input (s:=s) (b:=b) (arity:=arity)) :
    value D r=OriginalFamily.value D.signatures D.kernels r := by
  cases h : LocalAffineEncodedReference.value D r with
  | none =>
    simp only [value,optionalValue,selected,h,Option.map_none,Option.getD_none]
    exact (LocalAffineEncodedReference.none_original_zero D r h).symm
  | some w =>
    simp only [value,optionalValue,selected,h,Option.map_some,Option.getD_some]
    exact Relabel.Backend.supported_value D (r,w) (selected_supported D r w h)

def computes : Computes (inputEncoding (s:=s) (b:=b) (arity:=arity))
    (outputEncoding D) (OriginalFamily.value D.signatures D.kernels) :=
  congrComputes (rawComputes D) (value_exact D)

theorem inFP : InFP (inputEncoding (s:=s) (b:=b) (arity:=arity))
    (outputEncoding D) (OriginalFamily.value D.signatures D.kernels) := (computes D).inFP

theorem primitive_bound (r : Input (s:=s) (b:=b) (arity:=arity)) :
    primitiveCost (computes D).machine ((computes D).outputs r).steps
      (some (Turing.initList (computes D).machine.computer (inputEncoding.encode r))) ≤
      (primitivePolynomial (computes D)).eval (inputEncoding.encode r).length :=
  computes_primitive_cost (computes D) r

end
end Holant.LocalDrafts.MainChain.LocalAffineEvaluator
