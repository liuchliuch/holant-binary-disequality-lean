import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordCompare
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitReadInterface
import Holant.Complexity.GraphPreprocessing.FiniteRecode
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! The actual oriented-neighbor test combines real bitwise endpoint equality
and a real indexed read of the old reachability bitmap. Only its final Boolean
AND is a fixed finite decision table. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicate
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option Elab.async false

abbrev Input := (List Bool × List Bool) × BitRead.Input
def inputEncoding : Encoding Input Bool := pairEncoding WordCompare.inputEncoding BitRead.inputEncoding
def boolPair := pairEncoding encodingBoolBool encodingBoolBool
def conjunction (p : Bool × Bool) : Bool := p.1 && p.2
def value (x : Input) : Bool := WordCompare.value x.1 && BitRead.value x.2

theorem bool_length (p : Bool × Bool) : (boolPair.encode p).length ≤ 4 := by
  rcases p with ⟨a,b⟩; cases a <;> cases b <;> decide

noncomputable def andComputes : Computes boolPair encodingBoolBool conjunction :=
  FiniteRecode.computes boolPair encodingBoolBool conjunction 4 bool_length

noncomputable def comparisonComputes : Computes inputEncoding encodingBoolBool (fun x => WordCompare.value x.1) :=
  (Wiring.firstComputes WordCompare.inputEncoding BitRead.inputEncoding).andThen WordCompare.computes

noncomputable def membershipComputes : Computes inputEncoding encodingBoolBool (fun x => BitRead.value x.2) :=
  (Wiring.secondComputes WordCompare.inputEncoding BitRead.inputEncoding).andThen BitRead.computes

abbrev andMachine : Machine := FiniteRecode.machine boolPair encodingBoolBool conjunction 4
abbrev comparisonMachine : Machine := Wiring.firstMachine.compose WordCompare.machine
abbrev membershipMachine : Machine := secondMachine.compose BitRead.machine
abbrev machine : Machine := (pairMachine comparisonMachine membershipMachine).compose andMachine

noncomputable def computes : Computes inputEncoding encodingBoolBool value :=
  (pairComputes comparisonComputes membershipComputes).andThen andComputes

@[simp] theorem computes_machine : computes.machine = machine := rfl
noncomputable def timePolynomial : Polynomial ℕ := computes.time
noncomputable def timed (x : Input) : TM2OutputsInTime machine.computer (inputEncoding.encode x)
    (some (encodingBoolBool.encode (value x))) (timePolynomial.eval (inputEncoding.encode x).length) :=
  computes.outputs x
theorem inFP : InFP inputEncoding encodingBoolBool value := computes.inFP

/-- The caller supplies physical original vertex words and a read-only bitmap;
the machine contains no natural-number equality or table-lookup instruction. -/
def query (table : List Bool) (target endpoint opposite : Fin table.length) : Input :=
  ((List.replicate target.val true,List.replicate endpoint.val true),⟨table,opposite⟩)

theorem query_value (table : List Bool) (target endpoint opposite : Fin table.length) :
    value (query table target endpoint opposite) = (decide (target=endpoint) && table.get opposite) := by
  have he : List.replicate target.val true = List.replicate endpoint.val true ↔ target=endpoint := by
    constructor
    · intro h; have hn := congrArg List.length h; simp only [List.length_replicate] at hn; exact Fin.ext hn
    · intro h; subst endpoint; rfl
  simp only [value,query,WordCompare.value,BitRead.value,he]

theorem query_length (table : List Bool) (target endpoint opposite : Fin table.length) :
    (inputEncoding.encode (query table target endpoint opposite)).length ≤ 9*(table.length+1) := by
  have ht := target.isLt
  have he := endpoint.isLt
  have ho := opposite.isLt
  simp only [inputEncoding,query,pairEncoding,WordCompare.inputEncoding,Frame.wordEncoding,
    BitRead.input_word,List.length_append,Holant.Algebraic.frame_length,List.length_replicate,id_eq]
  omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicate
