import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertexInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordJoin
import Holant.Complexity.GraphPreprocessing.EndpointQuery
import Holant.Complexity.GraphPreprocessing.EdgeTableEncoding
import Holant.Complexity.GraphPreprocessing.OccurrenceLabel
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! One original edge's actual two-vertex table word. The input edge coordinate
is physical unary; both binary queries are constructed by real carry/framing
machines, and both original incidences are searched in the actual raw graph. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option Elab.async false

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) :=
  Σ r : {r : RawClosedNetwork // r.WellFormed s b arity}, Fin r.val.edges.length

def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool :=
  sigmaEncoding (RawClosedNetwork.validatedEncoding s b arity)
    (fun r => OccurrenceLabel.unaryPortEncoding r.val.edges.length)

variable {s b : ℕ} {arity : ℕ → ℕ}
def atSide (side : Bool) (x : Input s b arity) : EndpointVertex.Input s b arity := ⟨x.1,x.2,side⟩

def word (x : Input s b arity) : List Bool :=
  ReachRound.unary (x.1.val.lookup x.1.property (x.2,false)).1.val ++
    ReachRound.unary (x.1.val.lookup x.1.property (x.2,true)).1.val

noncomputable def queryComputes (s b : ℕ) (arity : ℕ → ℕ) (side : Bool) :
    Computes (inputEncoding s b arity) (EndpointVertex.inputEncoding s b arity) (atSide side) :=
  recode (rightMapComputes Frame.wordEncoding (UnaryBinary.computes.andThen
    (GraphPreprocessing.EndpointQuery.computes side)))
    (fun x => (RawClosedNetwork.encoding.encode x.1.val,x.2.val)) (fun _ => rfl) (fun _ => rfl)

noncomputable def vertexComputes (s b : ℕ) (arity : ℕ → ℕ) (side : Bool) :
    Computes (inputEncoding s b arity) Frame.wordEncoding (fun x => EndpointVertex.vertexBits (atSide side x)) :=
  (queryComputes s b arity side).andThen (EndpointVertex.computes s b arity)

/-- Appending the unary terminator is a finite fanout/constant/concatenation
program, including physical tail placement, not a list-valued instruction. -/
noncomputable def terminateComputes : Computes Frame.wordEncoding Frame.wordEncoding (fun w => w++[false]) :=
  (pairComputes (identityComputes Frame.wordEncoding)
    (constantComputes Frame.wordEncoding Frame.wordEncoding [false])).andThen WordJoin.computes

noncomputable def endComputes (s b : ℕ) (arity : ℕ → ℕ) (side : Bool) :
    Computes (inputEncoding s b arity) Frame.wordEncoding
      (fun x => ReachRound.unary (x.1.val.lookup x.1.property (x.2,side)).1.val) :=
  (vertexComputes s b arity side).andThen terminateComputes

abbrev queryMachine (side : Bool) : Machine :=
  rightMapMachine (UnaryBinary.machine.compose (GraphPreprocessing.EndpointQuery.machine side))
abbrev vertexMachine (side : Bool) : Machine := (queryMachine side).compose EndpointVertex.machine
abbrev terminateMachine : Machine := (pairMachine identityMachine (Constant.machine [false])).compose WordJoin.machine
abbrev endMachine (side : Bool) : Machine := (vertexMachine side).compose terminateMachine
abbrev machine : Machine := (pairMachine (endMachine false) (endMachine true)).compose WordJoin.machine

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding word :=
  (pairComputes (endComputes s b arity false) (endComputes s b arity true)).andThen WordJoin.computes

@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine = machine := rfl

noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time

noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime machine.computer ((inputEncoding s b arity).encode x) (some (word x))
      ((timePolynomial s b arity).eval ((inputEncoding s b arity).encode x).length) :=
  (computes s b arity).outputs x

theorem inFP : InFP (inputEncoding s b arity) Frame.wordEncoding word := (computes s b arity).inFP

/-- Each original edge contributes exactly its two original unary vertex IDs
and two delimiters, regardless of local-port ordering or loop identity. -/
theorem output_length (x : Input s b arity) : (word x).length ≤ 2*x.1.val.vertices.length := by
  have hu := (x.1.val.lookup x.1.property (x.2,false)).1.isLt
  have hv := (x.1.val.lookup x.1.property (x.2,true)).1.isLt
  simp only [word,List.length_append,ReachRound.unary_length]
  omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord
