import Holant.Proofs.LinearProgramming.Complexity.CounterLoop.ControlInvariant

/-! Rational LP physical resource implementation, adapted from the supplied reference.
A single physical search returns Bool plus original input and terminal stored
matrix/center. The receipt and center programs parse THAT returned state,
rather than run a second mathematical search or select another rational point.
This is the exact interface for subsequent original-point reconstruction:
accepted center satisfies Thickening.At, length is the original dimension,
and false means original infeasibility. Exact Codec.Response is not asserted.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion
open Holant.LocalDrafts.RemoteWork.RationalLP.Optimization Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search
open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing Codec
namespace Receipt
noncomputable section

abbrev Data := Bool × StepProgram.Query
def encoding := pairEncoding encodingBoolBool StepProgram.encoding
def value (d : Input) : Data := (result d,query (resultState d))
def parse : Computes CounterLoop.encoding encoding
    (fun s : State => (answer s,query s)) := pairComputes answerComputes queryComputes
def computes : Computes Source.highEncoding encoding (fun d : Source.HighInput => value d.val) :=
  Source.stateComputes.andThen parse

def output (d : Input) (hn : 2≤d.val.dimension) :
    TM2OutputsInTime computes.machine.computer (inputEncoding.encode d)
      (some (encoding.encode (value d))) (computes.time.eval (inputEncoding.encode d).length) :=
  computes.outputs ⟨d,hn⟩

theorem original (d : Source.HighInput) : (value d.val).2.1=d.val :=
  source_preserved d.val d.property
theorem accepted (d : Source.HighInput) : (value d.val).1=true ↔ ∃ x, Feasible d.val.val x :=
  Source.correct d
theorem rejected (d : Source.HighInput) : (value d.val).1=false ↔ ¬∃ x, Feasible d.val.val x :=
  Source.correct_false d

def center (d : Input) : List ℚ := (query (resultState d)).2.1
def stored : Computes CounterLoop.encoding StorageProgram.encoding
    (fun s : State => (query s).2) := queryComputes.andThen StorageProgram.stored
def parseCenter : Computes CounterLoop.encoding pointEncoding (fun s : State => (query s).2.1) :=
  stored.andThen (Wiring.firstComputes pointEncoding StorageProgram.matrixEncoding)
def centerComputes : Computes Source.highEncoding pointEncoding
    (fun d : Source.HighInput => center d.val) := Source.stateComputes.andThen parseCenter

theorem center_length (d : Input) (hn : 2≤d.val.dimension) : (center d).length=d.val.dimension := by
  obtain ⟨j,hj,he⟩ := ControlInvariant.terminal_counter d hn
  simp only [center,he,query,stamp,queryAt,StorageProgram.code,List.length_ofFn]

theorem thickened (d : Input) (hn : 2≤d.val.dimension) (ha : result d=true) :
    Thickening.At d.val (Thickening.epsilon d.val) (Codec.point d.val (center d)) := by
  exact accepted_center d hn ha

def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial computes

theorem primitive_cost (d : Source.HighInput) :
    primitiveCost computes.machine (computes.outputs d).steps
      (some (initList computes.machine.computer (Source.highEncoding.encode d)))≤
      primitivePolynomial.eval (inputEncoding.encode d.val).length :=
  computes_primitive_cost computes d

end
end Receipt
end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
