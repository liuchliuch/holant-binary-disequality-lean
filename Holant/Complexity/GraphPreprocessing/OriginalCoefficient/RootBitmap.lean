import Holant.Complexity.GraphPreprocessing.BitTable
import Holant.Complexity.GraphPreprocessing.OccurrenceLabel
import Holant.Complexity.GraphPreprocessing.UnaryBinary
import Holant.Complexity.GraphPreprocessing.Call

/-! Actual root-bitmap initialization from physical unary vertex and root IDs.
The vertex word allocates false cells one token at a time; BitTable's real indexed
write marks the root, after which the old-bit output and all work are erased. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmap
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := Fin 4 ⊕ Fin 3
abbrev Label := Fin 4 ⊕ Fin 12
abbrev Statement := Stmt Stack Label Unit

def returns (label : Fin 4) : Fin 12 := if label=2 then 5 else 11
def outside (phase : Fin 12) : Statement := match phase.val with
  | 0 => Frame.scanStmt (.inr 0) (.inr 2) (.inr 0) (.inr 1) (.inr 11)
  | 1 => copyMoveStmt (.inr 2) (.inr 1) (.inr 1) (.inr 2)
  | 2 => copyMoveStmt (.inr 0) (.inr 2) (.inr 2) (.inr 3)
  | 3 => copyMoveStmt (.inr 2) (.inl 1) (.inr 3) (.inr 4)
  | 4 => pop (.inr 1) (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (push (.inl 0) (fun _ => false) (load (fun _ => (none,())) (goto (fun _ => .inr 4))))
      (load (fun _ => (none,())) (goto (fun _ => .inl 0))))
  | 5 => clearStmt (.inl 3) (.inr 5) (.inr 6)
  | 11 => load (fun _ => (some false,())) .halt
  | _ => .halt

def program : Label → Statement := Returning.program (BitTable.machine (some true)).program returns outside

abbrev machine : Machine where
  K := Stack
  input := .inr 0
  output := .inl 0
  Label := Label
  main := .inr 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def work (input counter temporary table index output : List Bool) : Stack → List Bool :=
  Sum.elim (BitTable.tapes table index [] output) ![input,counter,temporary]
def config (label : Label) (input counter temporary table index output : List Bool) :=
  cfg label () (work input counter temporary table index output)

abbrev Input := Σ vertices : ℕ, Fin vertices
def inputEncoding : Encoding Input Bool := sigmaEncoding UnaryBinary.unaryEncoding OccurrenceLabel.unaryPortEncoding
def value (x : Input) : List Bool := (List.replicate x.1 false).set x.2.val true

@[simp] theorem input_word (x : Input) :
    inputEncoding.encode x = Holant.Algebraic.frame (List.replicate x.1 true)++List.replicate x.2.val true := rfl
@[simp] theorem value_length (x : Input) : (value x).length=x.1 := by simp [value]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmap
