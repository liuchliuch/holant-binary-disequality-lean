import Holant.Proofs.LinearProgramming.Foundation.Infrastructure.BitTable
import Holant.Complexity.GraphPreprocessing.OccurrenceLabel
import Holant.Complexity.GraphPreprocessing.Returning
import Holant.OneHot.StackProgram.Machine.StackWord

/-! Clean Boolean-table reading with an actual physical unary index. This is
an executable subroutine for the reachability predicate, not a list callback. -/
open Holant.Complexity Holant.Complexity.GraphPreprocessing

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.BitRead
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := Fin 4 ⊕ Fin 2
abbrev Label := Fin 4 ⊕ Fin 8
abbrev Statement := Stmt Stack Label Unit

def returns (l : Fin 4) : Fin 8 := if l=2 then 4 else 7

def controller (i : Fin 8) : Statement := match i.val with
  | 0 => Frame.scanStmt (.inr 0) (.inr 1) (.inr 0) (.inr 1) (.inr 7)
  | 1 => copyMoveStmt (.inr 1) (.inl 0) (.inr 1) (.inr 2)
  | 2 => copyMoveStmt (.inr 0) (.inr 1) (.inr 2) (.inr 3)
  | 3 => copyMoveStmt (.inr 1) (.inl 1) (.inr 3) (.inl 0)
  | 4 => clearStmt (.inl 0) (.inr 4) (.inr 5)
  | 7 => load (fun _ => (some false,())) .halt
  | _ => .halt

def program : Label → Statement := Returning.program (BitTable.machine none).program returns controller

abbrev machine : Machine where
  K := Stack
  input := .inr 0
  output := .inl 3
  Label := Label
  main := .inr 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def work (input table index output temporary : List Bool) : Stack → List Bool :=
  Sum.elim (BitTable.tapes table index [] output) ![input,temporary]

def config (l : Label) (input table index output temporary : List Bool) :=
  cfg l () (work input table index output temporary)

abbrev Input := Σ table : List Bool, Fin table.length

def inputEncoding : Encoding Input Bool :=
  sigmaEncoding Frame.wordEncoding (fun table => OccurrenceLabel.unaryPortEncoding table.length)

def value (x : Input) : Bool := x.1.get x.2

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.BitRead
