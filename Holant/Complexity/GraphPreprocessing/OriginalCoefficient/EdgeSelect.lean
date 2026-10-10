import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.UnarySkip
import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Complexity.BinaryCompose.Interface

/-! Literal original-edge indexed lookup of the opposite endpoint. The source
edge table uses false-delimited unary endpoints in original edge order. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def program (label : Fin 16) : Stmt (Fin 5) (Fin 16) Unit := match label.val with
  | 0 => Frame.scanStmt 0 4 0 1 15
  | 1 => copyMoveStmt 4 1 1 2
  | 2 => Frame.scanStmt 0 4 2 3 15
  | 3 => copyMoveStmt 4 2 3 4
  | 4 => pop 2 (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun _ => (none,())) (goto (fun _ => 5)))
        (load (fun _ => (none,())) (goto (fun _ => 15))))
      (load (fun _ => (none,())) (goto (fun _ => 7))))
  | 5 => UnarySkip.statement 1 5 6 15
  | 6 => UnarySkip.statement 1 6 4 15
  | 7 => pop 0 (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun _ => (none,())) (goto (fun _ => 8)))
        (load (fun _ => (none,())) (goto (fun _ => 9))))
      (load (fun _ => (none,())) (goto (fun _ => 15))))
  | 8 => UnaryField.statement 1 3 8 10 15
  | 9 => UnarySkip.statement 1 9 8 15
  | 10 => clearStmt 1 10 11
  | 11 => clearStmt 0 11 12
  | 12 => clearStmt 2 12 13
  | 15 => load (fun _ => (some false,())) .halt
  | _ => .halt

abbrev machine : Machine where
  K := Fin 5
  input := 0
  output := 3
  Label := Fin 16
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def tapes (input table index output temporary : List Bool) : Fin 5 → List Bool := ![input,table,index,output,temporary]
def config (l : Fin 16) (input table index output temporary : List Bool) := cfg l () (tapes input table index output temporary)

@[simp] theorem update_input (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) 0 word=tapes word table index output temporary := by
  funext k; fin_cases k <;> simp [tapes,Function.update]
@[simp] theorem update_table (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) 1 word=tapes input word index output temporary := by
  funext k; fin_cases k <;> simp [tapes,Function.update]
@[simp] theorem update_index (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) 2 word=tapes input table word output temporary := by
  funext k; fin_cases k <;> simp [tapes,Function.update]
@[simp] theorem update_output (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) 3 word=tapes input table index word temporary := by
  funext k; fin_cases k <;> simp [tapes,Function.update]
@[simp] theorem update_temporary (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) 4 word=tapes input table index output word := by
  funext k; fin_cases k <;> simp [tapes,Function.update]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
