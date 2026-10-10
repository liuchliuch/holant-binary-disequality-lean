import Holant.Complexity.GraphPreprocessing.ListIndex
import Holant.Complexity.GraphPreprocessing.Returning
import Holant.OneHot.StackProgram.GraphLabelEncoding
import Holant.Complexity.GraphPreprocessing.OccurrenceLabel
import Holant.OneHot.StackProgram.Machine.StackWord

/-! Clean physical access to an original ordered parent-table row. The framed
table and unary original vertex index are parsed, the actual list-index loop
runs, and the unselected suffix (including its terminator) is erased. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentRowSelect
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := Fin 4 ⊕ Fin 2
abbrev Label := Fin 7 ⊕ Fin 7
abbrev Statement := Stmt Stack Label Unit

def returns (i : Fin 7) : Fin 7 := if i=4 then 4 else 6

def controller (i : Fin 7) : Statement := match i.val with
  | 0 => Frame.scanStmt (.inr 0) (.inr 1) (.inr 0) (.inr 1) (.inr 6)
  | 1 => copyMoveStmt (.inr 1) (.inl 0) (.inr 1) (.inr 2)
  | 2 => copyMoveStmt (.inr 0) (.inr 1) (.inr 2) (.inr 3)
  | 3 => copyMoveStmt (.inr 1) (.inl 1) (.inr 3) (.inl 0)
  | 4 => clearStmt (.inl 0) (.inr 4) (.inr 5)
  | _ => .halt

def program : Label → Statement := Returning.program ListIndex.machine.program returns controller

abbrev machine : Machine where
  K := Stack
  input := .inr 0
  output := .inl 2
  Label := Label
  main := .inr 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def tapes (input table index output temporary : List Bool) : Stack → List Bool :=
  Sum.elim (ListIndex.tapes table index output []) ![input,temporary]
def config (l : Label) (input table index output temporary : List Bool) :=
  cfg l () (tapes input table index output temporary)

@[simp] theorem update_input (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) (.inr 0) word = tapes word table index output temporary := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
@[simp] theorem update_table (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) (.inl 0) word = tapes input word index output temporary := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
@[simp] theorem update_index (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) (.inl 1) word = tapes input table word output temporary := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
@[simp] theorem update_output (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) (.inl 2) word = tapes input table index word temporary := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
@[simp] theorem update_temporary (input table index output temporary word : List Bool) :
    Function.update (tapes input table index output temporary) (.inr 1) word = tapes input table index output word := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [tapes,ListIndex.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

theorem parse_table (table index : List Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 0) (Holant.Algebraic.frame table ++ index) [] [] [] [])
      (config (.inr 2) index table [] [] []) (2*(table.length+1)) := by
  have run := Frame.extract_exact (Sum.inr 0 : Stack) (.inl 0) (.inr 1)
    (by decide) (by decide) (by decide) (TM2.step program) (.inr 0) (.inr 1) (.inr 2) (.inr 6)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (tapes [] [] [] [] []) table index []
  simpa only [config,tapes3,update_input,update_table,update_temporary,List.append_nil] using run

theorem move_index (table index : List Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 2) index table [] [] [])
      (config (.inl 0) [] table index [] []) (2*(index.length+1)) := by
  have run := Holant.OneHot.StackProgram.Machine.StackWord.move_exact (Sum.inr 0 : Stack) (.inl 1) (.inr 1)
    (by decide) (by decide) (by decide) (TM2.step program) (.inr 2) (.inr 3) (.inl 0)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (tapes [] table [] [] []) index []
  simpa only [config,tapes3,update_input,update_index,update_temporary,List.append_nil] using run

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentRowSelect
