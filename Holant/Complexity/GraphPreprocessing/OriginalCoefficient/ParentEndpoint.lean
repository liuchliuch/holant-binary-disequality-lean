import Holant.Complexity.GraphPreprocessing.Traversal.ParentRead
import Holant.Complexity.GraphPreprocessing.Returning
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-! Clean physical parent-row projection. The root marker remains distinct from
edge zero and false orientation. Both original unary fields are skipped, the
parent edge is parsed and reframed, and every tape is cleared except output. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentEndpoint
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Traversal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := Fin 4 ⊕ Fin 0
abbrev Label := Fin 11 ⊕ Fin 10
abbrev Statement := Stmt Stack Label Unit

def returns (i : Fin 11) : Fin 10 := if i=8 then 0 else if i=7 then 4 else 5

def controller (i : Fin 10) : Statement := match i.val with
  | 0 => copyMoveStmt (.inl 1) (.inl 2) (.inr 0) (.inr 1)
  | 1 => FixedFieldMachines.FrameEmit.delimiterStmt (.inl 3) (.inr 2)
  | 2 => FixedFieldMachines.FrameEmit.emitStmt (.inl 2) (.inl 3) (.inr 2) (.inr 3)
  | 3 => push (.inl 3) (fun _ => true) .halt
  | 4 => push (.inl 3) (fun _ => false) .halt
  | 5 => clearStmt (.inl 0) (.inr 5) (.inr 6)
  | 6 => clearStmt (.inl 1) (.inr 6) (.inr 7)
  | 7 => clearStmt (.inl 2) (.inr 7) (.inr 8)
  | 8 => clearStmt (.inl 3) (.inr 8) (.inr 9)
  | _ => .halt

def program : Label → Statement := Returning.program ParentRead.program returns controller

abbrev machine : Machine where
  K := Stack
  input := .inl 0
  output := .inl 3
  Label := Label
  main := .inl 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def tapes (input edge scratch output : List Bool) : Stack → List Bool :=
  Sum.elim (ParentRead.tapes input edge scratch output) Fin.elim0

def config (l : Label) (input edge scratch output : List Bool) :=
  cfg l () (tapes input edge scratch output)

@[simp] theorem update_input (input edge scratch output word : List Bool) :
    Function.update (tapes input edge scratch output) (.inl 0) word = tapes word edge scratch output := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [tapes,ParentRead.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => exact Fin.elim0 k
@[simp] theorem update_edge (input edge scratch output word : List Bool) :
    Function.update (tapes input edge scratch output) (.inl 1) word = tapes input word scratch output := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [tapes,ParentRead.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => exact Fin.elim0 k
@[simp] theorem update_scratch (input edge scratch output word : List Bool) :
    Function.update (tapes input edge scratch output) (.inl 2) word = tapes input edge word output := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [tapes,ParentRead.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => exact Fin.elim0 k
@[simp] theorem update_output (input edge scratch output word : List Bool) :
    Function.update (tapes input edge scratch output) (.inl 3) word = tapes input edge scratch word := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [tapes,ParentRead.tapes,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => exact Fin.elim0 k

theorem tapes_empty : tapes [] [] [] [] = fun _ => [] := by
  funext k; cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => exact Fin.elim0 k

theorem initial (word : List Bool) :
    initList machine.computer word = config (.inl 0) word [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input [] [] [] [] word
  rw [tapes_empty] at h
  change wordTape (Sum.inl 0 : Stack) word = _ at h
  unfold config cfg
  congr 1

theorem halt_tag (parent : Bool) (word : List Bool) :
    TM2.step program (config (.inr (if parent then 3 else 4)) [] [] [] word) =
      some (haltList machine.computer (parent::word)) := by
  rw [Machine.halt_eq]
  have h := update_output [] [] [] [] (parent::word)
  rw [tapes_empty] at h
  change wordTape (Sum.inl 3 : Stack) (parent::word) = _ at h
  cases parent <;>
    change some (⟨none,(none,()),Function.update (tapes [] [] [] word) (.inl 3) (_::word)⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool × Unit)) = _
  all_goals rw [update_output,← h]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentEndpoint
