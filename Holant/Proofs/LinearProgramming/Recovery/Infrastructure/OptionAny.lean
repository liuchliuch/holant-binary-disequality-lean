import Holant.Proofs.LinearProgramming.Interface

set_option autoImplicit false

/-! Three literal input words implement optional Boolean collapse. Root none
becomes false, while a present comparison returns its actual Boolean bit. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure.OptionAny
open Holant.Complexity Holant.Complexity.GraphPreprocessing
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def program (label : Bool) : Stmt (Fin 2) Bool Unit := if label then
  pop 0 (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (push 1 (fun v => v.1.getD false) (load (fun _ => (none,())) .halt))
      (load (fun _ => (some false,())) .halt))
else
  pop 0 (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun _ => (none,())) (goto (fun _ => true)))
        (push 1 (fun _ => false) (load (fun _ => (none,())) .halt)))
      (load (fun _ => (some false,())) .halt))
abbrev machine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Bool
  main := false
  State := Option Bool × Unit
  initial := (none,())
  program := program
abbrev inputEncoding := optionEncoding encodingBoolBool
def value (q : Option Bool) : Bool := q.getD false
def ticks (q : Option Bool) : ℕ := if q.isSome then 2 else 1

theorem exact_run (q : Option Bool) :
    Holant.Complexity.StackProtocol.RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode q))
      (haltList machine.computer (encodingBoolBool.encode (value q))) (ticks q) := by
  cases q with
  | none =>
    rw [Machine.init_eq,Machine.halt_eq]
    simp only [Holant.Complexity.StackProtocol.RunsExactly,ticks,Option.isSome_none,Bool.false_eq_true,↓reduceIte,Function.iterate_one]
    dsimp [machine,FinTM2.step,TM2.step,TM2.stepAux,program,inputEncoding,optionEncoding,value,encodingBoolBool,encodeBool]
    simp [wordTape,Function.update,TM2.stepAux]
  | some bit =>
    cases bit <;> rw [Machine.init_eq,Machine.halt_eq] <;>
      simp only [Holant.Complexity.StackProtocol.RunsExactly,ticks,Option.isSome_some,↓reduceIte,Function.iterate_succ_apply,Function.iterate_zero]
    all_goals
      dsimp [machine,FinTM2.step,TM2.step,TM2.stepAux,program,inputEncoding,optionEncoding,value,encodingBoolBool,encodeBool]
      simp [wordTape,Function.update,TM2.stepAux]
  
noncomputable def computes : Computes inputEncoding encodingBoolBool value where
  machine := machine
  time := 2
  outputs q := {steps := ticks q,evals_in_steps := exact_run q,steps_le_m := by cases q <;> simp [ticks]}
theorem inFP : InFP inputEncoding encodingBoolBool value := computes.inFP
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure.OptionAny
