import Holant.Proofs.LinearProgramming.Foundation.Parsing

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Literal bit counter: pop each source bit, push one unary token, clear the
finite control and halt. No host-level input-length instruction is used.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.LengthCounter
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false

abbrev machine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  program _ := pop 0 (fun _ b => b)
    (branch Option.isSome
      (push 1 (fun _ => true) (load (fun _ => none) (goto (fun _ => ()))))
      (load (fun _ => none) .halt))

def config (input output : List Bool) : machine.Config := ⟨some (),none,![input,output]⟩

theorem step_cons (b : Bool) (input output : List Bool) :
    machine.computer.step (config (b::input) output) = some (config input (true::output)) := by
  simp [FinTM2.step,TM2.step,TM2.stepAux,machine,config]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem step_nil (output : List Bool) :
    machine.computer.step (config [] output) = some (haltList machine.computer output) := by
  rw [Machine.halt_eq]
  simp [FinTM2.step,TM2.step,TM2.stepAux,machine,config] <;>
    funext k <;> fin_cases k <;> simp [wordTape,Function.update]

theorem run (input output : List Bool) :
    (fun c : Option machine.Config => c.bind machine.computer.step)^[input.length+1]
      (some (config input output)) =
        some (haltList machine.computer (List.replicate input.length true ++ output)) := by
  induction input generalizing output with
  | nil => simpa using step_nil output
  | cons b input ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    simp only [Option.bind_some,step_cons]
    simpa [List.replicate_succ',List.append_assoc] using ih (true::output)

theorem initial (input : List Bool) : initList machine.computer input = config input [] := by
  rw [Machine.init_eq]
  congr 1
  funext k
  fin_cases k <;> rfl

noncomputable def computes : Computes Frame.wordEncoding UnaryBinary.unaryEncoding List.length where
  machine := machine
  time := Polynomial.X+1
  outputs input := {
    steps := input.length+1
    evals_in_steps := by
      change (fun c : Option machine.Config => c.bind machine.computer.step)^[input.length+1]
        (some (initList machine.computer input)) =
          some (haltList machine.computer (List.replicate input.length true))
      rw [initial]
      simpa only [List.append_nil] using run input []
    steps_le_m := by simp [Frame.wordEncoding] }

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.LengthCounter
