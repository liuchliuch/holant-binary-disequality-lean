import Holant.Complexity.GraphPreprocessing.Traversal.Machine
import Holant.Complexity.FixedFieldMachines.Wiring

/-! Linear bitwise emission of traversal literals. Input-dependent words are
never decoded by a fixed finite decision tree or loaded as one instruction. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.LiteralBits
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
abbrev tapes := Wiring.tapes
def program : Bool → Stmt (Fin 3) Bool Unit
  | false => copyMoveStmt 0 1 false true
  | true => pop 1 (fun st bit => (bit,st.2)) (branch (fun st => st.1.isSome)
      (push 0 (fun st => st.1.getD false) (push 0 (fun _ => false)
        (load (fun _ => (none,())) (goto (fun _ => true)))))
      (load (fun _ => (none,())) .halt))
abbrev machine : Machine where
  K := Fin 3
  input := 0
  output := 0
  Label := Bool
  main := false
  State := Option Bool × Unit
  initial := (none,())
  program := program

theorem emit_nil (out : List Bool) :
    machine.computer.step (cfg true () (tapes out [] []))=some (haltList machine.computer out) := by
  rw [Machine.halt_eq]
  dsimp [machine,FinTM2.step,TM2.step,program,TM2.stepAux,cfg,tapes,Wiring.tapes]
  simp only [Bool.cond_false,Bool.cond_true]
  congr 2
  funext k
  fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
theorem emit_cons (bit : Bool) (bits out : List Bool) :
    machine.computer.step (cfg true () (tapes out (bit::bits) []))=
      some (cfg true () (tapes (false::bit::out) bits [])) := by
  dsimp [machine,FinTM2.step,TM2.step,program,TM2.stepAux,cfg,tapes,Wiring.tapes]
  simp only [Bool.cond_false,Bool.cond_true]
  congr 2
  funext k
  fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
theorem emit_exact (bits out : List Bool) :
    RunsExactly machine.computer.step (cfg true () (tapes out bits []))
      (haltList machine.computer (Traversal.literals bits.reverse++out)) (bits.length+1) := by
  induction bits generalizing out with
  | nil => simpa using runsExactly_one (emit_nil out)
  | cons bit bits ih =>
    have h := (runsExactly_one (emit_cons bit bits out)).trans (ih (false::bit::out))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using h

theorem exact_run (word : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer word)
      (haltList machine.computer (Traversal.literals word)) (2*word.length+2) := by
  have first := copy_move_exact (0 : Fin 3) 2 1 (by decide) (by decide)
    machine.computer.step false true (executesAt_tm2 _ _ _ rfl) () (fun _ => []) word [] []
  have ht (a b : List Bool) : tapes3 (fun _ : Fin 3 => []) 0 2 1 a [] b=tapes a b [] := by
    funext k; fin_cases k <;> rfl
  rw [ht,ht] at first
  simp only [List.append_nil] at first
  have hi : cfg false () (tapes word [] [])=initList machine.computer word := by
    rw [Machine.init_eq]; congr 1; funext k; fin_cases k <;> rfl
  rw [hi] at first
  have all := first.trans (emit_exact word.reverse [])
  simpa [Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
noncomputable def computes : Computes Frame.wordEncoding Frame.wordEncoding Traversal.literals where
  machine := machine
  time := 2*Polynomial.X+2
  outputs word := {steps := 2*word.length+2,evals_in_steps := exact_run word,steps_le_m := by simp [Frame.wordEncoding]}
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.LiteralBits
