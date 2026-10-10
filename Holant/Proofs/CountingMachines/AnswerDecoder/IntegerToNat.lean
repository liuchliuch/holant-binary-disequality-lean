import Holant.Complexity.IntegerArithmetic.Encoding
import Holant.Complexity.FixedFieldMachines.PrimitiveCost
import Holant.Complexity.StackProtocol

/-! Task-local adaptation, pending independent Lean validation.
The literal parity-sign integer codec is consumed by a finite Boolean-stack
program. Nonnegative words lose their leading zero sign bit (empty zero stays
empty). Negative words are physically erased, including the EOF transition.
No integer decoder, arbitrary host operation, or uncharged halt is an opcode.
-/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.IntegerToNat

open Turing Computability Holant.Complexity BinaryCompose StackProtocol

abbrev machine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Fin 3
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program label := match label.val with
    | 0 => .pop () (fun v bit => (bit, v.2))
        (.branch (fun v => v.1.getD false)
          (.load (fun v => (none, v.2)) (.goto (fun _ => 1)))
          (.load (fun v => (none, v.2)) .halt))
    | 1 => clearStmt () 1 2
    | _ => .halt

theorem first_step (word : List Bool) :
    machine.computer.step (initList machine.computer word) =
      if word.head?.getD false then
        some (cfg (1 : Fin 3) () (wordTape () word.tail))
      else some (haltList machine.computer word.tail) := by
  have hu (xs ys : List Bool) : Function.update (wordTape () xs) () ys = wordTape () ys := by
    funext k
    cases k
    rfl
  rw [Machine.init_eq, Machine.halt_eq]
  cases word with
  | nil => simp [FinTM2.step, TM2.step, machine, TM2.stepAux, cfg, hu] <;> rfl
  | cons b word =>
    cases b <;>
      simp [FinTM2.step, TM2.step, machine, TM2.stepAux, cfg, hu] <;> rfl

theorem erase_exact (word : List Bool) :
    RunsExactly machine.computer.step (cfg (1 : Fin 3) () (wordTape () word))
      (haltList machine.computer []) (word.length + 2) := by
  have clear := clear_exact machine.computer.step () (1 : Fin 3) (2 : Fin 3)
    (executesAt_tm2 _ _ _ rfl) () (wordTape () word)
  have hu : Function.update (wordTape () word) () [] = wordTape () [] := by
    funext k
    cases k
    rfl
  rw [hu] at clear
  have last : machine.computer.step (cfg (2 : Fin 3) () (wordTape () [])) =
      some (haltList machine.computer []) := by
    rw [Machine.halt_eq]
    rfl
  simpa only [wordTape_at,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
    clear.trans (runsExactly_one last)

def steps (z : ℤ) : ℕ :=
  if IntegerArithmetic.negative z then (IntegerArithmetic.encoding.encode z).length + 2 else 1

theorem exact_run (z : ℤ) :
    RunsExactly machine.computer.step
      (initList machine.computer (IntegerArithmetic.encoding.encode z))
      (haltList machine.computer (encodingNatBool.encode z.toNat)) (steps z) := by
  have first := first_step (IntegerArithmetic.encoding.encode z)
  rw [IntegerArithmetic.encoding_head, IntegerArithmetic.encoding_tail] at first
  cases z with
  | ofNat m =>
    change RunsExactly machine.computer.step
      (initList machine.computer (IntegerArithmetic.encoding.encode (Int.ofNat m)))
      (haltList machine.computer (encodeNat m)) 1
    simpa only [IntegerArithmetic.negative, Bool.false_eq_true, if_false,
      IntegerArithmetic.payload] using runsExactly_one first
  | negSucc m =>
    have hz : encodingNatBool.encode (Int.negSucc m).toNat = [] := rfl
    rw [hz]
    have h := (runsExactly_one first).trans (erase_exact (encodeNat m))
    simpa only [steps,IntegerArithmetic.negative,IntegerArithmetic.payload,
      if_true,IntegerArithmetic.encoding_negSucc,List.length_cons,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Only this mathematical certificate's Polynomial field needs noncomputable
operations; its machine is the unchanged finite program defined above. -/
noncomputable def computes : Computes IntegerArithmetic.encoding encodingNatBool Int.toNat where
  machine := machine
  time := Polynomial.X + 2
  outputs z :=
    { steps := steps z
      evals_in_steps := exact_run z
      steps_le_m := by simp only [steps, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_ofNat]; split_ifs <;> omega }

theorem output_length_le (z : ℤ) :
    (encodingNatBool.encode z.toNat).length ≤ (IntegerArithmetic.encoding.encode z).length := by
  cases z with
  | ofNat m =>
    change (encodeNat m).length ≤ (IntegerArithmetic.encoding.encode (Int.ofNat m)).length
    have he : (IntegerArithmetic.encoding.encode (Int.ofNat m)).tail = encodeNat m := by
      simpa only [IntegerArithmetic.payload] using IntegerArithmetic.encoding_tail (Int.ofNat m)
    rw [← he]
    simp only [List.length_tail]
    omega
  | negSucc m =>
    change (0 : ℕ) ≤ (IntegerArithmetic.encoding.encode (Int.negSucc m)).length
    exact Nat.zero_le _

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.IntegerToNat
