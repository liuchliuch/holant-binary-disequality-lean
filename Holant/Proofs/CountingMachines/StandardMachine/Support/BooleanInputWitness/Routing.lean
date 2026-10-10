import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Guard
import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Counter
import Holant.Complexity.BinaryCompose.Transfer

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Small literal tape consumers for the returned guard
packet. A fixed finite Boolean table is emitted by push syntax; an unbounded
prefix is traversed by a pop loop. No whole-word function is a runtime opcode. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Routing
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing StackProtocol

namespace Prefix
def program (l : Fin 4) : Stmt (Fin 3) (Fin 4) Unit :=
  if l=0 then .pop 0 (fun _ _ => (none,())) (.goto (fun _ => 1))
  else if l=1 then copyMoveStmt 0 1 1 2
  else if l=2 then copyMoveStmt 1 2 2 3
  else .halt
abbrev machine : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 2
  Label := Fin 4
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

theorem header (b : Bool) (bits : List Bool) :
    machine.computer.step (cfg (0 : Fin 4) () (wordTape (0 : Fin 3) (b::bits))) =
      some (cfg (1 : Fin 4) () (wordTape (0 : Fin 3) bits)) := by
  dsimp [FinTM2.step,TM2.step,machine,program,cfg,TM2.stepAux,wordTape,cond]
  try simp only [Function.update_self,List.head?_cons,List.head?_nil,List.tail_cons,List.tail_nil,
    Option.isSome_none,Option.isSome_some,Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> simp [wordTape]
theorem halt (bits : List Bool) :
    machine.computer.step (cfg (3 : Fin 4) () (wordTape (2 : Fin 3) bits)) =
      some (haltList machine.computer bits) := by
  rw [Machine.halt_eq]
  rfl
theorem run (b : Bool) (bits : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (b::bits))
      (haltList machine.computer bits) (2*bits.length+4) := by
  have ht := transfer_exact machine.computer.step (0 : Fin 3) 2 1
    (by decide) (by decide) (by decide) (1 : Fin 4) 2 3
    (executesAt_tm2 program 1 _ rfl) (executesAt_tm2 program 2 _ rfl) () bits
  have h := ((runsExactly_one (header b bits)).trans ht).trans (runsExactly_one (halt bits))
  rw [Machine.init_eq]
  convert h using 1 <;> (try dsimp [machine,cfg]) <;> omega

def computes : Computes Guard.outputEncoding Frame.wordEncoding (fun p => p.getD []) where
  machine := machine
  time := 2*Polynomial.X+4
  outputs p := by
    cases p with
    | none =>
        refine { steps := 4, evals_in_steps := ?_, steps_le_m := by simp [Guard.outputEncoding] }
        change RunsExactly machine.computer.step _ _ _
        simpa [Guard.outputEncoding,Frame.wordEncoding] using run false []
    | some bits =>
        refine {
          steps := 2*bits.length+4
          evals_in_steps := ?_
          steps_le_m := by simp [Guard.outputEncoding] }
        change RunsExactly machine.computer.step _ _ _
        simpa [Guard.outputEncoding,Frame.wordEncoding] using run true bits
end Prefix

namespace Flag
def program (l : Fin 2) : Stmt (Fin 2) (Fin 2) Bool :=
  if l=0 then .pop 0 (fun _ b => (none,b.getD false)) (.goto (fun _ => 1))
  else .pop 0 (fun v b => (b,v.2))
    (.branch (fun v => v.1.isSome)
      (.load (fun v => (none,v.2)) (.goto (fun _ => 1)))
      (.push 1 (fun v => v.2) (.load (fun _ => (none,false)) .halt)))
abbrev machine : BinaryCompose.Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Fin 2
  main := 0
  State := Option Bool × Bool
  initial := (none,false)
  program := program
theorem header (b : Bool) (bits : List Bool) :
    machine.computer.step (initList machine.computer (b::bits)) =
      some (cfg (1 : Fin 2) b (wordTape (0 : Fin 2) bits)) := by
  rw [Machine.init_eq]
  dsimp [FinTM2.step,TM2.step,machine,program,cfg,TM2.stepAux,wordTape,cond]
  try simp only [Function.update_self,List.head?_cons,List.head?_nil,List.tail_cons,List.tail_nil,
    Option.isSome_none,Option.isSome_some,Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> simp [wordTape]
theorem cons (flag b : Bool) (bits : List Bool) :
    machine.computer.step (cfg (1 : Fin 2) flag (wordTape (0 : Fin 2) (b::bits))) =
      some (cfg (1 : Fin 2) flag (wordTape (0 : Fin 2) bits)) := by
  dsimp [FinTM2.step,TM2.step,machine,program,cfg,TM2.stepAux,wordTape,cond]
  try simp only [Function.update_self,List.head?_cons,List.head?_nil,List.tail_cons,List.tail_nil,
    Option.isSome_none,Option.isSome_some,Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> simp [wordTape]
theorem nil (flag : Bool) :
    machine.computer.step (cfg (1 : Fin 2) flag (wordTape (0 : Fin 2) [])) =
      some (haltList machine.computer [flag]) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step,TM2.step,machine,program,cfg,TM2.stepAux,wordTape,cond]
  try simp only [Function.update_self,List.head?_cons,List.head?_nil,List.tail_cons,List.tail_nil,
    Option.isSome_none,Option.isSome_some,Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> simp [wordTape]
theorem tail_run (flag : Bool) (bits : List Bool) :
    RunsExactly machine.computer.step (cfg (1 : Fin 2) flag (wordTape (0 : Fin 2) bits))
      (haltList machine.computer [flag]) (bits.length+1) := by
  induction bits with
  | nil => simpa using runsExactly_one (nil flag)
  | cons b bits ih =>
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (runsExactly_one (cons flag b bits)).trans ih
theorem run (flag : Bool) (bits : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (flag::bits))
      (haltList machine.computer [flag]) (bits.length+2) := by
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    (runsExactly_one (header flag bits)).trans (tail_run flag bits)
def computes : Computes Guard.outputEncoding encodingBoolBool Option.isSome where
  machine := machine
  time := Polynomial.X+2
  outputs p := by
    cases p with
    | none =>
        refine { steps := 2, evals_in_steps := ?_, steps_le_m := by simp [Guard.outputEncoding] }
        change RunsExactly machine.computer.step _ _ _
        simpa [Guard.outputEncoding,encodingBoolBool,encodeBool] using run false []
    | some bits =>
        refine {
          steps := bits.length+2
          evals_in_steps := ?_
          steps_le_m := by simp [Guard.outputEncoding] }
        change RunsExactly machine.computer.step _ _ _
        simpa [Guard.outputEncoding,encodingBoolBool,encodeBool] using run true bits
end Flag

namespace LiteralMap
variable (table : Bool → List Bool)
def pushWord (word : List Bool) (next : Stmt (Fin 3) (Fin 3) Unit) :
    Stmt (Fin 3) (Fin 3) Unit :=
  match word with
  | [] => next
  | bit::word => .push 1 (fun _ => bit) (pushWord word next)
def next : Stmt (Fin 3) (Fin 3) Unit :=
  .load (fun _ => (none,())) (.goto (fun _ => 0))
def program (l : Fin 3) : Stmt (Fin 3) (Fin 3) Unit :=
  if l=0 then .pop 0 (fun _ b => (b,()))
    (.branch (fun v => v.1.isSome)
      (.branch (fun v => v.1.getD false)
        (pushWord (table true) next) (pushWord (table false) next))
      (.load (fun _ => (none,())) (.goto (fun _ => 1))))
  else if l=1 then copyMoveStmt 1 2 1 2 else .halt
abbrev machine : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 2
  Label := Fin 3
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program table
def tapes (input reverse output : List Bool) : Fin 3 → List Bool := ![input,reverse,output]
def config (l : Fin 3) (input reverse output : List Bool) : (machine table).Config :=
  cfg l () (tapes input reverse output)
theorem update_input (input reverse output word : List Bool) :
    Function.update (tapes input reverse output) 0 word = tapes word reverse output := by
  funext k; fin_cases k <;> rfl
theorem update_reverse (input reverse output word : List Bool) :
    Function.update (tapes input reverse output) 1 word = tapes input word output := by
  funext k; fin_cases k <;> rfl
theorem push_eval (word : List Bool) (q : Stmt (Fin 3) (Fin 3) Unit)
    (v : Option Bool × Unit) (S : Fin 3 → List Bool) :
    TM2.stepAux (pushWord word q) v S =
      TM2.stepAux q v (Function.update S 1 (word.reverse++S 1)) := by
  induction word generalizing S with
  | nil => simp [pushWord,Function.update_eq_self]
  | cons bit word ih =>
      rw [pushWord,TM2.stepAux,ih]
      simp [List.reverse_cons,List.append_assoc,Function.update_idem]
theorem cons (bit : Bool) (bits reverse : List Bool) :
    (machine table).computer.step (config table 0 (bit::bits) reverse []) =
      some (config table 0 bits ((table bit).reverse++reverse) []) := by
  cases bit with
  | false =>
      change some (TM2.stepAux (pushWord (table false) next) (some false,())
        (Function.update (tapes (false::bits) reverse []) 0 bits)) = _
      rw [update_input,push_eval,update_reverse]
      rfl
  | true =>
      change some (TM2.stepAux (pushWord (table true) next) (some true,())
        (Function.update (tapes (true::bits) reverse []) 0 bits)) = _
      rw [update_input,push_eval,update_reverse]
      rfl
theorem nil (reverse : List Bool) :
    (machine table).computer.step (config table 0 [] reverse []) =
      some (config table 1 [] reverse []) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,wordTape,tapes,cond]
  try simp only [Function.update_self,List.head?_cons,List.head?_nil,List.tail_cons,List.tail_nil,
    Option.isSome_none,Option.isSome_some,Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem scan_run (bits reverse : List Bool) :
    RunsExactly (machine table).computer.step (config table 0 bits reverse [])
      (config table 1 [] ((bits.flatMap table).reverse++reverse) []) (bits.length+1) := by
  induction bits generalizing reverse with
  | nil => simpa using runsExactly_one (nil table reverse)
  | cons bit bits ih =>
      have h := (runsExactly_one (cons table bit bits reverse)).trans
        (ih ((table bit).reverse++reverse))
      simpa [List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
theorem move_cons (bit : Bool) (reverse output : List Bool) :
    (machine table).computer.step (config table 1 [] (bit::reverse) output) =
      some (config table 1 [] reverse (bit::output)) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,copyMoveStmt,TM2.stepAux,tapes,cond]
  try simp only [Function.update_self,List.head?_cons,List.head?_nil,List.tail_cons,List.tail_nil,
    Option.isSome_none,Option.isSome_some,Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem move_nil (output : List Bool) :
    (machine table).computer.step (config table 1 [] [] output) =
      some (config table 2 [] [] output) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,copyMoveStmt,TM2.stepAux,tapes,cond]
  try simp only [Function.update_self,List.head?_cons,List.head?_nil,List.tail_cons,List.tail_nil,
    Option.isSome_none,Option.isSome_some,Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem move_run (reverse output : List Bool) :
    RunsExactly (machine table).computer.step (config table 1 [] reverse output)
      (config table 2 [] [] (reverse.reverse++output)) (reverse.length+1) := by
  induction reverse generalizing output with
  | nil => simpa using runsExactly_one (move_nil table output)
  | cons bit reverse ih =>
      simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (runsExactly_one (move_cons table bit reverse output)).trans (ih (bit::output))
theorem halt (output : List Bool) :
    (machine table).computer.step (config table 2 [] [] output) =
      some (haltList (machine table).computer output) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,wordTape,tapes,cond]
  try simp only [Function.update_self,List.head?_cons,List.head?_nil,List.tail_cons,List.tail_nil,
    Option.isSome_none,Option.isSome_some,Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> simp [tapes,wordTape]
theorem initial (bits : List Bool) :
    config table 0 bits [] [] = initList (machine table).computer bits := by
  rw [Machine.init_eq]
  unfold config cfg
  congr 1; funext k; fin_cases k <;> simp [machine,tapes,wordTape]
def width : ℕ := (table false).length+(table true).length
theorem length_bound (bits : List Bool) : (bits.flatMap table).length ≤ width table*bits.length := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
      have hb : (table bit).length ≤ width table := by cases bit <;> simp [width]
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
def computes : Computes Frame.wordEncoding Frame.wordEncoding (List.flatMap table) where
  machine := machine table
  time := Polynomial.C (width table+1)*Polynomial.X+3
  outputs bits := by
    have hs := scan_run table bits []
    have hm := move_run table (bits.flatMap table).reverse []
    simp only [List.append_nil,List.reverse_reverse] at hs hm
    have h := (hs.trans hm).trans (runsExactly_one (halt table (bits.flatMap table)))
    rw [initial] at h
    refine {
      steps := bits.length+(bits.flatMap table).length+3
      evals_in_steps := ?_
      steps_le_m := ?_ }
    · change RunsExactly (machine table).computer.step _ _ _
      have ht : 1+((bits.flatMap table).reverse.length+1+(bits.length+1)) =
          bits.length+(bits.flatMap table).length+3 := by simp only [List.length_reverse]; omega
      rw [ht] at h
      exact h
    · have hb := length_bound table bits
      simp only [Frame.wordEncoding,Polynomial.eval_add,Polynomial.eval_mul,
        Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,id_eq]
      nlinarith
end LiteralMap
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Routing
