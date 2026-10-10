import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Padding
import Holant.Complexity.StackProtocol
import Holant.Complexity.GraphPreprocessing.Primitive

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Real unary-prefix/bit suffix guard. It reads one actual
counter token or witness bit at each row, preserves the ordered old prefix,
rejects every true suffix bit, and clears scratch before a clean result.
This component is not a supplied padding-correctness or whole-verifier oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Guard
open Turing Computability Holant.Complexity BinaryCompose StackProtocol

def decodePrefix : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false::bits => some (0,bits)
  | true::bits => (decodePrefix bits).map (fun p => (p.1+1,p.2))

theorem decodePrefix_unary (n : ℕ) (bits : List Bool) :
    decodePrefix (List.replicate n true ++ false::bits) = some (n,bits) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,decodePrefix] using (congrArg (Option.map (fun p : ℕ × List Bool => (p.1+1,p.2))) ih)

def inputEncoding : Encoding (List Bool × List Bool) Bool where
  encode p := List.replicate p.1.length true ++ false::(p.1++p.2)
  decode bits := (decodePrefix bits).bind (fun p =>
    if p.1 ≤ p.2.length then some (p.2.take p.1,p.2.drop p.1) else none)
  decode_encode p := by
    rw [decodePrefix_unary]
    simp [List.take_append,List.drop_append]

def outputEncoding : Encoding (Option (List Bool)) Bool where
  encode
    | none => [false]
    | some bits => true::bits
  decode
    | [] => none
    | false::_ => some none
    | true::bits => some (some bits)
  decode_encode p := by cases p <;> rfl

def check (p : List Bool × List Bool) : Option (List Bool) :=
  if p.2.all (!·) then some p.1 else none

/-- A separately encoded natural counter permits arbitrary short witnesses.
It is produced by Counter.oldWitnessComputes, never supplied to Source. -/
def rawEncoding : Encoding (ℕ × List Bool) Bool where
  encode p := List.replicate p.1 true ++ false::p.2
  decode := decodePrefix
  decode_encode p := decodePrefix_unary p.1 p.2

def program (l : Fin 10) : TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 10) (Option Bool × Unit) :=
  if l=0 then .pop 0 (fun v b => (b,v.2))
    (.branch (fun v => v.1.isSome)
      (.branch (fun v => v.1.getD false)
        (.push 1 (fun _ => true) (.load (fun _ => (none,())) (.goto (fun _ => 0))))
        (.load (fun _ => (none,())) (.goto (fun _ => 1))))
      (.load (fun _ => (none,())) (.goto (fun _ => 5))))
  else if l=1 then .pop 1 (fun v b => (b,v.2))
    (.branch (fun v => v.1.isSome)
      (.load (fun _ => (none,())) (.goto (fun _ => 2)))
      (.load (fun _ => (none,())) (.goto (fun _ => 3))))
  else if l=2 then .pop 0 (fun v b => (b,v.2))
    (.branch (fun v => v.1.isSome)
      (.push 2 (fun v => v.1.getD false)
        (.load (fun _ => (none,())) (.goto (fun _ => 1))))
      (.load (fun _ => (none,())) (.goto (fun _ => 5))))
  else if l=3 then .pop 0 (fun v b => (b,v.2))
    (.branch (fun v => v.1.isSome)
      (.branch (fun v => v.1.getD false)
        (.load (fun _ => (none,())) (.goto (fun _ => 5)))
        (.load (fun _ => (none,())) (.goto (fun _ => 3))))
      (.load (fun _ => (none,())) (.goto (fun _ => 4))))
  else if l=4 then copyMoveStmt 2 3 4 9
  else if l=5 then clearStmt 0 5 6
  else if l=6 then clearStmt 1 6 7
  else if l=7 then clearStmt 2 7 8
  else if l=8 then .push 3 (fun _ => false) (.load (fun _ => (none,())) .halt)
  else .push 3 (fun _ => true) (.load (fun _ => (none,())) .halt)

abbrev machine : BinaryCompose.Machine where
  K := Fin 4
  input := 0
  output := 3
  Label := Fin 10
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def tapes (input counter reverse output : List Bool) : Fin 4 → List Bool :=
  ![input,counter,reverse,output]
def config (l : Fin 10) (input counter reverse output : List Bool) : machine.Config :=
  cfg l () (tapes input counter reverse output)

theorem update_input (input counter reverse output word : List Bool) :
    Function.update (tapes input counter reverse output) 0 word = tapes word counter reverse output := by
  funext k; fin_cases k <;> rfl
theorem update_counter (input counter reverse output word : List Bool) :
    Function.update (tapes input counter reverse output) 1 word = tapes input word reverse output := by
  funext k; fin_cases k <;> rfl
theorem update_reverse (input counter reverse output word : List Bool) :
    Function.update (tapes input counter reverse output) 2 word = tapes input counter word output := by
  funext k; fin_cases k <;> rfl

theorem parse_cons (word counter reverse output : List Bool) :
    machine.computer.step (config 0 (true::word) counter reverse output) =
      some (config 0 word (true::counter) reverse output) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem parse_end (word counter reverse output : List Bool) :
    machine.computer.step (config 0 (false::word) counter reverse output) =
      some (config 1 word counter reverse output) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl

theorem parse_run (n : ℕ) (word counter reverse output : List Bool) :
    RunsExactly machine.computer.step
      (config 0 (List.replicate n true ++ false::word) counter reverse output)
      (config 1 word (List.replicate n true ++ counter) reverse output) (n+1) := by
  induction n generalizing counter with
  | zero => simpa using runsExactly_one (parse_end word counter reverse output)
  | succ n ih =>
      have he : List.replicate n true ++ true::counter =
          List.replicate (n+1) true ++ counter := by
        rw [List.replicate_succ']
        simp only [List.append_assoc,List.singleton_append]
      have h := (runsExactly_one (parse_cons
        (List.replicate n true ++ false::word) counter reverse output)).trans (ih (true::counter))
      simpa only [List.replicate_succ,List.cons_append,he,Nat.add_assoc] using h

theorem counter_cons (word counter reverse : List Bool) :
    machine.computer.step (config 1 word (true::counter) reverse []) =
      some (config 2 word counter reverse []) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem prefix_cons (bit : Bool) (word counter reverse : List Bool) :
    machine.computer.step (config 2 (bit::word) counter reverse []) =
      some (config 1 word counter (bit::reverse) []) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem prefix_eof (counter reverse : List Bool) :
    machine.computer.step (config 2 [] counter reverse []) =
      some (config 5 [] counter reverse []) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem counter_end (word reverse : List Bool) :
    machine.computer.step (config 1 word [] reverse []) = some (config 3 word [] reverse []) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl

theorem prefix_run (firstBits tail reverse : List Bool) :
    RunsExactly machine.computer.step
      (config 1 (firstBits++tail) (List.replicate firstBits.length true) reverse [])
      (config 3 tail [] (firstBits.reverse++reverse) []) (2*firstBits.length+1) := by
  induction firstBits generalizing reverse with
  | nil => simpa using runsExactly_one (counter_end tail reverse)
  | cons bit firstBits ih =>
      have h := ((runsExactly_one (counter_cons (bit::(firstBits++tail))
        (List.replicate firstBits.length true) reverse)).trans
        (runsExactly_one (prefix_cons bit (firstBits++tail)
          (List.replicate firstBits.length true) reverse))).trans (ih (bit::reverse))
      simpa [List.replicate_succ,List.reverse_cons,List.append_assoc,Nat.mul_add,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem short_prefix (bits : List Bool) (extra : ℕ) (reverse : List Bool) :
    RunsExactly machine.computer.step
      (config 1 bits (List.replicate (bits.length+extra+1) true) reverse [])
      (config 5 [] (List.replicate extra true) (bits.reverse++reverse) [])
      (2*bits.length+2) := by
  induction bits generalizing reverse with
  | nil =>
      simpa [List.replicate_succ] using
        (runsExactly_one (counter_cons [] (List.replicate extra true) reverse)).trans
          (runsExactly_one (prefix_eof (List.replicate extra true) reverse))
  | cons bit bits ih =>
      have h := ((runsExactly_one (counter_cons (bit::bits)
        (List.replicate (bits.length+extra+1) true) reverse)).trans
        (runsExactly_one (prefix_cons bit bits
          (List.replicate (bits.length+extra+1) true) reverse))).trans (ih (bit::reverse))
      simp only [List.length_cons]
      rw [show bits.length+1+extra+1 = (bits.length+extra+1)+1 by omega,List.replicate_succ]
      simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem suffix_false (tail reverse : List Bool) :
    machine.computer.step (config 3 (false::tail) [] reverse []) =
      some (config 3 tail [] reverse []) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem suffix_true (tail reverse : List Bool) :
    machine.computer.step (config 3 (true::tail) [] reverse []) =
      some (config 5 tail [] reverse []) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem suffix_end (reverse : List Bool) :
    machine.computer.step (config 3 [] [] reverse []) = some (config 4 [] [] reverse []) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl

theorem move_cons (bit : Bool) (reverse output : List Bool) :
    machine.computer.step (config 4 [] [] (bit::reverse) output) =
      some (config 4 [] [] reverse (bit::output)) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,copyMoveStmt,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem move_end (output : List Bool) :
    machine.computer.step (config 4 [] [] [] output) = some (config 9 [] [] [] output) := by
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,copyMoveStmt,TM2.stepAux,tapes]
  simp only [Bool.cond_true,Bool.cond_false]
  congr 2; funext k; fin_cases k <;> rfl
theorem move_run (reverse output : List Bool) :
    RunsExactly machine.computer.step (config 4 [] [] reverse output)
      (config 9 [] [] [] (reverse.reverse++output)) (reverse.length+1) := by
  induction reverse generalizing output with
  | nil => simpa using runsExactly_one (move_end output)
  | cons bit reverse ih =>
      simpa [List.reverse_cons,List.append_assoc] using
        (runsExactly_one (move_cons bit reverse output)).trans (ih (bit::output))

theorem emit_true (output : List Bool) :
    machine.computer.step (config 9 [] [] [] output) =
      some (haltList machine.computer (true::output)) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  congr 2; funext k; fin_cases k <;> rfl
theorem emit_false :
    machine.computer.step (config 8 [] [] [] []) =
      some (haltList machine.computer [false]) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step,TM2.step,machine,program,config,cfg,TM2.stepAux,tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem reject_run (input counter reverse : List Bool) :
    ∃ t ≤ input.length+counter.length+reverse.length+4,
      RunsExactly machine.computer.step (config 5 input counter reverse [])
        (haltList machine.computer [false]) t := by
  have h₀ := clear_exact machine.computer.step (0 : Fin 4) 5 6
    (executesAt_tm2 program 5 _ rfl) () (tapes input counter reverse [])
  have h₁ := clear_exact machine.computer.step (1 : Fin 4) 6 7
    (executesAt_tm2 program 6 _ rfl) () (tapes [] counter reverse [])
  have h₂ := clear_exact machine.computer.step (2 : Fin 4) 7 8
    (executesAt_tm2 program 7 _ rfl) () (tapes [] [] reverse [])
  simp only [update_input,update_counter,update_reverse] at h₀ h₁ h₂
  have h := ((h₀.trans h₁).trans h₂).trans (runsExactly_one emit_false)
  refine ⟨_,?_,h⟩
  simp [tapes]
  omega

theorem suffix_run (tail reverse : List Bool) :
    ∃ t ≤ tail.length+reverse.length+6,
      RunsExactly machine.computer.step (config 3 tail [] reverse [])
        (haltList machine.computer
          (outputEncoding.encode (if tail.all (!·) then some reverse.reverse else none))) t := by
  induction tail with
  | nil =>
      have hm := move_run reverse []
      simp only [List.append_nil] at hm
      have h := ((runsExactly_one (suffix_end reverse)).trans hm).trans
        (runsExactly_one (emit_true reverse.reverse))
      refine ⟨reverse.length+3,by simp only [List.length_nil]; omega,?_⟩
      simpa [outputEncoding,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  | cons bit tail ih =>
      cases bit with
      | false =>
          obtain ⟨t,ht,hr⟩ := ih
          refine ⟨t+1,by simp only [List.length_cons]; omega,?_⟩
          simpa using (runsExactly_one (suffix_false tail reverse)).trans hr
      | true =>
          obtain ⟨t,ht,hr⟩ := reject_run tail [] reverse
          refine ⟨t+1,by simp only [List.length_cons,List.length_nil] at *; omega,?_⟩
          simpa [outputEncoding] using (runsExactly_one (suffix_true tail reverse)).trans hr

theorem initial_eq (firstBits tail : List Bool) :
    config 0 (inputEncoding.encode (firstBits,tail)) [] [] [] =
      initList machine.computer (inputEncoding.encode (firstBits,tail)) := by
  rw [Machine.init_eq]
  unfold config cfg
  congr 1; funext k; fin_cases k <;> rfl

/-- Real clean computation for every old prefix and every suffix, including
noncanonical suffixes. The counter is consumed; no extra bits are ignored. -/
def computes : Computes inputEncoding outputEncoding check where
  machine := machine
  time := 6*Polynomial.X+10
  outputs p := Classical.choice (by
    obtain ⟨t,ht,hs⟩ := suffix_run p.2 p.1.reverse
    have hp := prefix_run p.1 p.2 []
    have hu := parse_run p.1.length (p.1++p.2) [] [] []
    simp only [List.append_nil] at hp hu
    have hr := (hu.trans hp).trans hs
    change RunsExactly machine.computer.step
      (config 0 (inputEncoding.encode p) [] [] []) _ _ at hr
    rw [initial_eq] at hr
    refine ⟨{
      steps := t+((2*p.1.length+1)+(p.1.length+1))
      evals_in_steps := ?_
      steps_le_m := ?_ }⟩
    · change RunsExactly machine.computer.step _ _ _
      simpa only [check,List.reverse_reverse] using hr
    · simp only [List.length_reverse] at ht
      simp [inputEncoding]
      omega)

/-- Same literal program, now proved on ALL counter/witness inputs. The EOF
case physically clears every remaining counter token and reverse prefix. -/
def rawComputes : Computes rawEncoding outputEncoding
    (fun p => Padding.extract p.1 p.2) where
  machine := machine
  time := 6*Polynomial.X+10
  outputs p := Classical.choice (by
    by_cases hn : p.1 ≤ p.2.length
    · have hl : (p.2.take p.1).length = p.1 := by
        simp only [List.length_take,Nat.min_eq_left hn]
      have hw : inputEncoding.encode (p.2.take p.1,p.2.drop p.1) =
          rawEncoding.encode p := by
        simp only [inputEncoding,rawEncoding,hl,List.take_append_drop]
      have hv : check (p.2.take p.1,p.2.drop p.1) = Padding.extract p.1 p.2 := by
        simp only [check,Padding.extract,if_pos hn]
      have h := computes.outputs (p.2.take p.1,p.2.drop p.1)
      change TM2OutputsInTime machine.computer _ _ ((6*Polynomial.X+10).eval _) at h
      exact ⟨by simpa only [hw,hv] using h⟩
    · let extra := p.1-p.2.length-1
      have he : p.2.length+extra+1 = p.1 := by dsimp [extra]; omega
      have hp := short_prefix p.2 extra []
      simp only [he,List.append_nil] at hp
      obtain ⟨t,ht,hr⟩ := reject_run [] (List.replicate extra true) p.2.reverse
      have hu := parse_run p.1 p.2 [] [] []
      simp only [List.append_nil] at hu
      have h := (hu.trans hp).trans hr
      have hi : config 0 (rawEncoding.encode p) [] [] [] =
          initList machine.computer (rawEncoding.encode p) := by
        rw [Machine.init_eq]
        unfold config cfg
        congr 1; funext k; fin_cases k <;> rfl
      change RunsExactly machine.computer.step
        (config 0 (rawEncoding.encode p) [] [] []) _ _ at h
      rw [hi] at h
      refine ⟨{
        steps := t+((2*p.2.length+2)+(p.1+1))
        evals_in_steps := ?_
        steps_le_m := ?_ }⟩
      · change RunsExactly machine.computer.step _ _ _
        simpa [Padding.extract,hn,outputEncoding] using h
      · simp only [List.length_nil,List.length_replicate,List.length_reverse] at ht
        simp [rawEncoding]
        omega)

theorem program_budget (l : Fin 10) : TM2Cost.budget (machine.program l) ≤ 10 := by
  fin_cases l <;> decide

theorem primitive_cost (p : List Bool × List Bool) :
    ∃ t ≤ computes.time.eval (inputEncoding.encode p).length,
      (GraphPreprocessing.Primitive.run machine.program t
        (some (initList machine.computer (inputEncoding.encode p)))).2 =
          some (haltList machine.computer (outputEncoding.encode (check p))) ∧
      (GraphPreprocessing.Primitive.run machine.program t
        (some (initList machine.computer (inputEncoding.encode p)))).1 ≤
          10*computes.time.eval (inputEncoding.encode p).length := by
  let h := computes.outputs p
  have hp := GraphPreprocessing.Primitive.execution_cost machine.program 10 program_budget
    h.steps _ _ h.evals_in_steps
  exact ⟨h.steps,h.steps_le_m,hp.1,hp.2.trans (Nat.mul_le_mul_left 10 h.steps_le_m)⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Guard
