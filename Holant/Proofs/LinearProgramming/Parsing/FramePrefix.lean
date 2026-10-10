import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Complexity.FixedFieldMachines.FrameEmit
import Holant.Complexity.GraphPreprocessing.Call
import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.Complexity.GraphPreprocessing.Primitive
import Holant.Complexity.FixedFieldMachines.PrimitiveCost
import Holant.OneHot.StackProgram.GraphLabelEncoding

/-! Clean total physical unframe operation
on arbitrary words. Existing FrameMachine has separate returning extraction
and rejection contracts, but its clean output does not tag that distinction.
Here only its already proved scan/restore/EOF protocols and existing transfer,
FrameEmit and clear protocols are installed in one finite program.

Four Boolean stacks and ten labels; the only state is Option Bool × Unit.
Success physically emits true :: frame headWord ++ suffix. Failure clears the
partial scratch and physically emits [false]. No unframe, length, decoded
identifier, rational operation or whole-word function occurs in the program.
-/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.FramePrefix
open Holant Turing Computability Holant.Algebraic
open Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing StackProtocol
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev pairEncoding := FixedFieldMachines.pairEncoding Frame.wordEncoding Frame.wordEncoding
abbrev resultEncoding := optionEncoding pairEncoding

abbrev machine : Machine where
  K := Fin 4
  input := 0
  output := 3
  Label := Fin 10
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program label := if label=0 then Frame.scanStmt 0 2 0 1 7
    else if label=1 then copyMoveStmt 2 1 1 2
    else if label=2 then copyMoveStmt 0 2 2 3
    else if label=3 then copyMoveStmt 2 3 3 4
    else if label=4 then copyMoveStmt 1 2 4 5
    else if label=5 then FrameEmit.delimiterStmt 3 6
    else if label=6 then FrameEmit.emitStmt 2 3 6 8
    else if label=7 then clearStmt 2 7 9
    else if label=8 then .push 3 (fun _ => true) .halt
    else .push 3 (fun _ => false) .halt

def tapes (input headWord scratch output : List Bool) : Fin 4 → List Bool :=
  ![input,headWord,scratch,output]

private theorem scan_tapes (input headWord scratch : List Bool) :
    tapes3 (fun _ : Fin 4 => []) 0 1 2 input headWord scratch=
      tapes input headWord scratch [] := by
  funext k
  fin_cases k <;> simp [tapes3,tapes,Function.update]

private theorem suffix_tapes (input headWord scratch output : List Bool) :
    tapes3 (tapes [] headWord [] []) (0 : Fin 4) 3 2 input output scratch=
      tapes input headWord scratch output := by
  funext k
  fin_cases k <;> simp [tapes3,tapes,Function.update]

private theorem emit_tapes (headWord scratch output : List Bool) :
    tapes3 (fun _ : Fin 4 => []) 1 3 2 headWord output scratch=
      tapes [] headWord scratch output := by
  funext k
  fin_cases k <;> simp [tapes3,tapes,Function.update]

private theorem tapes_scratch (input headWord scratch output : List Bool) :
    tapes input headWord scratch output (2 : Fin 4)=scratch := rfl

private theorem update_scratch (input headWord scratch output word : List Bool) :
    Function.update (tapes input headWord scratch output) (2 : Fin 4) word=
      tapes input headWord word output := by
  funext k
  fin_cases k <;> simp [tapes,Function.update]

private theorem update_output (input headWord scratch output word : List Bool) :
    Function.update (tapes input headWord scratch output) (3 : Fin 4) word=
      tapes input headWord scratch word := by
  funext k
  fin_cases k <;> simp [tapes,Function.update]

private theorem input_tapes (input : List Bool) :
    tapes input [] [] []=wordTape (0 : Fin 4) input := by
  funext k
  fin_cases k <;> simp [tapes,wordTape,Function.update]

private theorem output_tapes (output : List Bool) :
    tapes [] [] [] output=wordTape (3 : Fin 4) output := by
  funext k
  fin_cases k <;> simp [tapes,wordTape,Function.update]

private theorem scan_executes : ExecutesAt machine.computer.step (0 : Fin 10)
    (Frame.scanStmt 0 2 0 1 7) := by intro state tapes; rfl
private theorem restore_executes : ExecutesAt machine.computer.step (1 : Fin 10)
    (copyMoveStmt 2 1 1 2) := by intro state tapes; rfl
private theorem suffix_move_executes : ExecutesAt machine.computer.step (2 : Fin 10)
    (copyMoveStmt 0 2 2 3) := by intro state tapes; rfl
private theorem suffix_restore_executes : ExecutesAt machine.computer.step (3 : Fin 10)
    (copyMoveStmt 2 3 3 4) := by intro state tapes; rfl
private theorem frame_move_executes : ExecutesAt machine.computer.step (4 : Fin 10)
    (copyMoveStmt 1 2 4 5) := by intro state tapes; rfl
private theorem delimiter_executes : ExecutesAt machine.computer.step (5 : Fin 10)
    (FrameEmit.delimiterStmt 3 6) := by intro state tapes; rfl
private theorem emit_executes : ExecutesAt machine.computer.step (6 : Fin 10)
    (FrameEmit.emitStmt 2 3 6 8) := by intro state tapes; rfl
private theorem clear_executes : ExecutesAt machine.computer.step (7 : Fin 10)
    (clearStmt 2 7 9) := by intro state tapes; rfl

theorem program_budget (label : Fin 10) : TM2Cost.budget (machine.program label)≤8 := by
  fin_cases label <;> decide

private theorem initial (input : List Bool) :
    cfg (0 : Fin 10) () (tapes input [] [] [])=initList machine.computer input := by
  rw [Machine.init_eq]
  change (⟨some (0 : Fin 10),(none,()),tapes input [] [] []⟩ : machine.Config)=
    ⟨some 0,(none,()),wordTape (0 : Fin 4) input⟩
  rw [input_tapes]

private theorem finish_success (output : List Bool) :
    machine.computer.step (cfg (8 : Fin 10) () (tapes [] [] [] output))=
      some (haltList machine.computer (true::output)) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),
    Function.update (tapes [] [] [] output) (3 : Fin 4) (true::output)⟩ : machine.Config)=
    some ⟨none,(none,()),wordTape (3 : Fin 4) (true::output)⟩
  rw [update_output,output_tapes]

private theorem finish_rejection :
    machine.computer.step (cfg (9 : Fin 10) () (tapes [] [] [] []))=
      some (haltList machine.computer [false]) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),
    Function.update (tapes [] [] [] []) (3 : Fin 4) [false]⟩ : machine.Config)=
    some ⟨none,(none,()),wordTape (3 : Fin 4) [false]⟩
  rw [update_output,output_tapes]

private theorem extract (headWord suffix : List Bool) :
    RunsExactly machine.computer.step
      (cfg (0 : Fin 10) () (tapes (frame headWord++suffix) [] [] []))
      (cfg (2 : Fin 10) () (tapes suffix headWord [] [])) (2*(headWord.length+1)) := by
  have h := Frame.extract_exact (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step 0 1 2 7 scan_executes restore_executes () (fun _ => []) headWord suffix []
  simpa only [List.append_nil,scan_tapes] using h

private theorem move_suffix (headWord suffix : List Bool) :
    RunsExactly machine.computer.step
      (cfg (2 : Fin 10) () (tapes suffix headWord [] []))
      (cfg (4 : Fin 10) () (tapes [] headWord [] suffix)) (2*(suffix.length+1)) := by
  have h := transfer_exact_frame (0 : Fin 4) 3 2 (by decide) (by decide) (by decide)
    machine.computer.step 2 3 4 suffix_move_executes suffix_restore_executes ()
    (tapes [] headWord [] []) suffix []
  simpa only [List.append_nil,suffix_tapes] using h

private theorem frame_prefix (headWord suffix : List Bool) :
    RunsExactly machine.computer.step
      (cfg (4 : Fin 10) () (tapes [] headWord [] suffix))
      (cfg (8 : Fin 10) () (tapes [] [] [] (frame headWord++suffix))) (2*headWord.length+3) := by
  have h := FrameEmit.prepend_exact (1 : Fin 4) 3 2 (by decide) (by decide) (by decide)
    machine.computer.step 4 5 6 8 frame_move_executes delimiter_executes emit_executes ()
    (fun _ => []) headWord suffix
  simpa only [emit_tapes] using h

/-- Actual accepting run, with headWord and unconsumed suffix in original order.
This is the canonical existing pair/Option codec, not a different wire format. -/
theorem accepts_exact (headWord suffix : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (frame headWord++suffix))
      (haltList machine.computer (resultEncoding.encode (some (headWord,suffix))))
      (4*headWord.length+2*suffix.length+8) := by
  have run := (((extract headWord suffix).trans (move_suffix headWord suffix)).trans
    (frame_prefix headWord suffix)).trans (runsExactly_one (finish_success (frame headWord++suffix)))
  rw [initial] at run
  have ht : 1+((2*headWord.length+3)+
      (2*(suffix.length+1)+2*(headWord.length+1)))=
      4*headWord.length+2*suffix.length+8 := by omega
  have he : resultEncoding.encode (some (headWord,suffix))=
      true::(frame headWord++suffix) := rfl
  rw [he]
  simpa only [ht] using run

private theorem clear_partial (scratch : List Bool) :
    RunsExactly machine.computer.step
      (cfg (7 : Fin 10) () (tapes [] [] scratch []))
      (cfg (9 : Fin 10) () (tapes [] [] [] [])) (scratch.length+1) := by
  have h := clear_exact machine.computer.step (2 : Fin 4) 7 9 clear_executes ()
    (tapes [] [] scratch [])
  simpa only [tapes_scratch,update_scratch] using h

/-- Malformed EOF really reaches rejection, clears its partially extracted
bits and emits the ordinary Option-none word. No successful event is assumed. -/
theorem rejects (input : List Bool) (hbad : unframe input=none) :
    ∃ steps, steps≤2*input.length+3 ∧
      RunsExactly machine.computer.step (initList machine.computer input)
        (haltList machine.computer (resultEncoding.encode none)) steps := by
  obtain ⟨produced,time,ht,hp,hr⟩ := Frame.rejects (0 : Fin 4) 1 2 (by decide) (by decide)
    machine.computer.step 0 1 7 scan_executes () (fun _ => []) input [] [] hbad
  have parsed : RunsExactly machine.computer.step
      (cfg (0 : Fin 10) () (tapes input [] [] []))
      (cfg (7 : Fin 10) () (tapes [] [] produced.reverse [])) time := by
    simpa only [List.append_nil,scan_tapes] using hr
  have run := (parsed.trans (clear_partial produced.reverse)).trans (runsExactly_one finish_rejection)
  rw [initial] at run
  refine ⟨time+produced.length+2,by omega,?_⟩
  have ht' : 1+(produced.reverse.length+1+time)=time+produced.length+2 := by
    simp only [List.length_reverse]
    omega
  simpa only [ht',resultEncoding,optionEncoding] using run

/-- Total receipt on EVERY finite raw word. The host unframe is solely the
specification; all physical work is the ten-label program above. -/
def outputs (input : List Bool) : TM2OutputsInTime machine.computer input
    (some (resultEncoding.encode (unframe input))) (2*input.length+6) := by
  cases hu : unframe input with
  | none =>
    let steps := Classical.choose (rejects input hu)
    have hs : steps≤2*input.length+3 := (Classical.choose_spec (rejects input hu)).1
    have hr : RunsExactly machine.computer.step (initList machine.computer input)
        (haltList machine.computer (resultEncoding.encode none)) steps :=
      (Classical.choose_spec (rejects input hu)).2
    refine ⟨⟨steps,?_⟩,?_⟩
    · simp only [hu,Option.map_some]
      change @RunsExactly (Fin 4) (Fin 10) Unit machine.computer.step
        (initList machine.computer input) (haltList machine.computer (resultEncoding.encode none)) steps
      exact hr
    · change steps ≤ 2*input.length+6
      omega
  | some p =>
    have hi : input=frame p.1++p.2 := (Frame.unframe_some_iff input p.1 p.2).mp hu
    have hl : input.length=2*p.1.length+1+p.2.length := by
      rw [hi,List.length_append,frame_length]
    have hr := accepts_exact p.1 p.2
    rw [←hi] at hr
    refine ⟨⟨4*p.1.length+2*p.2.length+8,?_⟩,?_⟩
    · simp only [hu,Option.map_some]
      change @RunsExactly (Fin 4) (Fin 10) Unit machine.computer.step
        (initList machine.computer input)
        (haltList machine.computer (resultEncoding.encode (some p)))
        (4*p.1.length+2*p.2.length+8)
      exact hr
    · change 4*p.1.length+2*p.2.length+8 ≤ 2*input.length+6
      omega

def timePolynomial : Polynomial ℕ := 2*Polynomial.X+6

/-- Installed finite Boolean machine, including malformed input rejection. -/
def computes : Computes Frame.wordEncoding resultEncoding unframe where
  machine := machine
  time := timePolynomial
  outputs input := by
    simpa only [Frame.wordEncoding,id_eq,timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X] using outputs input

theorem primitive_bound (input : List Bool) :
    (Primitive.run machine.program (outputs input).steps
      (some (initList machine.computer input))).2=
        some (haltList machine.computer (resultEncoding.encode (unframe input))) ∧
    (Primitive.run machine.program (outputs input).steps
      (some (initList machine.computer input))).1≤8*(2*input.length+6) := by
  have h := Primitive.execution_cost machine.program 8 program_budget (outputs input).steps
    (initList machine.computer input)
    (haltList machine.computer (resultEncoding.encode (unframe input))) (outputs input).evals_in_steps
  exact ⟨h.1,h.2.trans (Nat.mul_le_mul_left 8 (outputs input).steps_le_m)⟩

theorem prefix_storage (input : List Bool) (j : ℕ) (hj : j≤(outputs input).steps)
    (c : machine.Config)
    (hc : (fun p => p.bind machine.computer.step)^[j]
      (some (initList machine.computer input))=some c) :
    stackSize c.stk ≤ input.length+(2*input.length+6)*machine.primitiveBudget := by
  have h := machine.run_size_le (initList machine.computer input) c j hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right machine.primitiveBudget (hj.trans (outputs input).steps_le_m)) input.length)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.FramePrefix
