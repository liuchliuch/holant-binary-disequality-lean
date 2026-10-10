import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Complexity.GraphPreprocessing.Call
import Holant.Complexity.FixedFieldMachines.FrameEmit
import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.OneHot.StackProgram.GraphLabelEncoding

/-! Actual framed-context distribution into an optional payload. A missing
payload discards the context; a present payload receives its literal frame.
The program reads, moves and emits individual Boolean cells only. -/
open Holant.Complexity
open Holant.Complexity.GraphPreprocessing

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Infrastructure.OptionContext
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def program (label : Fin 12) : Stmt (Fin 4) (Fin 12) Unit := match label.val with
  | 0 => Frame.scanStmt 0 2 0 1 11
  | 1 => copyMoveStmt 2 1 1 2
  | 2 => pop 0 (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun _ => (none,())) (goto (fun _ => 5)))
        (load (fun _ => (none,())) (goto (fun _ => 3))))
      (load (fun _ => (none,())) (goto (fun _ => 11))))
  | 3 => clearStmt 1 3 4
  | 4 => push 3 (fun _ => false) .halt
  | 5 => copyMoveStmt 0 2 5 6
  | 6 => copyMoveStmt 2 3 6 7
  | 7 => copyMoveStmt 1 2 7 8
  | 8 => FrameEmit.delimiterStmt 3 9
  | 9 => FrameEmit.emitStmt 2 3 9 10
  | 10 => push 3 (fun _ => true) .halt
  | 11 => load (fun _ => (some false,())) .halt
  | _ => .halt
abbrev machine : Machine where
  K := Fin 4
  input := 0
  output := 3
  Label := Fin 12
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def tapes (input context temporary output : List Bool) : Fin 4 → List Bool := ![input,context,temporary,output]
def config (l : Fin 12) (input context temporary output : List Bool) := cfg l () (tapes input context temporary output)

@[simp] theorem update_input (input context temporary output word : List Bool) :
    Function.update (tapes input context temporary output) 0 word=tapes word context temporary output := by
  funext k; fin_cases k <;> simp [tapes,Function.update]

@[simp] theorem update_context (input context temporary output word : List Bool) :
    Function.update (tapes input context temporary output) 1 word=tapes input word temporary output := by
  funext k; fin_cases k <;> simp [tapes,Function.update]

@[simp] theorem update_temporary (input context temporary output word : List Bool) :
    Function.update (tapes input context temporary output) 2 word=tapes input context word output := by
  funext k; fin_cases k <;> simp [tapes,Function.update]

@[simp] theorem update_output (input context temporary output word : List Bool) :
    Function.update (tapes input context temporary output) 3 word=tapes input context temporary word := by
  funext k; fin_cases k <;> simp [tapes,Function.update]

theorem tapes_empty : tapes [] [] [] [] = fun _ => [] := by funext k; fin_cases k <;> rfl

theorem initial (input : List Bool) : initList machine.computer input = config 0 input [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input [] [] [] [] input
  rw [tapes_empty] at h
  change wordTape (0 : Fin 4) input = _ at h
  change (⟨some 0,(none,()),wordTape (0 : Fin 4) input⟩ : machine.Config) = _
  rw [h]; rfl

theorem tag_halt (output : List Bool) (bit : Bool) :
    TM2.step program (config (if bit then 10 else 4) [] [] [] output) =
      some (haltList machine.computer (bit::output)) := by
  rw [Machine.halt_eq]
  have hw := update_output [] [] [] [] (bit::output)
  rw [tapes_empty] at hw
  change wordTape (3 : Fin 4) (bit::output) = _ at hw
  cases bit <;>
    change some (⟨none,(none,()),Function.update (tapes [] [] [] output) 3 (_::output)⟩ : machine.Config) = _
  all_goals rw [update_output,←hw]

theorem parse_context (context suffix : List Bool) :
    RunsExactly (TM2.step program) (config 0 (Holant.Algebraic.frame context++suffix) [] [] [])
      (config 2 suffix context [] []) (2*(context.length+1)) := by
  have h := Frame.extract_exact (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
    (TM2.step program) 0 1 2 11 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (tapes [] [] [] []) context suffix []
  simpa only [config,tapes3,update_input,update_context,update_temporary,List.append_nil] using h

theorem read_tag (context payload : List Bool) (bit : Bool) :
    TM2.step program (config 2 (bit::payload) context [] []) = some (config (if bit then 5 else 3) payload context [] []) := by
  cases bit <;>
    change some (cfg (_ : Fin 12) () (Function.update (tapes (_::payload) context [] []) 0 payload)) = _
  all_goals rw [update_input]; rfl

theorem none_exact (context : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (Holant.Algebraic.frame context++[false]))
      (haltList machine.computer [false]) (3*context.length+5) := by
  have clear := clear_exact (TM2.step program) (1 : Fin 4) 3 4 (executesAt_tm2 _ _ _ rfl) () (tapes [] context [] [])
  rw [update_context] at clear
  have all := (((parse_context context [false]).trans (runsExactly_one (read_tag context [] false))).trans clear).trans
    (runsExactly_one (tag_halt [] false))
  have ht : 3*context.length+5=1+((context.length+1)+(1+2*(context.length+1))) := by omega
  rw [initial,ht]
  exact all

theorem move_payload (context payload : List Bool) :
    RunsExactly (TM2.step program) (config 5 payload context [] []) (config 7 [] context [] payload) (2*(payload.length+1)) := by
  have h := transfer_exact_frame (0 : Fin 4) 3 2 (by decide) (by decide) (by decide)
    (TM2.step program) 5 6 7 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (tapes [] context [] []) payload []
  simpa only [config,tapes3,update_input,update_output,update_temporary,List.append_nil] using h

theorem frame_context (context payload : List Bool) :
    RunsExactly (TM2.step program) (config 7 [] context [] payload)
      (config 10 [] [] [] (Holant.Algebraic.frame context++payload)) (2*context.length+3) := by
  have h := FrameEmit.prepend_exact (1 : Fin 4) 3 2 (by decide) (by decide) (by decide)
    (TM2.step program) 7 8 9 10 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (tapes [] [] [] []) context payload
  simpa only [config,tapes3,update_context,update_output,update_temporary] using h

theorem some_exact (context payload : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (Holant.Algebraic.frame context++true::payload))
      (haltList machine.computer (true::(Holant.Algebraic.frame context++payload)))
      (4*context.length+2*payload.length+9) := by
  have all := ((((parse_context context (true::payload)).trans (runsExactly_one (read_tag context payload true))).trans
    (move_payload context payload)).trans (frame_context context payload)).trans
    (runsExactly_one (tag_halt (Holant.Algebraic.frame context++payload) true))
  have ht : 4*context.length+2*payload.length+9 =
      1+((2*context.length+3)+(2*(payload.length+1)+(1+2*(context.length+1)))) := by omega
  rw [initial,ht]
  exact all

end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Infrastructure.OptionContext
