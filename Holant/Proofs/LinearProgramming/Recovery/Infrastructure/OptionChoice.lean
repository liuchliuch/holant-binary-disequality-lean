import Holant.Complexity.GraphPreprocessing.Call
import Holant.Complexity.FixedFieldMachines.Wiring
import Holant.Complexity.FixedFieldMachines.Constant
import Holant.OneHot.StackProgram.GraphLabelEncoding

set_option autoImplicit false

/-! Actual optional-result selection with a fixed fallback word. The first
present result is retained, the unselected encoded result is physically erased,
and a finite literal program supplies the dense-component zero code. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure.OptionChoice
open Holant.Complexity Holant.Complexity.GraphPreprocessing
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def program (fallback : List Bool) (l : Fin 16) : Stmt (Fin 3) (Fin 16) Unit := match l.val with
  | 0 => Frame.scanStmt 0 2 0 1 12
  | 1 => copyMoveStmt 2 1 1 2
  | 2 => pop 1 (fun st bit => (bit,st.2))
    (branch (fun st => st.1==some true)
      (load (fun _ => (none,())) (goto (fun _ => 3)))
      (branch (fun st => st.1==some false)
        (load (fun _ => (none,())) (goto (fun _ => 10)))
        (load (fun _ => (none,())) (goto (fun _ => 12)))))
  | 3 => clearStmt 0 3 4
  | 4 => .halt
  | 5 => pop 0 (fun st bit => (bit,st.2))
    (branch (fun st => st.1==some true)
      (load (fun _ => (none,())) (goto (fun _ => 6)))
      (branch (fun st => st.1==some false)
        (load (fun _ => (none,())) (goto (fun _ => 8)))
        (load (fun _ => (none,())) (goto (fun _ => 12)))))
  | 6 => copyMoveStmt 0 2 6 7
  | 7 => copyMoveStmt 2 1 7 4
  | 8 => pop 0 (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun _ => (none,())) (goto (fun _ => 12)))
      (load (fun _ => (none,())) (goto (fun _ => 9))))
  | 9 => Constant.pushWord 1 fallback .halt
  | 10 => pop 1 (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun _ => (none,())) (goto (fun _ => 12)))
      (load (fun _ => (none,())) (goto (fun _ => 5))))
  | 12 => clearStmt 0 12 13
  | 13 => clearStmt 1 13 14
  | 14 => clearStmt 2 14 15
  | _ => load (fun _ => (some false,())) .halt
abbrev machine (fallback : List Bool) : Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 16
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program fallback
abbrev tapes := Wiring.tapes
def config (l : Fin 16) (input output temporary : List Bool) := cfg l () (tapes input output temporary)
@[simp] theorem update_input (input output temporary word : List Bool) :
    Function.update (tapes input output temporary) (0 : Fin 3) word=tapes word output temporary := by
  funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
@[simp] theorem update_output (input output temporary word : List Bool) :
    Function.update (tapes input output temporary) (1 : Fin 3) word=tapes input word temporary := by
  funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
@[simp] theorem update_temporary (input output temporary word : List Bool) :
    Function.update (tapes input output temporary) (2 : Fin 3) word=tapes input output word := by
  funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
theorem initial (fallback input : List Bool) : config 0 input [] []=initList (machine fallback).computer input := by
  rw [Machine.init_eq]; unfold config cfg; congr 1; funext k; fin_cases k <;> rfl

theorem parse (fallback first second : List Bool) :
    Holant.Complexity.StackProtocol.RunsExactly (machine fallback).computer.step (config 0 (Holant.Algebraic.frame first++second) [] [])
      (config 2 second first []) (2*(first.length+1)) := by
  have h := Frame.extract_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    (machine fallback).computer.step (0 : Fin 16) 1 2 12 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) first second []
  rw [←Wiring.tapes012,←Wiring.tapes012] at h
  simpa [config] using h

theorem read_first (fallback : List Bool) (bit : Bool) (input tail : List Bool) :
    (machine fallback).computer.step (config 2 input (bit::tail) [])=
      some (config (if bit then 3 else 10) input tail []) := by
  cases bit <;> change some (⟨some _,(none,()),Function.update (tapes input (_::tail) []) 1 tail⟩ : (machine fallback).Config)=_
  all_goals rw [update_output]; rfl

theorem first_none (fallback input : List Bool) :
    (machine fallback).computer.step (config 10 input [] [])=some (config 5 input [] []) := by
  change some (⟨some _,(none,()),Function.update (tapes input [] []) 1 []⟩ : (machine fallback).Config)=_
  rw [update_output]; rfl

theorem read_second (fallback : List Bool) (bit : Bool) (tail : List Bool) :
    (machine fallback).computer.step (config 5 (bit::tail) [] [])=
      some (config (if bit then 6 else 8) tail [] []) := by
  cases bit <;> change some (⟨some _,(none,()),Function.update (tapes (_::tail) [] []) 0 tail⟩ : (machine fallback).Config)=_
  all_goals rw [update_input]; rfl

theorem halt_output (fallback output : List Bool) : (machine fallback).computer.step (config 4 [] output [])=
    some (haltList (machine fallback).computer output) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),tapes [] output []⟩ : (machine fallback).Config)=_
  congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,wordTape,Function.update]

theorem clear_second (fallback output second : List Bool) :
    Holant.Complexity.StackProtocol.RunsExactly (machine fallback).computer.step (config 3 second output [])
      (haltList (machine fallback).computer output) (second.length+2) := by
  have h := clear_exact (machine fallback).computer.step (0 : Fin 3) (3 : Fin 16) 4
    (executesAt_tm2 _ _ _ rfl) () (tapes second output [])
  rw [update_input] at h
  have run := h.trans (runsExactly_one (halt_output fallback output))
  convert run using 1 <;> first | rfl | (simp [tapes,Wiring.tapes]; omega)

theorem transfer_second (fallback input : List Bool) :
    Holant.Complexity.StackProtocol.RunsExactly (machine fallback).computer.step (config 6 input [] []) (config 4 [] input []) (2*(input.length+1)) := by
  have h := transfer_exact_frame (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    (machine fallback).computer.step (6 : Fin 16) 7 4 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) input []
  rw [←Wiring.tapes012,←Wiring.tapes012] at h
  simpa [config] using h

theorem fallback_exact (fallback : List Bool) :
    Holant.Complexity.StackProtocol.RunsExactly (machine fallback).computer.step (config 8 [] [] [])
      (haltList (machine fallback).computer fallback) 2 := by
  have first : (machine fallback).computer.step (config 8 [] [] [])=some (config 9 [] [] []) := by
    change some (⟨some _,(none,()),Function.update (tapes [] [] []) 0 []⟩ : (machine fallback).Config)=_
    rw [update_input]; rfl
  have last : (machine fallback).computer.step (config 9 [] [] [])=some (haltList (machine fallback).computer fallback) := by
    rw [Machine.halt_eq]
    change some (TM2.stepAux (Constant.pushWord (1 : Fin 3) fallback .halt) (none,()) (tapes [] [] []))=_
    rw [Constant.pushWord_eval]
    simp only [TM2.stepAux,update_output,List.append_nil]
    congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,wordTape,Function.update]
  exact (runsExactly_one first).trans (runsExactly_one last)
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure.OptionChoice
