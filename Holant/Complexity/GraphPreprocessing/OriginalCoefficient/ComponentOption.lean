import Holant.Complexity.GraphPreprocessing.ComponentSelection.ClassifyList
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-! Physical classification dispatch into optional branch inputs. Tree mode
retains the original query; cycle mode frames it before the real unary cut ID.
Absent branches are cleared and emit none, so their providers never execute. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentOption
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines ComponentSelection
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def program (cycle : Bool) (l : Fin 16) : Stmt (Fin 3) (Fin 16) Unit := match l.val with
  | 0 => Frame.scanStmt 0 2 0 1 10
  | 1 => copyMoveStmt 2 1 1 2
  | 2 => pop 1 (fun st bit => (bit,st.2))
    (branch (fun st => st.1==some false)
      (load (fun _ => (none,())) (goto (fun _ => if cycle then 10 else 4)))
      (branch (fun st => st.1==some true)
        (load (fun _ => (none,())) (goto (fun _ => 3)))
        (load (fun _ => (none,())) (goto (fun _ => 10)))))
  | 3 => pop 1 (fun st bit => (bit,st.2))
    (branch (fun st => st.1==some false)
      (load (fun _ => (none,())) (goto (fun _ => if cycle then 11 else 10)))
      (load (fun _ => (none,())) (goto (fun _ => 10))))
  | 4 => pop 1 (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun _ => (none,())) (goto (fun _ => 10)))
      (load (fun _ => (none,())) (goto (fun _ => 5))))
  | 5 => copyMoveStmt 0 2 5 6
  | 6 => copyMoveStmt 2 1 6 7
  | 7 => push 1 (fun _ => true) .halt
  | 8 => FrameEmit.delimiterStmt 1 9
  | 9 => FrameEmit.emitStmt 2 1 9 7
  | 10 => clearStmt 0 10 12
  | 11 => copyMoveStmt 0 2 11 8
  | 12 => clearStmt 1 12 14
  | 14 => clearStmt 2 14 13
  | 13 => push 1 (fun _ => false) .halt
  | _ => .halt
abbrev machine (cycle : Bool) : Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 16
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program cycle
abbrev tapes := Wiring.tapes
def config (l : Fin 16) (input output temporary : List Bool) := cfg l () (tapes input output temporary)
theorem initial (cycle : Bool) (input : List Bool) : config 0 input [] []=initList (machine cycle).computer input := by
  rw [Machine.init_eq]; unfold config cfg; congr 1; funext k; fin_cases k <;> rfl
@[simp] theorem update_input (input output temporary word : List Bool) :
    Function.update (tapes input output temporary) (0 : Fin 3) word=tapes word output temporary := by
  funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
@[simp] theorem update_output (input output temporary word : List Bool) :
    Function.update (tapes input output temporary) (1 : Fin 3) word=tapes input word temporary := by
  funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
@[simp] theorem update_temporary (input output temporary word : List Bool) :
    Function.update (tapes input output temporary) (2 : Fin 3) word=tapes input output word := by
  funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]

theorem parse (cycle : Bool) (tag input : List Bool) :
    RunsExactly (machine cycle).computer.step (config 0 (Holant.Algebraic.frame tag++input) [] [])
      (config 2 input tag []) (2*(tag.length+1)) := by
  have h := Frame.extract_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    (machine cycle).computer.step (0 : Fin 16) 1 2 10 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) tag input []
  rw [←Wiring.tapes012,←Wiring.tapes012] at h
  simpa [config] using h

theorem read_first (cycle bit : Bool) (input tail : List Bool) :
    (machine cycle).computer.step (config 2 input (bit::tail) [])=
      some (config (if bit then 3 else if cycle then 10 else 4) input tail []) := by
  cases cycle <;> cases bit <;>
    change some (⟨some _,(none,()),Function.update (tapes input (_::tail) []) 1 tail⟩ : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 16) (Option Bool × Unit))=_
  all_goals rw [update_output]; rfl

theorem read_second (cycle bit : Bool) (input tail : List Bool) :
    (machine cycle).computer.step (config 3 input (bit::tail) [])=
      some (config (if bit then 10 else if cycle then 11 else 10) input tail []) := by
  cases cycle <;> cases bit <;>
    change some (⟨some _,(none,()),Function.update (tapes input (_::tail) []) 1 tail⟩ : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 16) (Option Bool × Unit))=_
  all_goals rw [update_output]; rfl

theorem tree_eof (input : List Bool) : (machine false).computer.step (config 4 input [] [])=some (config 5 input [] []) := by
  change some (⟨some 5,(none,()),Function.update (tapes input [] []) 1 []⟩ : (machine false).Config)=_
  rw [update_output]; rfl

theorem halt_some (cycle : Bool) (output : List Bool) : (machine cycle).computer.step (config 7 [] output [])=
    some (haltList (machine cycle).computer (true::output)) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (tapes [] output []) 1 (true::output)⟩ : (machine cycle).Config)=_
  rw [update_output]
  congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,wordTape,Function.update]

theorem skip (cycle : Bool) (input rest temporary : List Bool) :
    RunsExactly (machine cycle).computer.step (config 10 input rest temporary)
      (haltList (machine cycle).computer [false]) (input.length+rest.length+temporary.length+4) := by
  have a := clear_exact (machine cycle).computer.step (0 : Fin 3) (10 : Fin 16) 12
    (executesAt_tm2 _ _ _ rfl) () (tapes input rest temporary)
  rw [update_input] at a
  have b := clear_exact (machine cycle).computer.step (1 : Fin 3) (12 : Fin 16) 14
    (executesAt_tm2 _ _ _ rfl) () (tapes [] rest temporary)
  rw [update_output] at b
  have c := clear_exact (machine cycle).computer.step (2 : Fin 3) (14 : Fin 16) 13
    (executesAt_tm2 _ _ _ rfl) () (tapes [] [] temporary)
  rw [update_temporary] at c
  have d : (machine cycle).computer.step (config 13 [] [] [])=some (haltList (machine cycle).computer [false]) := by
    rw [Machine.halt_eq]
    change some (⟨none,(none,()),Function.update (tapes [] [] []) 1 [false]⟩ : (machine cycle).Config)=_
    rw [update_output]
    congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,wordTape,Function.update]
  have h := ((a.trans b).trans c).trans (runsExactly_one d)
  convert h using 1 <;> first | rfl | (simp [tapes,Wiring.tapes]; omega)

theorem tree_transfer (input : List Bool) :
    RunsExactly (machine false).computer.step (config 5 input [] []) (config 7 [] input []) (2*(input.length+1)) := by
  have h := transfer_exact_frame (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    (machine false).computer.step (5 : Fin 16) 6 7 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) input []
  rw [←Wiring.tapes012,←Wiring.tapes012] at h
  simpa [config] using h

theorem cycle_frame (input edge : List Bool) :
    RunsExactly (machine true).computer.step (config 11 input edge [])
      (config 7 [] (Holant.Algebraic.frame input++edge) []) (2*input.length+3) := by
  have h := FrameEmit.prepend_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    (machine true).computer.step (11 : Fin 16) 8 9 7 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) input edge
  rw [←Wiring.tapes012,←Wiring.tapes012] at h
  simpa [config] using h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentOption
