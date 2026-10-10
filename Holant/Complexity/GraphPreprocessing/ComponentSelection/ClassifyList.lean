import Holant.Complexity.GraphPreprocessing.ComponentSelection.Semantics
import Holant.Complexity.GraphPreprocessing.ComponentSelection.SelectedEntry
import Holant.Complexity.GraphPreprocessing.UnaryBinary

/-! Physical 0/1/multiple classification of an increasing unary edge list.
The singleton keeps its real original ID; the dense branch clears both the
first edge and the entire remaining list. No invented cut ID is emitted. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection.ClassifyList
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
def outputEncoding : Encoding Classification Bool where
  encode
    | .tree => [false]
    | .unicycle e => true::false::List.replicate e true
    | .dense => [true,true]
  decode
    | [false] => some .tree
    | true::false::tail => (UnaryBinary.unaryEncoding.decode tail).map Classification.unicycle
    | [true,true] => some .dense
    | _ => none
  decode_encode c := by cases c <;> simp [UnaryBinary.unaryEncoding]
def program (l : Fin 8) : Stmt (Fin 3) (Fin 8) Unit := match l.val with
  | 0 => pop 0 (fun st bit => (bit,st.2))
    (branch (fun st => st.1==some true)
      (load (fun _ => (none,())) (goto (fun _ => 1)))
      (push 1 (fun _ => false) (load (fun _ => (none,())) .halt)))
  | 1 => Frame.scanStmt 0 2 1 2 7
  | 2 => copyMoveStmt 2 1 2 3
  | 3 => pop 0 (fun st bit => (bit,st.2))
    (branch (fun st => st.1==some true)
      (load (fun _ => (none,())) (goto (fun _ => 4)))
      (push 1 (fun _ => false) (push 1 (fun _ => true) (load (fun _ => (none,())) .halt))))
  | 4 => clearStmt 0 4 5
  | 5 => clearStmt 1 5 6
  | 6 => push 1 (fun _ => true) (push 1 (fun _ => true) .halt)
  | _ => .halt
abbrev machine : Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 8
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program
abbrev tapes := Wiring.tapes
def config (l : Fin 8) (input output temporary : List Bool) := cfg l () (tapes input output temporary)
theorem initial (input : List Bool) : config 0 input [] []=initList machine.computer input := by
  rw [Machine.init_eq]; unfold config cfg; congr 1; funext k; fin_cases k <;> rfl
theorem nil_step : machine.computer.step (config 0 [false] [] [])=some (haltList machine.computer [false]) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (Function.update (tapes [false] [] []) 0 []) 1 [false]⟩ : machine.Config)=_
  congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,wordTape,Function.update]
theorem cons_step (rest : List Bool) : machine.computer.step (config 0 (true::rest) [] [])=some (config 1 rest [] []) := by
  change some (⟨some 1,(none,()),Function.update (tapes (true::rest) [] []) 0 rest⟩ : machine.Config)=_
  unfold config cfg; congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
theorem parse (edge rest : List Bool) :
    RunsExactly machine.computer.step (config 1 (Holant.Algebraic.frame edge++rest) [] [])
      (config 3 rest edge []) (2*(edge.length+1)) := by
  have h := Frame.extract_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step (1 : Fin 8) 2 3 7 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) edge rest []
  rw [←Wiring.tapes012,←Wiring.tapes012] at h
  simpa [config] using h
theorem singleton_step (edge : List Bool) : machine.computer.step (config 3 [false] edge [])=
    some (haltList machine.computer (true::false::edge)) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (Function.update (Function.update (tapes [false] edge []) 0 [])
    1 (false::edge)) 1 (true::false::edge)⟩ : machine.Config)=_
  congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,wordTape,Function.update]
theorem second_step (edge rest : List Bool) : machine.computer.step (config 3 (true::rest) edge [])=
    some (config 4 rest edge []) := by
  change some (⟨some 4,(none,()),Function.update (tapes (true::rest) edge []) 0 rest⟩ : machine.Config)=_
  unfold config cfg; congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
theorem dense_finish (edge rest : List Bool) :
    RunsExactly machine.computer.step (config 4 rest edge []) (haltList machine.computer [true,true])
      (rest.length+edge.length+3) := by
  have first := clear_exact machine.computer.step (0 : Fin 3) (4 : Fin 8) 5
    (executesAt_tm2 _ _ _ rfl) () (tapes rest edge [])
  have ht : Function.update (tapes rest edge []) 0 []=tapes [] edge [] := by
    funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
  rw [ht] at first
  have last := clear_exact machine.computer.step (1 : Fin 3) (5 : Fin 8) 6
    (executesAt_tm2 _ _ _ rfl) () (tapes [] edge [])
  have ho : Function.update (tapes [] edge []) 1 []=tapes [] [] [] := by
    funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
  rw [ho] at last
  have done : machine.computer.step (config 6 [] [] [])=some (haltList machine.computer [true,true]) := by
    rw [Machine.halt_eq]
    change some (⟨none,(none,()),Function.update (Function.update (tapes [] [] []) 1 [true]) 1 [true,true]⟩ : machine.Config)=_
    congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,wordTape,Function.update]
  have h := (first.trans last).trans (runsExactly_one done)
  convert h using 1 <;> first | rfl | (simp [tapes,Wiring.tapes]; omega)
abbrev inputEncoding := framedListEncoding UnaryBinary.unaryEncoding
def ticks (xs : List ℕ) : ℕ := match xs with
  | [] => 1
  | [e] => 2*e+4
  | e::f::tail => 3*e+(Holant.Algebraic.frame (List.replicate f true)++framedListEncode UnaryBinary.unaryEncoding tail).length+7
theorem exact_run (xs : List ℕ) :
    RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode xs))
      (haltList machine.computer (outputEncoding.encode (classify xs))) (ticks xs) := by
  cases xs with
  | nil => rw [←initial]; exact runsExactly_one nil_step
  | cons e xs =>
    cases xs with
    | nil =>
      have h := ((runsExactly_one (cons_step (Holant.Algebraic.frame (List.replicate e true)++[false]))).trans
        (parse (List.replicate e true) [false])).trans (runsExactly_one (singleton_step (List.replicate e true)))
      rw [initial] at h
      convert h using 1 <;> first | rfl | (simp [ticks]; omega)
    | cons f tail =>
      let rest := Holant.Algebraic.frame (List.replicate f true)++framedListEncode UnaryBinary.unaryEncoding tail
      have h := ((((runsExactly_one (cons_step (Holant.Algebraic.frame (List.replicate e true)++(true::rest)))).trans
        (parse (List.replicate e true) (true::rest))).trans (runsExactly_one (second_step (List.replicate e true) rest))).trans
        (dense_finish (List.replicate e true) rest))
      rw [initial] at h
      convert h using 1 <;> first | rfl | (simp [ticks,rest]; omega)
noncomputable def computes : Computes inputEncoding outputEncoding classify where
  machine := machine
  time := 2*Polynomial.X+7
  outputs xs := {
    steps := ticks xs
    evals_in_steps := exact_run xs
    steps_le_m := by
      cases xs with
      | nil => simp [ticks]
      | cons e xs => cases xs <;>
          simp [ticks,inputEncoding,framedListEncoding,framedListEncode,UnaryBinary.unaryEncoding,Holant.Algebraic.frame_length] <;> omega }
theorem inFP : InFP inputEncoding outputEncoding classify := computes.inFP
end Holant.Complexity.GraphPreprocessing.ComponentSelection.ClassifyList
