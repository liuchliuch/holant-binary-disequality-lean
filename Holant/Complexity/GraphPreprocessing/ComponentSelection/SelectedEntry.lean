import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordJoin

/-! A physical Boolean gate for a framed list entry. The false case consumes
the complete payload; the true case frames it bit by bit and emits its tag. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection.SelectedEntry
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

abbrev tapes := Wiring.tapes
def program (l : Fin 10) : Stmt (Fin 3) (Fin 10) Unit := match l.val with
  | 0 => Frame.scanStmt 0 2 0 1 9
  | 1 => copyMoveStmt 2 1 1 2
  | 2 => pop 1 (fun st bit => (bit,st.2))
      (branch (fun st => st.1==some true)
        (load (fun _ => (none,())) (goto (fun _ => 4)))
        (load (fun _ => (none,())) (goto (fun _ => 3))))
  | 3 => clearStmt 0 3 8
  | 4 => copyMoveStmt 0 2 4 5
  | 5 => FrameEmit.delimiterStmt 1 6
  | 6 => FrameEmit.emitStmt 2 1 6 7
  | 7 => push 1 (fun _ => true) .halt
  | _ => .halt
abbrev machine : Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 10
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program
def config (l : Fin 10) (a b c : List Bool) := cfg l () (tapes a b c)
def value (p : Bool × List Bool) : List Bool := if p.1 then true :: Holant.Algebraic.frame p.2 else []
def inputEncoding := pairEncoding encodingBoolBool Frame.wordEncoding

theorem initial (word : List Bool) : config 0 word [] []=initList machine.computer word := by
  rw [Machine.init_eq]; unfold config cfg; congr 1; funext k; fin_cases k <;> rfl
theorem halt_false : machine.computer.step (config 8 [] [] [])=some (haltList machine.computer []) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),tapes [] [] []⟩ : machine.Config)=_
  congr 2; funext k; fin_cases k <;> rfl
theorem halt_true (word : List Bool) : machine.computer.step (config 7 [] word [])=
    some (haltList machine.computer (true::word)) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (tapes [] word []) 1 (true::word)⟩ : machine.Config)=_
  congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,wordTape,Function.update]
theorem parse (bit : Bool) (word : List Bool) :
    RunsExactly machine.computer.step (config 0 (Holant.Algebraic.frame [bit]++word) [] [])
      (config 2 word [bit] []) 4 := by
  have h := Frame.extract_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step (0 : Fin 10) 1 2 9 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) [bit] word []
  rw [←Wiring.tapes012,←Wiring.tapes012] at h
  exact h
theorem branch_step (bit : Bool) (word : List Bool) :
    machine.computer.step (config 2 word [bit] [])=some (config (if bit then 4 else 3) word [] []) := by
  cases bit <;> change some (⟨some _,(none,()),Function.update (tapes word [_] []) 1 []⟩ : machine.Config)=_
  all_goals unfold config cfg; congr 2; funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
theorem clear (word : List Bool) :
    RunsExactly machine.computer.step (config 3 word [] []) (config 8 [] [] []) (word.length+1) := by
  have h := clear_exact machine.computer.step (0 : Fin 3) (3 : Fin 10) 8
    (executesAt_tm2 _ _ _ rfl) () (tapes word [] [])
  have ht : Function.update (tapes word [] []) 0 []=tapes [] [] [] := by
    funext k; fin_cases k <;> simp [tapes,Wiring.tapes,Function.update]
  rw [ht] at h
  exact h
theorem emit (word : List Bool) :
    RunsExactly machine.computer.step (config 4 word [] []) (config 7 [] (Holant.Algebraic.frame word) [])
      (2*word.length+3) := by
  have h := FrameEmit.prepend_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step (4 : Fin 10) 5 6 7 (executesAt_tm2 _ _ _ rfl)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (fun _ => []) word []
  rw [←Wiring.tapes012,←Wiring.tapes012] at h
  simpa [config] using h
def ticks (p : Bool × List Bool) : ℕ := if p.1 then 2*p.2.length+9 else p.2.length+7
theorem exact_run (p : Bool × List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode p))
      (haltList machine.computer (value p)) (ticks p) := by
  rcases p with ⟨bit,word⟩
  cases bit with
  | false =>
    have h := (((parse false word).trans (runsExactly_one (branch_step false word))).trans
      (clear word)).trans (runsExactly_one halt_false)
    rw [initial] at h
    convert h using 1 <;> first | rfl | (simp [ticks]; omega)
  | true =>
    have h := (((parse true word).trans (runsExactly_one (branch_step true word))).trans
      (emit word)).trans (runsExactly_one (halt_true (Holant.Algebraic.frame word)))
    rw [initial] at h
    convert h using 1 <;> first | rfl | (simp [ticks]; omega)
noncomputable def computes : Computes inputEncoding Frame.wordEncoding value where
  machine := machine
  time := 2*Polynomial.X+9
  outputs p := {
    steps := ticks p
    evals_in_steps := exact_run p
    steps_le_m := by
      rcases p with ⟨bit,word⟩
      cases bit <;> simp [ticks,inputEncoding,pairEncoding,encodingBoolBool,encodeBool,Frame.wordEncoding] <;> omega }
end Holant.Complexity.GraphPreprocessing.ComponentSelection.SelectedEntry
