import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.LiteralBits
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-! Direct parsing of the parent flag and two label words. This finite program
avoids a decision tree whose depth is the combined size of those words. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.HeaderWords
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
open Holant.Algebraic
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
abbrev Statement := Stmt (Fin 4) (Fin 21) Unit
def expect (bit : Bool) (next : Fin 21) : Statement :=
  pop 0 (fun st b => (b,st.2)) (branch (fun st => st.1==some bit)
    (load (fun _ => (none,())) (goto (fun _ => next)))
    (load (fun _ => (none,())) (goto (fun _ => 20))))
def program (l : Fin 21) : Statement := match l.val with
  | 0 => expect true 1
  | 1 => pop 0 (fun st b => (b,st.2)) (branch (fun st => st.1==some true)
      (load (fun _ => (none,())) (goto (fun _ => 3)))
      (branch (fun st => st.1==some false)
        (load (fun _ => (none,())) (goto (fun _ => 2)))
        (load (fun _ => (none,())) (goto (fun _ => 20)))))
  | 2 => expect false 4
  | 3 => expect false 8
  | 4 => Frame.scanStmt 0 2 4 5 20
  | 5 => copyMoveStmt 2 3 5 6
  | 6 => clearStmt 0 6 13
  | 8 => Frame.scanStmt 0 2 8 9 20
  | 9 => copyMoveStmt 2 3 9 10
  | 10 => copyMoveStmt 0 2 10 11
  | 11 => FrameEmit.delimiterStmt 1 12
  | 12 => FrameEmit.emitStmt 2 1 12 13
  | 13 => copyMoveStmt 3 2 13 14
  | 14 => FrameEmit.delimiterStmt 1 15
  | 15 => FrameEmit.emitStmt 2 1 15 19
  | 20 => load (fun _ => (some false,())) .halt
  | _ => .halt
abbrev machine : Machine where
  K := Fin 4
  input := 0
  output := 1
  Label := Fin 21
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program
def tapes (input output temporary first : List Bool) : Fin 4 → List Bool := ![input,output,temporary,first]
def config (l : Fin 21) (input output temporary first : List Bool) := cfg l () (tapes input output temporary first)

theorem tag_exact (flag : Bool) (word : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (frame [flag]++word))
      (config (if flag then 8 else 4) word [] [] []) 3 := by
  cases flag <;> rw [Machine.init_eq]
  all_goals
    simp [RunsExactly,Function.iterate_succ_apply,machine,FinTM2.step,TM2.step,program,expect,TM2.stepAux,cfg,config,frame,wordTape,tapes,Function.update]
    funext k
    fin_cases k <;> rfl

theorem extract (flag : Bool) (a b : List Bool) :
    RunsExactly machine.computer.step (config (if flag then 8 else 4) (frame a++b) [] [] [])
      (config (if flag then 10 else 6) b [] [] a) (2*(a.length+1)) := by
  have ht (u v w : List Bool) : tapes3 (fun _ : Fin 4 => []) 0 3 2 u v w=tapes u [] w v := by
    funext k; fin_cases k <;> rfl
  cases flag
  · have h := Frame.extract_exact (0 : Fin 4) 3 2 (by decide) (by decide) (by decide)
      machine.computer.step 4 5 6 20 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (fun _ => []) a b []
    rw [ht,ht] at h
    simpa only [config,List.append_nil,Bool.false_eq_true,↓reduceIte] using h
  · have h := Frame.extract_exact (0 : Fin 4) 3 2 (by decide) (by decide) (by decide)
      machine.computer.step 8 9 10 20 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) () (fun _ => []) a b []
    rw [ht,ht] at h
    simpa only [config,List.append_nil,Bool.false_eq_true,↓reduceIte] using h

theorem clear_second (a b : List Bool) :
    RunsExactly machine.computer.step (config 6 b [] [] a) (config 13 [] [] [] a) (b.length+1) := by
  have h := clear_exact machine.computer.step (0 : Fin 4) 6 13 (executesAt_tm2 _ _ _ rfl) () (tapes b [] [] a)
  have hu : Function.update (tapes b [] [] a) (0 : Fin 4) []=tapes [] [] [] a := by
    funext k; fin_cases k <;> rfl
  rw [hu] at h
  simpa only [config,tapes,Matrix.cons_val_zero] using h
theorem frame_second (a b : List Bool) :
    RunsExactly machine.computer.step (config 10 b [] [] a) (config 13 [] (frame b) [] a) (2*b.length+3) := by
  have h := FrameEmit.prepend_exact (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step 10 11 12 13 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
      (executesAt_tm2 _ _ _ rfl) () (tapes [] [] [] a) b []
  have ht (u v w : List Bool) : tapes3 (tapes [] [] [] a) 0 1 2 u v w=tapes u v w a := by
    funext k; fin_cases k <;> rfl
  rw [ht,ht] at h
  simpa only [config,List.append_nil,Bool.false_eq_true,↓reduceIte] using h
theorem frame_first (a out : List Bool) :
    RunsExactly machine.computer.step (config 13 [] out [] a) (config 19 [] (frame a++out) [] []) (2*a.length+3) := by
  have h := FrameEmit.prepend_exact (3 : Fin 4) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step 13 14 15 19 (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
      (executesAt_tm2 _ _ _ rfl) () (fun _ => []) a out
  have ht (u v w : List Bool) : tapes3 (fun _ : Fin 4 => []) 3 1 2 u v w=tapes [] v w u := by
    funext k; fin_cases k <;> rfl
  rw [ht,ht] at h
  exact h
theorem halt_step (out : List Bool) : machine.computer.step (config 19 [] out [] [])=some (haltList machine.computer out) := by
  rw [Machine.halt_eq]
  simp [machine,FinTM2.step,TM2.step,TM2.stepAux,program,config,cfg,tapes,wordTape,Function.update]
  funext k
  fin_cases k <;> rfl

def output (x : Bool × (List Bool × List Bool)) := frame x.2.1++if x.1 then frame x.2.2 else []
def ticks (x : Bool × (List Bool × List Bool)) := if x.1 then 4*x.2.1.length+2*x.2.2.length+12 else 4*x.2.1.length+x.2.2.length+10
def inputEncoding := pairEncoding encodingBoolBool (pairEncoding Frame.wordEncoding Frame.wordEncoding)
theorem exact_run (flag : Bool) (a b : List Bool) :
    RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode (flag,a,b)))
      (haltList machine.computer (output (flag,a,b))) (ticks (flag,a,b)) := by
  have first := (tag_exact flag (frame a++b)).trans (extract flag a b)
  cases flag
  · have all := ((first.trans (clear_second a b)).trans (frame_first a [])).trans (runsExactly_one (halt_step (frame a++[])))
    convert all using 1 <;> simp [ticks,output,inputEncoding,pairEncoding,encodingBoolBool,encodeBool,Frame.wordEncoding] <;> omega
  · have all := ((first.trans (frame_second a b)).trans (frame_first a (frame b))).trans (runsExactly_one (halt_step (frame a++frame b)))
    convert all using 1 <;> simp [ticks,output,inputEncoding,pairEncoding,encodingBoolBool,encodeBool,Frame.wordEncoding] <;> omega
noncomputable def computes : Computes inputEncoding Frame.wordEncoding output where
  machine := machine
  time := 2*Polynomial.X+12
  outputs x := {
    steps := ticks x
    evals_in_steps := exact_run x.1 x.2.1 x.2.2
    steps_le_m := by
      have hb : (encodingBoolBool.encode x.1).length=1 := by cases x.1 <;> rfl
      simp only [inputEncoding,pairEncoding_length,hb,Frame.wordEncoding,ticks,Polynomial.eval_add,Polynomial.eval_mul,
        Polynomial.eval_ofNat,Polynomial.eval_X,id_eq]
      split <;> omega }
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.HeaderWords
