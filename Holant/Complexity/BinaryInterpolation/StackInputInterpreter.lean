import Holant.OneHot.StackProgram.Machine.Interpreter

/-! A physical framed-code/initial-stack entry point for the existing finite
interpreter. It reads every initial answer bit from the input tapes and enters
the proved fetch loop; no variable data is put into finite control. -/
namespace Holant.Complexity.BinaryInterpolation.StackInputInterpreter
open Turing Computability BinaryCompose StackProtocol
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open Family
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A]
variable (workers : Op A→BinaryCompose.Machine) (labels : Encoding A Bool) (C : ℕ)
set_option backward.isDefEq.respectTransparency false

abbrev NewLabels := Fin 5⊕Family.Labels workers
abbrev Config := TM2.Cfg (fun _ : Keys workers => Bool) (NewLabels workers) (States workers)

def layout : StackEmbedding (Keys workers) (Keys workers) where
  key := id
  lift := id
  lookup _ _ := rfl
  update _ _ _ := rfl

def states : StateEmbedding (States workers) (States workers) where
  put := id
  get := id
  get_put _ := rfl

def program : NewLabels workers→TM2.Stmt (fun _ : Keys workers => Bool)
    (NewLabels workers) (States workers)
  | .inl i =>
    if i=0 then GraphPreprocessing.Frame.scanStmt (.inl 0) (.inl 3) (.inl 0) (.inl 1) (.inl 4)
    else if i=1 then copyMoveStmt (.inl 0) (.inl 2) (.inl 1) (.inl 2)
    else if i=2 then copyMoveStmt (.inl 2) (.inl 1) (.inl 2) (.inl 3)
    else if i=3 then copyMoveStmt (.inl 3) (.inl 0) (.inl 3) (.inr (.inl 1))
    else .halt
  | .inr l => embedStmt (layout workers) (states workers) Sum.inr none
      (Dynamic.program workers labels C l)

abbrev machine : BinaryCompose.Machine where
  K := Keys workers
  input := .inl 0
  output := .inl 1
  Label := NewLabels workers
  main := .inl 0
  State := States workers
  initial := (none,Family.initial workers)
  program := program workers labels C

def mapped (c : Family.Config workers) : Config workers :=
  embedCfg (layout workers) (states workers) Sum.inr none c

theorem lift_run (c d : Family.Config workers) (t : ℕ)
    (h : RunsExactly (Dynamic.machine workers labels C).computer.step c d t) :
    RunsExactly (machine workers labels C).computer.step
      (mapped workers c) (mapped workers d) t :=
  embed_run (layout workers) (states workers) Sum.inr none
    (Dynamic.program workers labels C) (program workers labels C) (fun _ => rfl) c d t h

private theorem scan (code stack : List Bool) :
    RunsExactly (machine workers labels C).computer.step
      (cfg (.inl 0) (Family.initial workers) (Family.tapes workers (Holant.Algebraic.frame code++stack) [] [] []))
      (cfg (.inl 1) (Family.initial workers) (Family.tapes workers stack [] [] code.reverse))
      (code.length+1) := by
  have h := GraphPreprocessing.Frame.scan_exact
    (.inl 0 : Keys workers) (.inl 1) (.inl 3) (by simp) (by simp)
    (machine workers labels C).computer.step (.inl 0) (.inl 1) (.inl 4)
    (executesAt_tm2 _ _ _ rfl) (Family.initial workers) (fun _ => []) code stack [] []
  simp only [List.append_nil] at h
  convert h using 1 <;> congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [Family.tapes,tapes3,Function.update]
  | inr k => rfl

private theorem move_stack (code stack : List Bool) :
    RunsExactly (machine workers labels C).computer.step
      (cfg (.inl 1) (Family.initial workers) (Family.tapes workers stack [] [] code.reverse))
      (cfg (.inl 3) (Family.initial workers) (Family.tapes workers [] stack [] code.reverse))
      (2*(stack.length+1)) := by
  have h := StackWord.move_exact (.inl 0 : Keys workers) (.inl 1) (.inl 2)
    (by simp) (by simp) (by simp) (machine workers labels C).computer.step
    (.inl 1) (.inl 2) (.inl 3) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    (Family.initial workers) (Family.tapes workers [] [] [] code.reverse) stack []
  simp only [List.append_nil] at h
  convert h using 1 <;> congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [Family.tapes,tapes3,Function.update]
  | inr k => rfl

private theorem restore_code (code stack : List Bool) :
    RunsExactly (machine workers labels C).computer.step
      (cfg (.inl 3) (Family.initial workers) (Family.tapes workers [] stack [] code.reverse))
      (cfg (.inr (.inl 1)) (Family.initial workers) (Family.tapes workers code stack [] []))
      (code.length+1) := by
  have h := copy_move_exact (.inl 3 : Keys workers) (.inl 1) (.inl 0)
    (by simp) (by simp) (machine workers labels C).computer.step
    (.inl 3) (.inr (.inl 1)) (executesAt_tm2 _ _ _ rfl)
    (Family.initial workers) (fun _ => []) code.reverse stack []
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h
  convert h using 1 <;> congr 1 <;> funext k <;> cases k with
  | inl k => fin_cases k <;> simp [Family.tapes,tapes3,Function.update]
  | inr k => rfl

/-- Exact counted framing and transfer, with the code and initial stack unchanged. -/
theorem start (code stack : List Bool) :
    RunsExactly (machine workers labels C).computer.step
      (initList (machine workers labels C).computer (Holant.Algebraic.frame code++stack))
      (mapped workers (cfg (.inl 1) (Family.initial workers) (Family.tapes workers code stack [] [])))
      (2*code.length+2*stack.length+4) := by
  have h := ((scan workers labels C code stack).trans (move_stack workers labels C code stack)).trans
    (restore_code workers labels C code stack)
  have hinit : initList (machine workers labels C).computer (Holant.Algebraic.frame code++stack)=
      cfg (.inl 0) (Family.initial workers) (Family.tapes workers (Holant.Algebraic.frame code++stack) [] [] []) := by
    rw [BinaryCompose.Machine.init_eq]
    congr 1
    funext k
    cases k with
    | inl k => fin_cases k <;> simp [Family.tapes,wordTape,Function.update]
    | inr k => rfl
  rw [hinit]
  convert h using 1 <;> (first | rfl | omega)

end
end Holant.Complexity.BinaryInterpolation.StackInputInterpreter
