import Holant.Complexity.GraphPreprocessing.NetworkCounts
import Holant.Complexity.GraphPreprocessing.Returning
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-! Clean physical preparation of the original raw input and its actual unary
vertex/edge counters. Counts come from the real framed-list scan, then both
retained fields are framed for the finite edge-materialization driver. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CountsPackage
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Stack := Fin 7 ⊕ Fin 0
abbrev Label := Fin 10 ⊕ Fin 8
abbrev Statement := Stmt Stack Label Unit

def returns (l : Fin 10) : Fin 8 := if l=8 then 0 else 7

def controller (l : Fin 8) : Statement := match l.val with
  | 0 => copyMoveStmt (.inl 5) (.inl 2) (.inr 0) (.inr 1)
  | 1 => FixedFieldMachines.FrameEmit.delimiterStmt (.inl 6) (.inr 2)
  | 2 => FixedFieldMachines.FrameEmit.emitStmt (.inl 2) (.inl 6) (.inr 2) (.inr 3)
  | 3 => copyMoveStmt (.inl 0) (.inl 2) (.inr 3) (.inr 4)
  | 4 => FixedFieldMachines.FrameEmit.delimiterStmt (.inl 6) (.inr 5)
  | 5 => FixedFieldMachines.FrameEmit.emitStmt (.inl 2) (.inl 6) (.inr 5) (.inr 6)
  | 7 => load (fun _ => (some false,())) .halt
  | _ => .halt

def program : Label → Statement := Returning.program NetworkCounts.machine.program returns controller

abbrev machine : Machine where
  K := Stack
  input := .inl 0
  output := .inl 6
  Label := Label
  main := .inl 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def work (raw vertices output temporary : List Bool) : Stack → List Bool :=
  Sum.elim (NetworkCounts.tapes raw [] temporary [] [] vertices output) Fin.elim0

def config (l : Label) (raw vertices output temporary : List Bool) := cfg l () (work raw vertices output temporary)

@[simp] theorem update_raw (raw vertices output temporary word : List Bool) :
    Function.update (work raw vertices output temporary) (.inl 0) word = work word vertices output temporary := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [work,NetworkCounts.tapes,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => exact Fin.elim0 k
@[simp] theorem update_vertices (raw vertices output temporary word : List Bool) :
    Function.update (work raw vertices output temporary) (.inl 5) word = work raw word output temporary := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [work,NetworkCounts.tapes,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => exact Fin.elim0 k
@[simp] theorem update_output (raw vertices output temporary word : List Bool) :
    Function.update (work raw vertices output temporary) (.inl 6) word = work raw vertices word temporary := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [work,NetworkCounts.tapes,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => exact Fin.elim0 k
@[simp] theorem update_temporary (raw vertices output temporary word : List Bool) :
    Function.update (work raw vertices output temporary) (.inl 2) word = work raw vertices output word := by
  funext k; cases k with
  | inl k => fin_cases k <;> simp [work,NetworkCounts.tapes,Function.update,
      -Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => exact Fin.elim0 k

def word (r : RawClosedNetwork) : List Bool :=
  Holant.Algebraic.frame (RawClosedNetwork.encoding.encode r) ++
    (Holant.Algebraic.frame (List.replicate r.vertices.length true) ++ List.replicate r.edges.length true)

theorem frame_vertices (raw vertices edges : List Bool) :
    RunsExactly (TM2.step program) (config (.inr 0) raw vertices edges [])
      (config (.inr 3) raw [] (Holant.Algebraic.frame vertices ++ edges) []) (2*vertices.length+3) := by
  have run := FixedFieldMachines.FrameEmit.prepend_exact (Sum.inl 5 : Stack) (.inl 6) (.inl 2)
    (by decide) (by decide) (by decide) (TM2.step program) (.inr 0) (.inr 1) (.inr 2) (.inr 3)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (work raw [] [] []) vertices edges
  simpa only [config,tapes3,update_vertices,update_output,update_temporary] using run

theorem frame_raw (raw suffix : List Bool) :
    RunsExactly (TM2.step program) (config (.inr 3) raw [] suffix [])
      (config (.inr 6) [] [] (Holant.Algebraic.frame raw ++ suffix) []) (2*raw.length+3) := by
  have run := FixedFieldMachines.FrameEmit.prepend_exact (Sum.inl 0 : Stack) (.inl 6) (.inl 2)
    (by decide) (by decide) (by decide) (TM2.step program) (.inr 3) (.inr 4) (.inr 5) (.inr 6)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (work [] [] [] []) raw suffix
  simpa only [config,tapes3,update_raw,update_output,update_temporary] using run

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CountsPackage
