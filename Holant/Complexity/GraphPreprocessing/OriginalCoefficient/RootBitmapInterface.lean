import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmapStages
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicateSpec

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmap
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem write_root (x : Input) :
    RunsExactly (TM2.step program)
      (config (.inl 0) [] [] [] (List.replicate x.1 false) (List.replicate x.2.val true) [])
      (config (.inr 5) [] [] [] (value x) [] [false]) (2*(x.2.val+1)+1) := by
  let i : Fin (List.replicate x.1 false).length := ⟨x.2.val,by simpa using x.2.isLt⟩
  have hi : (List.replicate x.1 false).get i = false := by simp [List.get_eq_getElem]
  have source := BitTable.get_exact (some true) (List.replicate x.1 false) i []
  simp only [Option.getD_some,hi] at source
  have h := Returning.run_active (BitTable.machine (some true)).program returns outside _ _
    (![[],[],[]] : Fin 3 → List Bool) _ source rfl
  have ret := Returning.return_step (BitTable.machine (some true)).program returns outside (2 : Fin 4) rfl
    (none,()) (BitTable.tapes (value x) [] [] [false]) (![[],[],[]] : Fin 3 → List Bool)
  change RunsExactly (TM2.step program) _ _ _ at h
  change TM2.step program _ = _ at ret
  simpa [Returning.cfg,BitTable.config,config,cfg,work,returns,value,i,Nat.add_comm] using h.trans (runsExactly_one ret)

theorem clear_output (table : List Bool) :
    RunsExactly (TM2.step program) (config (.inr 5) [] [] [] table [] [false])
      (config (.inr 6) [] [] [] table [] []) 2 := by
  have h := clear_exact (TM2.step program) (Sum.inl 3 : Stack) (.inr 5) (.inr 6)
    (executesAt_tm2 _ _ _ rfl) () (work [] [] [] table [] [false])
  rw [update_output] at h
  exact h

theorem work_empty : work [] [] [] [] [] [] = fun _ => [] := by
  funext k; rcases k with k|k <;> fin_cases k <;> rfl

theorem initial (input : List Bool) :
    initList machine.computer input = config (.inr 0) input [] [] [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input [] [] [] [] [] [] input
  rw [work_empty] at h
  change wordTape (Sum.inr 0 : Stack) input = _ at h
  change (⟨some (.inr 0),(none,()),wordTape (Sum.inr 0 : Stack) input⟩ : machine.Config) = _
  rw [h]; rfl

theorem halt_step (table : List Bool) :
    TM2.step program (config (.inr 6) [] [] [] table [] []) = some (haltList machine.computer table) := by
  rw [Machine.halt_eq]
  have h := update_table [] [] [] [] [] [] table
  rw [work_empty] at h
  change wordTape (Sum.inl 0 : Stack) table = _ at h
  change some (⟨none,(none,()),work [] [] [] table [] []⟩ : machine.Config) = _
  rw [← h]

def ticks (x : Input) : ℕ := 3*x.1+4*x.2.val+11

theorem exact_run (x : Input) :
    RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode x))
      (haltList machine.computer (value x)) (ticks x) := by
  have alloc := allocate x.1 [] (List.replicate x.2.val true)
  simp only [List.append_nil] at alloc
  have all := (((((parse_count (List.replicate x.1 true) (List.replicate x.2.val true)).trans
    (move_root (List.replicate x.1 true) (List.replicate x.2.val true))).trans alloc).trans
    (write_root x)).trans (clear_output (value x))).trans (runsExactly_one (halt_step (value x)))
  rw [input_word,initial]
  have ht : ticks x = 1+(2+((2*(x.2.val+1)+1)+((x.1+1)+
      (2*((List.replicate x.2.val true).length+1)+2*((List.replicate x.1 true).length+1))))) := by
    simp only [ticks,List.length_replicate]; omega
  rw [ht]
  exact all

theorem ticks_le (x : Input) : ticks x≤4*(inputEncoding.encode x).length+7 := by
  simp only [ticks,input_word,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

noncomputable def computes : Computes inputEncoding Frame.wordEncoding value where
  machine := machine
  time := 4*Polynomial.X+7
  outputs x := {
    steps := ticks x
    evals_in_steps := exact_run x
    steps_le_m := by simpa using ticks_le x }

theorem inFP : InFP inputEncoding Frame.wordEncoding value := computes.inFP

theorem program_budget (label : Label) : TM2Cost.budget (program label)≤8 := by
  cases label with
  | inl l =>
    change TM2Cost.budget (Returning.stmt (returns l) ((BitTable.machine (some true)).program l))≤8
    rw [Returning.statement_budget]
    exact BitTable.program_budget _ _
  | inr l => fin_cases l <;> simp [program,Returning.program,outside,Frame.scanStmt_budget,copyMoveStmt,clearStmt,TM2Cost.budget]

theorem primitive_bound (x : Input) :
    (Primitive.run program (ticks x) (some (initList machine.computer (inputEncoding.encode x)))).2 =
      some (haltList machine.computer (value x)) ∧
    (Primitive.run program (ticks x) (some (initList machine.computer (inputEncoding.encode x)))).1 ≤
      8*(4*(inputEncoding.encode x).length+7) := by
  have h := Primitive.execution_cost program 8 program_budget _ _ _ (exact_run x)
  exact ⟨h.1,le_trans h.2 (Nat.mul_le_mul_left _ (ticks_le x))⟩

theorem get_value (x : Input) (i : Fin x.1) :
    (value x)[i.val]'(by simpa using i.isLt) = decide (i=x.2) := by
  simp [value,List.getElem_set,Fin.ext_iff,eq_comm]

theorem graph_value (g : Graph) (root : g.Vertex) :
    value ⟨g.vertices,root⟩ = NeighborPredicate.bitmap g {root} := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hv : i<g.vertices := by simpa using hi
    have h := get_value ⟨g.vertices,root⟩ ⟨i,hv⟩
    simpa [NeighborPredicate.bitmap] using h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmap
