import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitReadStages

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitRead
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem read_bit (table : List Bool) (i : Fin table.length) :
    RunsExactly (TM2.step program) (config (.inl 0) [] table (List.replicate i.val true) [] [])
      (config (.inr 4) [] table [] [table.get i] []) (2*(i.val+1)+1) := by
  have source := BitTable.get_exact none table i []
  simp only [Option.getD_none,List.get_eq_getElem,List.set_getElem_self] at source
  have h := Returning.run_active (BitTable.machine none).program returns controller _ _
    (![[],[]] : Fin 2 → List Bool) _ source rfl
  have ret := Returning.return_step (BitTable.machine none).program returns controller
    (2 : Fin 4) rfl (none,()) (BitTable.tapes table [] [] [table.get i]) (![[],[]] : Fin 2 → List Bool)
  change RunsExactly (TM2.step program) _ _ _ at h
  change TM2.step program _ = _ at ret
  simpa [Returning.cfg,BitTable.config,config,cfg,work,returns,
    List.get_eq_getElem,Nat.add_comm] using h.trans (runsExactly_one ret)

theorem clear_table (table : List Bool) (bit : Bool) :
    RunsExactly (TM2.step program) (config (.inr 4) [] table [] [bit] [])
      (config (.inr 5) [] [] [] [bit] []) (table.length+1) := by
  have h := clear_exact (TM2.step program) (Sum.inl 0 : Stack) (.inr 4) (.inr 5)
    (executesAt_tm2 _ _ _ rfl) () (work [] table [] [bit] [])
  rw [update_table] at h
  exact h

theorem work_empty : work [] [] [] [] [] = fun _ => [] := by
  funext k; rcases k with k|k <;> fin_cases k <;> rfl

theorem initial (input : List Bool) :
    initList machine.computer input = config (.inr 0) input [] [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input [] [] [] [] [] input
  rw [work_empty] at h
  change wordTape (Sum.inr 0 : Stack) input = _ at h
  change (⟨some (.inr 0),(none,()),wordTape (Sum.inr 0 : Stack) input⟩ : machine.Config) = _
  rw [h]; rfl

theorem halt_step (bit : Bool) :
    TM2.step program (config (.inr 5) [] [] [] [bit] []) =
      some (haltList machine.computer [bit]) := by
  rw [Machine.halt_eq]
  have h := update_output [] [] [] [] [] [bit]
  rw [work_empty] at h
  change wordTape (Sum.inl 3 : Stack) [bit] = _ at h
  change some (⟨none,(none,()),work [] [] [] [bit] []⟩ : machine.Config) = _
  rw [← h]

@[simp] theorem input_word (x : Input) :
    inputEncoding.encode x = Holant.Algebraic.frame x.1 ++ List.replicate x.2.val true := rfl

def ticks (x : Input) : ℕ := 3*x.1.length+4*x.2.val+9

/-- One actual finite program, including frame parsing, unary-index moves,
table restoration, erasure, and the clean terminal transition. -/
theorem exact_run (x : Input) :
    RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode x))
      (haltList machine.computer (encodingBoolBool.encode (value x))) (ticks x) := by
  have all := ((((parse_table x.1 (List.replicate x.2.val true)).trans
    (move_index x.1 (List.replicate x.2.val true))).trans (read_bit x.1 x.2)).trans
    (clear_table x.1 (x.1.get x.2))).trans (runsExactly_one (halt_step (x.1.get x.2)))
  rw [input_word,initial]
  have ht : ticks x = 1+((x.1.length+1)+((2*(x.2.val+1)+1)+
      (2*((List.replicate x.2.val true).length+1)+2*(x.1.length+1)))) := by
    simp only [ticks,List.length_replicate]; omega
  rw [ht]
  exact all

theorem ticks_le (x : Input) : ticks x ≤ 4*(inputEncoding.encode x).length+5 := by
  simp only [ticks,input_word,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

noncomputable def computes : Computes inputEncoding encodingBoolBool value where
  machine := machine
  time := 4*Polynomial.X+5
  outputs x := {
    steps := ticks x
    evals_in_steps := exact_run x
    steps_le_m := by simpa using ticks_le x}

theorem inFP : InFP inputEncoding encodingBoolBool value := computes.inFP

theorem primitive_bound (x : Input) :
    (Primitive.run machine.program (ticks x) (some (initList machine.computer (inputEncoding.encode x)))).2 =
      some (haltList machine.computer (encodingBoolBool.encode (value x))) ∧
    (Primitive.run machine.program (ticks x) (some (initList machine.computer (inputEncoding.encode x)))).1 ≤
      machine.primitiveBudget*(4*(inputEncoding.encode x).length+5) := by
  have h := Primitive.execution_cost machine.program machine.primitiveBudget
    machine.program_budget_le _ _ _ (exact_run x)
  exact ⟨h.1,le_trans h.2 (Nat.mul_le_mul_left _ (ticks_le x))⟩

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitRead
