import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.OptionChoice

set_option autoImplicit false

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure.OptionChoice
open Holant.Complexity Holant.Complexity.GraphPreprocessing
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem some_first (fallback output second : List Bool) :
    Holant.Complexity.StackProtocol.RunsExactly (machine fallback).computer.step
      (initList (machine fallback).computer (Holant.Algebraic.frame (true::output)++second))
      (haltList (machine fallback).computer output) (2*output.length+second.length+7) := by
  have h := ((parse fallback (true::output) second).trans (runsExactly_one (read_first fallback true second output))).trans
    (clear_second fallback output second)
  rw [←initial]
  convert h using 1 <;> simp <;> omega

theorem some_second (fallback output : List Bool) :
    Holant.Complexity.StackProtocol.RunsExactly (machine fallback).computer.step
      (initList (machine fallback).computer (Holant.Algebraic.frame [false]++(true::output)))
      (haltList (machine fallback).computer output) (2*output.length+10) := by
  have h := (((((parse fallback [false] (true::output)).trans
    (runsExactly_one (read_first fallback false (true::output) []))).trans
    (runsExactly_one (first_none fallback (true::output)))).trans
    (runsExactly_one (read_second fallback true output))).trans (transfer_second fallback output)).trans
    (runsExactly_one (halt_output fallback output))
  rw [←initial]
  convert h using 1 <;> simp <;> omega

theorem neither (fallback : List Bool) :
    Holant.Complexity.StackProtocol.RunsExactly (machine fallback).computer.step
      (initList (machine fallback).computer (Holant.Algebraic.frame [false]++[false]))
      (haltList (machine fallback).computer fallback) 9 := by
  have h := ((((parse fallback [false] [false]).trans
    (runsExactly_one (read_first fallback false [false] []))).trans
    (runsExactly_one (first_none fallback [false]))).trans
    (runsExactly_one (read_second fallback false []))).trans (fallback_exact fallback)
  rw [←initial]
  exact h

def optionWords := optionEncoding Frame.wordEncoding
def inputEncoding := pairEncoding optionWords optionWords
def value (fallback : List Bool) (x : Option (List Bool) × Option (List Bool)) := x.1.getD (x.2.getD fallback)
noncomputable def computes (fallback : List Bool) : Computes inputEncoding Frame.wordEncoding (value fallback) where
  machine := machine fallback
  time := 3*Polynomial.X+10
  outputs x := by
    rcases x with ⟨first,second⟩
    cases first with
    | some first =>
      refine {steps := 2*first.length+(optionWords.encode second).length+7
              evals_in_steps := some_first fallback first (optionWords.encode second)
              steps_le_m := ?_}
      simp only [inputEncoding,pairEncoding,optionWords,optionEncoding,Frame.wordEncoding,List.length_append,
        Holant.Algebraic.frame_length,List.length_cons,id_eq,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      omega
    | none =>
      cases second with
      | some second =>
        refine { steps := 2*second.length+10, evals_in_steps := some_second fallback second, steps_le_m := ?_ }
        simp [inputEncoding,pairEncoding,optionWords,optionEncoding,Frame.wordEncoding,Holant.Algebraic.frame_length]
        omega
      | none =>
        refine {steps := 9, evals_in_steps := neither fallback, steps_le_m := ?_}
        simp [inputEncoding,pairEncoding,optionWords,optionEncoding,Frame.wordEncoding,Holant.Algebraic.frame_length]
theorem inFP (fallback : List Bool) : InFP inputEncoding Frame.wordEncoding (value fallback) := (computes fallback).inFP
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure.OptionChoice
