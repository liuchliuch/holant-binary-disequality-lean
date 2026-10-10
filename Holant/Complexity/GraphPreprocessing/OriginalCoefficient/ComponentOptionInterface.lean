import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentOption

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentOption
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines ComponentSelection
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem tree_exact (cycle : Bool) (input : List Bool) :
    RunsExactly (machine cycle).computer.step
      (initList (machine cycle).computer (Holant.Algebraic.frame [false]++input))
      (haltList (machine cycle).computer (if cycle then [false] else true::input))
      (if cycle then input.length+9 else 2*input.length+9) := by
  cases cycle with
  | false =>
    have h := ((((parse false [false] input).trans (runsExactly_one (read_first false false input []))).trans
      (runsExactly_one (tree_eof input))).trans (tree_transfer input)).trans (runsExactly_one (halt_some false input))
    rw [←initial]
    convert h using 1 <;> simp <;> omega
  | true =>
    have h := ((parse true [false] input).trans (runsExactly_one (read_first true false input []))).trans (skip true input [] [])
    rw [←initial]
    convert h using 1 <;> simp <;> omega

theorem cycle_exact (cycle : Bool) (e : ℕ) (input : List Bool) :
    RunsExactly (machine cycle).computer.step
      (initList (machine cycle).computer (Holant.Algebraic.frame (true::false::List.replicate e true)++input))
      (haltList (machine cycle).computer (if cycle then true::(Holant.Algebraic.frame input++List.replicate e true) else [false]))
      (if cycle then 2*input.length+2*e+12 else input.length+3*e+12) := by
  cases cycle with
  | false =>
    have h := (((parse false (true::false::List.replicate e true) input).trans
      (runsExactly_one (read_first false true input (false::List.replicate e true)))).trans
      (runsExactly_one (read_second false false input (List.replicate e true)))).trans (skip false input (List.replicate e true) [])
    rw [←initial]
    convert h using 1 <;> simp <;> omega
  | true =>
    have h := ((((parse true (true::false::List.replicate e true) input).trans
      (runsExactly_one (read_first true true input (false::List.replicate e true)))).trans
      (runsExactly_one (read_second true false input (List.replicate e true)))).trans (cycle_frame input (List.replicate e true))).trans
      (runsExactly_one (halt_some true (Holant.Algebraic.frame input++List.replicate e true)))
    rw [←initial]
    convert h using 1 <;> simp <;> omega

theorem dense_exact (cycle : Bool) (input : List Bool) :
    RunsExactly (machine cycle).computer.step
      (initList (machine cycle).computer (Holant.Algebraic.frame [true,true]++input))
      (haltList (machine cycle).computer [false]) (input.length+12) := by
  have h := (((parse cycle [true,true] input).trans (runsExactly_one (read_first cycle true input [true]))).trans
    (runsExactly_one (read_second cycle true input []))).trans (skip cycle input [] [])
  rw [←initial]
  convert h using 1 <;> simp <;> omega

def inputEncoding := pairEncoding ClassifyList.outputEncoding Frame.wordEncoding
def value (cycle : Bool) (x : Classification × List Bool) : Option (List Bool) := match x.1 with
  | .tree => if cycle then none else some x.2
  | .unicycle e => if cycle then some (Holant.Algebraic.frame x.2++List.replicate e true) else none
  | .dense => none
noncomputable def computes (cycle : Bool) :
    Computes inputEncoding (optionEncoding Frame.wordEncoding) (value cycle) where
  machine := machine cycle
  time := 3*Polynomial.X+12
  outputs x := by
    rcases x with ⟨kind,input⟩
    cases kind with
    | tree =>
      refine { steps := if cycle then input.length+9 else 2*input.length+9
               evals_in_steps := ?_
               steps_le_m := ?_ }
      · cases cycle <;> exact tree_exact _ input
      · cases cycle <;> simp [inputEncoding,pairEncoding,ClassifyList.outputEncoding,Holant.Algebraic.frame_length,Frame.wordEncoding] <;> omega
    | unicycle e =>
      refine { steps := if cycle then 2*input.length+2*e+12 else input.length+3*e+12
               evals_in_steps := ?_
               steps_le_m := ?_ }
      · cases cycle <;> exact cycle_exact _ e input
      · cases cycle <;> simp [inputEncoding,pairEncoding,ClassifyList.outputEncoding,Holant.Algebraic.frame_length,Frame.wordEncoding] <;> omega
    | dense =>
      refine { steps := input.length+12
               evals_in_steps := dense_exact cycle input
               steps_le_m := ?_ }
      simp [inputEncoding,pairEncoding,ClassifyList.outputEncoding,Holant.Algebraic.frame_length,Frame.wordEncoding]
      omega

theorem inFP (cycle : Bool) : InFP inputEncoding (optionEncoding Frame.wordEncoding) (value cycle) := (computes cycle).inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentOption
