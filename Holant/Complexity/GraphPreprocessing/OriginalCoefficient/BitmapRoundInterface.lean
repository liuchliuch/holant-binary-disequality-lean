import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundRun
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundGraph

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

noncomputable def timed (x : Input) :
    TM2OutputsInTime (machine neighborMachine).computer (inputEncoding.encode x) (some (value x))
      (timePolynomial.eval (inputEncoding.encode x).length) where
  steps := Classical.choose (whole_run x)
  evals_in_steps := (Classical.choose_spec (whole_run x)).2
  steps_le_m := (Classical.choose_spec (whole_run x)).1

/-- A clean finite Boolean-stack witness for a synchronous round, with its
counter, intermediate query widths, provider payloads and cleanup all derived. -/
noncomputable def computes : Computes inputEncoding Frame.wordEncoding value where
  machine := machine neighborMachine
  time := timePolynomial
  outputs := timed

theorem inFP : InFP inputEncoding Frame.wordEncoding value := computes.inFP

noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C (machine neighborMachine).primitiveBudget

theorem primitive_bound (x : Input) :
    primitiveCost (machine neighborMachine) (timed x).steps
      (some (initList (machine neighborMachine).computer (inputEncoding.encode x))) ≤
        primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right (machine neighborMachine).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (primitiveCost_le _ _ _) h

noncomputable def graph_timed (g : Graph) (s : Finset g.Vertex) :
    TM2OutputsInTime (machine neighborMachine).computer
      (Holant.Algebraic.frame (NeighborPredicate.bitmap g s)++ReachRound.encode (ReachRound.graphEdges g))
      (some (NeighborPredicate.bitmap g (g.round s)))
      (timePolynomial.eval (Holant.Algebraic.frame (NeighborPredicate.bitmap g s)++ReachRound.encode (ReachRound.graphEdges g)).length) := by
  simpa only [graph_input_word,graph_value] using timed (graphInput g s)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
