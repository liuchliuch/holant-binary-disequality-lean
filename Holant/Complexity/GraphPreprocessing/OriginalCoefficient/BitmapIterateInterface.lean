import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateRun

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

noncomputable def timed (x : Input) :
    TM2OutputsInTime (machine roundMachine).computer (inputEncoding.encode x) (some (value x))
      (timePolynomial.eval (inputEncoding.encode x).length) where
  steps := Classical.choose (whole_run x)
  evals_in_steps := (Classical.choose_spec (whole_run x)).2
  steps_le_m := (Classical.choose_spec (whole_run x)).1

/-- Clean V-round closure by an actual finite machine. Intermediate widths are
proved invariant for the genuine synchronous-round provider. -/
noncomputable def computes : Computes inputEncoding Frame.wordEncoding value where
  machine := machine roundMachine
  time := timePolynomial
  outputs := timed

theorem inFP : InFP inputEncoding Frame.wordEncoding value := computes.inFP

noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C (machine roundMachine).primitiveBudget
theorem primitive_bound (x : Input) :
    primitiveCost (machine roundMachine) (timed x).steps
      (some (initList (machine roundMachine).computer (inputEncoding.encode x))) ≤
        primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right (machine roundMachine).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (primitiveCost_le _ _ _) h

noncomputable def graph_timed (g : Graph) (s : Finset g.Vertex) :
    TM2OutputsInTime (machine roundMachine).computer (word g s)
      (some (NeighborPredicate.bitmap g ((g.round^[g.vertices]) s)))
      (timePolynomial.eval (word g s).length) where
  steps := Classical.choose (whole_graph g s)
  evals_in_steps := (Classical.choose_spec (whole_graph g s)).2
  steps_le_m := (Classical.choose_spec (whole_graph g s)).1

theorem iterate_round_reach (g : Graph) (root : g.Vertex) (k : ℕ) :
    (g.round^[k]) {root} = g.reach root k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',Graph.reach_succ,ih]

/-- Actual V-round reachability from an already serialized singleton bitmap;
RootBitmap supplies that bitmap by a separate proved physical initializer. -/
noncomputable def reach_timed (g : Graph) (root : g.Vertex) :
    TM2OutputsInTime (machine roundMachine).computer (word g {root})
      (some (NeighborPredicate.bitmap g (g.reach root g.vertices)))
      (timePolynomial.eval (word g {root}).length) := by
  simpa only [iterate_round_reach] using graph_timed g {root}

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
