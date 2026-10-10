import Holant.Complexity.BinaryInterpolation.WeightCompiler.Reference

/-! Exact semantic result of the generated postprocessor, retaining all m+1
answer values and producing the one numerator/denominator pair to be divided. -/
namespace Holant.Complexity.BinaryInterpolation
open Holant.OneHot.StackProgram
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

theorem weighted_numerator (geometric : Bool) (m : ℕ) (gamma rho : K) (y : Fin (m+1)→K) :
    WeightedStack.value (WeightFormulas.coefficients gamma rho)
      (List.ofFn (fun i => (WeightFormulas.weight geometric m i,y i))) 0=
      commonNumerator
        (queryDenominator (WeightFormulas.nodes geometric rho m) (WeightFormulas.scales gamma m)) y := by
  rw [WeightedStack.value_eq_sum]
  simp only [zero_add,List.map_ofFn,Function.comp_apply,Fin.sum_ofFn,
    WeightFormulas.eval_weight,commonNumerator]

theorem reference_value (geometric : Bool) (m : ℕ) (gamma rho : K) (y : Fin (m+1)→K) :
    ∃trace,run (WeightFormulas.coefficients gamma rho) (WeightCompiler.reference geometric m)
      (List.ofFn y)=some
        ([commonNumerator
          (queryDenominator (WeightFormulas.nodes geometric rho m) (WeightFormulas.scales gamma m)) y,
          commonDenominator
          (queryDenominator (WeightFormulas.nodes geometric rho m) (WeightFormulas.scales gamma m))],trace) := by
  let coeff := WeightFormulas.coefficients gamma rho
  let pairs := List.ofFn (fun i => (WeightFormulas.weight geometric m i,y i))
  have hw := WeightedStack.run_code coeff pairs 0 []
  simp only [pairs,List.map_ofFn,Function.comp_def,List.append_nil] at hw
  dsimp only [coeff] at hw
  rw [weighted_numerator] at hw
  refine ⟨WeightedStack.trace coeff pairs 0++
    (WeightFormulas.totalDenominator geometric m).trace coeff,?_⟩
  simp only [WeightCompiler.reference, run_append]
  simp only [run, step, bind, Option.bind_some, pure, List.nil_append]
  simp only [hw, Option.bind_some, RingFormula.run_code,
    WeightFormulas.eval_totalDenominator]
  simp [run, step, coeff, List.append_assoc, pairs]

theorem reference_length_le (geometric : Bool) (m : ℕ) :
    (WeightCompiler.reference geometric m).length≤
      (m+1)*(WeightFormulas.weightSize m+4)+WeightFormulas.weightSize m+2 := by
  simp only [WeightCompiler.reference,List.length_append,List.length_singleton,
    WeightedStack.code_length,RingFormula.code_length,List.map_ofFn,Function.comp_def]
  have hs : (List.ofFn (fun i : Fin (m+1) => (WeightFormulas.weight geometric m i).size+4)).sum≤
      (m+1)*(WeightFormulas.weightSize m+4) := by
    rw [Fin.sum_ofFn]
    calc
      _ ≤ ∑_i : Fin (m+1),(WeightFormulas.weightSize m+4) :=
        Finset.sum_le_sum (fun i _ => Nat.add_le_add_right (WeightFormulas.weight_size_le geometric m i) 4)
      _ = _ := by simp
  have hd := WeightFormulas.totalDenominator_size_le geometric m
  omega

end
end Holant.Complexity.BinaryInterpolation
