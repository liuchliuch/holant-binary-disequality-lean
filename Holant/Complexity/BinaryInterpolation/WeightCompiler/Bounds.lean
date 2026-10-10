import Holant.Complexity.BinaryInterpolation.WeightCompiler.Compile

/-! A small explicit quartic output bound, in addition to the physical compiler's
polynomial transition and primitive-instruction bounds. -/
namespace Holant.Complexity.BinaryInterpolation.WeightCompiler
open Holant.OneHot.StackProgram RingFormula WeightFormulas
open GraphPreprocessing.OriginalCoefficient
noncomputable section

/-- Instruction count before serialization. -/
def codeBound (m : ℕ) : ℕ := (m+2)*weightSize m + 4*(m+1)+2

theorem reference_length_le (geometric : Bool) (m : ℕ) :
    (reference geometric m).length ≤ codeBound m := by
  have hw : ((List.ofFn (WeightFormulas.weight geometric m)).flatMap
      (fun p => p.code ++ ([.copy 2,.mul,.add,.erase 1] : Code))).length ≤
      (m+1)*(weightSize m+4) := by
    rw [List.length_flatMap, List.map_ofFn, Fin.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin (m+1), (weightSize m+4) := by
        apply Finset.sum_le_sum
        intro i _
        simpa [RingFormula.code_length] using
          Nat.add_le_add_right (weight_size_le geometric m i) 4
      _ = _ := by simp
  have hd := totalDenominator_size_le geometric m
  simp only [reference,weighted_code,List.length_append,List.length_singleton,RingFormula.code_length]
  unfold codeBound
  nlinarith

def quartic : Polynomial ℕ :=
  let X := Polynomial.X
  let D := 2*((X+1)*X)+(X+1)*(4*X+10)+3
  let W := (X+1)*(D+1)+1
  20*((X+2)*W+4*(X+1)+2)+1

theorem quartic_eval (m : ℕ) : quartic.eval m = 20*codeBound m+1 := by
  simp [quartic,codeBound,weightSize,denominatorSize]

/-- Boolean labels 0,1,2,3 and fixed bounded-stack indices have fixed size.
Every instruction frame and the final terminator are included in this bound. -/
theorem quartic_output_bound (geometric : Bool) (m : ℕ) :
    ((codeEncoding labels).encode (reference geometric m)).length ≤ quartic.eval m := by
  have hb := codeEncoding_length_le labels 3
    (fun i => GraphPreprocessing.SignatureLabel.binaryFinEncoding_length_le 4 i)
    (reference geometric m)
  rw [quartic_eval]
  have hc := reference_length_le geometric m
  nlinarith

end
end Holant.Complexity.BinaryInterpolation.WeightCompiler
