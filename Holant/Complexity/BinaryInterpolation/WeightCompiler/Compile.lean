import Holant.Complexity.BinaryInterpolation.WeightCompiler.Reference
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Combinators
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! One finite Boolean program compiles interpolation weights for a variable
unary occurrence count. The spectral choice is fixed at compile time. -/
namespace Holant.Complexity.BinaryInterpolation.WeightCompiler
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable {A : Type}
noncomputable def ifEmits {ea : Encoding A Bool} {p : A → Bool} {f g : A → Code}
    (test : Computes ea encodingBoolBool p) (yes : Emits ea f) (no : Emits ea g) :
    Emits ea (fun x => if p x then f x else g x) :=
  congrComputes (ifComputes test yes no) (fun x => by cases h : p x <;> simp [h])

noncomputable def nodeEmits (geometric : Bool) : Emits unary (nodeCode geometric) := by
  cases geometric
  · exact appendEmits (constantEmits unary [.zero])
      (repeatEmits unary id (identityComputes unary) [.one,.add])
  · exact appendEmits (constantEmits unary [.one])
      (repeatEmits unary id (identityComputes unary) [.literal 1,.mul])

abbrev pairUnary := pairEncoding unary unary
abbrev tripleUnary := pairEncoding pairUnary unary
noncomputable def firstUnary : Computes pairUnary unary (fun x => x.1) := Wiring.firstComputes unary unary
noncomputable def secondUnary : Computes pairUnary unary (fun x => x.2) := Wiring.secondComputes unary unary
noncomputable def contextUnary : Computes tripleUnary pairUnary (fun x => x.1) := Wiring.firstComputes pairUnary unary
noncomputable def thirdUnary : Computes tripleUnary unary (fun x => x.2) := Wiring.secondComputes pairUnary unary
noncomputable def middleUnary : Computes tripleUnary unary (fun x => x.1.2) := contextUnary.andThen secondUnary

noncomputable def differenceEmits (geometric : Bool) :
    Emits tripleUnary (fun x => differenceCode geometric x.1.2 x.2) :=
  appendEmits (appendEmits (appendEmits
    ((thirdUnary.andThen successorComputes).andThen (nodeEmits geometric))
    (constantEmits tripleUnary [.literal 2,.mul]))
    ((middleUnary.andThen successorComputes).andThen (nodeEmits geometric)))
    (constantEmits tripleUnary [.add])

noncomputable def equalIndicesComputes :
    Computes tripleUnary encodingBoolBool (fun x => decide (x.2=x.1.2)) :=
  (pairComputes thirdUnary middleUnary).andThen (equalComputes unary)

noncomputable def differenceFactorEmits (geometric : Bool) :
    Emits tripleUnary
      (fun x => (if x.2=x.1.2 then [.one] else differenceCode geometric x.1.2 x.2) ++ [.mul]) := by
  let chosen := ifEmits equalIndicesComputes
    (constantEmits tripleUnary [.one]) (differenceEmits geometric)
  exact congrComputes (appendEmits chosen (constantEmits tripleUnary [.mul]))
    (fun x => by simp)

noncomputable def exponentComputes : Computes pairUnary unary (fun x => (x.2+1)*x.1) :=
  (pairComputes (secondUnary.andThen successorComputes) firstUnary).andThen multiplyUnaryComputes

noncomputable def denominatorEmits (geometric : Bool) :
    Emits pairUnary (fun x => denominatorCode geometric x.1 x.2) :=
  appendEmits (appendEmits (appendEmits (appendEmits
    (constantEmits pairUnary [.one])
    (reverseRangeEmits pairUnary (fun x => x.1+1) (firstUnary.andThen successorComputes)
      _ (differenceFactorEmits geometric)))
    (constantEmits pairUnary [.one]))
    (repeatEmits pairUnary (fun x => (x.2+1)*x.1) exponentComputes [.literal 0,.mul]))
    (constantEmits pairUnary [.mul])

noncomputable def reindexComputes : Computes tripleUnary pairUnary (fun x => (x.1.1,x.2)) :=
  pairComputes (contextUnary.andThen firstUnary) thirdUnary

noncomputable def denominatorFactorEmits (geometric : Bool) :
    Emits tripleUnary
      (fun x => (if x.2=x.1.2 then [.one] else denominatorCode geometric x.1.1 x.2) ++ [.mul]) := by
  let chosen := ifEmits equalIndicesComputes (constantEmits tripleUnary [.one])
    (reindexComputes.andThen (denominatorEmits geometric))
  exact congrComputes (appendEmits chosen (constantEmits tripleUnary [.mul]))
    (fun x => by simp)

noncomputable def weightEmits (geometric : Bool) :
    Emits pairUnary (fun x => weightCode geometric x.1 x.2) :=
  appendEmits (constantEmits pairUnary [.one])
    (reverseRangeEmits pairUnary (fun x => x.1+1) (firstUnary.andThen successorComputes)
      _ (denominatorFactorEmits geometric))

noncomputable def totalDenominatorEmits (geometric : Bool) :
    Emits unary (totalDenominatorCode geometric) :=
  appendEmits (constantEmits unary [.one])
    (reverseRangeEmits unary (fun m => m+1) successorComputes _
      (appendEmits (denominatorEmits geometric) (constantEmits pairUnary [.mul])))

noncomputable def generatedEmits (geometric : Bool) :
    Emits unary (generatedCode geometric) :=
  appendEmits (appendEmits (appendEmits (constantEmits unary [.zero])
    (rangeEmits unary (fun m => m+1) successorComputes _
      (appendEmits (weightEmits geometric) (constantEmits pairUnary [.copy 2,.mul,.add,.erase 1]))))
    (totalDenominatorEmits geometric)) (constantEmits unary [.swap])

/-- The terminator is physically emitted after the exact reference bytecode. -/
noncomputable def computes (geometric : Bool) :
    Computes unary (codeEncoding labels) (reference geometric) :=
  recode (joinComputes (generatedEmits geometric)
    (constantComputes unary Frame.wordEncoding [false])) id (fun _ => rfl)
    (fun m => by
      change chunk (generatedCode geometric m) ++ [false] =
        framedListEncode (opEncoding labels) (reference geometric m)
      rw [generated_eq_reference]
      simpa only [chunk,List.append_nil,framedListEncode] using
        entries_append_encode (opEncoding labels) (reference geometric m) [])

noncomputable def transitionPolynomial (geometric : Bool) : Polynomial ℕ := (computes geometric).time
noncomputable def primitiveBound (geometric : Bool) : Polynomial ℕ := primitivePolynomial (computes geometric)
noncomputable def outputPolynomial (geometric : Bool) : Polynomial ℕ := (computes geometric).outputBound.bound

/-- Original unary input length is exactly m, so this is an original-input time
bound, independent of the eventual expanded bytecode. -/
theorem transition_bound (geometric : Bool) (m : ℕ) :
    ((computes geometric).outputs m).steps ≤ (transitionPolynomial geometric).eval m := by
  simpa [transitionPolynomial,unary,UnaryBinary.unaryEncoding] using ((computes geometric).outputs m).steps_le_m

theorem primitive_bound (geometric : Bool) (m : ℕ) :
    primitiveCost (computes geometric).machine ((computes geometric).outputs m).steps
      (some (initList (computes geometric).machine.computer (unary.encode m))) ≤
        (primitiveBound geometric).eval m := by
  simpa [primitiveBound,unary,UnaryBinary.unaryEncoding] using computes_primitive_cost (computes geometric) m

theorem output_bound (geometric : Bool) (m : ℕ) :
    ((codeEncoding labels).encode (reference geometric m)).length ≤
      (outputPolynomial geometric).eval m := by
  simpa [outputPolynomial,unary,UnaryBinary.unaryEncoding] using (computes geometric).outputBound.length_le m

theorem inFP (geometric : Bool) : InFP unary (codeEncoding labels) (reference geometric) :=
  (computes geometric).inFP

end Holant.Complexity.BinaryInterpolation.WeightCompiler
