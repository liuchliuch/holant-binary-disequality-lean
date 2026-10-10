import Holant.Proofs.Hardness.BinaryThreeSupportStarProgrammeReference
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Compile

/-! An actual finite Boolean-stack producer of the signed-star bytecode.
All dynamic indices, loops, products and instruction frames are emitted by
the existing concrete range/append/repeat machines. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarProgramme
open Turing Computability Holant.Complexity Holant.Algebraic
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.Complexity.BinaryInterpolation
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler Holant.OneHot.StackProgram
open WeightCompiler
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

def differenceEmits : Emits tripleUnary (fun x=>differenceCode x.1.2 x.2) :=
  appendEmits (appendEmits (appendEmits
    (thirdUnary.andThen (nodeEmits true)) (constantEmits tripleUnary [.literal 2,.mul]))
    (middleUnary.andThen (nodeEmits true))) (constantEmits tripleUnary [.add])
def negativeEmits : Emits tripleUnary (fun x=>negativeCode x.2) :=
  appendEmits (thirdUnary.andThen (nodeEmits true))
    (constantEmits tripleUnary [.literal 2,.mul,.literal 2,.add])
def differenceFactorEmits : Emits tripleUnary
    (fun x=>(if x.2=x.1.2 then [.one] else differenceCode x.1.2 x.2) ++ [.mul]) := by
  let chosen := ifEmits equalIndicesComputes (constantEmits tripleUnary [.one]) differenceEmits
  exact congrComputes (appendEmits chosen (constantEmits tripleUnary [.mul])) (fun x=>by simp)
def negativeFactorEmits : Emits tripleUnary
    (fun x=>(if x.2=x.1.2 then [.one] else negativeCode x.2) ++ [.mul]) := by
  let chosen := ifEmits equalIndicesComputes (constantEmits tripleUnary [.one]) negativeEmits
  exact congrComputes (appendEmits chosen (constantEmits tripleUnary [.mul])) (fun x=>by simp)
def divisorEmits : Emits pairUnary (fun x=>divisorCode x.1 x.2) :=
  appendEmits (constantEmits pairUnary [.one])
    (reverseRangeEmits pairUnary (fun x=>x.1+1) (firstUnary.andThen successorComputes)
      _ differenceFactorEmits)
def numeratorEmits : Emits pairUnary (fun x=>numeratorCode x.1 x.2) :=
  appendEmits (constantEmits pairUnary [.one])
    (reverseRangeEmits pairUnary (fun x=>x.1+1) (firstUnary.andThen successorComputes)
      _ negativeFactorEmits)
def divisorFactorEmits : Emits tripleUnary
    (fun x=>(if x.2=x.1.2 then [.one] else divisorCode x.1.1 x.2) ++ [.mul]) := by
  let chosen := ifEmits equalIndicesComputes (constantEmits tripleUnary [.one])
    (reindexComputes.andThen divisorEmits)
  exact congrComputes (appendEmits chosen (constantEmits tripleUnary [.mul])) (fun x=>by simp)
def outerEmits : Emits pairUnary (fun x=>outerCode x.1 x.2) :=
  appendEmits (constantEmits pairUnary [.one])
    (reverseRangeEmits pairUnary (fun x=>x.1+1) (firstUnary.andThen successorComputes)
      _ divisorFactorEmits)
def weightEmits : Emits pairUnary (fun x=>weightCode x.1 x.2) :=
  appendEmits (appendEmits (appendEmits (appendEmits (appendEmits
    outerEmits numeratorEmits) (constantEmits pairUnary [.mul]))
    (constantEmits pairUnary [.one]))
    (repeatEmits pairUnary (fun x=>x.1) firstUnary [.literal 2,.mul]))
    (constantEmits pairUnary [.mul])
def totalDenominatorEmits : Emits unary totalDenominatorCode :=
  appendEmits (constantEmits unary [.one])
    (reverseRangeEmits unary (fun m=>m+1) successorComputes _
      (appendEmits divisorEmits (constantEmits pairUnary [.mul])))
def generatedEmits : Emits unary generatedCode :=
  appendEmits (appendEmits (appendEmits (constantEmits unary [.zero])
    (rangeEmits unary (fun m=>m+1) successorComputes _
      (appendEmits weightEmits (constantEmits pairUnary [.copy 2,.mul,.add,.erase 1]))))
    totalDenominatorEmits) (constantEmits unary [.swap])

def computes : Computes unary (codeEncoding labels) reference :=
  recode (joinComputes generatedEmits (constantComputes unary Frame.wordEncoding [false]))
    id (fun _=>rfl) (fun m=>by
      change chunk (generatedCode m) ++ [false]=framedListEncode (opEncoding labels) (reference m)
      rw [generated_eq_reference]
      simpa only [chunk,List.append_nil,framedListEncode] using
        entries_append_encode (opEncoding labels) (reference m) [])

def codeBound (m : ℕ) : ℕ := (m+2)*weightSize m+4*(m+1)+2
theorem reference_length_le (m : ℕ) : (reference m).length≤codeBound m := by
  have hw : ((List.ofFn (weight m)).flatMap
      (fun p=>p.code ++ ([.copy 2,.mul,.add,.erase 1] : Code))).length≤
      (m+1)*(weightSize m+4) := by
    rw [List.length_flatMap,List.map_ofFn,Fin.sum_ofFn]
    calc
      _ ≤ ∑_i : Fin (m+1),(weightSize m+4) := by
        apply Finset.sum_le_sum
        intro i _
        simpa [RingFormula.code_length] using Nat.add_le_add_right (weight_size m i) 4
      _ = _ := by simp
  have hd := totalDenominator_size m
  simp only [reference,WeightCompiler.weighted_code,List.length_append,List.length_singleton,
    RingFormula.code_length]
  unfold codeBound
  nlinarith

def quartic : Polynomial ℕ :=
  let X := Polynomial.X
  let D := (X+1)*(4*X+6)+1
  let O := (X+1)*(D+1)+1
  let W := 2*X+D+O+3
  20*((X+2)*W+4*(X+1)+2)+1
theorem quartic_eval (m : ℕ) : quartic.eval m=20*codeBound m+1 := by
  simp [quartic,codeBound,weightSize,outerSize,divisorSize]
theorem quartic_output_bound (m : ℕ) :
    ((codeEncoding labels).encode (reference m)).length≤quartic.eval m := by
  have hb := codeEncoding_length_le labels 3
    (fun i=>GraphPreprocessing.SignatureLabel.binaryFinEncoding_length_le 4 i) (reference m)
  rw [quartic_eval]
  have hc := reference_length_le m
  nlinarith

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarProgramme
