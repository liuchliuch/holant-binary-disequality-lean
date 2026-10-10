import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeBinaryUnsignedInterpolationFormulas
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Bounds

/-! Executable variable-size Lagrange bytecode for a fixed finite target.
Literal3 is the actual target, not an instance-dependent oracle constant.
The old geometric denominators and all physical code-emission loops are reused. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationCode
open Computability Holant.Complexity Holant.Complexity.BinaryCompose
open Holant.Complexity.FixedFieldMachines Holant.OneHot.StackProgram
open Holant.Complexity.FixedGadgetSubstitution.Compiler
open Holant.Complexity.GraphPreprocessing
open Holant.OneHot Holant.OneHot.StackProgram.GraphLabelEncoding
open scoped BigOperators
open Holant.Complexity.BinaryInterpolation
namespace F
export OrdinaryNegativeBinaryUnsignedInterpolationFormulas
  (difference numerator weight totalDenominator weightSize numeratorSize weight_size totalDenominator_size)
end F
namespace W
export WeightCompiler
  (Code labels unary pairUnary tripleUnary chunk Emits appendEmits constantEmits rangeEmits reverseRangeEmits
   successorComputes firstUnary thirdUnary ifEmits equalIndicesComputes nodeEmits nodeCode
   weightCode weightEmits totalDenominatorCode totalDenominatorEmits prodList_code ofFn_code_flatMap weighted_code)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option Elab.async false

def reference (m : ℕ) : W.Code :=
  [.zero] ++ WeightedStack.code (List.ofFn (F.weight m)) ++ (F.totalDenominator m).code ++ [.swap]
def differenceCode (j : ℕ) : W.Code := W.nodeCode true (j+1) ++ [.literal 2,.mul,.literal 3,.add]
def numeratorCode (m i : ℕ) : W.Code := [.one] ++ (List.range (m+1)).reverse.flatMap
  (fun j=>(if j=i then [.one] else differenceCode j) ++ [.mul])
def weightCode (m i : ℕ) : W.Code := W.weightCode true m i ++ numeratorCode m i ++ [.mul]
def generatedCode (m : ℕ) : W.Code :=
  [.zero] ++ (List.range (m+1)).flatMap
    (fun i=>weightCode m i ++ [.copy 2,.mul,.add,.erase 1]) ++ W.totalDenominatorCode true m ++ [.swap]

theorem difference_code (j : ℕ) : (F.difference j).code=differenceCode j := by
  simp [F.difference,RingFormula.code,WeightCompiler.node_code,differenceCode,List.append_assoc]

theorem numerator_code (m : ℕ) (i : Fin (m+1)) : (F.numerator m i).code=numeratorCode m i.val := by
  simp only [F.numerator,RingFormula.without,W.prodList_code]
  rw [W.ofFn_code_flatMap (f:=fun j=>if j=i.val then [.one] else differenceCode j)]
  · rfl
  · intro j
    by_cases h : j=i
    · subst j
      simp [RingFormula.code]
    · have hv : j.val≠i.val := fun e=>h (Fin.ext e)
      simp [h,hv,difference_code]

theorem weight_code (m : ℕ) (i : Fin (m+1)) : (F.weight m i).code=weightCode m i.val := by
  simp only [F.weight,RingFormula.code,WeightCompiler.weight_code,numerator_code]
  rfl

theorem generated_eq_reference (m : ℕ) : generatedCode m=reference m := by
  simp only [reference,W.weighted_code,F.totalDenominator,WeightCompiler.totalDenominator_code,
    List.ofFn_eq_map,List.flatMap_map,weight_code]
  unfold generatedCode
  rw [←List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map]

def differenceEmits : W.Emits W.tripleUnary (fun x=>differenceCode x.2) :=
  W.appendEmits ((W.thirdUnary.andThen W.successorComputes).andThen (W.nodeEmits true))
    (W.constantEmits W.tripleUnary [.literal 2,.mul,.literal 3,.add])

def numeratorFactorEmits : W.Emits W.tripleUnary
    (fun x=>(if x.2=x.1.2 then [.one] else differenceCode x.2) ++ [.mul]) := by
  let chosen := W.ifEmits W.equalIndicesComputes (W.constantEmits W.tripleUnary [.one]) differenceEmits
  exact congrComputes (W.appendEmits chosen (W.constantEmits W.tripleUnary [.mul])) (fun x=>by simp)

def numeratorEmits : W.Emits W.pairUnary (fun x=>numeratorCode x.1 x.2) :=
  W.appendEmits (W.constantEmits W.pairUnary [.one])
    (W.reverseRangeEmits W.pairUnary (fun x=>x.1+1) (W.firstUnary.andThen W.successorComputes)
      _ numeratorFactorEmits)

def weightEmits : W.Emits W.pairUnary (fun x=>weightCode x.1 x.2) :=
  W.appendEmits (W.appendEmits (W.weightEmits true) numeratorEmits) (W.constantEmits W.pairUnary [.mul])

def generatedEmits : W.Emits W.unary generatedCode :=
  W.appendEmits (W.appendEmits (W.appendEmits (W.constantEmits W.unary [.zero])
    (W.rangeEmits W.unary (fun m=>m+1) W.successorComputes _
      (W.appendEmits weightEmits (W.constantEmits W.pairUnary [.copy 2,.mul,.add,.erase 1]))))
    (W.totalDenominatorEmits true)) (W.constantEmits W.unary [.swap])

def computes : Computes W.unary (codeEncoding W.labels) reference :=
  recode (joinComputes generatedEmits (constantComputes W.unary Frame.wordEncoding [false]))
    id (fun _=>rfl) (fun m=>by
      change W.chunk (generatedCode m) ++ [false]=framedListEncode (opEncoding W.labels) (reference m)
      rw [generated_eq_reference]
      simpa only [W.chunk,List.append_nil,framedListEncode] using
        entries_append_encode (opEncoding W.labels) (reference m) [])

def codeBound (m : ℕ) : ℕ := (m+2)*F.weightSize m+4*(m+1)+2

theorem reference_length_le (m : ℕ) : (reference m).length≤codeBound m := by
  have hw : ((List.ofFn (F.weight m)).flatMap
      (fun p=>p.code ++ ([.copy 2,.mul,.add,.erase 1] : W.Code))).length≤(m+1)*(F.weightSize m+4) := by
    rw [List.length_flatMap,List.map_ofFn,Fin.sum_ofFn]
    calc
      _ ≤ ∑_i : Fin (m+1),(F.weightSize m+4) := by
        apply Finset.sum_le_sum
        intro i _
        simpa [RingFormula.code_length] using Nat.add_le_add_right (F.weight_size m i) 4
      _ = _ := by simp
  have hd := F.totalDenominator_size m
  simp only [reference,W.weighted_code,List.length_append,List.length_singleton,RingFormula.code_length]
  unfold codeBound
  nlinarith

def weightPolynomial : Polynomial ℕ :=
  WeightCompiler.quartic+(Polynomial.X+1)*(2*Polynomial.X+8)+2

def polynomial : Polynomial ℕ :=
  (Polynomial.X+2)*weightPolynomial+4*(Polynomial.X+1)+2

theorem weightSize_le (m : ℕ) : F.weightSize m≤weightPolynomial.eval m := by
  have h : WeightFormulas.weightSize m≤WeightCompiler.quartic.eval m := by
    rw [WeightCompiler.quartic_eval]
    unfold WeightCompiler.codeBound
    nlinarith
  simp [weightPolynomial,F.weightSize,F.numeratorSize]
  omega

theorem codeBound_le (m : ℕ) : codeBound m≤polynomial.eval m := by
  have h := Nat.mul_le_mul_left (m+2) (weightSize_le m)
  simpa [polynomial,codeBound] using Nat.add_le_add_right (Nat.add_le_add_right h (4*(m+1))) 2


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationCode
end
