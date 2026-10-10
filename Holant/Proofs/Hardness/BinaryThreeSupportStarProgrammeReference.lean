import Holant.Proofs.Hardness.BinaryThreeSupportStarProgrammeFormulas
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Reference

namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarProgramme
open Holant.Complexity.BinaryInterpolation
open Holant.OneHot.StackProgram RingFormula
abbrev Code := Holant.OneHot.StackProgram.Code (Fin 4)

def reference (m : ℕ) : Code := [.zero] ++ WeightedStack.code (List.ofFn (weight m)) ++
  (totalDenominator m).code ++ [.swap]
def differenceCode (i j : ℕ) : Code := WeightCompiler.nodeCode true j ++ [.literal 2,.mul] ++
  WeightCompiler.nodeCode true i ++ [.add]
def negativeCode (j : ℕ) : Code := WeightCompiler.nodeCode true j ++ [.literal 2,.mul,.literal 2,.add]
def divisorCode (m i : ℕ) : Code := [.one] ++ (List.range (m+1)).reverse.flatMap
  (fun j=>(if j=i then [.one] else differenceCode i j) ++ [.mul])
def numeratorCode (m i : ℕ) : Code := [.one] ++ (List.range (m+1)).reverse.flatMap
  (fun j=>(if j=i then [.one] else negativeCode j) ++ [.mul])
def outerCode (m i : ℕ) : Code := [.one] ++ (List.range (m+1)).reverse.flatMap
  (fun j=>(if j=i then [.one] else divisorCode m j) ++ [.mul])
def weightCode (m i : ℕ) : Code := outerCode m i ++ numeratorCode m i ++ [.mul] ++
  [.one] ++ (List.replicate m [.literal 2,.mul]).flatten ++ [.mul]
def totalDenominatorCode (m : ℕ) : Code := [.one] ++ (List.range (m+1)).reverse.flatMap
  (fun i=>divisorCode m i ++ [.mul])
def generatedCode (m : ℕ) : Code := [.zero] ++ (List.range (m+1)).flatMap
  (fun i=>weightCode m i ++ [.copy 2,.mul,.add,.erase 1]) ++ totalDenominatorCode m ++ [.swap]

theorem node_code (t : ℕ) : (node t).code=WeightCompiler.nodeCode true t := by
  simp [node,WeightCompiler.nodeCode,WeightCompiler.power_code,code]
theorem difference_code (i j : ℕ) : (difference i j).code=differenceCode i j := by
  simp [difference,differenceCode,code,node_code,List.append_assoc]
theorem negative_code (j : ℕ) : (negative j).code=negativeCode j := by
  simp [negative,negativeCode,code,node_code,List.append_assoc]

theorem divisor_code (m : ℕ) (i : Fin (m+1)) : (divisor m i).code=divisorCode m i.val := by
  simp only [divisor,without,WeightCompiler.prodList_code]
  rw [WeightCompiler.ofFn_code_flatMap
    (f:=fun j=>if j=i.val then [.one] else differenceCode i.val j)]
  · rfl
  · intro j
    by_cases h : j=i
    · subst j; simp [code]
    · have hv : j.val≠i.val := fun e=>h (Fin.ext e)
      simp [h,hv,difference_code]

theorem numerator_code (m : ℕ) (i : Fin (m+1)) : (numerator m i).code=numeratorCode m i.val := by
  simp only [numerator,without,WeightCompiler.prodList_code]
  rw [WeightCompiler.ofFn_code_flatMap
    (f:=fun j=>if j=i.val then [.one] else negativeCode j)]
  · rfl
  · intro j
    by_cases h : j=i
    · subst j; simp [code]
    · have hv : j.val≠i.val := fun e=>h (Fin.ext e)
      simp [h,hv,negative_code]

theorem outer_code (m : ℕ) (i : Fin (m+1)) : (without (divisor m) i).code=outerCode m i.val := by
  simp only [without,WeightCompiler.prodList_code]
  rw [WeightCompiler.ofFn_code_flatMap
    (f:=fun j=>if j=i.val then [.one] else divisorCode m j)]
  · rfl
  · intro j
    by_cases h : j=i
    · subst j; simp [code]
    · have hv : j.val≠i.val := fun e=>h (Fin.ext e)
      simp [h,hv,divisor_code]

theorem weight_code (m : ℕ) (i : Fin (m+1)) : (weight m i).code=weightCode m i.val := by
  simp [weight,code,outer_code,numerator_code,WeightCompiler.power_code,weightCode,List.append_assoc]
theorem totalDenominator_code (m : ℕ) : (totalDenominator m).code=totalDenominatorCode m := by
  simp only [totalDenominator,WeightCompiler.prodList_code]
  rw [WeightCompiler.ofFn_code_flatMap _ _ (divisor_code m)]
  rfl
theorem generated_eq_reference (m : ℕ) : generatedCode m=reference m := by
  simp only [reference,WeightCompiler.weighted_code,totalDenominator_code,List.ofFn_eq_map,
    List.flatMap_map,Function.comp_def,weight_code]
  unfold generatedCode
  rw [←List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarProgramme
