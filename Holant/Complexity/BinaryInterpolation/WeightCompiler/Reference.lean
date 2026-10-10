import Holant.Complexity.BinaryInterpolation.WeightFormulaBounds
import Holant.Complexity.BinaryInterpolation.WeightedStack
import Holant.Complexity.GraphPreprocessing.SignatureLabel

/-! The exact postprocessor syntax and its loop-shaped serialization. -/
namespace Holant.Complexity.BinaryInterpolation.WeightCompiler
open Holant.OneHot.StackProgram RingFormula

abbrev Code := Holant.OneHot.StackProgram.Code (Fin 4)
def reference (geometric : Bool) (m : ℕ) : Code :=
  [.zero] ++ WeightedStack.code (List.ofFn (WeightFormulas.weight geometric m)) ++
    (WeightFormulas.totalDenominator geometric m).code ++ [.swap]

def nodeCode (geometric : Bool) (t : ℕ) : Code :=
  if geometric then [.one] ++ (List.replicate t [.literal 1,.mul]).flatten
  else [.zero] ++ (List.replicate t [.one,.add]).flatten

def differenceCode (geometric : Bool) (i j : ℕ) : Code :=
  nodeCode geometric (j+1) ++ [.literal 2,.mul] ++ nodeCode geometric (i+1) ++ [.add]

def denominatorCode (geometric : Bool) (m i : ℕ) : Code :=
  [.one] ++ (List.range (m+1)).reverse.flatMap
    (fun j => (if j=i then [.one] else differenceCode geometric i j) ++ [.mul]) ++
    [.one] ++ (List.replicate ((i+1)*m) [.literal 0,.mul]).flatten ++ [.mul]

def weightCode (geometric : Bool) (m i : ℕ) : Code :=
  [.one] ++ (List.range (m+1)).reverse.flatMap
    (fun j => (if j=i then [.one] else denominatorCode geometric m j) ++ [.mul])

def totalDenominatorCode (geometric : Bool) (m : ℕ) : Code :=
  [.one] ++ (List.range (m+1)).reverse.flatMap
    (fun i => denominatorCode geometric m i ++ [.mul])

def generatedCode (geometric : Bool) (m : ℕ) : Code :=
  [.zero] ++ (List.range (m+1)).flatMap
    (fun i => weightCode geometric m i ++ [.copy 2,.mul,.add,.erase 1]) ++
      totalDenominatorCode geometric m ++ [.swap]

theorem power_code (p : RingFormula (Fin 4)) (n : ℕ) :
    (p.power n).code = [.one] ++ (List.replicate n (p.code ++ [.mul])).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [power,code,ih,List.replicate_succ',List.append_assoc]

theorem sum_replicate_one_code (n : ℕ) :
    (sumList (List.replicate n (.one : RingFormula (Fin 4)))).code =
      [.zero] ++ (List.replicate n [.one,.add]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,sumList,code,ih,List.replicate_succ']
    simp [code,List.append_assoc]

theorem node_code (geometric : Bool) (t : ℕ) :
    (WeightFormulas.node geometric t).code = nodeCode geometric t := by
  cases geometric <;> simp [WeightFormulas.node,nodeCode,power_code,sum_replicate_one_code,code]

theorem prodList_code (ps : List (RingFormula (Fin 4))) :
    (prodList ps).code = [.one] ++ ps.reverse.flatMap (fun p => p.code ++ [.mul]) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [prodList,code,ih,List.append_assoc]

theorem ofFn_code_flatMap {n : ℕ} (p : Fin n → RingFormula (Fin 4)) (f : ℕ → Code)
    (h : ∀ i, (p i).code = f i.val) :
    (List.ofFn p).reverse.flatMap (fun q => q.code ++ [.mul]) =
      (List.range n).reverse.flatMap (fun i => f i ++ [.mul]) := by
  rw [List.ofFn_eq_map,←List.map_coe_finRange_eq_range]
  simp only [←List.map_reverse,List.flatMap_map,Function.comp_def]
  apply List.flatMap_congr
  intro i _
  rw [h]

theorem denominator_code (geometric : Bool) (m : ℕ) (i : Fin (m+1)) :
    (WeightFormulas.denominator geometric m i).code = denominatorCode geometric m i.val := by
  simp only [WeightFormulas.denominator,code,without,prodList_code,power_code]
  rw [ofFn_code_flatMap (f := fun j => if j=i.val then [.one] else differenceCode geometric i.val j)]
  · simp [denominatorCode,code,List.append_assoc]
  · intro j
    by_cases h : j=i
    · subst j; simp [code]
    · have hv : j.val ≠ i.val := fun e => h (Fin.ext e)
      simp [h,hv,code,node_code,differenceCode,List.append_assoc]

theorem weight_code (geometric : Bool) (m : ℕ) (i : Fin (m+1)) :
    (WeightFormulas.weight geometric m i).code = weightCode geometric m i.val := by
  simp only [WeightFormulas.weight,without,prodList_code]
  rw [ofFn_code_flatMap (f := fun j => if j=i.val then [.one] else denominatorCode geometric m j)]
  · rfl
  · intro j
    by_cases h : j=i
    · subst j; simp [code]
    · have hv : j.val ≠ i.val := fun e => h (Fin.ext e)
      simp [h,hv,denominator_code]

theorem totalDenominator_code (geometric : Bool) (m : ℕ) :
    (WeightFormulas.totalDenominator geometric m).code = totalDenominatorCode geometric m := by
  simp only [WeightFormulas.totalDenominator,prodList_code]
  rw [ofFn_code_flatMap _ _ (denominator_code geometric m)]
  rfl

theorem weighted_code (ps : List (RingFormula (Fin 4))) :
    WeightedStack.code ps = ps.flatMap (fun p => p.code ++ [.copy 2,.mul,.add,.erase 1]) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [WeightedStack.code,ih,List.append_assoc]

theorem generated_eq_reference (geometric : Bool) (m : ℕ) :
    generatedCode geometric m = reference geometric m := by
  simp only [reference,weighted_code,totalDenominator_code,List.ofFn_eq_map,List.flatMap_map,
    Function.comp_def,weight_code]
  unfold generatedCode
  rw [←List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map]

end Holant.Complexity.BinaryInterpolation.WeightCompiler
