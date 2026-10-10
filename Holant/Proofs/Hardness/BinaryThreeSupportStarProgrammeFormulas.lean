import Holant.Proofs.Hardness.BinaryThreeSupportStarCommon
import Holant.Complexity.BinaryInterpolation.WeightFormulaBounds

/-! Explicit division-free formulas for the signed-star postprocessor. Its
four fixed literal labels have values 1,2,-1,1 in the original field. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarProgramme
open Holant.Complexity.BinaryInterpolation
open RingFormula
open scoped BigOperators
abbrev Formula := RingFormula (Fin 4)

def node (t : ℕ) : Formula := (.literal 1 : Formula).power t
def difference (i j : ℕ) : Formula := .add (node i) (.mul (.literal 2) (node j))
def negative (j : ℕ) : Formula := .add (.literal 2) (.mul (.literal 2) (node j))
def divisor (m : ℕ) (i : Fin (m+1)) : Formula := without (fun j=>difference i.val j.val) i
def numerator (m : ℕ) (i : Fin (m+1)) : Formula := without (fun j=>negative j.val) i
def weight (m : ℕ) (i : Fin (m+1)) : Formula :=
  .mul ((.literal 2 : Formula).power m) (.mul (numerator m i) (without (divisor m) i))
def totalDenominator (m : ℕ) : Formula := prodList (List.ofFn (divisor m))

variable {K : Type*} [Field K]
def coefficients : Fin 4→K := ![1,2,-1,1]

@[simp] theorem eval_node (t : ℕ) : (node t).eval (coefficients (K:=K))=(2 : K)^t := by
  simp [node,coefficients,eval]
@[simp] theorem eval_difference (i j : ℕ) :
    (difference i j).eval (coefficients (K:=K))=(2 : K)^i-2^j := by
  simp only [difference,eval,eval_node]
  simp [coefficients,sub_eq_add_neg]
@[simp] theorem eval_negative (j : ℕ) :
    (negative j).eval (coefficients (K:=K))=(-1 : K)-2^j := by
  simp only [negative,eval,eval_node]
  simp [coefficients,sub_eq_add_neg]
@[simp] theorem eval_divisor (m : ℕ) (i : Fin (m+1)) :
    (divisor m i).eval (coefficients (K:=K))=BinaryThreeSupportStarCommon.divisor i := by
  simp [divisor,BinaryThreeSupportStarCommon.divisor,BinaryThreeSupportStarCommon.node]
@[simp] theorem eval_numerator (m : ℕ) (i : Fin (m+1)) :
    (numerator m i).eval (coefficients (K:=K))=BinaryThreeSupportStarCommon.numerator i := by
  simp [numerator,BinaryThreeSupportStarCommon.numerator,BinaryThreeSupportStarCommon.node]
@[simp] theorem eval_weight (m : ℕ) (i : Fin (m+1)) :
    (weight m i).eval (coefficients (K:=K))=(-1 : K)^m *
      (BinaryThreeSupportStarCommon.numerator i *
        ∏j∈Finset.univ.erase i,BinaryThreeSupportStarCommon.divisor j) := by
  simp only [weight,eval,eval_power,eval_without,eval_numerator,eval_divisor]
  simp [coefficients,eval]
@[simp] theorem eval_totalDenominator (m : ℕ) :
    (totalDenominator m).eval (coefficients (K:=K))=
      commonDenominator (BinaryThreeSupportStarCommon.divisor (K:=K) (m:=m)) := by
  simp only [totalDenominator,eval_prodList,List.map_ofFn,Fin.prod_ofFn,
    Function.comp_def,eval_divisor,commonDenominator]

def divisorSize (m : ℕ) : ℕ := (m+1)*(4*m+6)+1
def outerSize (m : ℕ) : ℕ := (m+1)*(divisorSize m+1)+1
def weightSize (m : ℕ) : ℕ := 2*m+divisorSize m+outerSize m+3

theorem node_size (t : ℕ) : (node t).size=2*t+1 := by simp [node,size_power,size,Nat.mul_comm]
theorem divisor_size (m : ℕ) (i : Fin (m+1)) : (divisor m i).size≤divisorSize m := by
  apply size_without_le _ _ (4*m+5) (by omega)
  intro j
  have hi := i.isLt
  have hj := j.isLt
  simp only [difference,size,node_size]
  omega
theorem numerator_size (m : ℕ) (i : Fin (m+1)) : (numerator m i).size≤divisorSize m := by
  apply size_without_le _ _ (4*m+5) (by omega)
  intro j
  have hj := j.isLt
  simp only [negative,size,node_size]
  omega
theorem outer_size (m : ℕ) (i : Fin (m+1)) : (without (divisor m) i).size≤outerSize m := by
  apply size_without_le
  · unfold divisorSize; omega
  · exact divisor_size m
theorem weight_size (m : ℕ) (i : Fin (m+1)) : (weight m i).size≤weightSize m := by
  have hn := numerator_size m i
  have ho := outer_size m i
  simp only [weight,size,size_power,weightSize] at *
  omega
theorem totalDenominator_size (m : ℕ) : (totalDenominator m).size≤weightSize m := by
  have hh := size_prodList_le (List.ofFn (divisor m)) (divisorSize m)
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact divisor_size m i)
  simp only [List.length_ofFn] at hh
  exact hh.trans (by unfold weightSize outerSize; omega)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarProgramme
