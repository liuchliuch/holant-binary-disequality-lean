import Holant.Complexity.BinaryInterpolation.FormulaProducts

/-! Explicit division-free weight formulas for both spectral alternatives.
The only literal labels are gamma,rho,-1,1, fixed before an input arrives. -/
namespace Holant.Complexity.BinaryInterpolation.WeightFormulas
open RingFormula
open scoped BigOperators

abbrev Formula := RingFormula (Fin 4)

def node (geometric : Bool) (t : ℕ) : Formula :=
  if geometric then (.literal 1 : Formula).power t else sumList (List.replicate t .one)

def denominator (geometric : Bool) (m : ℕ) (i : Fin (m+1)) : Formula :=
  .mul ((.literal 0 : Formula).power ((i.val+1)*m))
    (without (fun j : Fin (m+1) =>
      .add (node geometric (i.val+1)) (.mul (.literal 2) (node geometric (j.val+1)))) i)

def weight (geometric : Bool) (m : ℕ) (i : Fin (m+1)) : Formula :=
  without (denominator geometric m) i

def totalDenominator (geometric : Bool) (m : ℕ) : Formula :=
  prodList (List.ofFn (denominator geometric m))

variable {K : Type*} [Field K]

def coefficients (gamma rho : K) : Fin 4→K := ![gamma,rho,-1,1]
def nodes (geometric : Bool) (rho : K) (m : ℕ) (i : Fin (m+1)) : K :=
  if geometric then rho^(i.val+1) else ((i.val+1:ℕ):K)
def scales (gamma : K) (m : ℕ) (i : Fin (m+1)) : K := gamma^(i.val+1)

@[simp] theorem eval_node (geometric : Bool) (t : ℕ) (gamma rho : K) :
    (node geometric t).eval (coefficients gamma rho)=
      if geometric then rho^t else (t:K) := by
  cases geometric <;> simp [node,coefficients,eval,eval_power,eval_sumList,List.sum_replicate]

theorem eval_denominator (geometric : Bool) (m : ℕ) (i : Fin (m+1)) (gamma rho : K) :
    (denominator geometric m i).eval (coefficients gamma rho)=
      queryDenominator (nodes geometric rho m) (scales gamma m) i := by
  simp only [denominator,eval,eval_power,eval_without,eval_node]
  simp only [coefficients,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    queryDenominator,scales,interpolationDenominator,nodes,pow_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  cases geometric <;> simp [eval,coefficients,sub_eq_add_neg,add_comm]

theorem eval_weight (geometric : Bool) (m : ℕ) (i : Fin (m+1)) (gamma rho : K) :
    (weight geometric m i).eval (coefficients gamma rho)=
      ∏j∈Finset.univ.erase i,queryDenominator (nodes geometric rho m) (scales gamma m) j := by
  simp only [weight,eval_without,eval_denominator]

theorem eval_totalDenominator (geometric : Bool) (m : ℕ) (gamma rho : K) :
    (totalDenominator geometric m).eval (coefficients gamma rho)=
      commonDenominator (queryDenominator (nodes geometric rho m) (scales gamma m)) := by
  simp only [totalDenominator,eval_prodList,List.map_ofFn,Fin.prod_ofFn,
    Function.comp_apply,eval_denominator,commonDenominator]

end Holant.Complexity.BinaryInterpolation.WeightFormulas
