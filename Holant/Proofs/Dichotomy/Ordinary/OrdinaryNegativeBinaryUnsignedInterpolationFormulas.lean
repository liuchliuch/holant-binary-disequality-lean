import Holant.Complexity.BinaryInterpolation.WeightFormulaBounds
import Holant.Complexity.BinaryInterpolation.CommonDenominator
import Holant.Proofs.Hardness.BinaryThreeSupportStarCommon

/-! Lagrange evaluation at an arbitrary fixed original-field unary weight.
The samples have genuine geometric nodes and their original scale powers.
Four literal labels suffice: gamma, rho, minus one, and the target weight. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeBinaryUnsignedInterpolationFormulas
open Holant.Complexity.BinaryInterpolation
open RingFormula
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

abbrev Formula := RingFormula (Fin 4)

def difference (j : ℕ) : Formula := .add (.literal 3) (.mul (.literal 2) (WeightFormulas.node true (j+1)))
def numerator (m : ℕ) (i : Fin (m+1)) : Formula := without (fun j=>difference j.val) i
def weight (m : ℕ) (i : Fin (m+1)) : Formula := .mul (numerator m i) (WeightFormulas.weight true m i)
abbrev totalDenominator (m : ℕ) : Formula := WeightFormulas.totalDenominator true m

variable {K : Type*} [Field K]
def coefficients (gamma rho target : K) : Fin 4→K := ![gamma,rho,-1,target]
def nodes (rho : K) (m : ℕ) (i : Fin (m+1)) : K := rho^(i.val+1)
def divisors (gamma rho : K) (m : ℕ) (i : Fin (m+1)) : K :=
  gamma^((i.val+1)*m)*(∏j∈Finset.univ.erase i,(nodes rho m i-nodes rho m j))
def numerators (rho target : K) (m : ℕ) (i : Fin (m+1)) : K :=
  ∏j∈Finset.univ.erase i,(target-nodes rho m j)

@[simp] theorem eval_node (j : ℕ) (gamma rho target : K) :
    (WeightFormulas.node true j).eval (coefficients gamma rho target)=rho^j := by
  simp [WeightFormulas.node,coefficients,eval]

@[simp] theorem eval_difference (j : ℕ) (gamma rho target : K) :
    (difference j).eval (coefficients gamma rho target)=target-rho^(j+1) := by
  simp only [difference,eval,eval_node]
  simp [coefficients,sub_eq_add_neg]

@[simp] theorem eval_denominator (m : ℕ) (i : Fin (m+1)) (gamma rho target : K) :
    (WeightFormulas.denominator true m i).eval (coefficients gamma rho target)=divisors gamma rho m i := by
  simp only [WeightFormulas.denominator,eval,eval_power,eval_without,eval_node]
  simp [coefficients,divisors,nodes,sub_eq_add_neg]

@[simp] theorem eval_numerator (m : ℕ) (i : Fin (m+1)) (gamma rho target : K) :
    (numerator m i).eval (coefficients gamma rho target)=numerators rho target m i := by
  simp [numerator,numerators,nodes]

@[simp] theorem eval_weight (m : ℕ) (i : Fin (m+1)) (gamma rho target : K) :
    (weight m i).eval (coefficients gamma rho target)=numerators rho target m i*
      ∏j∈Finset.univ.erase i,divisors gamma rho m j := by
  simp only [weight,eval,eval_numerator,WeightFormulas.weight,eval_without,eval_denominator]

@[simp] theorem eval_totalDenominator (m : ℕ) (gamma rho target : K) :
    (totalDenominator m).eval (coefficients gamma rho target)=commonDenominator (divisors gamma rho m) := by
  simp only [totalDenominator,WeightFormulas.totalDenominator,eval_prodList,List.map_ofFn,
    Fin.prod_ofFn,Function.comp_apply,eval_denominator,commonDenominator]

theorem divisors_ne_zero (gamma rho : K) (m : ℕ) (hg : gamma≠0)
    (hi : Function.Injective (nodes rho m)) (i : Fin (m+1)) : divisors gamma rho m i≠0 := by
  apply mul_ne_zero (pow_ne_zero _ hg)
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (fun h=>(Finset.mem_erase.mp hj).1 (hi h).symm)

theorem basis_eval (rho target : K) (m : ℕ) (i : Fin (m+1)) :
    (Lagrange.basis Finset.univ (nodes rho m) i).eval target=
      numerators rho target m i/(∏j∈Finset.univ.erase i,(nodes rho m i-nodes rho m j)) := by
  simp only [Lagrange.basis,Lagrange.basisDivisor,Polynomial.eval_prod,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_X,Finset.prod_mul_distrib]
  simp only [numerators,div_eq_mul_inv,Finset.prod_inv_distrib]
  exact mul_comm _ _

/-- The exact common-denominator result consumed by the finite interpreter. -/
theorem recover (gamma rho target : K) (m : ℕ) (hg : gamma≠0)
    (hi : Function.Injective (nodes rho m)) (p : Polynomial K) (hd : p.natDegree≤m) :
    commonNumerator (divisors gamma rho m)
      (fun i=>gamma^((i.val+1)*m)*p.eval (nodes rho m i)*numerators rho target m i) /
      commonDenominator (divisors gamma rho m)=p.eval target := by
  have hdeg : p.degree<((Finset.univ : Finset (Fin (m+1))).card : ℕ) := by
    rw [Finset.card_univ,Fintype.card_fin]
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hd)
  have hp := Lagrange.eq_interpolate (s:=(Finset.univ : Finset (Fin (m+1))))
    (v:=nodes rho m) hi.injOn hdeg
  have hpEval := congrArg (fun q : Polynomial K=>q.eval target) hp
  rw [Lagrange.interpolate_apply,Polynomial.eval_finsetSum] at hpEval
  simp only [Polynomial.eval_mul,Polynomial.eval_C,basis_eval] at hpEval
  rw [hpEval]
  rw [←sum_div_common _ _ (divisors_ne_zero gamma rho m hg hi)]
  apply Finset.sum_congr rfl
  intro i _
  have hz : gamma^((i.val+1)*m)≠0 := pow_ne_zero _ hg
  simp only [divisors,div_eq_mul_inv,mul_inv_rev]
  field_simp

/-- No root enumeration premise is needed for geometric interpolation. -/
theorem nodes_injective (rho : K) (hr : rho≠0) (hinf : ∀k : ℕ,0<k → rho^k≠1) (m : ℕ) :
    Function.Injective (nodes rho m) := geometric_nodes_injective rho hr hinf

def numeratorSize (m : ℕ) : ℕ := (m+1)*(2*m+8)+1
def weightSize (m : ℕ) : ℕ := numeratorSize m+WeightFormulas.weightSize m+1

theorem numerator_size (m : ℕ) (i : Fin (m+1)) : (numerator m i).size≤numeratorSize m := by
  apply size_without_le _ _ (2*m+7) (by omega)
  intro j
  have hj := j.isLt
  simp only [difference,size,WeightFormulas.node_size]
  omega

theorem weight_size (m : ℕ) (i : Fin (m+1)) : (weight m i).size≤weightSize m := by
  have hn := numerator_size m i
  have hw := WeightFormulas.weight_size_le true m i
  simp only [weight,size,weightSize]
  omega

theorem totalDenominator_size (m : ℕ) : (totalDenominator m).size≤weightSize m :=
  (WeightFormulas.totalDenominator_size_le true m).trans (by unfold weightSize; omega)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeBinaryUnsignedInterpolationFormulas
end
