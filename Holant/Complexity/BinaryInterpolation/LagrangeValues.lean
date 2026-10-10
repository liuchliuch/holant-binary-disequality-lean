import Holant.Complexity.BinaryInterpolation.NetworkPolynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.GroupTheory.OrderOfElement

/-! Exact m+1-value recovery for the actual network polynomial. The finite
formula is explicit field arithmetic; a machine implementation and actual
chain-query realization are separate source3.1 obligations. -/
namespace Holant.Complexity.BinaryInterpolation
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {m n : ℕ}

def interpolationDenominator (nodes : Fin (m+1)→K) (i : Fin (m+1)) : K :=
  ∏ j ∈ Finset.univ.erase i, (nodes i - nodes j)

def recoverTop (nodes values : Fin (m+1)→K) : K :=
  ∑i,values i/interpolationDenominator nodes i

theorem interpolationDenominator_ne_zero (nodes : Fin (m+1)→K)
    (hi : Function.Injective nodes) (i : Fin (m+1)) : interpolationDenominator nodes i≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  exact (Finset.mem_erase.mp hj).1 (hi he).symm

theorem denominator_factors (i : Fin (m+1)) :
    (Finset.univ.erase i).card=m := by simp

theorem recoverTop_eq_coefficient (nodes : Fin (m+1)→K) (hi : Function.Injective nodes)
    (P : Polynomial K) (hP : P.natDegree≤m) :
    recoverTop nodes (fun i => P.eval (nodes i))=P.coeff m := by
  have hd : P.degree < ((Finset.univ : Finset (Fin (m+1))).card : ℕ) := by
    simp only [Finset.card_univ,Fintype.card_fin]
    calc
      P.degree ≤ (P.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (m : WithBot ℕ) := by exact_mod_cast hP
      _ < ((m+1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self m
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) (v := nodes) hi.injOn hd
  simpa [recoverTop,interpolationDenominator] using h.symm

/-- Recover the literal all-right designated-occurrence network from exactly
m+1 evaluations, where m is the number of original marked vertices. -/
theorem network_interpolation (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (L R : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
    (x : Fin n→Bool) (nodes : Fin (S.card+1)→K) (hi : Function.Injective nodes) :
    recoverTop nodes (fun i => (pencilNetwork N S L R (nodes i)).denote x)=
      (rightNetwork N S R).denote x := by
  have h := recoverTop_eq_coefficient nodes hi (networkPolynomial N S L R x)
    (networkPolynomial_degree N S L R x)
  simpa only [networkPolynomial_eval,networkPolynomial_top_coefficient] using h

/-- Non-root-of-unity geometric nodes at the positive exponents1,...,m+1
are pairwise distinct, with no analytic or numerical approximation. -/
theorem geometric_nodes_injective (rho : K) (hr : rho≠0)
    (hinf : ∀r : ℕ,0<r → rho^r≠1) :
    Function.Injective (fun i : Fin (m+1) => rho^(i.val+1)) := by
  have hu : ¬IsOfFinOrder (Units.mk0 rho hr) := by
    intro h
    obtain ⟨r,hr0,he⟩ := h.exists_pow_eq_one
    exact hinf r hr0 (by simpa using congrArg Units.val he)
  have hp : Function.Injective (fun r : ℕ => (Units.mk0 rho hr)^r) :=
    injective_pow_iff_not_isOfFinOrder.mpr hu
  intro i j he
  have h := hp (show (Units.mk0 rho hr)^(i.val+1)=(Units.mk0 rho hr)^(j.val+1) from Units.ext he)
  exact Fin.ext (Nat.add_right_cancel h)

end
end Holant.Complexity.BinaryInterpolation
