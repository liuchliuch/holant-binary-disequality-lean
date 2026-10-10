import Holant.Proofs.AlgebraicRecognition.WitnessOutput.BranchConsumers.Recovery
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.API
import Mathlib.Algebra.Polynomial.Coeff


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
open Polynomial
open BranchConsumers (decodeList)

namespace Code
abbrev Poly := RationalPolynomialCode

def neg (p : Poly) : Poly := p.map (fun t => (t.1,-t.2))
def sub (p q : Poly) : Poly := p ++ neg q
def termMul (t u : ℕ × ℚ) : ℕ × ℚ := (t.1+u.1,t.2*u.2)
def mul (p q : Poly) : Poly := p.flatMap (fun t => q.map (termMul t))
def one : Poly := [(0,1)]
def power (p : Poly) : ℕ → Poly
  | 0 => one
  | k+1 => mul (power p k) p
def product (ps : List Poly) : Poly := ps.foldr mul one

def coeff (p : Poly) (k : ℕ) : ℚ :=
  (p.map (fun t => if t.1=k then t.2 else 0)).sum
def isZero (p : Poly) : Bool := p.all (fun t => decide (coeff p t.1=0))
def equal (p q : Poly) : Bool := isZero (sub p q)
def dense (v : List ℚ) : Poly :=
  (List.range v.length).map (fun i => (i,v.getD i 0))

theorem polynomial_sum (p : Poly) :
    p.polynomial=(p.map (fun t => Polynomial.monomial t.1 t.2)).sum := by
  induction p with
  | nil => rfl
  | cons t ts ih => cases t; simp [RationalPolynomialCode.polynomial,ih]

@[simp] theorem polynomial_neg (p : Poly) : (neg p).polynomial= -p.polynomial := by
  induction p with
  | nil => simp [neg,RationalPolynomialCode.polynomial]
  | cons t ts ih =>
    rcases t with ⟨n,q⟩
    change Polynomial.monomial n (-q) + RationalPolynomialCode.polynomial (neg ts) =
      -(Polynomial.monomial n q + RationalPolynomialCode.polynomial ts)
    rw [ih,Polynomial.monomial_neg,neg_add]

@[simp] theorem polynomial_sub (p q : Poly) :
    (sub p q).polynomial=p.polynomial-q.polynomial := by
  simp [sub,sub_eq_add_neg]

theorem polynomial_row (t : ℕ × ℚ) (q : Poly) :
    RationalPolynomialCode.polynomial (q.map (termMul t))=
      Polynomial.monomial t.1 t.2*q.polynomial := by
  induction q with
  | nil => simp [RationalPolynomialCode.polynomial]
  | cons u us ih =>
    rcases t with ⟨k,a⟩
    rcases u with ⟨l,b⟩
    change Polynomial.monomial (k+l) (a*b) +
        RationalPolynomialCode.polynomial (us.map (termMul (k,a))) =
      Polynomial.monomial k a *
        (Polynomial.monomial l b + RationalPolynomialCode.polynomial us)
    rw [ih,mul_add,Polynomial.monomial_mul_monomial]

@[simp] theorem polynomial_mul (p q : Poly) :
    (mul p q).polynomial=p.polynomial*q.polynomial := by
  induction p with
  | nil => simp [mul,RationalPolynomialCode.polynomial]
  | cons t ts ih =>
    rcases t with ⟨k,a⟩
    change RationalPolynomialCode.polynomial ((q.map (termMul (k,a))) ++ mul ts q) =
      (Polynomial.monomial k a + RationalPolynomialCode.polynomial ts)*q.polynomial
    rw [RationalPolynomialCode.polynomial_append,polynomial_row,ih,add_mul]

@[simp] theorem polynomial_one : one.polynomial=(1 : ℚ[X]) := by
  simp [one,RationalPolynomialCode.polynomial]
@[simp] theorem polynomial_power (p : Poly) (k : ℕ) :
    (power p k).polynomial=p.polynomial^k := by
  induction k with
  | zero => simp [power]
  | succ k ih => simp [power,ih,pow_succ]
@[simp] theorem polynomial_product (ps : List Poly) :
    (product ps).polynomial=(ps.map RationalPolynomialCode.polynomial).prod := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih => simpa [product] using congrArg (p.polynomial*·) ih

theorem coeff_correct (p : Poly) (k : ℕ) : coeff p k=p.polynomial.coeff k := by
  induction p with
  | nil => simp [coeff,RationalPolynomialCode.polynomial]
  | cons t ts ih =>
    rcases t with ⟨n,q⟩
    change (if n=k then q else 0)+coeff ts k=
      (Polynomial.monomial n q+RationalPolynomialCode.polynomial ts).coeff k
    rw [Polynomial.coeff_add,Polynomial.coeff_monomial,ih]

theorem coeff_eq_zero_of_absent (p : Poly) (k : ℕ)
    (h : ∀ t ∈ p, t.1≠k) : coeff p k=0 := by
  apply List.sum_eq_zero
  intro q hq
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hq
  simp [h t ht]

theorem isZero_iff (p : Poly) : isZero p=true ↔ p.polynomial=0 := by
  constructor
  · intro h
    have hz : ∀ t ∈ p, coeff p t.1=0 := by simpa [isZero] using h
    apply Polynomial.ext
    intro k
    by_cases hk : ∃ t ∈ p, t.1=k
    · obtain ⟨t,ht,rfl⟩ := hk
      simpa only [Polynomial.coeff_zero] using (coeff_correct p t.1).symm.trans (hz t ht)
    · have ha : ∀ t ∈ p, t.1≠k := by
        intro t ht he
        exact hk ⟨t,ht,he⟩
      simpa only [Polynomial.coeff_zero] using
        (coeff_correct p k).symm.trans (coeff_eq_zero_of_absent p k ha)
  · intro h
    simp only [isZero,List.all_eq_true,decide_eq_true_eq]
    intro t ht
    rw [coeff_correct,h,Polynomial.coeff_zero]

theorem equal_iff (p q : Poly) : equal p q=true ↔ p.polynomial=q.polynomial := by
  rw [equal,isZero_iff,polynomial_sub,sub_eq_zero]

theorem dense_correct {K : Type*} [Field K] [Algebra ℚ K] (z : K) (v : List ℚ) :
    Polynomial.aeval z (dense v).polynomial=decodeList z v := by
  rw [polynomial_sum,map_list_sum]
  simp only [dense,List.map_map,Function.comp_def,Polynomial.aeval_monomial,
    decodeList,Algebra.smul_def]

end Code
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
