import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-! Exact removal of three nonzero weights. Repeated monomial values remain
repeated factors. No ordering, positivity, modulus, or root-of-unity test is
used, and all coefficients remain in the original field. The oracle samples
use strictly positive powers only. This module proves finite algebra, not a
machine reduction or a counting-hardness theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportAnnihilator
open scoped BigOperators
open Polynomial

variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev Grid (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin (n+1)

def monomial (a b c : K) {n : ℕ} (i : Grid n) : K :=
  a^i.1.val * b^i.2.1.val * c^i.2.2.val

theorem monomial_ne_zero {a b c : K} (ha : a≠0) (hb : b≠0) (hc : c≠0)
    {n : ℕ} (i : Grid n) : monomial a b c i≠0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)) (pow_ne_zero _ hc)

/-- A support indicator on the finite multiplicity spectrum. Collisions are
harmless, so no deduplication or field-equality branch is required. -/
def polynomial (n : ℕ) (a b c : K) : K[X] :=
  1-∏i : Grid n, (1-C ((monomial a b c i)⁻¹)*X)

theorem eval_polynomial (n : ℕ) (a b c t : K) :
    (polynomial n a b c).eval t =
      1-∏i : Grid n, (1-(monomial a b c i)⁻¹*t) := by
  simp [polynomial,eval_prod]

@[simp] theorem eval_zero (n : ℕ) (a b c : K) :
    (polynomial n a b c).eval 0=0 := by simp [eval_polynomial]

@[simp] theorem coeff_zero (n : ℕ) (a b c : K) :
    (polynomial n a b c).coeff 0=0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact eval_zero n a b c

theorem eval_monomial (n : ℕ) {a b c : K} (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (i : Grid n) : (polynomial n a b c).eval (monomial a b c i)=1 := by
  rw [eval_polynomial]
  have h : (∏j : Grid n, (1-(monomial a b c j)⁻¹*monomial a b c i))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [inv_mul_cancel₀ (monomial_ne_zero ha hb hc i),sub_self]
  rw [h,sub_zero]

theorem natDegree_le (n : ℕ) (a b c : K) :
    (polynomial n a b c).natDegree ≤ (n+1)^3 := by
  unfold polynomial
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · apply (natDegree_prod_le _ _).trans
    calc
      (∑i : Grid n,(1-C ((monomial a b c i)⁻¹)*X).natDegree) ≤
          ∑_i : Grid n,1 := by
        apply Finset.sum_le_sum
        intro i _
        apply (natDegree_sub_le _ _).trans
        apply max_le
        · simp
        · exact natDegree_mul_le.trans (by simp)
      _ = (n+1)^3 := by simp [Grid,pow_succ,Nat.mul_assoc]

def filtered (n : ℕ) (a b c t : K) : K :=
  ∑k ∈ Finset.range (polynomial n a b c).natDegree,
    (polynomial n a b c).coeff (k+1)*t^(k+1)

theorem filtered_eq_eval (n : ℕ) (a b c t : K) :
    filtered n a b c t=(polynomial n a b c).eval t := by
  rw [Polynomial.eval_eq_sum_range,Finset.sum_range_succ']
  simp [filtered]

/-- A literal finite linear combination of positive-power partition sums.
The supplied spectrum premise only identifies the summands; it is not a
hardness, reduction, realization, or interpolation-success assumption. -/
theorem count_nonzero {A : Type*} [Fintype A] (w : A→K) (n : ℕ)
    {a b c : K} (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hs : ∀x,w x≠0→∃i : Grid n,w x=monomial a b c i) :
    (∑x,if w x=0 then (0 : K) else 1)=
      ∑k ∈ Finset.range (polynomial n a b c).natDegree,
        (polynomial n a b c).coeff (k+1)*(∑x,w x^(k+1)) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [←filtered,filtered_eq_eval]
  by_cases hx : w x=0
  · simp [hx]
  · obtain ⟨i,hi⟩ := hs x hx
    rw [ite_eq_right hx,hi,eval_monomial n ha hb hc]

theorem product_exponents {n : ℕ} (f : Fin n→K) (a b c : K)
    (hf : ∀i,f i=a ∨ f i=b ∨ f i=c) :
    ∃i j k : ℕ,i+j+k=n ∧ (∏v,f v)=a^i*b^j*c^k := by
  induction n with
  | zero => exact ⟨0,0,0,by simp⟩
  | succ n ih =>
    obtain ⟨i,j,k,hs,hv⟩ := ih (fun v=>f v.succ) (fun v=>hf v.succ)
    rw [Fin.prod_univ_succ,hv]
    rcases hf 0 with ha|hb|hc
    · refine ⟨i+1,j,k,by omega,?_⟩
      rw [ha,pow_succ]
      ring
    · refine ⟨i,j+1,k,by omega,?_⟩
      rw [hb,pow_succ]
      ring
    · refine ⟨i,j,k+1,by omega,?_⟩
      rw [hc,pow_succ]
      ring

/-- The finite spectrum is derived directly from the three original values. -/
theorem product_spectrum {n : ℕ} (f : Fin n→K) (a b c : K)
    (hf : ∀i,f i=0 ∨ f i=a ∨ f i=b ∨ f i=c)
    (hz : (∏v,f v)≠0) : ∃i : Grid n,(∏v,f v)=monomial a b c i := by
  have hnonzero (v : Fin n) : f v≠0 :=
    (Finset.prod_ne_zero_iff.mp hz) v (Finset.mem_univ v)
  have hchoices (v : Fin n) : f v=a ∨ f v=b ∨ f v=c :=
    (hf v).resolve_left (hnonzero v)
  obtain ⟨i,j,k,hs,hv⟩ := product_exponents f a b c hchoices
  exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩,⟨k,by omega⟩),hv⟩

/-- Arbitrary finite Boolean CSP assignment spaces are allowed, including
isolated variables. At most (n+1)^3 positive Hadamard-power answers suffice. -/
theorem count_constraints {A : Type*} [Fintype A] {n : ℕ}
    (f : A→Fin n→K) {a b c : K} (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hf : ∀x i,f x i=0 ∨ f x i=a ∨ f x i=b ∨ f x i=c) :
    (∑x,if (∏i,f x i)=0 then (0 : K) else 1)=
      ∑k ∈ Finset.range (polynomial n a b c).natDegree,
        (polynomial n a b c).coeff (k+1)*(∑x,∏i,(f x i)^(k+1)) := by
  have h := count_nonzero (fun x=>∏i,f x i) n ha hb hc
    (fun x hz=>product_spectrum (f x) a b c (hf x) hz)
  simpa only [Finset.prod_pow] using h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportAnnihilator
