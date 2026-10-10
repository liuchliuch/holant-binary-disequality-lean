import Holant.Proofs.Hardness.BinaryThreeSupportGates
import Mathlib.LinearAlgebra.Lagrange

/-! Finite exact removal of signed independent-set vertices by ordinary
unweighted stars. The polynomial records unselected marked vertices, so the
nodes are the integers 2^k and the sole final correction is (-1)^m. All
arithmetic remains in any original characteristic-zero coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStars
open scoped BigOperators
open Polynomial
namespace G
export BinaryThreeSupportGates (nand sign)
end G

variable {K : Type*} [Field K]

def zeros {m : ℕ} (x : Fin m→Bool) : ℕ := (Finset.univ.filter (fun i=>x i=false)).card

theorem zeros_le {m : ℕ} (x : Fin m→Bool) : zeros x≤m := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin m)

/-- k independently summed fresh leaves on a marked vertex. -/
def star (k : ℕ) (x : Bool) : K :=
  ∑y : Fin k→Bool,∏i,G.nand x (y i)

theorem star_exact (k : ℕ) (x : Bool) :
    star (K:=K) k x=if x then 1 else 2^k := by
  rw [star,←Fintype.prod_sum]
  cases x <;> simp [G.nand,Fintype.sum_bool]

theorem star_product {m : ℕ} (k : ℕ) (x : Fin m→Bool) :
    (∏i,star (K:=K) k (x i))=(2^k : K)^zeros x := by
  simp only [star_exact]
  have he (i : Fin m) : (if x i then (1 : K) else 2^k)=
      if x i=false then (2^k : K) else 1 := by cases x i <;> rfl
  simp_rw [he]
  rw [←Finset.prod_filter]
  simp [zeros]

variable {A : Type*} [Fintype A] {m : ℕ}

def polynomial (base : A→K) (bits : A→Fin m→Bool) : K[X] :=
  ∑x,Polynomial.monomial (zeros (bits x)) (base x)

theorem polynomial_eval (base : A→K) (bits : A→Fin m→Bool) (t : K) :
    (polynomial base bits).eval t=∑x,base x*t^zeros (bits x) := by
  simp [polynomial,eval_finsetSum]

theorem polynomial_natDegree_le (base : A→K) (bits : A→Fin m→Bool) :
    (polynomial base bits).natDegree≤m := by
  unfold polynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  exact (Polynomial.natDegree_monomial_le (base x)).trans (zeros_le (bits x))

/-- An actual sum over m*k fresh leaf choices, grouped by marked vertex. -/
def sample (base : A→K) (bits : A→Fin m→Bool) (k : ℕ) : K :=
  ∑x,∑leaves : Fin m→Fin k→Bool,base x*(∏i,∏j,G.nand (bits x i) (leaves i j))

theorem sample_exact (base : A→K) (bits : A→Fin m→Bool) (k : ℕ) :
    sample base bits k=(polynomial base bits).eval (2^k) := by
  rw [polynomial_eval]
  apply Finset.sum_congr rfl
  intro x _
  rw [←Finset.mul_sum]
  rw [←Fintype.prod_sum (fun i : Fin m=>fun l : Fin k→Bool=>
    ∏j,G.nand (bits x i) (l j))]
  congr 1
  exact star_product k (bits x)

theorem minus_one_product {m : ℕ} (x : Fin m→Bool) :
    (∏i,G.sign (K:=K) (x i))=(-1 : K)^m * (-1)^zeros x := by
  have he (i : Fin m) : G.sign (K:=K) (x i)=
      (-1)*(if x i=false then (-1 : K) else 1) := by
    cases x i <;> simp [G.sign]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  rw [←Finset.prod_filter]
  simp [zeros]

def signed (base : A→K) (bits : A→Fin m→Bool) : K :=
  ∑x,base x*(∏i,G.sign (bits x i))

theorem signed_exact (base : A→K) (bits : A→Fin m→Bool) :
    signed base bits=(-1 : K)^m*(polynomial base bits).eval (-1) := by
  simp only [signed,minus_one_product,polynomial_eval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

variable [CharZero K]

theorem nodes_injective : Function.Injective (fun k : ℕ=>(2 : K)^k) := by
  intro i j h
  apply Nat.pow_right_injective (a:=2) (by omega)
  apply Nat.cast_injective (R:=K)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

/-- Exactly m+1 explicit unweighted star values recover the signed sum.
The Lagrange basis consists only of field additions, multiplications and
division by the proved nonzero differences of the distinct integer nodes. -/
theorem signed_interpolation (base : A→K) (bits : A→Fin m→Bool) :
    signed base bits=(-1 : K)^m*
      (∑k ∈ Finset.range (m+1),sample base bits k *
        (Lagrange.basis (Finset.range (m+1)) (fun j : ℕ=>(2 : K)^j) k).eval (-1)) := by
  rw [signed_exact]
  congr 1
  have hd : (polynomial base bits).degree < ((Finset.range (m+1)).card : ℕ) := by
    rw [Finset.card_range]
    exact (Polynomial.degree_le_natDegree).trans_lt
      (by exact_mod_cast (lt_of_le_of_lt (polynomial_natDegree_le base bits) (Nat.lt_succ_self m)))
  have hi := Lagrange.eq_interpolate
    (s:=Finset.range (m+1)) (v:=fun j : ℕ=>(2 : K)^j)
    nodes_injective.injOn hd
  rw [hi,Lagrange.interpolate_apply,eval_finsetSum]
  simp only [eval_mul,eval_C,sample_exact]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStars
