import Holant.Proofs.Hardness.EOBinaryPlaneIsing
import Holant.Proofs.Hardness.EOBinaryPlaneOrient

/-! A single unpinned apex turns positive zero-field Ising into a one-variable
independent-set spectrum. Each original edge contributes two apex edges and
one edge with its first opposite-port pair physically reversed. Loops remain
loops, repeated edges remain repeated, and declared isolated variables remain.
These are exact finite sums, not an assumed oracle or hardness reduction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingWeights
open Holant
open scoped BigOperators
namespace I
export EOBinaryPlaneIsing (internal Independent relative apex_sum independentCount)
end I
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m n : ℕ}

def interaction (p q : K) (x y : Bool) : K := if x=y then p else q

def table (p q : K) : Signature K 2 := fun z=>interaction p q (z 0) (z 1)

def block (p q : K) (a x y : Bool) : K :=
  interaction p q x a * interaction p q y a * interaction p q (!x) y

theorem block_eq (p q : K) (hp : p≠0) (a x y : Bool) :
    block p q a x y=p^2*q*(q/p)^(2*(if Bool.xor a x=true ∧ Bool.xor a y=true then 1 else 0)) := by
  cases a <;> cases x <;> cases y <;> simp [block,interaction]
  all_goals ring_nf
  all_goals first | exact Or.inl trivial | (rw [mul_assoc,←mul_pow,mul_inv_cancel₀ hp]; simp)

/-- Original-field scalar, independently of every spin assignment. -/
def scalar (p q : K) (m : ℕ) : K := (p^2*q)^m

theorem scalar_eq (p q : K) (m : ℕ) : scalar p q m=p^(2*m)*q^m := by
  rw [scalar,mul_pow,←pow_mul]

theorem scalar_ne_zero {p q : K} (hp : p≠0) (hq : q≠0) (m : ℕ) :
    scalar p q m≠0 := pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hp) hq)

theorem internal_bound (left right : Fin m→Fin n) (x : Fin n→Bool) :
    I.internal left right x≤m := by
  calc
    I.internal left right x≤∑_e : Fin m,(1 : ℕ) := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs <;> omega
    _=m := by simp

def weight (p q : K) (left right : Fin m→Fin n) (z : Fin (n+1)→Bool) : K :=
  ∏e,block p q (z 0) (z (left e).succ) (z (right e).succ)

theorem weight_eq (p q : K) (hp : p≠0) (left right : Fin m→Fin n)
    (z : Fin (n+1)→Bool) :
    weight p q left right z=scalar p q m*(q/p)^(2*I.internal left right (I.relative z)) := by
  unfold weight
  simp_rw [block_eq p q hp]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,scalar]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum,←Finset.mul_sum]
  rfl

/-- k copies of all three rows, never a new powered-signature palette label. -/
def partition (p q : K) (left right : Fin m→Fin n) (k : ℕ) : K :=
  ∑z : Fin (n+1)→Bool,∏e,block p q (z 0) (z (left e).succ) (z (right e).succ)^k

def moment (rho : K) (left right : Fin m→Fin n) (k : ℕ) : K :=
  ∑x : Fin n→Bool,(rho^(2*I.internal left right x))^k

theorem partition_eq (p q : K) (hp : p≠0) (left right : Fin m→Fin n) (k : ℕ) :
    partition p q left right k=scalar p q m^k*(2*moment (q/p) left right k) := by
  unfold partition
  simp_rw [Finset.prod_pow]
  change (∑z : Fin (n+1)→Bool,weight p q left right z^k)=_
  simp_rw [weight_eq p q hp,mul_pow]
  rw [←Finset.mul_sum]
  congr 1
  exact I.apex_sum (fun x=>((q/p)^(2*I.internal left right x))^k)

@[simp] theorem partition_zero (p q : K) (left right : Fin m→Fin n) :
    partition p q left right 0=(2 : K)^(n+1) := by
  simp [partition]

theorem normalized_partition (p q : K) (hp : p≠0) (hq : q≠0)
    (left right : Fin m→Fin n) (k : ℕ) :
    partition p q left right k/scalar p q m^k=2*moment (q/p) left right k := by
  rw [partition_eq p q hp]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (scalar_ne_zero hp hq m))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingWeights
