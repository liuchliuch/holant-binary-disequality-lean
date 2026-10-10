import Holant.TensorClosure
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Pivot slices recover the factors of an actual tensor decomposition

All candidate factors below are restrictions of the input table at a nonzero
input row, divided by that row. The reconstruction theorem does not assume a
supplied factorization is correct: it is the algebraic lemma used to prove that
a finite search through port partitions is complete. It is generic in the field
and the original factor arities, including nullary factors.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionNormalization

open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- Replace the coordinates in one block, keeping every other port at `pivot`. -/
def blockWord (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) (i : Fin count) (y : Fin (arity i) → Bool) : Fin n → Bool :=
  fun j => Function.update (fun k l => pivot (ports ⟨k,l⟩)) i y
    (ports.symm j).1 (ports.symm j).2

@[simp] theorem blockWord_same (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) (i : Fin count) (y : Fin (arity i) → Bool)
    (j : Fin (arity i)) :
    blockWord count arity ports pivot i y (ports ⟨i,j⟩) = y j := by
  unfold blockWord
  rw [ports.symm_apply_apply]
  simp only [Function.update_self]

@[simp] theorem blockWord_other (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) (i k : Fin count) (h : k ≠ i)
    (y : Fin (arity i) → Bool) (j : Fin (arity k)) :
    blockWord count arity ports pivot i y (ports ⟨k,j⟩) = pivot (ports ⟨k,j⟩) := by
  simp [blockWord, h]

/-- Literal input-table restriction and normalization, requiring no hidden factors. -/
def normalizedSlice (f : Signature K n) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) (i : Fin count) : Signature K (arity i) :=
  fun y => f (blockWord count arity ports pivot i y) / f pivot

variable (D : TensorDecomposition K n)

theorem factor_pivot_ne_zero (pivot : Fin n → Bool) (hp : D.value pivot ≠ 0)
    (i : Fin D.count) : D.factor i (fun j => pivot (D.ports ⟨i,j⟩)) ≠ 0 := by
  intro hz
  apply hp
  have hprod : (∏ k, D.factor k (fun j => pivot (D.ports ⟨k,j⟩))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz
  simp [TensorDecomposition.value, hprod]

theorem value_blockWord (pivot : Fin n → Bool) (i : Fin D.count)
    (y : Fin (D.arity i) → Bool) :
    D.value (blockWord D.count D.arity D.ports pivot i y) =
      (D.scale : K) * (D.factor i y *
        ∏ k ∈ Finset.univ.erase i, D.factor k (fun j => pivot (D.ports ⟨k,j⟩))) := by
  unfold TensorDecomposition.value
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  apply congrArg₂ (· * ·)
  · congr 1
    funext j
    exact blockWord_same _ _ _ _ _ _ _
  · apply Finset.prod_congr rfl
    intro k hk
    congr 1
    funext j
    exact blockWord_other _ _ _ _ _ _ (Finset.mem_erase.mp hk).1 _ _

/-- The recovered slice equals the corresponding original factor divided by
its pivot entry. This identifies the searched table without choosing new values. -/
theorem normalizedSlice_eq (pivot : Fin n → Bool) (hp : D.value pivot ≠ 0)
    (i : Fin D.count) (y : Fin (D.arity i) → Bool) :
    normalizedSlice D.value D.count D.arity D.ports pivot i y =
      D.factor i y / D.factor i (fun j => pivot (D.ports ⟨i,j⟩)) := by
  have hi := factor_pivot_ne_zero D pivot hp i
  apply (div_eq_div_iff hp hi).2
  rw [value_blockWord]
  conv_rhs =>
    rw [TensorDecomposition.value,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  ring

/-- At every nonzero pivot, multiplying the normalized input slices recovers
exactly the input tensor, with the pivot itself as its normalization scalar. -/
theorem reconstruct (pivot : Fin n → Bool) (hp : D.value pivot ≠ 0)
    (x : Fin n → Bool) :
    D.value pivot * ∏ i, normalizedSlice D.value D.count D.arity D.ports pivot i
      (fun j => x (D.ports ⟨i,j⟩)) = D.value x := by
  have hprod : (∏ i, D.factor i (fun j => pivot (D.ports ⟨i,j⟩))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => factor_pivot_ne_zero D pivot hp i)
  simp_rw [normalizedSlice_eq D pivot hp]
  rw [Finset.prod_div_distrib]
  unfold TensorDecomposition.value
  field_simp

end Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionNormalization
