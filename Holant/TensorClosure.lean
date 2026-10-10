import Holant.Support
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
Tensor closure with exact ordered block data, and the binary-endpoint obstruction
used by manuscript Lemma 2.12. The obstruction is proved from the actual one-hot
support condition; no factor-primality oracle is assumed.
-/

namespace Holant

/-- A finite tensor factorization, including nullary factors, an explicit port
permutation, and its nonzero normalization scalar. -/
structure TensorDecomposition (K : Type*) [Monoid K] (n : ℕ) where
  count : ℕ
  arity : Fin count → ℕ
  factor : (i : Fin count) → Signature K (arity i)
  ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n
  scale : Kˣ

namespace TensorDecomposition

variable {K : Type*} [CommMonoid K] {n : ℕ}

def value (D : TensorDecomposition K n) : Signature K n :=
  fun x => (D.scale : K) * ∏ i : Fin D.count, D.factor i (fun j => x (D.ports ⟨i, j⟩))

end TensorDecomposition

namespace Signature

variable {K : Type*} [Field K] {n : ℕ}

/-- Tensor products of members of a class, with a common disjoint port partition. -/
def TensorClosure (C : (n : ℕ) → Signature K n → Prop) (f : Signature K n) : Prop :=
  ∃ D : TensorDecomposition K n, (∀ i, C (D.arity i) (D.factor i)) ∧ D.value = f

/-- A Boolean word of length at most one is one of its two constant endpoint words. -/
theorem word_constant_of_length_le_one {m : ℕ} (hm : m ≤ 1) (x : Fin m → Bool) :
    x = (fun _ => false) ∨ x = (fun _ => true) := by
  cases m with
  | zero =>
    left
    funext i
    exact Fin.elim0 i
  | succ m =>
    have hm0 : m = 0 := by omega
    subst m
    cases h : x 0 with
    | false =>
      left
      funext i
      have hi : i = 0 := Fin.eq_zero i
      simpa only [hi] using h
    | true =>
      right
      funext i
      have hi : i = 0 := Fin.eq_zero i
      simpa only [hi] using h

/-- A tensor product of one-hot factors with both full endpoint words nonzero
must in fact have full support. This rules out a nonsingular diagonal binary. -/
theorem tensorClosure_oneHot_full_support {f : Signature K n}
    (hF : TensorClosure (fun _ g => OneHot g) f)
    (h0 : f (fun _ => false) ≠ 0) (h1 : f (fun _ => true) ≠ 0) :
    ∀ x, f x ≠ 0 := by
  obtain ⟨D, hD, rfl⟩ := hF
  have hf0 : ∀ i, D.factor i (fun _ => false) ≠ 0 := by
    intro i hz
    have hp : (∏ j, D.factor j (fun _ => false)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact h0 (by simp [TensorDecomposition.value, hp])
  have hf1 : ∀ i, D.factor i (fun _ => true) ≠ 0 := by
    intro i hz
    have hp : (∏ j, D.factor j (fun _ => true)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact h1 (by simp [TensorDecomposition.value, hp])
  have hArity : ∀ i, D.arity i ≤ 1 := by
    intro i
    by_contra h
    have hw : 1 < weight (fun _ : Fin (D.arity i) => true) := by
      simpa [weight] using Nat.lt_of_not_ge h
    exact hf1 i (hD i _ hw)
  intro x
  apply mul_ne_zero (Units.ne_zero D.scale)
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases word_constant_of_length_le_one (hArity i)
      (fun j => x (D.ports ⟨i, j⟩)) with h | h
  · rw [h]
    exact hf0 i
  · rw [h]
    exact hf1 i

/-- Concrete support obstruction for the matching alternative in Lemma 2.12. -/
theorem not_tensorClosure_oneHot_of_binary_endpoints (f : Signature K 2)
    (h0 : f (fun _ => false) ≠ 0) (h1 : f (fun _ => true) ≠ 0)
    (h01 : f ![false, true] = 0) :
    ¬ TensorClosure (fun _ g => OneHot g) f := by
  intro h
  exact (tensorClosure_oneHot_full_support h h0 h1 ![false, true]) h01

end Signature
end Holant
