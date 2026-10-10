import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineCycle
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The trace description of an alternating cycle is its literal Boolean
tensor contraction, including all internal indices and the closing wire. -/

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The next position on a nonempty cycle: the last position wraps to zero. -/
def cycleNext (n : ℕ) : Fin (n + 1) → Fin (n + 1) :=
  Fin.lastCases 0 Fin.succ

@[simp] theorem cycleNext_last (n : ℕ) : cycleNext n (Fin.last n) = 0 := by
  simp [cycleNext]

@[simp] theorem cycleNext_castSucc (n : ℕ) (i : Fin n) :
    cycleNext n i.castSucc = i.succ := by
  simp [cycleNext]

theorem cycleNext_eq_finRotate (n : ℕ) : cycleNext n = finRotate (n + 1) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i =>
    rw [cycleNext_castSucc]
    exact (finRotate_of_lt i.isLt).symm

private theorem sum_bool_tuples_succ (n : ℕ) (f : (Fin (n + 1) → Bool) → ℂ) :
    (∑ x, f x) = ∑ a : Bool, ∑ x : Fin n → Bool, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

/-- Matrix multiplication expands as a sum over all intermediate Boolean
indices. The first and last bits are the prescribed boundary values. -/
theorem matrixProduct_eq_sum_paths (n : ℕ) (A : Fin (n + 1) → Mat) (a b : Bool) :
    matrixProduct (List.ofFn A) a b =
      ∑ x : Fin n → Bool, ∏ i : Fin (n + 1),
        A i (Fin.cons (α := fun _ => Bool) a x i) (Fin.snoc (α := fun _ => Bool) x b i) := by
  induction n generalizing a b with
  | zero =>
    simp [List.ofFn_succ, matrixProduct, Fin.snoc]
  | succ n ih =>
    rw [List.ofFn_succ, matrixProduct, Kernel.mul]
    simp_rw [ih]
    rw [sum_bool_tuples_succ]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Fin.cons_snoc_eq_snoc_cons]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]

/-- Closing the two boundary indices is exactly the Boolean contraction
around a cycle. This identity holds for arbitrary complex binary matrices. -/
theorem trace_matrixProduct_eq_sum (n : ℕ) (A : Fin (n + 1) → Mat) :
    Kernel.trace (matrixProduct (List.ofFn A)) =
      ∑ x : Fin (n + 1) → Bool, ∏ i : Fin (n + 1),
        A i (x i) (x (finRotate (n + 1) i)) := by
  unfold Kernel.trace
  simp_rw [matrixProduct_eq_sum_paths, Fin.snoc_eq_cons_rotate]
  rw [sum_bool_tuples_succ]

/-- Each factor is itself a product of two matrices. Both families of
Boolean indices remain explicit, including the cyclic closing indices. -/
theorem trace_matrixProduct_mul_eq_sum (n : ℕ) (A B : Fin (n + 1) → Mat) :
    Kernel.trace (matrixProduct (List.ofFn (fun i => Kernel.mul (A i) (B i)))) =
      ∑ x : Fin (n + 1) → Bool, ∑ y : Fin (n + 1) → Bool,
        ∏ i : Fin (n + 1), A i (x i) (y i) * B i (y i) (x (finRotate (n + 1) i)) := by
  rw [trace_matrixProduct_eq_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Kernel.mul, Fintype.prod_sum]

/-- The manuscript's alternating-cycle coefficient is the genuine tensor
contraction of its oriented dual M-edges with its oriented N-edges. -/
theorem cycleCoefficient_eq_sum (n : ℕ) (fixed : Fin (n + 1) → Label)
    (mReverse nReverse : Fin (n + 1) → Bool) (labels : Fin (n + 1) → Label) :
    cycleCoefficient n fixed mReverse nReverse labels =
      ∑ x : Fin (n + 1) → Bool, ∑ y : Fin (n + 1) → Bool,
        ∏ i : Fin (n + 1),
          oriented (mReverse i) (dual (labels i)) (x i) (y i) *
            oriented (nReverse i) (E (fixed i)) (y i) (x (finRotate (n + 1) i)) := by
  exact trace_matrixProduct_mul_eq_sum n
    (fun i => oriented (mReverse i) (dual (labels i)))
    (fun i => oriented (nReverse i) (E (fixed i)))

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
