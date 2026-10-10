import Holant.Proofs.Traversal.ArityTwo.Transfer
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Rotate


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo
open Holant
open scoped BigOperators
variable {K : Type*} [CommSemiring K]

theorem sum_bool_tuples_succ (n : ℕ) (f : (Fin (n+1) → Bool) → K) :
    (∑ x, f x) = ∑ a : Bool, ∑ x : Fin n → Bool, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f,Fintype.sum_prod_type]
  rfl

theorem product_eq_sum_paths (n : ℕ) (A : Fin (n+1) → Kernel K) (a b : Bool) :
    product (List.ofFn A) a b =
      ∑ x : Fin n → Bool, ∏ i : Fin (n+1),
        A i (Fin.cons (α := fun _ => Bool) a x i) (Fin.snoc (α := fun _ => Bool) x b i) := by
  induction n generalizing a b with
  | zero => simp [List.ofFn_succ,product,Fin.snoc]
  | succ n ih =>
    rw [List.ofFn_succ,product,Kernel.mul]
    simp_rw [ih]
    rw [sum_bool_tuples_succ]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Fin.cons_snoc_eq_snoc_cons]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ]

theorem pathValue_eq_assignment_sum (n : ℕ) (A : Fin (n+1) → Kernel K)
    (left right : Bool → K) :
    pathValue left (List.ofFn A) right =
      ∑ a : Bool, ∑ b : Bool, ∑ x : Fin n → Bool,
        left a * (∏ i : Fin (n+1),
          A i (Fin.cons (α := fun _ => Bool) a x i) (Fin.snoc (α := fun _ => Bool) x b i)) * right b := by
  simp only [pathValue,message,Kernel.act,product_eq_sum_paths]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]

theorem cycleValue_eq_assignment_sum (n : ℕ) (A : Fin (n+1) → Kernel K) :
    cycleValue (List.ofFn A) =
      ∑ x : Fin (n+1) → Bool, ∏ i : Fin (n+1), A i (x i) (x (finRotate (n+1) i)) := by
  unfold cycleValue Kernel.trace
  simp_rw [product_eq_sum_paths,Fin.snoc_eq_cons_rotate]
  rw [sum_bool_tuples_succ]

theorem product_flat_pairs (pairs : List (Kernel K × Kernel K)) :
    product (pairs.flatMap (fun p => [p.1,p.2])) =
      product (pairs.map (fun p => Kernel.mul p.1 p.2)) := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.map_cons,product,ih,
      Kernel.mul_assoc]

/-- The two independent Boolean coordinates at every binary occurrence
remain visible; the second factor is the real outgoing oriented edge kernel. -/
theorem cycle_pairs_eq_assignment_sum (n : ℕ) (B E : Fin (n+1) → Kernel K) :
    cycleValue ((List.ofFn (fun i => (B i,E i))).flatMap (fun p => [p.1,p.2])) =
      ∑ x : Fin (n+1) → Bool, ∑ y : Fin (n+1) → Bool,
        ∏ i : Fin (n+1), B i (x i) (y i) * E i (y i) (x (finRotate (n+1) i)) := by
  rw [cycleValue,product_flat_pairs]
  change cycleValue ((List.ofFn (fun i => (B i,E i))).map (fun p => Kernel.mul p.1 p.2)) = _
  rw [List.map_ofFn,cycleValue_eq_assignment_sum]
  apply Finset.sum_congr rfl
  intro x _
  change (∏ i, ∑ y : Bool, B i (x i) y * E i y (x (finRotate (n+1) i))) = _
  exact Fintype.prod_sum _

end Holant.LocalDrafts.TraversalCompletion.ArityTwo
