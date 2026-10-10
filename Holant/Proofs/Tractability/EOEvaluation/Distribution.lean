import Holant.Tractable.Criteria
import Holant.ChargeConservation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic


namespace Holant.LocalDrafts.Tractability.EOEvaluation.Distribution
open Holant.Tractable
open scoped BigOperators
noncomputable section

/-- The original ordered local Boolean word, with its actual finite index type. -/
abbrev Word (n : ℕ) := Fin n → Bool

def spin (b : Bool) : ℚ := if b then 1 else -1

theorem spin_triple (a b c : Bool) :
    spin (Bool.xor (Bool.xor a b) c) = spin a * spin b * spin c := by
  cases a <;> cases b <;> cases c <;> norm_num [spin]

theorem charge_sum {n : ℕ} (x : Word n) :
    (Holant.charge x : ℚ) = ∑ j, spin (x j) := by
  have hb (b : Bool) : spin b = 2 * (if b then (1 : ℚ) else 0) - 1 := by
    cases b <;> norm_num [spin]
  simp only [hb, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Holant.charge, Holant.weight, Nat.cast_sum, Int.cast_sub]

abbrev Mass (n : ℕ) := Word n → ℚ
def mean {n : ℕ} (w : Mass n) (j : Fin n) : ℚ := ∑ a, w a * spin (a j)
def tripleMass {n : ℕ} (w : Mass n) (a b c : Word n) := w a * w b * w c
def convolution {n : ℕ} (w : Mass n) : Mass n := fun d =>
  ∑ a, ∑ b, ∑ c, if tripleXor a b c = d then tripleMass w a b c else 0

theorem tripleMass_nonneg {n : ℕ} {w : Mass n} (hw : ∀ a, 0 ≤ w a)
    (a b c : Word n) : 0 ≤ tripleMass w a b c :=
  mul_nonneg (mul_nonneg (hw a) (hw b)) (hw c)

theorem convolution_nonneg {n : ℕ} {w : Mass n} (hw : ∀ a, 0 ≤ w a) (d : Word n) :
    0 ≤ convolution w d := by
  unfold convolution
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro b _
  apply Finset.sum_nonneg; intro c _
  split_ifs
  · exact tripleMass_nonneg hw a b c
  · exact le_rfl

theorem expectation {n : ℕ} (w : Mass n) (f : Word n → ℚ) :
    (∑ d, convolution w d * f d) =
      ∑ a, ∑ b, ∑ c, tripleMass w a b c * f (tripleXor a b c) := by
  classical
  simp only [convolution, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem total_convolution {n : ℕ} (w : Mass n) :
    (∑ d, convolution w d) = (∑ a, w a) ^ 3 := by
  calc
    _ = ∑ a, ∑ b, ∑ c, w a * w b * w c := by
      simpa only [mul_one, tripleMass] using expectation w (fun _ => 1)
    _ = (∑ a, w a) ^ 3 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul] <;> ring

theorem mean_convolution {n : ℕ} (w : Mass n) (j : Fin n) :
    mean (convolution w) j = mean w j ^ 3 := by
  rw [mean, expectation]
  simp only [tripleXor, spin_triple, tripleMass]
  calc
    _ = ∑ a, ∑ b, ∑ c, (w a * spin (a j)) * (w b * spin (b j)) * (w c * spin (c j)) := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro c _
      ring
    _ = mean w j ^ 3 := by
      unfold mean
      simp only [← Finset.mul_sum, ← Finset.sum_mul] <;> ring

theorem cubic_expansion {n : ℕ} (w : Mass n) :
    (∑ j, mean w j ^ 3) =
      ∑ a, ∑ b, ∑ c, tripleMass w a b c * (Holant.charge (tripleXor a b c) : ℚ) := by
  calc
    _ = ∑ j, ∑ d, convolution w d * spin (d j) := by
      apply Finset.sum_congr rfl; intro j _
      exact (mean_convolution w j).symm
    _ = ∑ d, convolution w d * (Holant.charge d : ℚ) := by
      rw [Finset.sum_comm]
      simp only [charge_sum, Finset.mul_sum]
    _ = _ := expectation w (fun d => (Holant.charge d : ℚ))

theorem selected_le_convolution {n : ℕ} {w : Mass n} (hw : ∀ a, 0 ≤ w a)
    (a b c : Word n) : tripleMass w a b c ≤ convolution w (tripleXor a b c) := by
  have hn (a' b' c' : Word n) :
      0 ≤ (if tripleXor a' b' c' = tripleXor a b c then tripleMass w a' b' c' else 0) := by
    split_ifs
    · exact tripleMass_nonneg hw a' b' c'
    · exact le_rfl
  calc
    _ ≤ ∑ c', if tripleXor a b c' = tripleXor a b c then tripleMass w a b c' else 0 := by
      simpa using Finset.single_le_sum (fun c' _ => hn a b c') (Finset.mem_univ c)
    _ ≤ ∑ b', ∑ c', if tripleXor a b' c' = tripleXor a b c then tripleMass w a b' c' else 0 :=
      Finset.single_le_sum (fun b' _ => Finset.sum_nonneg (fun c' _ => hn a b' c')) (Finset.mem_univ b)
    _ ≤ convolution w (tripleXor a b c) := by
      unfold convolution
      exact Finset.single_le_sum (fun a' _ => Finset.sum_nonneg (fun b' _ =>
        Finset.sum_nonneg (fun c' _ => hn a' b' c'))) (Finset.mem_univ a)

end
end Holant.LocalDrafts.Tractability.EOEvaluation.Distribution
