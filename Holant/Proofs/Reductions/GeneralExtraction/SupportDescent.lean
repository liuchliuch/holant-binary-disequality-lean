import Holant.Proofs.Reductions.GeneralExtraction.NamedContraction
import Mathlib.Tactic.LinearCombination


noncomputable section
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.SupportDescent
open scoped BigOperators
open Holant.Certificates.MatchingContractionClosure
open Holant.OpenNetworkComposition.ProjectiveSubstitution
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction

variable {P : Type*} [Fintype P] [DecidableEq P]

def «matches» (b : Bool) (x : P → Bool) : ℕ := ∑ i, if x i = b then 1 else 0

theorem balance_count (b : Bool) (x : P → Bool) :
    balance b x = 2 * («matches» b x : ℤ) - Fintype.card P := by
  have he : (∑ i : P, if x i = b then (1 : ℤ) else -1) =
      2 * (∑ i : P, if x i = b then (1 : ℤ) else 0) - ∑ _ : P, (1 : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i = b <;> simp [h]
  simpa [balance, «matches», Nat.cast_sum] using he

theorem matches_le (b : Bool) (x : P → Bool) : «matches» b x ≤ Fintype.card P := by
  calc
    «matches» b x ≤ ∑ _ : P, 1 := Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = _ := by simp

theorem balance_negate (b : Bool) (x : P → Bool) : balance (!b) x = -balance b x := by
  unfold balance
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases b <;> cases x i <;> norm_num

theorem balance_reindex {Q : Type*} [Fintype Q] (e : P ≃ Q)
    (b : Bool) (x : Q → Bool) : balance b (fun i => x (e i)) = balance b x :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem exists_majority_of_nonnegative (b : Bool) (x : P → Bool)
    (hpos : 0 < Fintype.card P) (hb : 0 ≤ balance b x) : ∃ i, x i = b := by
  by_contra hn
  push_neg at hn
  have he : balance b x = -(Fintype.card P : ℤ) := by simp [balance, hn]
  rw [he] at hb
  omega

/-- Strict maximal balance forces every bit, not merely a nonzero constant
entry. This is the missing pure-pin inference in Corollary 41. -/
theorem all_eq_of_card_le_balance (b : Bool) (x : P → Bool)
    (h : (Fintype.card P : ℤ) ≤ balance b x) : x = fun _ => b := by
  have hm := matches_le b x
  have hb := balance_count b x
  have he : «matches» b x = Fintype.card P := by omega
  have hs : (∑ i : P, if x i = b then (1 : ℕ) else 0) = ∑ _ : P, (1 : ℕ) := by
    simpa [«matches»] using he
  have each := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ (Finset.univ : Finset P)) =>
      show (if x i = b then (1 : ℕ) else 0) ≤ 1 by split <;> omega)).mp hs
  funext i
  have hi := each i (Finset.mem_univ i)
  by_contra hn
  simp [hn] at hi

variable {K : Type*} [Field K]

/-- Every successful term in an X contraction has the same balance as its
remaining word. This does not assume the two terms fail to cancel. -/
theorem contraction_support (b : Bool) (f : Tensor K P) (i j : P) (hij : i ≠ j)
    (y : Remaining i j → Bool)
    (hy : contractPair i j Signature.disequality f y ≠ 0) :
    ∃ x : P → Bool, f x ≠ 0 ∧ balance b x = balance b y := by
  let x₀ := insertPair i j false true (extendRemaining i j y)
  let x₁ := insertPair i j true false (extendRemaining i j y)
  have he : contractPair i j Signature.disequality f y = f x₀ + f x₁ := by
    simp [contractPair, Signature.disequality, Fintype.sum_bool, x₀, x₁, add_comm]
  have hb₀ : balance b x₀ = balance b y := by
    have h := sum_pair (fun p => if x₀ p = b then (1 : ℤ) else -1) i j hij
    have ht : (fun p : Remaining i j => x₀ p.val) = y := by
      funext p
      simp [x₀, insertPair_other p.property.1 p.property.2, extendRemaining,
        p.property.1, p.property.2]
    have ht' : balance b (fun p : Remaining i j => x₀ p.val) = balance b y := congrArg (balance b) ht
    have heq : x₀ i ≠ x₀ j := by simp [x₀, insertPair_first hij, insertPair_second]
    exact (balance_remaining b x₀ i j heq).symm.trans ht'
  have hb₁ : balance b x₁ = balance b y := by
    have h := sum_pair (fun p => if x₁ p = b then (1 : ℤ) else -1) i j hij
    have ht : (fun p : Remaining i j => x₁ p.val) = y := by
      funext p
      simp [x₁, insertPair_other p.property.1 p.property.2, extendRemaining,
        p.property.1, p.property.2]
    have ht' : balance b (fun p : Remaining i j => x₁ p.val) = balance b y := congrArg (balance b) ht
    have heq : x₁ i ≠ x₁ j := by simp [x₁, insertPair_first hij, insertPair_second]
    exact (balance_remaining b x₁ i j heq).symm.trans ht'
  by_cases h₀ : f x₀ = 0
  · exact ⟨x₁, by simpa [he, h₀] using hy, hb₁⟩
  · exact ⟨x₀, h₀, hb₀⟩

/-- Includes the balanced-support case needed for Lemma 42. The third
choice uses the swapped supported candidate, preserving its exact charge. -/
theorem exact_contraction (htwo : (2 : K) ≠ 0) (b : Bool)
    (f : Tensor K P) (x : P → Bool) (hf : f x ≠ 0)
    (hb : 0 ≤ balance b x) (hn : 2 < Fintype.card P) (hm : ∃ i, x i ≠ b) :
    ∃ i j : P, ∃ hij : i ≠ j, ∃ y : Remaining i j → Bool,
      contractPair i j Signature.disequality f y ≠ 0 ∧ balance b y = balance b x := by
  obtain ⟨i, hi⟩ := hm
  obtain ⟨j, hj⟩ := exists_majority_of_nonnegative b x (by omega) hb
  have hxij : x i ≠ x j := by simpa [hj] using hi
  have hij : i ≠ j := fun h => hxij (congrArg x h)
  have hc := remaining_card i j hij
  have hr : 0 ≤ balance b (fun p : Remaining i j => x p.val) := by
    rwa [balance_remaining b x i j hxij]
  obtain ⟨k, hk⟩ := exists_majority_of_nonnegative b
    (fun p : Remaining i j => x p.val) (by omega) hr
  have hik : i ≠ k.val := Ne.symm k.property.1
  have hjk : j ≠ k.val := Ne.symm k.property.2
  have hxik : x i ≠ x k.val := by simpa [hk] using hi
  let y := x ∘ Equiv.swap i j
  have hyjk : y j ≠ y k.val := by
    simp [y, Equiv.swap_apply_def, hjk, k.property.1, k.property.2, hi, hk]
  by_cases h₁ : contractPair i j Signature.disequality f (fun p => x p.val) ≠ 0
  · exact ⟨i, j, hij, _, h₁, balance_remaining b x i j hxij⟩
  by_cases h₂ : contractPair i k.val Signature.disequality f (fun p => x p.val) ≠ 0
  · exact ⟨i, k.val, hik, _, h₂, balance_remaining b x i k.val hxik⟩
  have h₃ : contractPair j k.val Signature.disequality f (fun p => y p.val) ≠ 0 := by
    intro hz
    have e₁ := contract_at_word f x i j hxij
    have e₂ := contract_at_word f x i k.val hxik
    have e₃ := contract_at_word f y j k.val hyjk
    rw [swap_triangle x i j k.val hij hik hjk (hj.trans hk.symm)] at e₃
    have z₁ := not_ne_iff.mp h₁
    have z₂ := not_ne_iff.mp h₂
    have he : (2 : K) * f x = 0 := by
      dsimp [y] at e₃ hz
      linear_combination -e₁ - e₂ + e₃ + z₁ + z₂ - hz
    exact hf ((mul_eq_zero.mp he).resolve_left htwo)
  refine ⟨j, k.val, hjk, _, h₃, ?_⟩
  rw [balance_remaining b y j k.val hyjk]
  exact balance_swap b x i j

end Holant.LocalDrafts.Hardness.GeneralExtraction.SupportDescent
