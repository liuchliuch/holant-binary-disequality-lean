import Mathlib.Tactic.LinearCombination
import Holant.OpenNetworkComposition.ProjectiveSubstitutionPorts
import Holant.Support


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.OpenNetworkComposition.ProjectiveSubstitution

universe u
variable {P : Type u} [Fintype P] [DecidableEq P]

/-- Charge towards the chosen bit, on any finite set of named ports. -/
def balance (b : Bool) (x : P → Bool) : ℤ :=
  ∑ i, if x i = b then 1 else -1

theorem sum_pair {A : Type*} [AddCommMonoid A] (g : P → A)
    (i j : P) (hij : i ≠ j) :
    (∑ p, g p) = g i + g j + ∑ p : Remaining i j, g p.val := by
  let r := Fintype.equivFin (Remaining i j)
  let e := pairOrder i j hij r
  calc
    (∑ p, g p) = ∑ q, g (e q) := by
      exact Fintype.sum_equiv e.symm _ _ (by intro p; simp)
    _ = g i + g j + ∑ q : Fin (Fintype.card (Remaining i j)), g (r.symm q).val := by
      simp only [Fin.sum_univ_succ, e, pairOrder_zero, pairOrder_one, pairOrder_tail]
      ac_rfl
    _ = _ := by
      congr 1
      exact Fintype.sum_equiv r.symm _ _ (fun _ => rfl)

theorem remaining_card (i j : P) (hij : i ≠ j) :
    Fintype.card (Remaining i j) + 2 = Fintype.card P := by
  have h := Fintype.card_congr (pairOrder i j hij (Fintype.equivFin _))
  simpa using h

theorem balance_remaining (b : Bool) (x : P → Bool) (i j : P)
    (hx : x i ≠ x j) :
    balance b (fun p : Remaining i j => x p.val) = balance b x := by
  have hij : i ≠ j := fun h => hx (congrArg x h)
  have h := sum_pair (fun p => if x p = b then (1 : ℤ) else -1) i j hij
  unfold balance
  cases hi : x i <;> cases hj : x j <;> cases b <;> simp_all

theorem balance_swap (b : Bool) (x : P → Bool) (i j : P) :
    balance b (x ∘ Equiv.swap i j) = balance b x := by
  exact Fintype.sum_equiv (Equiv.swap i j) _ _ (fun _ => rfl)

theorem exists_majority_bit (b : Bool) (x : P → Bool) (h : 0 < balance b x) :
    ∃ i, x i = b := by
  by_contra hn
  push_neg at hn
  have he : balance b x = -(Fintype.card P : ℤ) := by simp [balance, hn]
  have hc : (0 : ℤ) ≤ Fintype.card P := Nat.cast_nonneg _
  omega

variable {K : Type*} [Field K]

/-- Closing a unlike pair sums the original word and its transposition. -/
theorem contract_at_word (f : Tensor K P) (x : P → Bool) (i j : P)
    (hx : x i ≠ x j) :
    contractPair i j Signature.disequality f (fun p => x p.val) =
      f x + f (x ∘ Equiv.swap i j) := by
  have hij : i ≠ j := fun h => hx (congrArg x h)
  have hself : insertPair i j (x i) (x j)
      (extendRemaining i j (fun p => x p.val)) = x := by
    funext p
    by_cases hi : p = i
    · subst p; simp [insertPair_first hij]
    by_cases hj : p = j
    · subst p; simp [insertPair_second]
    simp [insertPair_other hi hj, extendRemaining, hi, hj]
  have hswap : insertPair i j (x j) (x i)
      (extendRemaining i j (fun p => x p.val)) = x ∘ Equiv.swap i j := by
    funext p
    by_cases hi : p = i
    · subst p; simp [insertPair_first hij]
    by_cases hj : p = j
    · subst p; simp [insertPair_second]
    simp [insertPair_other hi hj, extendRemaining, hi, hj, Equiv.swap_apply_def]
  unfold contractPair
  cases hi : x i <;> cases hj : x j <;>
    simp_all [Signature.disequality, Fintype.sum_bool, add_comm]

/-- Moving the unique minority bit among three positions forms a triangle. -/
theorem swap_triangle (x : P → Bool) (i j k : P)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (he : x j = x k) :
    (x ∘ Equiv.swap i j) ∘ Equiv.swap j k = x ∘ Equiv.swap i k := by
  funext p
  by_cases hi : p = i
  · subst p; simp [Function.comp_def, Equiv.swap_apply_def, hij, hik, hjk, he]
  by_cases hj : p = j
  · subst p
    simp [Function.comp_def, Equiv.swap_apply_def, hij, hik, hjk, he,
      Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  by_cases hk : p = k
  · subst p
    simp [Function.comp_def, Equiv.swap_apply_def, hij, hik, hjk, he,
      Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  simp [Function.comp_def, Equiv.swap_apply_def, hi, hj, hk]

/-- A strict majority supported word with a minority bit has a nonzero
native self-contraction with the same strict majority. The third branch
uses a transposed word; the original coefficient need not survive the
first or second attempted contraction. -/
theorem nonzero_majority_contraction (htwo : (2 : K) ≠ 0)
    (b : Bool) (f : Tensor K P) (x : P → Bool)
    (hf : f x ≠ 0) (hb : 0 < balance b x) (hm : ∃ i, x i ≠ b) :
    ∃ i j : P, ∃ hij : i ≠ j, ∃ y : Remaining i j → Bool,
      contractPair i j Signature.disequality f y ≠ 0 ∧ 0 < balance b y := by
  obtain ⟨i, hi⟩ := hm
  obtain ⟨j, hj⟩ := exists_majority_bit b x hb
  have hxij : x i ≠ x j := by simpa [hj] using hi
  have hij : i ≠ j := fun h => hxij (congrArg x h)
  have hr : 0 < balance b (fun p : Remaining i j => x p.val) := by
    rwa [balance_remaining b x i j hxij]
  obtain ⟨k, hk⟩ := exists_majority_bit b (fun p : Remaining i j => x p.val) hr
  have hik : i ≠ k.val := Ne.symm k.property.1
  have hjk : j ≠ k.val := Ne.symm k.property.2
  have hxik : x i ≠ x k.val := by simpa [hk] using hi
  let y := x ∘ Equiv.swap i j
  have hyjk : y j ≠ y k.val := by simp [y, Equiv.swap_apply_def, hjk, k.property.1, k.property.2, hi, hk]
  by_cases h₁ : contractPair i j Signature.disequality f (fun p => x p.val) ≠ 0
  · exact ⟨i, j, hij, _, h₁, hr⟩
  by_cases h₂ : contractPair i k.val Signature.disequality f (fun p => x p.val) ≠ 0
  · exact ⟨i, k.val, hik, _, h₂, by rwa [balance_remaining b x i k.val hxik]⟩
  have h₃ : contractPair j k.val Signature.disequality f (fun p => y p.val) ≠ 0 := by
    intro hz
    have e₁ := contract_at_word f x i j hxij
    have e₂ := contract_at_word f x i k.val hxik
    have e₃ := contract_at_word f y j k.val hyjk
    have he : y ∘ Equiv.swap j k.val = x ∘ Equiv.swap i k.val :=
      swap_triangle x i j k.val hij hik hjk (hj.trans hk.symm)
    rw [he] at e₃
    have z₁ := not_ne_iff.mp h₁
    have z₂ := not_ne_iff.mp h₂
    have hdouble : (2 : K) * f x = 0 := by
      dsimp [y] at e₃ hz
      linear_combination -e₁ - e₂ + e₃ + z₁ + z₂ - hz
    exact hf ((mul_eq_zero.mp hdouble).resolve_left htwo)
  refine ⟨j, k.val, hjk, _, h₃, ?_⟩
  rw [balance_remaining b y j k.val hyjk]
  simpa [y, balance_swap] using hb

/-- The actual gadget at the end of descent has a nonzero all-b coefficient
and positive arity. Every descent step is an actual same-family X closure.
There is no pinning or arbitrary coefficient-selection resource. -/
theorem majority_cap (family : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (b : Bool) (f : Tensor K P) (ha : Actual family f)
    (x : P → Bool) (hf : f x ≠ 0) (hb : 0 < balance b x) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : Signature K n,
      Gadget.RealizesUpTo family .disequality g ∧ g (fun _ => b) ≠ 0 := by
  have aux : ∀ n : ℕ, ∀ (Q : Type u) [Fintype Q] [DecidableEq Q],
      Fintype.card Q = n → ∀ (g : Tensor K Q), Actual family g →
      ∀ z : Q → Bool, g z ≠ 0 → 0 < balance b z →
      ∃ m : ℕ, 0 < m ∧ ∃ h : Signature K m,
        Gadget.RealizesUpTo family .disequality h ∧ h (fun _ => b) ≠ 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Q _ _ hn g hg z hz hbz
      by_cases hall : ∀ q, z q = b
      · have he : z = fun _ => b := funext hall
        have hnpos : 0 < n := by
          have hbalance : balance b z = (Fintype.card Q : ℤ) := by simp [balance, hall]
          rw [hbalance, hn] at hbz
          omega
        let e := Fintype.equivFin Q
        refine ⟨Fintype.card Q, by omega, Tensor.reindex e g, hg.ordered e, ?_⟩
        simpa [Tensor.reindex, he] using hz
      · push_neg at hall
        obtain ⟨i, j, hij, y, hy, hby⟩ :=
          nonzero_majority_contraction htwo b g z hz hbz hall
        have hc := remaining_card i j hij
        apply ih (Fintype.card (Remaining i j)) (by omega) (Remaining i j) rfl
          (contractPair i j Signature.disequality g) (hg.contractPair i j hij htwo) y hy hby
  exact aux _ P rfl f ha x hf hb

theorem balance_true {n : ℕ} (x : Fin n → Bool) : balance true x = Holant.charge x := by
  have he : (∑ i, (if x i = true then (1 : ℤ) else -1)) =
      2 * (∑ i, if x i then (1 : ℤ) else 0) - ∑ _ : Fin n, (1 : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> norm_num
  simpa [balance, Holant.charge, Holant.weight, Nat.cast_sum] using he

theorem balance_false {n : ℕ} (x : Fin n → Bool) : balance false x = -Holant.charge x := by
  rw [← balance_true]
  unfold balance
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> norm_num

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
