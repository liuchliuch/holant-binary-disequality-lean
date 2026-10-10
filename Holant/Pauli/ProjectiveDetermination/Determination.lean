import Holant.Pauli.ProjectiveDetermination.Transform
import Holant.Pauli.ProjectiveDetermination.Cards

/-! Manuscript Lemma8.2: all actual Pauli pair contractions determine a tensor
line once there are at least five physical ports. Repeated Bell-coordinate
vanishing is derived from the card hypothesis, then discharged by pigeonhole. -/
namespace Holant.Pauli.ProjectiveDetermination
noncomputable section
open scoped BigOperators ComplexConjugate

private theorem sum_rotate {α β χ : Type*} [Fintype α] [Fintype β] [Fintype χ]
    (f : α → β → χ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Each repeated Bell index vanishes because of the four literal Pauli
contraction equations on every remaining physical assignment. -/
theorem transform_zero_of_equal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : PairedTensor ι) (r s : ι) (hne : r ≠ s)
    (hcards : ∀ g z, doubleCard r s g W z = 0)
    (l : ι → Label) (heq : l r = l s) : transform W l = 0 := by
  classical
  rw [transform_pair W r s hne l, sum_rotate]
  apply Finset.sum_eq_zero
  intro z hz
  have hdiag := local_diagonal_zero (fun a b : Local => W (fill r s a b z)) (fun g => hcards g z) (l r)
  calc
    (∑ a : Local, ∑ b : Local,
      W (fill r s a b z)*(bell (l r) a*bell (l s) b*∏ i : Rest r s, bell (l i) (z i))) =
        localBellSlice (fun a b => W (fill r s a b z)) (l r)*∏ i : Rest r s, bell (l i) (z i) := by
      unfold localBellSlice
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [← heq]
      ring
    _ = 0 := by rw [hdiag,zero_mul]

/-- A word with at least five positions over four labels repeats on a genuinely
distinct increasing physical pair. -/
theorem repeated_label (n : ℕ) (hn : 5 ≤ n) (l : Fin n → Label) :
    ∃ r s : Fin n, r < s ∧ l r = l s := by
  classical
  by_contra hrepeat
  have hi : Function.Injective l := by
    intro r s h
    rcases lt_trichotomy r s with hrs | heq | hsr
    · exact False.elim (hrepeat ⟨r,s,hrs,h⟩)
    · exact heq
    · exact False.elim (hrepeat ⟨s,r,hsr,h.symm⟩)
  have hc := Fintype.card_le_of_injective l hi
  simp only [Fintype.card_fin] at hc
  omega

/-- The Bell support argument is a theorem about actual pair contractions on an
arbitrary double tensor, and does not assume the desired coefficient support. -/
theorem all_doubleCards_zero (n : ℕ) (hn : 5 ≤ n) (W : PairedTensor (Fin n))
    (h : ∀ (r s : Fin n), r < s → ∀ g z, doubleCard r s g W z = 0) : W = 0 := by
  apply transform_zero
  intro l
  obtain ⟨r,s,hrs,heq⟩ := repeated_label n hn l
  exact transform_zero_of_equal W r s (ne_of_lt hrs) (h r s hrs) l heq

/-- Full first assertion of manuscript Lemma8.2. Either card may be zero;
contractions use all four original real Pauli kernels on every original pair. -/
theorem pauli_projective_determination (n : ℕ) (hn : 5 ≤ n) (u v : Signature ℂ n)
    (h : ∀ (r s : Fin n), r < s → ∀ g : Label, Dependent (card r s g u) (card r s g v)) :
    Dependent u v := by
  apply (doubleTensor_zero_iff u v).mp
  apply all_doubleCards_zero n hn
  intro r s hrs g z
  exact dependent_cards_zero r s g u v (h r s hrs g) z

/-- The conclusion also has the usual nontrivial linear-relation form. -/
theorem pauli_projective_determination_relation (n : ℕ) (hn : 5 ≤ n) (u v : Signature ℂ n)
    (h : ∀ (r s : Fin n), r < s → ∀ g : Label, Dependent (card r s g u) (card r s g v)) :
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ x, a*u x+b*v x = 0 :=
  (dependent_iff_relation u v).mp (pauli_projective_determination n hn u v h)

/-- Full scalar-times-real consequence. Zero cards are already included in
IsRealLine, represented by scalar1 and the zero real tensor. -/
theorem pauli_real_line (n : ℕ) (hn : 5 ≤ n) (u : Signature ℂ n)
    (h : ∀ (r s : Fin n), r < s → ∀ g : Label, IsRealLine (card r s g u)) : IsRealLine u := by
  apply (realLine_iff_conjugate_dependent u).mpr
  apply pauli_projective_determination n hn
  intro r s hrs g
  have hh := (realLine_iff_conjugate_dependent (card r s g u)).mp (h r s hrs g)
  have hc : card r s g (fun x => conj (u x)) = fun z => conj (card r s g u z) := by
    funext z
    exact card_conjugate r s g u z
  rw [hc]
  exact hh

/-- Literal zero-or-real-line phrasing of the source consequence. -/
theorem pauli_zero_or_real_line (n : ℕ) (hn : 5 ≤ n) (u : Signature ℂ n)
    (h : ∀ (r s : Fin n), r < s → ∀ g : Label,
      card r s g u = 0 ∨ IsRealLine (card r s g u)) : IsRealLine u := by
  apply pauli_real_line n hn u
  intro r s hrs g
  rcases h r s hrs g with hz | hr
  · refine ⟨1,one_ne_zero,fun _ => 0,?_⟩
    funext x
    simp [hz]
  · exact hr

end
end Holant.Pauli.ProjectiveDetermination
