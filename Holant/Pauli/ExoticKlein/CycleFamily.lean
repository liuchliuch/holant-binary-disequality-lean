import Holant.Pauli.ExoticKlein.Cycle

/-! Product-of-cycles support counting for arbitrary cycle lengths, fixed
N-labels and orientations. The bridge from an arbitrary matching pair to this
explicit cycle model is developed separately. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators

abbrev CycleLabels {c : ℕ} (extra : Fin c → ℕ) := (i : Fin c) → Fin (extra i+1) → Label
abbrev CycleDirections {c : ℕ} (extra : Fin c → ℕ) := (i : Fin c) → Fin (extra i+1) → Bool

def edgeCount {c : ℕ} (extra : Fin c → ℕ) : ℕ := ∑ i, (extra i+1)

def familyCoefficient {c : ℕ} (extra : Fin c → ℕ) (fixed : CycleLabels extra)
    (mReverse nReverse : CycleDirections extra) (labels : CycleLabels extra) : ℂ :=
  ∏ i, cycleCoefficient (extra i) (fixed i) (mReverse i) (nReverse i) (labels i)

def familySupportEquiv {c : ℕ} (extra : Fin c → ℕ) (fixed : CycleLabels extra)
    (mReverse nReverse : CycleDirections extra) :
    {labels : CycleLabels extra // familyCoefficient extra fixed mReverse nReverse labels ≠ 0} ≃
      ((i : Fin c) → {labels : Fin (extra i+1) → Label //
        cycleCoefficient (extra i) (fixed i) (mReverse i) (nReverse i) labels ≠ 0}) where
  toFun labels i := ⟨labels.val i,
    (Finset.prod_ne_zero_iff.mp labels.property) i (Finset.mem_univ i)⟩
  invFun labels := ⟨fun i => (labels i).val,
    Finset.prod_ne_zero_iff.mpr (fun i _ => (labels i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every factor is an actual cycle trace. No support-size hypothesis is used. -/
theorem family_support_card {c : ℕ} (extra : Fin c → ℕ) (fixed : CycleLabels extra)
    (mReverse nReverse : CycleDirections extra) :
    Fintype.card {labels : CycleLabels extra // familyCoefficient extra fixed mReverse nReverse labels ≠ 0} =
      4^(edgeCount extra-c) := by
  rw [Fintype.card_congr (familySupportEquiv extra fixed mReverse nReverse),Fintype.card_pi]
  simp only [cycle_support_card]
  rw [Finset.prod_pow_eq_pow_sum]
  have he : edgeCount extra = (∑ i, extra i)+c := by simp [edgeCount,Finset.sum_add_distrib]
  rw [he,Nat.add_sub_cancel]

/-- Nonzero scalar multiples of matching products retain precisely this support. -/
theorem scaled_family_support_card {c : ℕ} (extra : Fin c → ℕ) (fixed : CycleLabels extra)
    (mReverse nReverse : CycleDirections extra) (s : ℂ) (hs : s ≠ 0) :
    Fintype.card {labels : CycleLabels extra // s*familyCoefficient extra fixed mReverse nReverse labels ≠ 0} =
      4^(edgeCount extra-c) := by
  let e := Equiv.subtypeEquivRight (fun labels =>
    show s*familyCoefficient extra fixed mReverse nReverse labels ≠ 0 ↔
      familyCoefficient extra fixed mReverse nReverse labels ≠ 0 by simp [hs])
  rw [Fintype.card_congr e]
  exact family_support_card extra fixed mReverse nReverse

theorem sum_one_unique {c : ℕ} (extra : Fin c → ℕ) (h : ∑ i, extra i = 1) :
    ∃ i, extra i = 1 ∧ ∀ j, j ≠ i → extra j = 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, extra i ≠ 0 := by
    by_contra hn
    push_neg at hn
    simp only [hn,Finset.sum_const_zero] at h
    contradiction
  have hle : extra i ≤ ∑ j, extra j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hione : extra i = 1 := by omega
  refine ⟨i,hione,?_⟩
  intro j hji
  have hs := Finset.sum_erase_add Finset.univ extra (Finset.mem_univ i)
  rw [hione,h] at hs
  change (Finset.univ.erase i).sum extra + 1 = 1 at hs
  have hz : (Finset.univ.erase i).sum extra = 0 := by omega
  have hle' : extra j ≤ (Finset.univ.erase i).sum extra :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hji])
  omega

/-- Support4 forces exactly one length4 alternating cycle and common edges
elsewhere. The two varying-edge projection theorem is a separate refinement. -/
theorem family_support_four {c : ℕ} (extra : Fin c → ℕ) (fixed : CycleLabels extra)
    (mReverse nReverse : CycleDirections extra)
    (h : Fintype.card {labels : CycleLabels extra // familyCoefficient extra fixed mReverse nReverse labels ≠ 0} = 4) :
    ∃ i, extra i = 1 ∧ ∀ j, j ≠ i → extra j = 0 := by
  rw [family_support_card] at h
  have hp : edgeCount extra-c = 1 := Nat.pow_right_injective (by decide : 2 ≤ 4) (by simpa using h)
  have he : edgeCount extra = (∑ i, extra i)+c := by simp [edgeCount,Finset.sum_add_distrib]
  rw [he,Nat.add_sub_cancel] at hp
  exact sum_one_unique extra hp

end
end Holant.Pauli.ExoticKlein
