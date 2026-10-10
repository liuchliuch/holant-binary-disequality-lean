import Holant.Pauli.ExoticKlein.MatchingVariation

/-! Faithful support and coordinate variation of four actual matching-basis
terms, retaining arbitrary nonzero scalar coefficients. -/
namespace Holant.Pauli.ExoticKlein.EightPort
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {P : Type*} [Fintype P] [LinearOrder P]

 def fourTensor (M : Matching P 3) (weight : Label → ℂ) (labels : Label → Fin 3 → Label) : Tensor ℂ P :=
  fun x => ∑ g, weight g*M.tensor (labels g) x

 theorem fourTensor_coefficient (M : Matching P 3) (weight : Label → ℂ) (labels : Label → Fin 3 → Label)
    (hfirst : ∀ g, labels g 0 = g) (a : Fin 3 → Label) :
    M.coefficient (fourTensor M weight labels) a = if a = labels (a 0) then weight (a 0) else 0 := by
  classical
  unfold Matching.coefficient fourTensor
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ g, ∑ x, M.dualTensor a x*(weight g*M.tensor (labels g) x)) =
        ∑ g, weight g*M.coefficient (M.tensor (labels g)) a := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [Matching.coefficient,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ g, if a = labels g then weight g else 0 := by
      simp only [Matching.same_matching_coefficient,mul_ite,mul_one,mul_zero]
    _ = if a = labels (a 0) then weight (a 0) else 0 := by
      apply Finset.sum_eq_single (a 0)
      · intro g hg hne
        have hn : a ≠ labels g := by
          intro he
          have hh := congrFun he 0
          rw [hfirst] at hh
          exact hne hh.symm
        simp only [hn,ite_false]
      · simp

 theorem fourTensor_coefficient_at (M : Matching P 3) (weight : Label → ℂ) (labels : Label → Fin 3 → Label)
    (hfirst : ∀ g, labels g 0 = g) (g : Label) :
    M.coefficient (fourTensor M weight labels) (labels g) = weight g := by
  rw [fourTensor_coefficient M weight labels hfirst,hfirst]
  simp only [ite_true]

 def fourSupportEquiv (M : Matching P 3) (weight : Label → ℂ) (labels : Label → Fin 3 → Label)
    (hfirst : ∀ g, labels g 0 = g) (hw : ∀ g, weight g ≠ 0) :
    Label ≃ {a : Fin 3 → Label // M.coefficient (fourTensor M weight labels) a ≠ 0} where
  toFun g := ⟨labels g,by rw [fourTensor_coefficient_at M weight labels hfirst]; exact hw g⟩
  invFun a := a.val 0
  left_inv g := hfirst g
  right_inv a := by
    apply Subtype.ext
    have h := a.property
    rw [fourTensor_coefficient M weight labels hfirst] at h
    split_ifs at h with he
    · exact he.symm
    · exact False.elim (h rfl)

 theorem fourTensor_support_card (M : Matching P 3) (weight : Label → ℂ) (labels : Label → Fin 3 → Label)
    (hfirst : ∀ g, labels g 0 = g) (hw : ∀ g, weight g ≠ 0) :
    Fintype.card {a : Fin 3 → Label // M.coefficient (fourTensor M weight labels) a ≠ 0} = 4 := by
  rw [← Fintype.card_congr (fourSupportEquiv M weight labels hfirst hw),card_label]

 theorem fourTensor_ne_zero (M : Matching P 3) (weight : Label → ℂ) (labels : Label → Fin 3 → Label)
    (hfirst : ∀ g, labels g 0 = g) (hw : ∀ g, weight g ≠ 0) : fourTensor M weight labels ≠ 0 := by
  intro h
  have hc := fourTensor_coefficient_at M weight labels hfirst (0 : Label)
  rw [h] at hc
  simp only [Matching.coefficient,Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hc
  exact hw 0 hc.symm

 theorem fourTensor_coordinate_varies (M : Matching P 3) (weight : Label → ℂ) (labels : Label → Fin 3 → Label)
    (hfirst : ∀ g, labels g 0 = g) (hw : ∀ g, weight g ≠ 0) (i : Fin 3)
    (hi : ∃ a b, labels a i ≠ labels b i) :
    ∃ a b : Fin 3 → Label, M.coefficient (fourTensor M weight labels) a ≠ 0 ∧
      M.coefficient (fourTensor M weight labels) b ≠ 0 ∧ a i ≠ b i := by
  obtain ⟨a,b,hab⟩ := hi
  refine ⟨labels a,labels b,?_,?_,hab⟩
  · rw [fourTensor_coefficient_at M weight labels hfirst]; exact hw a
  · rw [fourTensor_coefficient_at M weight labels hfirst]; exact hw b

/-- Four nonzero matching-basis terms varying on all three edges cannot be
any scalar multiple of any actual three-edge matching product. -/
 theorem fourTensor_not_matching (M : Matching P 3) (weight : Label → ℂ) (labels : Label → Fin 3 → Label)
    (hfirst : ∀ g, labels g 0 = g) (hw : ∀ g, weight g ≠ 0)
    (hvar : ∀ i, ∃ a b, labels a i ≠ labels b i)
    (N : Matching P 3) (fixed : Fin 3 → Label) (s : ℂ) (hs : s ≠ 0) :
    fourTensor M weight labels ≠ (fun x => s*N.tensor fixed x) := by
  intro he
  have hc (a : Fin 3 → Label) : M.coefficient (fourTensor M weight labels) a = s*M.overlap N fixed a := by
    rw [he]
    simp only [Matching.coefficient,Matching.overlap,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hn (a : Fin 3 → Label) : M.coefficient (fourTensor M weight labels) a ≠ 0 ↔ M.overlap N fixed a ≠ 0 := by
    rw [hc]
    simp [hs]
  have hcard : Fintype.card {a : Fin 3 → Label // M.overlap N fixed a ≠ 0} = 4 := by
    rw [← Fintype.card_congr (Equiv.subtypeEquivRight hn)]
    exact fourTensor_support_card M weight labels hfirst hw
  obtain ⟨i,j,hij,hijall⟩ := M.support_four_exactly_two_varying_edges N fixed hcard
  have hall (k : Fin 3) : k = i ∨ k = j := by
    apply (hijall k).mp
    obtain ⟨a,b,ha,hb,hab⟩ := fourTensor_coordinate_varies M weight labels hfirst hw k (hvar k)
    exact ⟨a,b,(hn a).mp ha,(hn b).mp hb,hab⟩
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  fin_cases i <;> fin_cases j <;> simp_all

end
end Holant.Pauli.ExoticKlein.EightPort
