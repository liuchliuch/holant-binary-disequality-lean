import Holant.Pauli.ExoticKlein.EightPortSetup

/-! The two actual contractions cannot both lose their middle varying label.
This uses invertibility of A1 and the literal nonidentity transpose involution. -/
namespace Holant.Pauli.ExoticKlein.EightPort
noncomputable section
set_option backward.isDefEq.respectTransparency false

@[simp] theorem D35_zero (A1 A2 : Label ≃+ Label) : D35 A1 A2 0 = 0 := by
  simp only [D35,map_zero,theta_zero,add_zero]

@[simp] theorem D45_zero (A1 A2 : Label ≃+ Label) : D45 A1 A2 0 = 0 := by
  simp only [D45,map_zero,add_zero]

 theorem D35_or_D45_nonzero (A1 A2 : Label ≃+ Label) :
    (∃ g, D35 A1 A2 g ≠ 0) ∨ (∃ g, D45 A1 A2 g ≠ 0) := by
  classical
  by_contra hn
  push_neg at hn
  have h35 := (add_eq_zero_iff (theta (A1 (A1.symm yLabel))) (A2 (A1.symm yLabel))).mp (hn.1 (A1.symm yLabel))
  have h45 := (add_eq_zero_iff (A1 (A1.symm yLabel)) (A2 (A1.symm yLabel))).mp (hn.2 (A1.symm yLabel))
  have he := h35.trans h45.symm
  simp only [AddEquiv.apply_symm_apply,theta_y] at he
  exact y_ne_z he.symm

@[simp] theorem labelTriple_first (D : Label → Label) (A3 : Label ≃+ Label) (g : Label) :
    labelTriple D A3 g 0 = g := rfl

 theorem labelTriple_all_vary (D : Label → Label) (hD0 : D 0 = 0) (hD : ∃ g, D g ≠ 0)
    (A3 : Label ≃+ Label) : ∀ i : Fin 3, ∃ a b, labelTriple D A3 a i ≠ labelTriple D A3 b i := by
  intro i
  fin_cases i
  · exact ⟨0,xLabel,zero_ne_x⟩
  · obtain ⟨g,hg⟩ := hD
    refine ⟨g,0,?_⟩
    change D g ≠ D 0
    rwa [hD0]
  · refine ⟨0,xLabel,?_⟩
    change A3 0 ≠ A3 xLabel
    exact fun h => zero_ne_x (A3.injective h)

end
end Holant.Pauli.ExoticKlein.EightPort
