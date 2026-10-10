import Holant.ReedMuller.CharacterRecognition.Basic

/-! Extract phase-coefficient constraints from literal sign-character pair cards. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ}

@[simp] theorem card_origin (Q : QuadraticPhase r) (j : Fin r) (b : ZMod 2) :
    card Q j b (origin r)=1+sign b*root (Q.linear j) := by simp [card]

theorem card_basis (Q : QuadraticPhase r) (j k : Fin r) (b : ZMod 2) (h : j≠k) :
    card Q j b (basis k)=root (Q.linear k)*(1+sign b*root (Q.linear j)*sign (beta Q j k)) := by
  rw [card,phase_basis,phase_two Q k j (Ne.symm h),beta_comm Q k j]
  ring

theorem card_two (Q : QuadraticPhase r) (j k m : Fin r) (b : ZMod 2)
    (hjk : j≠k) (hjm : j≠m) (hkm : k≠m) :
    card Q j b (xor (basis k) (basis m))=
      root (Q.linear k)*root (Q.linear m)*sign (beta Q k m)*
        (1+sign b*root (Q.linear j)*sign (beta Q j k+beta Q j m)) := by
  rw [card,phase_two Q k m hkm,phase_three Q j k m hjk hjm hkm,sign_add]
  ring

theorem PairCards.full_of_origin {Q : QuadraticPhase r} (h : PairCards Q)
    (j : Fin r) (b : ZMod 2) (hn : 1+sign b*root (Q.linear j)≠0) :
    SliceCharacter (card Q j b) j := by
  rcases h j b with hz|hf
  · exact False.elim (hn (by simpa using hz (origin r) rfl))
  · exact hf

/-- The scalar and all coordinate-linear phase factors cancel in the actual
four-point sign-character identity. -/
theorem card_rectangle {Q : QuadraticPhase r} {j : Fin r} {b : ZMod 2}
    (h : SliceCharacter (card Q j b) j) (k m : Fin r)
    (hjk : j≠k) (hjm : j≠m) (hkm : k≠m) :
    sign (beta Q k m)*(1+sign b*root (Q.linear j))*
        (1+sign b*root (Q.linear j)*sign (beta Q j k+beta Q j m))=
      (1+sign b*root (Q.linear j)*sign (beta Q j k))*
        (1+sign b*root (Q.linear j)*sign (beta Q j m)) := by
  have hh := h.rectangle (basis k) (basis m) (by simp [basis,hjk]) (by simp [basis,hjm])
  rw [card_two Q j k m b hjk hjm hkm,card_origin,card_basis Q j k b hjk,
    card_basis Q j m b hjm] at hh
  apply mul_left_cancel₀ (mul_ne_zero (root_ne_zero (Q.linear k)) (root_ne_zero (Q.linear m)))
  linear_combination hh

/-- In the all-odd case, the full plus cards force exactly the manuscript's
beta relation; no relation between phase parameters is a hypothesis. -/
theorem beta_relation_of_odd {Q : QuadraticPhase r} (h : PairCards Q)
    (ho : ∀ j,Odd (Q.linear j)) (j k m : Fin r)
    (hjk : j≠k) (hjm : j≠m) (hkm : k≠m) :
    beta Q k m=beta Q j k*beta Q j m := by
  have hf := h.full_of_origin j 0 (by simpa using odd_bracket_ne_zero (Q.linear j) (ho j) 0)
  apply odd_rectangle_forces (Q.linear j) (ho j)
  simpa using card_rectangle hf k m hjk hjm hkm

/-- The literal pair-card hypothesis, together with odd linear coefficients,
forces the binary mixed-coefficient graph to be empty or complete. -/
theorem empty_or_complete_of_odd {Q : QuadraticPhase r} (h : PairCards Q)
    (ho : ∀ j,Odd (Q.linear j)) :
    (∀ j k,beta Q j k=0) ∨ (∀ j k,j≠k → beta Q j k=1) :=
  graph_empty_or_complete (beta Q) (beta_comm Q) (beta_self Q) (beta_relation_of_odd h ho)

/-- An even coordinate selects the actual nonzero sign of its pair card. -/
theorem even_select_sign (q : ZMod 4) (hq : Even q) :
    ∃ b : ZMod 2,sign b*root q=1 := by
  rcases hq with rfl|rfl
  · exact ⟨0,by simp⟩
  · exact ⟨1,by simp⟩

/-- Fullness of the selected actual card rules out every nonzero entry in
an even coordinate's mixed row. -/
theorem even_row_zero {Q : QuadraticPhase r} (h : PairCards Q)
    (j : Fin r) (he : Even (Q.linear j)) : ∀ k,beta Q j k=0 := by
  obtain ⟨b,hb⟩ := even_select_sign (Q.linear j) he
  have hf := h.full_of_origin j b (by rw [hb]; norm_num)
  intro k
  by_cases hjk : j=k
  · subst k; simp
  rcases TwoTranslate.binary_cases (beta Q j k) with hz|ho
  · exact hz
  have hn := hf.nonzero (basis k) (by simp [basis,hjk])
  rw [card_basis Q j k b hjk,hb,ho] at hn
  simp at hn

/-- The same selected full card forces every other linear coefficient even. -/
theorem even_forces_all_even {Q : QuadraticPhase r} (h : PairCards Q)
    (j : Fin r) (he : Even (Q.linear j)) : ∀ k,Even (Q.linear k) := by
  obtain ⟨b,hb⟩ := even_select_sign (Q.linear j) he
  have hf := h.full_of_origin j b (by rw [hb]; norm_num)
  have hr := even_row_zero h j he
  intro k
  by_cases hjk : j=k
  · simpa [←hjk] using he
  have hh := hf.square (basis k) (by simp [basis,hjk])
  rw [card_basis Q j k b hjk,card_origin,hb,hr k] at hh
  simp only [sign_zero,mul_one] at hh
  apply even_of_root_square
  linear_combination (1/4 : ℂ)*hh

/-- Once one even coefficient exists, all mixed coefficients vanish. -/
theorem even_forces_empty {Q : QuadraticPhase r} (h : PairCards Q)
    (j : Fin r) (he : Even (Q.linear j)) : ∀ k m,beta Q k m=0 := by
  intro k m
  exact even_row_zero h k (even_forces_all_even h j he k) m

/-- Exhaustive dichotomy, derived from actual card coefficients. -/
theorem coefficient_dichotomy {Q : QuadraticPhase r} (h : PairCards Q) :
    ((∀ j,Even (Q.linear j)) ∧ ∀ j k,beta Q j k=0) ∨
    ((∀ j,Odd (Q.linear j)) ∧
      ((∀ j k,beta Q j k=0) ∨ (∀ j k,j≠k → beta Q j k=1))) := by
  classical
  by_cases he : ∃ j,Even (Q.linear j)
  · obtain ⟨j,hj⟩ := he
    exact Or.inl ⟨even_forces_all_even h j hj,even_forces_empty h j hj⟩
  have ho : ∀ j,Odd (Q.linear j) := fun j =>
    (even_or_odd (Q.linear j)).resolve_left (fun hj => he ⟨j,hj⟩)
  exact Or.inr ⟨ho,empty_or_complete_of_odd h ho⟩

end
end Holant.ReedMuller.CharacterRecognition
