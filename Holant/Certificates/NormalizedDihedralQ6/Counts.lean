import Holant.Certificates.NormalizedDihedralQ6.Maximum

/-! The full labelled multiplicities in Proposition A.9. Counting uses an
explicit bijection for each of the 48 sector-zero choices, never a Python
assertion or an assumed orbit size. -/
namespace Holant.Certificates.NormalizedDihedralQ6

abbrev Choices := Sector × Sector

theorem normalized_filter_card (P : Sector → Prop) [DecidablePred P] :
    ((Finset.univ : Finset Choices).filter (fun d => P (normalizeOdd d.1 d.2))).card =
      48 * ((Finset.univ : Finset Sector).filter P).card := by
  simpa only [Fintype.card_subtype] using normalized_property_card P

open scoped Classical in
theorem matching_choices_count :
    ((Finset.univ : Finset Choices).filter (fun d => matchingCoset (support d.1 d.2))).card = 96 := by
  have he : ((Finset.univ : Finset Choices).filter (fun d => matchingCoset (support d.1 d.2))) =
      Finset.univ.filter (fun d => printedWitness (normalizeOdd d.1 d.2) = none) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,original_matching_iff]
  rw [he,normalized_filter_card (fun d => printedWitness d = none),canonical_counts.1]

open scoped Classical in
theorem maximum_six_choices_count :
    ((Finset.univ : Finset Choices).filter
      (fun d => ¬ matchingCoset (support d.1 d.2) ∧ HasMaximum (support d.1 d.2) 6)).card = 1152 := by
  have he : ((Finset.univ : Finset Choices).filter
      (fun d => ¬ matchingCoset (support d.1 d.2) ∧ HasMaximum (support d.1 d.2) 6)) =
      Finset.univ.filter (fun d => ∃ p γ, printedWitness (normalizeOdd d.1 d.2) = some (p,γ,6)) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,original_maximum_iff]
  rw [he,normalized_filter_card (fun d => ∃ p γ, printedWitness d = some (p,γ,6)),canonical_counts.2.1]

open scoped Classical in
theorem maximum_eight_choices_count :
    ((Finset.univ : Finset Choices).filter
      (fun d => ¬ matchingCoset (support d.1 d.2) ∧ HasMaximum (support d.1 d.2) 8)).card = 1056 := by
  have he : ((Finset.univ : Finset Choices).filter
      (fun d => ¬ matchingCoset (support d.1 d.2) ∧ HasMaximum (support d.1 d.2) 8)) =
      Finset.univ.filter (fun d => ∃ p γ, printedWitness (normalizeOdd d.1 d.2) = some (p,γ,8)) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,original_maximum_iff]
  rw [he,normalized_filter_card (fun d => ∃ p γ, printedWitness d = some (p,γ,8)),canonical_counts.2.2]

theorem nonmatching_lowering (d₀ d₁ : Sector) (h : ¬ matchingCoset (support d₀ d₁)) :
    HasMaximum (support d₀ d₁) 6 ∨ HasMaximum (support d₀ d₁) 8 := by
  cases hw : printedWitness (normalizeOdd d₀ d₁) with
  | none => exact (h ((original_matching_iff d₀ d₁).mpr hw)).elim
  | some w =>
    rcases w with ⟨p,γ,n⟩
    have hn := (printed_witness (normalizeOdd d₀ d₁) p γ n hw).2.1
    have hm := ((original_maximum_iff d₀ d₁ n).mpr ⟨p,γ,hw⟩).2
    rcases hn with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr hm

open scoped Classical in
/-- Proposition A.9, with all labelled choices and the actual injective
four-port projection maximum. Matching cosets are the full semantic predicate. -/
theorem normalized_dihedral_support_lowering :
    Fintype.card Choices = 2304 ∧
    ((Finset.univ : Finset Choices).filter (fun d => matchingCoset (support d.1 d.2))).card = 96 ∧
    (∀ d₀ d₁, ¬ matchingCoset (support d₀ d₁) →
      HasMaximum (support d₀ d₁) 6 ∨ HasMaximum (support d₀ d₁) 8) ∧
    ((Finset.univ : Finset Choices).filter
      (fun d => ¬ matchingCoset (support d.1 d.2) ∧ HasMaximum (support d.1 d.2) 6)).card = 1152 ∧
    ((Finset.univ : Finset Choices).filter
      (fun d => ¬ matchingCoset (support d.1 d.2) ∧ HasMaximum (support d.1 d.2) 8)).card = 1056 :=
  ⟨all_labelled_choices_card,matching_choices_count,nonmatching_lowering,
    maximum_six_choices_count,maximum_eight_choices_count⟩

end Holant.Certificates.NormalizedDihedralQ6
