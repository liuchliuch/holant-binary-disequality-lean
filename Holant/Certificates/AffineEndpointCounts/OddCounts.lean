import Holant.Certificates.AffineEndpointCounts.OddChecks
import Holant.Certificates.AffineEndpointCounts.OddNecessity

/-! The 304 nonexceptional remaining states have exactly two actual affine shifts,
with the source's 176/128 histogram. -/
namespace Holant.Certificates.AffineEndpointCounts
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd

 theorem odd_phase_zero_iff (s : State) (h : phaseTest s 0) (δ : Fin 4) :
    phaseTest s δ ↔ δ=0 ∨ δ=2 := by
  obtain ⟨p,rfl⟩ := phaseTest_preimage s 0 h
  exact odd_family_phase_set p δ

 theorem odd_phase_one_iff (s : State) (h : phaseTest s 1) (δ : Fin 4) :
    phaseTest s δ ↔ δ=1 ∨ δ=3 := by
  obtain ⟨p,rfl⟩ := phaseTest_preimage s 1 h
  exact odd_shifted_family_phase_set p δ

 theorem odd_phase_classes_disjoint : Disjoint (oddPhaseStates 0) (oddPhaseStates 1) := by
  apply Finset.disjoint_left.mpr
  intro s h0 h1
  have hp0 := (Finset.mem_filter.mp h0).2.2.2
  have hp1 := (Finset.mem_filter.mp h1).2.2.2
  have hf := (odd_phase_zero_iff s hp0 1).mp hp1
  rcases hf with hf | hf <;> contradiction

 theorem odd_remaining_union : oddRemainingStates=oddPhaseStates 0 ∪ oddPhaseStates 1 := by
  ext s
  simp only [oddRemainingStates,oddPhaseStates,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · rintro ⟨hr,hn⟩
    rcases remaining_phase_test s hr hn with h0 | h1
    · exact Or.inl ⟨hr,hn,h0⟩
    · exact Or.inr ⟨hr,hn,h1⟩
  · rintro (⟨hr,hn,_⟩ | ⟨hr,hn,_⟩) <;> exact ⟨hr,hn⟩

 theorem odd_phase_histogram : (oddPhaseStates 0).card=176 ∧ (oddPhaseStates 1).card=128 := by
  rw [oddPhaseStates_card,oddPhaseStates_card]
  exact ⟨odd_even_shift_parameter_count,odd_odd_shift_parameter_count⟩

 theorem odd_remaining_count : oddRemainingStates.card=304 := by
  rw [odd_remaining_union,Finset.card_union_of_disjoint odd_phase_classes_disjoint,
    odd_phase_histogram.1,odd_phase_histogram.2]

 def oddValidShifts (s : State) : Finset (Fin 4) := Finset.univ.filter (phaseTest s)

 theorem oddValidShifts_mem_iff (s : State) (δ : Fin 4) :
    δ∈oddValidShifts s ↔ Affine (shiftedOdd s δ) := by
  simp only [oddValidShifts,Finset.mem_filter,Finset.mem_univ,true_and,shiftedOdd_affine_iff_phaseTest]

 theorem odd_phase_zero_set (s : State) (h : phaseTest s 0) : oddValidShifts s={0,2} := by
  ext δ
  simp only [oddValidShifts,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    Finset.mem_singleton,odd_phase_zero_iff s h]

 theorem odd_phase_one_set (s : State) (h : phaseTest s 1) : oddValidShifts s={1,3} := by
  ext δ
  simp only [oddValidShifts,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    Finset.mem_singleton,odd_phase_one_iff s h]

 theorem odd_remaining_valid_sets (s : State) (h : s∈oddRemainingStates) :
    oddValidShifts s={0,2} ∨ oddValidShifts s={1,3} := by
  obtain ⟨_,hr,hn⟩ := Finset.mem_filter.mp h
  rcases remaining_phase_test s hr hn with h0 | h1
  · exact Or.inl (odd_phase_zero_set s h0)
  · exact Or.inr (odd_phase_one_set s h1)

 theorem odd_remaining_exactly_two (s : State) (h : s∈oddRemainingStates) :
    (oddValidShifts s).card=2 := by
  rcases odd_remaining_valid_sets s h with hs | hs <;> rw [hs] <;> decide

 theorem odd_valid_set_histogram :
    (oddRemainingStates.filter (fun s => oddValidShifts s={0,2})).card=176 ∧
    (oddRemainingStates.filter (fun s => oddValidShifts s={1,3})).card=128 := by
  have h0 : oddRemainingStates.filter (fun s => oddValidShifts s={0,2})=oddPhaseStates 0 := by
    ext s
    simp only [oddRemainingStates,oddPhaseStates,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨hr,hn⟩,hs⟩
      refine ⟨hr,hn,?_⟩
      have hm : (0 : Fin 4)∈oddValidShifts s := by rw [hs]; simp
      exact (Finset.mem_filter.mp hm).2
    · rintro ⟨hr,hn,hp⟩
      exact ⟨⟨hr,hn⟩,odd_phase_zero_set s hp⟩
  have h1 : oddRemainingStates.filter (fun s => oddValidShifts s={1,3})=oddPhaseStates 1 := by
    ext s
    simp only [oddRemainingStates,oddPhaseStates,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨hr,hn⟩,hs⟩
      refine ⟨hr,hn,?_⟩
      have hm : (1 : Fin 4)∈oddValidShifts s := by rw [hs]; simp
      exact (Finset.mem_filter.mp hm).2
    · rintro ⟨hr,hn,hp⟩
      exact ⟨⟨hr,hn⟩,odd_phase_one_set s hp⟩
  rw [h0,h1]
  exact odd_phase_histogram

 theorem odd_all_affine_shifts_in_family (s : State) (δ : Fin 4)
    (h : Affine (shiftedOdd s δ)) :
    ∃ p : FamilyParameters,shiftedOdd s δ=shiftedOdd (familyState p) 0 :=
  shifted_in_family s δ ((shiftedOdd_affine_iff_phaseTest s δ).mp h)

end Holant.Certificates.AffineEndpointCounts
