import Holant.Certificates.AffineEndpointCounts.OddCounts
import Holant.Certificates.AffineEndpointCounts.OddTables

/-! Proposition A.2(v): exact normalized odd counts and native-network semantics.
The analytic phase shift is an operation on coefficients, not a supplied gadget. -/
namespace Holant.Certificates.AffineEndpointCounts
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
noncomputable section

 theorem odd_affine_shift_actual_exit (s : State) (δ : Fin 4)
    (h : Affine (shiftedOdd s δ)) :
    NativeRankOrDense (phaseShift (complexOdd s) δ) := by
  obtain ⟨p,hp⟩ := odd_all_affine_shifts_in_family s δ h
  have hc : complexShiftedOdd s δ=complexOdd (familyState p) := by
    rw [←complexShiftedOdd_zero]
    funext x
    exact congrArg (fun f : Signature AlgebraicComplex 4 => (f x : ℂ)) hp
  rw [←complexShiftedOdd_phaseShift,hc]
  exact family_rank_or_dense p

 theorem odd_exceptional_count_and_exit :
    ((Finset.univ : Finset State).filter Exceptional).card=64 ∧
    ∀ s,Exceptional s → classify s=.remaining ∧ SupportSixExit (complexOdd s) := by
  refine ⟨exceptional_count,?_⟩
  intro s hs
  exact ⟨exceptional_remaining s hs,exceptional_actual_exit s hs⟩

 theorem odd_remaining_shift_semantics (s : State) (h : s∈oddRemainingStates) :
    (oddValidShifts s).card=2 ∧
    (oddValidShifts s={0,2} ∨ oddValidShifts s={1,3}) ∧
    (∀ δ,δ∈oddValidShifts s ↔ Affine (shiftedOdd s δ)) ∧
    (∀ δ,δ∈oddValidShifts s →
      (∃ p : FamilyParameters,shiftedOdd s δ=shiftedOdd (familyState p) 0) ∧
      NativeRankOrDense (phaseShift (complexOdd s) δ)) := by
  refine ⟨odd_remaining_exactly_two s h,odd_remaining_valid_sets s h,oddValidShifts_mem_iff s,?_⟩
  intro δ hδ
  have ha := (oddValidShifts_mem_iff s δ).mp hδ
  exact ⟨odd_all_affine_shifts_in_family s δ ha,odd_affine_shift_actual_exit s δ ha⟩

/-- All five numerical statements in A.2(v), each on the literal state space,
with actual affine membership and actual native contraction conclusions. -/
 theorem source_A2v_odd_counts :
    Fintype.card State=16384 ∧ routeCount .rankOne=15792 ∧
    routeCount .infiniteOrder=224 ∧ routeCount .remaining=368 ∧
    ((Finset.univ : Finset State).filter Exceptional).card=64 ∧
    oddRemainingStates.card=304 ∧
    (oddRemainingStates.filter (fun s => oddValidShifts s={0,2})).card=176 ∧
    (oddRemainingStates.filter (fun s => oddValidShifts s={1,3})).card=128 ∧
    oddFamilyStates.card=512 ∧ oddNativeRankStates.card=336 ∧ oddDenseResidueStates.card=176 :=
  ⟨deterministic_partition.1,deterministic_partition.2.1,
    deterministic_partition.2.2.1,deterministic_partition.2.2.2,
    exceptional_count,odd_remaining_count,odd_valid_set_histogram.1,odd_valid_set_histogram.2,
    odd_family_counts⟩

/-- Every normalized full-support odd table has the frozen source classification,
while every nonexceptional remainder has exactly the certified two affine shifts. -/
 theorem source_A2v_normalized_odd (f : Signature ℂ 4) (hf : NormalizedOdd f) :
    ∃ s : State,f=complexOdd s ∧
      (classify s=.rankOne → RankOneExit f) ∧
      (classify s=.infiniteOrder → InfiniteExit f) ∧
      (classify s=.remaining →
        (Exceptional s ∧ SupportSixExit f) ∨
        (s∈oddRemainingStates ∧ (oddValidShifts s).card=2 ∧
          (oddValidShifts s={0,2} ∨ oddValidShifts s={1,3}) ∧
          ∀ δ,δ∈oddValidShifts s ↔ Affine (shiftedOdd s δ))) := by
  obtain ⟨s,hs,hr,hi,he⟩ := fourth_root_odd_contractions f hf
  refine ⟨s,hs,hr,hi,?_⟩
  intro hc
  rcases he hc with h | h
  · exact Or.inl h
  · have hm : s∈oddRemainingStates := Finset.mem_filter.mpr ⟨Finset.mem_univ s,hc,h.1⟩
    exact Or.inr ⟨hm,odd_remaining_exactly_two s hm,odd_remaining_valid_sets s hm,oddValidShifts_mem_iff s⟩

end
end Holant.Certificates.AffineEndpointCounts
