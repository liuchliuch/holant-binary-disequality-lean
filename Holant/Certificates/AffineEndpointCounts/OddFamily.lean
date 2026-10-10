import Holant.Certificates.AffineEndpointCounts.OddData

/-! Exact native-loop/dense partition of the actual 512 odd affine tables. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def OddNativeRankOne (s : State) : Prop :=
  ∃ e : Fin 6,Matrix.rank (fun x y : Bool => nativeContract (complexOdd s) e ![x,y])=1

theorem rankOneTest_iff_actual_rank (P Q : Gaussian) :
    rankOneTest (P,Q)=true ↔ (transfer P Q).rank=1 := by
  constructor
  · exact fun h => (rankOneTest_rank P Q h).1
  · intro h
    classical
    rw [transfer,Matrix.rank_diagonal,Fintype.card_subtype] at h
    by_cases hP : P=(0,0) <;> by_cases hQ : Q=(0,0)
    all_goals simp [Finset.filter_insert,Finset.filter_singleton,embed_zero_iff,hP,hQ] at h
    all_goals simp [rankOneTest,hP,hQ]

theorem odd_native_rank_iff (p : FamilyParameters) :
    OddNativeRankOne (familyState p) ↔ hasNativeRankOne p=true := by
  simp only [OddNativeRankOne,complexOdd_native_matrix,hasNativeRankOne,List.any_eq_true,List.mem_ofFn]
  constructor
  · rintro ⟨e,he⟩
    exact ⟨nativePair (familyState p) e,⟨e,rfl⟩,(rankOneTest_iff_actual_rank _ _).mpr he⟩
  · rintro ⟨q,⟨e,rfl⟩,he⟩
    exact ⟨e,(rankOneTest_iff_actual_rank _ _).mp he⟩

def oddFamilyStates : Finset State := Finset.univ.image familyState

def oddNativeRankStates : Finset State :=
  (Finset.univ.filter (fun p => hasNativeRankOne p=true)).image familyState

def oddDenseResidueStates : Finset State :=
  (Finset.univ.filter (fun p => hasNativeRankOne p=false)).image familyState

theorem odd_native_rank_states_iff (s : State) :
    s∈oddNativeRankStates ↔ s∈oddFamilyStates ∧ OddNativeRankOne s := by
  simp only [oddNativeRankStates,oddFamilyStates,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,rfl⟩,(odd_native_rank_iff p).mpr hp⟩
  · rintro ⟨⟨p,rfl⟩,hr⟩
    exact ⟨p,(odd_native_rank_iff p).mp hr,rfl⟩

theorem odd_dense_residue_states_iff (s : State) :
    s∈oddDenseResidueStates ↔ s∈oddFamilyStates ∧ ¬OddNativeRankOne s := by
  simp only [oddDenseResidueStates,oddFamilyStates,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨⟨p,rfl⟩,?_⟩
    rw [odd_native_rank_iff,hp]
    decide
  · rintro ⟨⟨p,rfl⟩,hr⟩
    refine ⟨p,?_,rfl⟩
    rw [odd_native_rank_iff] at hr
    exact Bool.eq_false_iff.mpr hr

theorem odd_family_counts : oddFamilyStates.card=512 ∧
    oddNativeRankStates.card=336 ∧ oddDenseResidueStates.card=176 := by
  refine ⟨affine_family_count,?_,?_⟩
  · rw [oddNativeRankStates,Finset.card_image_of_injective _ familyState_injective]
    exact affine_native_loop_histogram.1
  · rw [oddDenseResidueStates,Finset.card_image_of_injective _ familyState_injective]
    exact affine_native_loop_histogram.2

theorem odd_family_native_actual (s : State) (h : s∈oddNativeRankStates) :
    ∃ e : Fin 6,Matrix.rank (fun x y : Bool => nativeContract (complexOdd s) e ![x,y])=1 ∧
      Gadget.Realizes ({⟨4,complexOdd s⟩} : SignatureFamily ℂ) .disequality
        (nativeContract (complexOdd s) e) := by
  obtain ⟨e,he⟩ := ((odd_native_rank_states_iff s).mp h).2
  exact ⟨e,he,nativeContract_realizes _ _⟩

theorem odd_family_dense_actual (s : State) (h : s∈oddDenseResidueStates) :
    ¬OddNativeRankOne s ∧
    ∃ e : Fin 3,DenseProduct (twoCopyNative (complexOdd s) (initialPair e)) ∧
      Gadget.Realizes ({⟨4,complexOdd s⟩} : SignatureFamily ℂ) .disequality
        (twoCopyNative (complexOdd s) (initialPair e)) := by
  obtain ⟨hf,hn⟩ := (odd_dense_residue_states_iff s).mp h
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hf
  refine ⟨hn,?_⟩
  rcases family_rank_or_dense p with hr | hd
  · obtain ⟨e,he,_⟩ := hr
    exact False.elim (hn ⟨e,he⟩)
  · exact hd

end
end Holant.Certificates.AffineEndpointCounts
