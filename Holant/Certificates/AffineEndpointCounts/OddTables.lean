import Holant.Certificates.AffineEndpointCounts.OddFamily
import Holant.Certificates.AffineEndpointCounts.OddNecessity

/-! The exact counts count distinct actual signatures, not parameter labels. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

 theorem odd_root_embed_injective : Function.Injective (fun k : Fin 4 => embed (fourthRoot k)) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (norm_num [fourthRoot,embed,Complex.ext_iff] at h)

 theorem complexOdd_injective : Function.Injective complexOdd := by
  intro s t h
  have ha (j : Fin 4) : alpha s j=alpha t j := by
    apply odd_root_embed_injective
    have he := congrFun h (singleWord j)
    simpa only [complexOdd,oddTable_single,a] using he
  have hb (j : Fin 4) : beta s j=beta t j := by
    apply odd_root_embed_injective
    have he := congrFun h (complementWord j)
    simpa only [complexOdd,oddTable_complement,b] using he
  exact Prod.ext (Prod.ext (ha 1) (Prod.ext (ha 2) (ha 3)))
    (Prod.ext (hb 0) (Prod.ext (hb 1) (Prod.ext (hb 2) (hb 3))))

 theorem complexOdd_normalized (s : State) : NormalizedOdd (complexOdd s) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [complexOdd,oddTable_single] using source_a0 s
  · intro x hx
    exact oddTable_even_zero _ _ x hx
  · intro j
    simp only [complexOdd,oddTable_single,oddTable_complement,a,b]
    exact ⟨fourthRoot_power _,fourthRoot_power _⟩

 def oddNormalizedTables : Finset (Signature ℂ 4) := by
  classical
  exact Finset.univ.image complexOdd

 def oddAffineFamilyTables : Finset (Signature ℂ 4) := by
  classical
  exact oddFamilyStates.image complexOdd

 def oddNativeRankTables : Finset (Signature ℂ 4) := by
  classical
  exact oddNativeRankStates.image complexOdd

 def oddDenseResidueTables : Finset (Signature ℂ 4) := by
  classical
  exact oddDenseResidueStates.image complexOdd

 theorem oddNormalizedTables_iff (f : Signature ℂ 4) :
    f∈oddNormalizedTables ↔ NormalizedOdd f := by
  classical
  simp only [oddNormalizedTables,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨s,rfl⟩
    exact complexOdd_normalized s
  · intro hf
    obtain ⟨s,hs⟩ := normalizedOdd_state f hf
    exact ⟨s,hs.symm⟩

 theorem odd_family_states_iff_affine (s : State) :
    s∈oddFamilyStates ↔ Affine (shiftedOdd s 0) := by
  simp only [oddFamilyStates,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,rfl⟩
    exact family_affine p
  · intro hs
    exact ⟨recoverFamily s 0,(phase_test_in_family s
      ((shiftedOdd_affine_iff_phaseTest s 0).mp hs)).symm⟩

 theorem oddAffineFamilyTables_iff (f : Signature ℂ 4) :
    f∈oddAffineFamilyTables ↔ NormalizedOdd f ∧
      ∃ g : Signature AlgebraicComplex 4,Affine g ∧ (fun x => (g x : ℂ))=f := by
  classical
  constructor
  · intro hf
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hf
    exact ⟨complexOdd_normalized s,shiftedOdd s 0,
      (odd_family_states_iff_affine s).mp hs,complexShiftedOdd_zero s⟩
  · rintro ⟨hn,g,hg,he⟩
    obtain ⟨s,rfl⟩ := normalizedOdd_state f hn
    have hsg : shiftedOdd s 0=g := by
      funext x
      apply Subtype.ext
      exact congrFun ((complexShiftedOdd_zero s).trans he.symm) x
    apply Finset.mem_image.mpr
    refine ⟨s,(odd_family_states_iff_affine s).mpr ?_,rfl⟩
    rw [hsg]
    exact hg

 theorem odd_actual_table_counts :
    oddNormalizedTables.card=16384 ∧ oddAffineFamilyTables.card=512 ∧
    oddNativeRankTables.card=336 ∧ oddDenseResidueTables.card=176 := by
  classical
  simp only [oddNormalizedTables,oddAffineFamilyTables,oddNativeRankTables,oddDenseResidueTables,
    Finset.card_image_of_injective _ complexOdd_injective,Finset.card_univ]
  exact ⟨state_count,odd_family_counts⟩

 theorem odd_native_rank_table_actual (f : Signature ℂ 4) (h : f∈oddNativeRankTables) :
    ∃ e : Fin 6,Matrix.rank (fun x y : Bool => nativeContract f e ![x,y])=1 ∧
      Gadget.Realizes ({⟨4,f⟩} : SignatureFamily ℂ) .disequality (nativeContract f e) := by
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp h
  exact odd_family_native_actual s hs

 theorem odd_dense_residue_table_actual (f : Signature ℂ 4) (h : f∈oddDenseResidueTables) :
    (¬∃ e : Fin 6,Matrix.rank (fun x y : Bool => nativeContract f e ![x,y])=1) ∧
    ∃ e : Fin 3,DenseProduct (twoCopyNative f (initialPair e)) ∧
      Gadget.Realizes ({⟨4,f⟩} : SignatureFamily ℂ) .disequality (twoCopyNative f (initialPair e)) := by
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp h
  exact odd_family_dense_actual s hs

 theorem odd_family_actual_table_injective :
    Function.Injective (fun p : FamilyParameters => complexOdd (familyState p)) :=
  complexOdd_injective.comp familyState_injective

end
end Holant.Certificates.AffineEndpointCounts
