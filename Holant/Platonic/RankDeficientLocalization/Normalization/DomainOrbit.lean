import Holant.Platonic.RankDeficientLocalization.Normalization.DomainPermutations
import Holant.Platonic.RankDeficientLocalization.Normalization.CardPresentations

/-! A.19 applied to the entire kernel-avoiding rich line.  Its actual three
points, all nonzero scales, and the recovered residual matching order are kept. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical

variable {g : PlatonicModel} {Φ : Mat →ₗ[ℂ] FourTensor}

def rainbowIndices (R : RainbowDomainLine Φ (representative g)) : Finset (Fin (size g)) :=
  {R.first,R.second,R.third}

theorem rainbowIndices_card (R : RainbowDomainLine Φ (representative g)) :
    (rainbowIndices R).card=3 := by
  rw [rainbowIndices,←R.exact_points]
  exact R.intersection_card

theorem rainbowIndices_secant (R : RainbowDomainLine Φ (representative g)) :
    DomainSecant g (rainbowIndices R) := by
  refine ⟨R.first,R.second,R.first_ne_second,?_⟩
  intro k
  rw [rainbowIndices,←R.exact_points]
  exact mem_matrixIntersection _ _ _

theorem domain_orbit (R : RainbowDomainLine Φ (representative g)) :
    ∃D : DomainAction g, ∃k : Fin 3 → Fin (size g), ∃c : Fin 3 → ℂ,
      Function.Injective k ∧ (∀r,c r≠0) ∧
      Finset.univ.image k=rainbowIndices R ∧
      ∀r,D.apply (normalTriangle r)=c r • representative g (k r) := by
  obtain ⟨U,V,hU,hV,hUV⟩ := PlatonicAtlas.actual_left_right_orbit g _ (rainbowIndices_secant R)
  let D : DomainAction g := ⟨U,V,false,hU,hV⟩
  have hex (r : Fin 3) : ∃k : Fin (size g),∃c : ℂ,c≠0 ∧
      D.apply (normalTriangle r)=c • representative g k :=
    (complete g _).mp (D.mem (normalTriangle_mem g r))
  choose k c hc he using hex
  have hmem (r : Fin 3) : k r∈rainbowIndices R := by
    apply (hUV (k r)).mpr
    refine ⟨normalIndex g r,?_,?_⟩
    · rw [rainbowIndices_card,normal_seed]
      exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
    · rw [normal_representative]
      exact (show Proportional (D.apply (normalTriangle r)) (representative g (k r)) from
        ⟨c r,hc r,he r⟩).symm
  have hinj : Function.Injective k := by
    intro r s hrs
    have hh : D.linear (normalTriangle r)=(c r/c s) • D.linear (normalTriangle s) := by
      change D.apply (normalTriangle r)=(c r/c s) • D.apply (normalTriangle s)
      rw [he r,he s,hrs,smul_smul,div_mul_cancel₀ _ (hc s)]
    have h := D.injective (hh.trans (D.linear.map_smul _ _).symm)
    exact normalTriangle_faithful r s h
  refine ⟨D,k,c,hinj,hc,?_,he⟩
  apply Finset.eq_of_subset_of_card_le
  · rintro i hi
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hi
    exact hmem r
  · rw [Finset.card_image_of_injective _ hinj,rainbowIndices_card]
    simp

theorem rainbow_card_nonzero (R : RainbowDomainLine Φ (representative g))
    (i : Fin (size g)) (hi : i∈rainbowIndices R) : Φ (representative g i)≠0 := by
  simp only [rainbowIndices,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl
  · exact R.card₀.nonzero
  · exact R.card₁.nonzero
  · exact R.card₂.nonzero

/-- Actual group directions and the selected rainbow force a bijection of the
three source points with the three residual matchings. -/
theorem domain_matching_order (R : RainbowDomainLine Φ (representative g))
    (hcards : ∀K : Mat,groupDirection g K → matchingCone g (Φ K)) :
    ∃D : DomainAction g, ∃ℓ : Equiv.Perm (Fin 3), ∀r : Fin 3,
      ∃U V : Mat,groupDirection g U ∧ groupDirection g V ∧
        Φ (D.apply (normalTriangle r))=matchingTensor (ℓ r) U V := by
  obtain ⟨D,k,c,hk,hc,himage,he⟩ := domain_orbit R
  have hkmem (r : Fin 3) : k r∈rainbowIndices R := by
    rw [←himage]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  have hn (r : Fin 3) : Φ (D.apply (normalTriangle r))≠0 := by
    rw [he r,map_smul]
    exact smul_ne_zero (hc r) (rainbow_card_nonzero R _ (hkmem r))
  have hex (r : Fin 3) : ∃l : Fin 3,∃U V : Mat,groupDirection g U ∧ groupDirection g V ∧
      Φ (D.apply (normalTriangle r))=matchingTensor l U V :=
    (matchingCone_presentation g _ (hcards _ (D.mem (normalTriangle_mem g r)))).resolve_left (hn r)
  choose l U V hU hV hF using hex
  have hInv (r : Fin 3) : InvertibleMatching (l r) (Φ (D.apply (normalTriangle r))) :=
    ⟨U r,V r,groupDirection_det_ne_zero g (hU r),groupDirection_det_ne_zero g (hV r),hF r⟩
  have hline : Φ (D.apply (normalTriangle 0))+Φ (D.apply (normalTriangle 1))=
      (2 : ℂ) • Φ (D.apply (normalTriangle 2)) := by
    have h := congrArg (fun K : Mat => Φ (D.linear K)) normalTriangle_relation
    simp only [map_add,map_smul,DomainAction.linear_apply] at h
    exact h
  have htypes := invertible_matching_sum_indices (hInv 0) (hInv 1)
    ((hInv 2).smul 2 (by norm_num)) hline
  have hnotcommon : ¬(l 0=l 1 ∧ l 1=l 2) := by
    rintro ⟨h01,h12⟩
    have hl (r : Fin 3) : l r=l 0 := by
      fin_cases r
      · rfl
      · exact h01.symm
      · exact (h01.trans h12).symm
    have hMatch (i : Fin (size g)) (hi : i∈rainbowIndices R)
        (E : NonsingularCard (Φ (representative g i))) : E.matching=fourMatching (l 0) := by
      rw [←himage] at hi
      obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hi
      have hval : Φ (representative g (k r))=
          matchingTensor (l r) ((c r)⁻¹ • U r) (V r) := by
        rw [matchingTensor_smul_left,←hF r,he r,map_smul,smul_smul,inv_mul_cancel₀ (hc r),one_smul]
      rw [←hl r]
      have hdu : (((c r)⁻¹ • U r) : Mat).det≠0 := by
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (hc r)))
          (groupDirection_det_ne_zero g (hU r))
      exact card_matching_of_tensor E hdu (groupDirection_det_ne_zero g (hV r)) hval
    exact R.different₀₁ ((hMatch R.first (by simp [rainbowIndices]) R.card₀).trans
      (hMatch R.second (by simp [rainbowIndices]) R.card₁).symm)
  have hdistinct := htypes.resolve_left hnotcommon
  have hli : Function.Injective l := by
    have hfinite : ∀t : Fin 3 → Fin 3,t 0≠t 1 → t 0≠t 2 → t 1≠t 2 → Function.Injective t := by decide
    exact hfinite l hdistinct.1 hdistinct.2.1 hdistinct.2.2
  refine ⟨D,Equiv.ofBijective l ⟨hli,Finite.surjective_of_injective hli⟩,?_⟩
  intro r
  exact ⟨U r,V r,hU r,hV r,hF r⟩

/-- Ordered physical-domain normalization: normalPlus has matching0,
normalMinus matching1, and Q0 matching2. No colouring or ordered-line premise. -/
theorem ordered_domain_matching (R : RainbowDomainLine Φ (representative g))
    (hcards : ∀K : Mat,groupDirection g K → matchingCone g (Φ K)) :
    ∃D : DomainAction g, ∀r : Fin 3,∃U V : Mat,
      groupDirection g U ∧ groupDirection g V ∧ Φ (D.apply (normalTriangle r))=matchingTensor r U V := by
  obtain ⟨D,ℓ,hℓ⟩ := domain_matching_order R hcards
  obtain ⟨E,c,hc,he⟩ := domain_ordering g ℓ.symm
  refine ⟨D.comp E,?_⟩
  intro r
  obtain ⟨U,V,hU,hV,hF⟩ := hℓ (ℓ.symm r)
  refine ⟨c r • U,V,groupDirection_smul g hU (hc r),hV,?_⟩
  rw [DomainAction.comp_apply,he r]
  change Φ (D.linear (c r • normalTriangle (ℓ.symm r)))=_
  rw [map_smul,map_smul,DomainAction.linear_apply,hF,matchingTensor_smul_left,ℓ.apply_symm_apply]

end
end Holant.Platonic.RankDeficientLocalization.Normalization
