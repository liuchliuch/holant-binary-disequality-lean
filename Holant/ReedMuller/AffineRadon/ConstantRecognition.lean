import Holant.ReedMuller.AffineRadon.SelfDualRecognition

/-! Actual nonzero flat quotient cards force constant original orbit sums;
three accessible directions then force the whole original coefficient table
constant on its derived self-dual support. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {f : Signature AlgebraicComplex (2*r)}

 theorem flat_constant_nonzero_support (h : Signature ℂ n) (hf : Flat h) :
    ∃ c : ℂ,c≠0 ∧ ∀ x,h x≠0 → h x=c := by
  obtain ⟨c,a,D,hD,rfl⟩ := hf
  refine ⟨c,c.ne_zero,?_⟩
  intro x hx
  unfold flatSignature at hx ⊢
  split_ifs with h
  · rfl
  · exact False.elim (hx (by simp [h]))

 theorem ActualNormalForm.constant_orbit_sum (hr : 4≤r) (A : ActualNormalForm f)
    (hd : FlatRadonCards (fun x => (f (wordVector x):ℂ)))
    (v : BinaryVector (2*r)) (hv : Accessible v) (hvU : v∈A.direction) :
    ∃ c : ℂ,∀ x,x-A.shift∈A.direction → (f (wordVector x):ℂ)+(f (wordVector (x+v)):ℂ)=c := by
  let g : BinaryVector (2*r) → ℂ := fun x => (f (wordVector x):ℂ)
  have hRank := A.support_half_rank hr hd
  have hSelf := A.direction_selfDual hr hd
  obtain ⟨F,hF,hflat⟩ := hd v hv
  have hperp : ∀ x,x∈A.direction → dot x F.v=0 := by
    intro x hx
    rw [hF]
    exact (hSelf x).mp hx v hvU
  have H := A.complex_signed_locus v hvU 0
  simp only [CharacterFlat.sign_zero,one_mul] at H
  rcases H with hz | hs | ⟨b,D,hb,hDU,hvD,hDim,hD⟩
  · exact ⟨0,fun x _ => hz x⟩
  · let ε := dot A.shift F.v
    let card : Signature ℂ (2*r-2) := fun x => RadonFrame.actualRadon F ε g (vectorWord x)
    have hsp : ∀ x,g x+g (x+F.v)≠0 ↔ x-A.shift∈A.direction := by simpa only [hF,g] using hs
    have hc := RadonFrame.actualRadon_support_of_orbit_support F ε g A.shift A.shift A.direction
      hsp (by simp) rfl
    have hn : card≠0 := by
      intro hz
      have he := congrFun hz (wordVector (RadonFrame.boundaryProjection F A.shift))
      have hne := (hc (RadonFrame.boundaryProjection F A.shift)).mpr (by simp)
      exact hne (by simpa only [card,vector_word,Pi.zero_apply] using he)
    obtain ⟨c,hcn,hconst⟩ := flat_constant_nonzero_support card ((hflat ε).resolve_left hn)
    refine ⟨c,?_⟩
    intro x hx
    have hl : dot x F.v=ε := by
      have h := hperp (x-A.shift) hx
      have he : dot (x-A.shift) F.v=dot x F.v-dot A.shift F.v := by
        simp [dot,sub_mul,Finset.sum_sub_distrib]
      rw [he] at h
      exact sub_eq_zero.mp h
    have he := RadonFrame.actualRadon_projection F g x
    rw [hl] at he
    have hcard : card (wordVector (RadonFrame.boundaryProjection F x))=g x+g (x+F.v) := by
      simpa only [card,vector_word] using he
    have hne : card (wordVector (RadonFrame.boundaryProjection F x))≠0 := by
      rw [hcard]
      exact (hsp x).mpr hx
    have hvv := hconst _ hne
    rw [hcard] at hvv
    simpa only [g,hF] using hvv
  · have hsp : ∀ x,g x+g (x+F.v)≠0 ↔ x-b∈D := by simpa only [hF,g] using hD
    have hc := RadonFrame.orbit_support_flat_card_dimension F (dot b F.v)
      g b b D hsp (by simp) rfl (hflat _)
    have hDp : ∀ x,x∈D → dot x F.v=0 := fun x hx => hperp x (hDU hx)
    have hDv : F.v∈D := by simpa only [hF] using hvD
    have hproj := RadonFrame.projectedLayerDimension_add_one_of_perpendicular_mem F D hDp hDv
    omega

 theorem ActualNormalForm.flat_of_radon_cards (hr : 4≤r) (A : ActualNormalForm f)
    (hd : FlatRadonCards (fun x => (f (wordVector x):ℂ))) : Flat (fun x => (f x:ℂ)) := by
  have hSelf := A.direction_selfDual hr hd
  have hRank := A.support_half_rank hr hd
  have hEven : ∀ x,x∈A.direction → dot (ones (2*r)) x=0 := by
    intro x hx
    rw [dot_ones]
    exact (hSelf x).mp hx x hx
  obtain ⟨p,q,hp,hq,hpa,hqa,hpqa⟩ := exists_accessible_triple A.direction hEven (by omega)
  obtain ⟨cp,hcp⟩ := A.constant_orbit_sum hr hd p hpa hp
  obtain ⟨cq,hcq⟩ := A.constant_orbit_sum hr hd q hqa hq
  obtain ⟨cpq,hcpq⟩ := A.constant_orbit_sum hr hd (p+q) hpqa (A.direction.add_mem hp hq)
  exact A.flat_of_three_orbit_sums hSelf p q hp cp cq cpq hcp hcq hcpq

end
end Holant.ReedMuller.AffineRadon
