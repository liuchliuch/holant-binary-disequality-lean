import Holant.ReedMuller.AffineRadon.SupportRank

/-! Literal flat-card hypotheses exclude the near-self-dual alternative.
Both full and cancelled orbit supports are derived from the actual quadratic
phase and compared with actual projected flat directions. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {r : ℕ} {f : Signature AlgebraicComplex (2*r)}

 theorem ActualNormalForm.orbit_zero_of_nonselfDual (hr : 4≤r) (A : ActualNormalForm f)
    (hd : FlatRadonCards (fun x => (f (wordVector x):ℂ))) (hn : ¬SelfDual A.direction)
    (v : BinaryVector (2*r)) (hv : Accessible v) (hvU : v∈A.direction)
    (hvO : v∈dotOrthogonal A.direction) :
    ∀ x,(f (wordVector x):ℂ)+(f (wordVector (x+v)):ℂ)=0 := by
  let g : BinaryVector (2*r) → ℂ := fun x => (f (wordVector x):ℂ)
  have hRank := A.support_half_rank hr hd
  obtain ⟨F,hF,hflat⟩ := hd v hv
  have hperp : ∀ x,x∈A.direction → dot x F.v=0 := by
    intro x hx
    rw [hF]
    exact hvO x hx
  have H := A.complex_signed_locus v hvU 0
  simp only [CharacterFlat.sign_zero,one_mul] at H
  rcases H with hz | hs | ⟨b,D,hb,hDU,hvD,hDim,hD⟩
  · exact hz
  · have hsp : ∀ x,g x+g (x+F.v)≠0 ↔ x-A.shift∈A.direction := by simpa only [hF,g] using hs
    have hc := RadonFrame.orbit_support_flat_card_selfDual F (dot A.shift F.v)
      g A.shift A.shift A.direction hsp (by simp) rfl (hflat _)
    exact False.elim (hn (RadonFrame.selfDual_of_projected_selfDual F A.direction hperp (by omega) hc))
  · have hsp : ∀ x,g x+g (x+F.v)≠0 ↔ x-b∈D := by simpa only [hF,g] using hD
    have hc := RadonFrame.orbit_support_flat_card_dimension F (dot b F.v)
      g b b D hsp (by simp) rfl (hflat _)
    have hDp : ∀ x,x∈D → dot x F.v=0 := fun x hx => hperp x (hDU hx)
    have hDv : F.v∈D := by simpa only [hF] using hvD
    have hproj := RadonFrame.projectedLayerDimension_add_one_of_perpendicular_mem F D hDp hDv
    omega

 theorem ActualNormalForm.direction_selfDual (hr : 4≤r) (A : ActualNormalForm f)
    (hd : FlatRadonCards (fun x => (f (wordVector x):ℂ))) : SelfDual A.direction := by
  have hRank := A.support_half_rank hr hd
  have hAcc := A.accessible_orthogonal_mem hr hd
  rcases selfDual_or_nearSelfDual hr A.direction hRank hAcc with he | hnear
  · exact (selfDual_iff_eq_dotOrthogonal _).mpr he
  · obtain ⟨hA,hArank,u,hu,huu,hSup,hDisj⟩ := hnear
    let A0 := evenSpace (2*r) ⊓ dotOrthogonal A.direction
    have hn : ¬SelfDual A.direction := by
      intro h
      have H := (h u).mp hu u hu
      rw [huu] at H
      exact one_ne_zero H
    obtain ⟨p,q,hp,hq,hpa,hqa,hpqa⟩ := exists_accessible_triple A0
      (fun x hx => hx.1) (by dsimp only [A0];omega)
    have hpz := A.orbit_zero_of_nonselfDual hr hd hn p hpa (hA hp) hp.2
    have hqz := A.orbit_zero_of_nonselfDual hr hd hn q hqa (hA hq) hq.2
    have hpq := A0.add_mem hp hq
    have hpqz := A.orbit_zero_of_nonselfDual hr hd hn (p+q) hpqa (hA hpq) hpq.2
    let g : BinaryVector (2*r) → ℂ := fun x => (f (wordVector x):ℂ)
    have hgn : g≠0 := by
      intro h
      exact ((A.complex_support A.shift).mpr (by simp)) (congrFun h A.shift)
    rcases three_orbit_sums_not_all_zero g hgn p q with ⟨x,hx⟩ | ⟨x,hx⟩ | ⟨x,hx⟩
    · exact False.elim (hx (hpz x))
    · exact False.elim (hx (hqz x))
    · exact False.elim (hx (hpqz x))

end
end Holant.ReedMuller.AffineRadon
