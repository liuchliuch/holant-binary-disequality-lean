import Holant.Certificates.RainbowOrbit.GeneratedOrbit

/-! The exact number of actual rainbow lines through the normalized P0(I,I)
point, from the faithful original three-matrix orbit parameterization. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
local instance rainbowIncidencesPointDecidable : DecidableEq Point := Classical.decEq _

 theorem inverseTranspose_exists (g : PlatonicModel) (i : Fin (size g)) :
    ∃j : Fin (size g),Proportional (representative g i)⁻¹.transpose (representative g j) :=
  (complete g _).mp (direction_inverseTranspose g (representative_mem g i))

 def starIndex (g : PlatonicModel) (i : Fin (size g)) : Fin (size g) :=
  Classical.choose (inverseTranspose_exists g i)

 theorem starIndex_proportional (g : PlatonicModel) (i : Fin (size g)) :
    Proportional (representative g i)⁻¹.transpose (representative g (starIndex g i)) :=
  Classical.choose_spec (inverseTranspose_exists g i)

 theorem orbit_zero_at_base_iff (g : PlatonicModel) (t : OrbitIndex g) :
    orbitPoint g t 0=basePoint 0 ↔ t 0=identityIndex g ∧ t 2=starIndex g (t 1) := by
  have he : act (orbitLegs g t) A=P0 (representative g (t 0)).transpose
      (representative g (t 1)*(representative g (t 2)).transpose) := by
    rw [A_matrix,act_P0]
    simp [orbitLegs,reducedLegs]
  have hU := representative_det_ne_zero g (t 0)
  have hV : (representative g (t 1)*(representative g (t 2)).transpose).det≠0 := by
    simp [Matrix.det_mul,representative_det_ne_zero]
  constructor
  · intro hp
    have hh := (proportional_point_iff _ _ _ _).mpr hp
    change Proportional (act (orbitLegs g t) A) A at hh
    rw [he,A_matrix] at hh
    have hf := proportional_matching_factors 0 _ _ (1 : BinaryMatrix) (1 : BinaryMatrix)
      (by simpa using hU) hV hh
    have hfirst : Proportional (representative g (t 0)) (representative g (identityIndex g)) := by
      simpa only [Matrix.transpose_transpose,Matrix.transpose_one,representative_identity] using hf.1.transpose
    have hlast : Proportional (representative g (t 2)) (representative g (t 1))⁻¹.transpose := by
      have h := (hf.2.mul_left (representative g (t 1))⁻¹).transpose
      simpa only [←mul_assoc,Matrix.nonsing_inv_mul _
        (isUnit_iff_ne_zero.mpr (representative_det_ne_zero g (t 1))),
        one_mul,mul_one,Matrix.transpose_transpose] using h
    obtain ⟨c,_,hc⟩ := hfirst
    obtain ⟨d,_,hd⟩ := hlast.trans (starIndex_proportional g (t 1))
    exact ⟨projectively_injective g _ _ c hc,projectively_injective g _ _ d hd⟩
  · rintro ⟨hfirst,hlast⟩
    apply (proportional_point_iff _ _ _ _).mp
    change Proportional (act (orbitLegs g t) A) A
    rw [he,A_matrix,hfirst,representative_identity,Matrix.transpose_one,hlast]
    have hf : Proportional (representative g (t 1)*
        (representative g (starIndex g (t 1))).transpose) (1 : BinaryMatrix) := by
      have h := ((starIndex_proportional g (t 1)).symm.transpose).mul_left (representative g (t 1))
      simpa only [Matrix.transpose_transpose,Matrix.mul_nonsing_inv _
        (isUnit_iff_ne_zero.mpr (representative_det_ne_zero g (t 1)))] using h
    exact matching_proportional 0 (Proportional.refl (1 : BinaryMatrix)) hf

 theorem base_mem_line_iff (g : PlatonicModel) (t : OrbitIndex g) :
    basePoint 0∈line g t ↔ orbitPoint g t 0=basePoint 0 := by
  constructor
  · intro h
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp h
    have he : r=0 := (orbitPoint_rainbow g t).point_labels (basePoint_rainbow g) r 0 hr
    simpa [he] using hr
  · intro h
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,h⟩

 def throughBaseIndex (g : PlatonicModel) (i : Fin (size g)) : OrbitIndex g :=
  ![identityIndex g,i,starIndex g i]

 theorem throughBaseIndex_injective (g : PlatonicModel) : Function.Injective (throughBaseIndex g) := by
  intro i j h
  exact congrFun h 1

 theorem throughBaseIndex_exact (g : PlatonicModel) :
    Finset.univ.filter (fun t : OrbitIndex g => basePoint 0∈line g t)=
      Finset.univ.image (throughBaseIndex g) := by
  ext t
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,
    base_mem_line_iff,orbit_zero_at_base_iff]
  constructor
  · rintro ⟨h0,h2⟩
    refine ⟨t 1,?_⟩
    funext r
    fin_cases r <;> simp [throughBaseIndex,h0,h2]
  · rintro ⟨i,rfl⟩
    simp [throughBaseIndex]

/-- Counts the semantic unordered rainbow lines, with their exact point
sets, through the original normalized P0(Q0,Q0) point. -/
 theorem rainbow_lines_through_base (g : PlatonicModel) :
    ((lines g).filter (fun S => basePoint 0∈S)).card=size g := by
  rw [lines,Finset.filter_map,Finset.card_map]
  change (Finset.univ.filter (fun t : OrbitIndex g => basePoint 0∈line g t)).card=_
  rw [throughBaseIndex_exact,Finset.card_image_of_injective _ (throughBaseIndex_injective g)]
  simp

end
end Holant.Certificates.PlatonicAtlas
