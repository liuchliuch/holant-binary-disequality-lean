import Holant.Certificates.RainbowOrbit.Geometry
import Holant.Certificates.MatchingProductBridge.GroupInverses

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev GroupLegs (g : PlatonicModel) (L : Legs) : Prop := ∀j,groupDirection g (L j)

theorem direction_one (g : PlatonicModel) : groupDirection g (1 : BinaryMatrix) := by
  rw [←representative_identity g]
  exact representative_mem g _

theorem direction_transpose (g : PlatonicModel) {U : BinaryMatrix} (hU : groupDirection g U) :
    groupDirection g U.transpose := groupDirection_transpose g hU

theorem direction_inverse (g : PlatonicModel) {U : BinaryMatrix} (hU : groupDirection g U) :
    groupDirection g (U⁻¹ : BinaryMatrix) := groupDirection_inverse g hU

theorem direction_inverseTranspose (g : PlatonicModel) {U : BinaryMatrix} (hU : groupDirection g U) :
    groupDirection g U⁻¹.transpose := direction_transpose g (direction_inverse g hU)

theorem GroupLegs.det {g : PlatonicModel} {L : Legs} (hL : GroupLegs g L) :
    ∀j,(L j).det≠0 := fun j => groupDirection_det_ne_zero g (hL j)

theorem GroupLegs.inverse {g : PlatonicModel} {L : Legs} (hL : GroupLegs g L) :
    GroupLegs g (fun j => (L j)⁻¹) := fun j => direction_inverse g (hL j)

theorem normalization_mem (g : PlatonicModel) (U V S : BinaryMatrix)
    (hU : groupDirection g U) (hV : groupDirection g V) (hS : groupDirection g S) :
    GroupLegs g (normalization U V S) := by
  have hs := groupDirection_mul g (groupDirection_mul g (direction_inverse g hU) hS)
    (direction_inverseTranspose g hV)
  have hfirst : GroupLegs g (firstNormalization U V) := by
    intro j
    fin_cases j <;> simp only [firstNormalization,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Matrix.cons_val_fin_one]
    · exact direction_inverse g hU
    · exact direction_one g
    · exact direction_inverse g hV
    · exact direction_one g
  have hsecond : GroupLegs g (secondNormalization (U⁻¹*S*V⁻¹.transpose)) := by
    intro j
    fin_cases j <;> simp only [secondNormalization,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Matrix.cons_val_fin_one]
    · exact direction_inverse g hs
    · exact direction_transpose g hs
    · exact direction_one g
    · exact direction_one g
  exact fun j => groupDirection_mul g (hsecond j) (hfirst j)

def base (r : Fin 3) : FourTensor := ![A,B,C] r

theorem base_nonzero (r : Fin 3) : base r≠0 := by
  have h0 : (Matrix.of Q0).det≠0 :=
    groupDirection_det_ne_zero .tetrahedral (quaternion_axis_direction .tetrahedral 0)
  have h2 : (Matrix.of Q2).det≠0 :=
    groupDirection_det_ne_zero .tetrahedral (quaternion_axis_direction .tetrahedral 2)
  fin_cases r
  · exact matching_nonzero 0 _ _ h0 h0
  · exact matching_nonzero 1 _ _ h0 h0
  · exact matching_nonzero 2 _ _ h2 h2


theorem base_labels (r s : Fin 3) (h : Proportional (base r) (base s)) : r=s := by
  obtain ⟨U,V,hU,hV,he⟩ : InvertibleMatching r (base r) := by
    fin_cases r
    · exact A_invertibleMatching
    · exact B_invertibleMatching
    · exact ⟨_,_,groupDirection_det_ne_zero .tetrahedral (quaternion_axis_direction .tetrahedral 2),
        groupDirection_det_ne_zero .tetrahedral (quaternion_axis_direction .tetrahedral 2),rfl⟩
  obtain ⟨S,T,hS,hT,hf⟩ : InvertibleMatching s (base s) := by
    fin_cases s
    · exact A_invertibleMatching
    · exact B_invertibleMatching
    · exact ⟨_,_,groupDirection_det_ne_zero .tetrahedral (quaternion_axis_direction .tetrahedral 2),
        groupDirection_det_ne_zero .tetrahedral (quaternion_axis_direction .tetrahedral 2),rfl⟩
  rw [he,hf] at h
  exact proportional_matching_labels r s U V S T hU hV hS hT h

theorem stabilizer_fixes_base (T : BinaryMatrix) (hT : T.det≠0) (r : Fin 3) :
    act (stabilizerTuple T) (base r)=base r := by
  obtain ⟨h0,h1,h2⟩ := stabilizer_fixes T hT
  fin_cases r <;> assumption

def reducedTuple (L : Legs) : Legs := fun j => L j*stabilizerTuple (L 0)⁻¹ j

theorem reducedTuple_zero (L : Legs) (hL : (L 0).det≠0) : reducedTuple L 0=1 := by
  simp [reducedTuple,stabilizerTuple,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL)]

theorem reducedTuple_mem (g : PlatonicModel) (L : Legs) (hL : GroupLegs g L) :
    GroupLegs g (reducedTuple L) := by
  intro j
  apply groupDirection_mul g (hL j)
  fin_cases j <;> simp only [stabilizerTuple,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.cons_val_fin_one]
  · exact direction_inverse g (hL 0)
  · exact direction_inverseTranspose g (direction_inverse g (hL 0))
  · exact direction_inverseTranspose g (direction_inverse g (hL 0))
  · exact direction_inverse g (hL 0)

theorem reducedTuple_action (L : Legs) (hL : (L 0).det≠0) (r : Fin 3) :
    act (reducedTuple L) (base r)=act L (base r) := by
  unfold reducedTuple
  rw [←act_comp,stabilizer_fixes_base _ (by simpa [Matrix.det_nonsing_inv] using hL) r]

theorem reducedTuple_eq (L : Legs) (hL : (L 0).det≠0) :
    reducedTuple L=reducedLegs (reducedTuple L 1) (reducedTuple L 2) (reducedTuple L 3) := by
  funext j
  fin_cases j
  · exact reducedTuple_zero L hL
  all_goals rfl

def InMatching (g : PlatonicModel) (r : Fin 3) (F : FourTensor) : Prop :=
  ∃ U V : BinaryMatrix,groupDirection g U ∧ groupDirection g V ∧ F=matchingTensor r U V

theorem base_inMatching (g : PlatonicModel) (r : Fin 3) : InMatching g r (base r) := by
  have h0 : groupDirection g (Matrix.of Q0) := quaternion_axis_direction g 0
  have h2 : groupDirection g (Matrix.of Q2) := quaternion_axis_direction g 2
  fin_cases r
  · exact ⟨_,_,h0,h0,rfl⟩
  · exact ⟨_,_,h0,h0,rfl⟩
  · exact ⟨_,_,h2,h2,rfl⟩

theorem InMatching.act {g : PlatonicModel} {r : Fin 3} {F : FourTensor}
    (hF : InMatching g r F) (L : Legs) (hL : GroupLegs g L) : InMatching g r (act L F) := by
  obtain ⟨U,V,hU,hV,rfl⟩ := hF
  have hmem (i j : Fin 4) (M : BinaryMatrix) (hM : groupDirection g M) :
      groupDirection g (L i*M*(L j).transpose) :=
    groupDirection_mul g (groupDirection_mul g (hL i) hM) (direction_transpose g (hL j))
  fin_cases r
  · exact ⟨_,_,hmem 0 1 U hU,hmem 2 3 V hV,act_P0 L U V⟩
  · exact ⟨_,_,hmem 0 2 U hU,hmem 1 3 V hV,act_P1 L U V⟩
  · exact ⟨_,_,hmem 0 3 U hU,hmem 1 2 V hV,act_P2 L U V⟩

end
end Holant.Certificates.RainbowOrbit
