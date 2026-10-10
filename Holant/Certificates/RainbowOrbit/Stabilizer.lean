import Holant.Certificates.RainbowOrbit.Normalization

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem Proportional.transpose {U V : BinaryMatrix} (h : Proportional U V) :
    Proportional U.transpose V.transpose := by
  obtain ⟨c,hc,rfl⟩ := h
  exact ⟨c,hc,Matrix.transpose_smul c V⟩

theorem Proportional.mul_left {U V : BinaryMatrix} (h : Proportional U V) (M : BinaryMatrix) :
    Proportional (M*U) (M*V) := by
  obtain ⟨c,hc,rfl⟩ := h
  exact ⟨c,hc,Matrix.mul_smul M c V⟩

theorem Proportional.mul_right {U V : BinaryMatrix} (h : Proportional U V) (M : BinaryMatrix) :
    Proportional (U*M) (V*M) := by
  obtain ⟨c,hc,rfl⟩ := h
  exact ⟨c,hc,Matrix.smul_mul c V M⟩

theorem Proportional.mul {U V S T : BinaryMatrix} (h : Proportional U V)
    (k : Proportional S T) : Proportional (U*S) (V*T) :=
  (h.mul_right S).trans (k.mul_left V)

theorem proportional_cancel_left (M U V : BinaryMatrix) (hM : M.det≠0) :
    Proportional (M*U) (M*V) ↔ Proportional U V := by
  constructor
  · intro h
    have hh := h.mul_left M⁻¹
    simpa only [←mul_assoc,Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),one_mul] using hh
  · exact fun h => h.mul_left M

def stabilizerTuple (T : BinaryMatrix) : Legs := ![T,T⁻¹.transpose,T⁻¹.transpose,T]

theorem stabilizer_fixes (T : BinaryMatrix) (hT : T.det≠0) :
    act (stabilizerTuple T) A=A ∧ act (stabilizerTuple T) B=B ∧
    act (stabilizerTuple T) C=C := by
  have hi := isUnit_iff_ne_zero.mpr hT
  have ht : T⁻¹.transpose*T.transpose=(1 : BinaryMatrix) := by
    rw [←Matrix.transpose_mul,Matrix.mul_nonsing_inv _ hi,Matrix.transpose_one]
  have ha : act (stabilizerTuple T) A=A := by
    rw [A_matrix,act_P0]
    simp [stabilizerTuple,Matrix.mul_nonsing_inv _ hi,ht]
  have hb : act (stabilizerTuple T) B=B := by
    rw [B_matrix,act_P1]
    simp [stabilizerTuple,Matrix.mul_nonsing_inv _ hi,ht]
  refine ⟨ha,hb,?_⟩
  have hc : C=A+(-1:ℂ) • B := by rw [←A_sub_B]; module
  rw [hc,act_add,act_smul,ha,hb]

/-- The first two points already determine every projective stabilizer leg. -/
theorem stabilizer_necessary (L : Legs) (hL : ∀j,(L j).det≠0)
    (ha : Proportional (act L A) A) (hb : Proportional (act L B) B) :
    Proportional (L 1) (L 0)⁻¹.transpose ∧
    Proportional (L 2) (L 0)⁻¹.transpose ∧ Proportional (L 3) (L 0) := by
  rw [A_matrix,act_P0] at ha
  rw [B_matrix,act_P1] at hb
  simp only [mul_one] at ha hb
  have hd (i j : Fin 4) : ((L i)*(L j).transpose).det≠0 := by
    simp [Matrix.det_mul,hL i,hL j]
  have haf := proportional_matching_factors 0 _ _ (1 : BinaryMatrix) (1 : BinaryMatrix)
    (hd 0 1) (hd 2 3) ha
  have hbf := proportional_matching_factors 1 _ _ (1 : BinaryMatrix) (1 : BinaryMatrix)
    (hd 0 2) (hd 1 3) hb
  have h1 : Proportional (L 1) (L 0)⁻¹.transpose := by
    have hh := (haf.1.mul_left (L 0)⁻¹).transpose
    simpa only [←mul_assoc,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hL 0)),
      one_mul,mul_one,Matrix.transpose_transpose] using hh
  have h2 : Proportional (L 2) (L 0)⁻¹.transpose := by
    have hh := (hbf.1.mul_left (L 0)⁻¹).transpose
    simpa only [←mul_assoc,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hL 0)),
      one_mul,mul_one,Matrix.transpose_transpose] using hh
  have h3 : Proportional (L 3) (L 0) := by
    have hh := (h1.mul_right (L 3).transpose).symm.trans hbf.2
    have hh' := (hh.mul_left (L 0).transpose).transpose
    have hi : (L 0).transpose*(L 0)⁻¹.transpose=(1 : BinaryMatrix) := by
      rw [←Matrix.transpose_mul,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hL 0)),
        Matrix.transpose_one]
    simpa only [←mul_assoc,hi,one_mul,mul_one,Matrix.transpose_transpose] using hh'
  exact ⟨h1,h2,h3⟩

def reducedLegs (U V W : BinaryMatrix) : Legs := ![1,U,V,W]

/-- Removing the first stabilizer coordinate leaves an injective parameterization. -/
theorem reduced_action_injective (U V W U' V' W' : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0) (hW : W.det≠0)
    (ha : Proportional (act (reducedLegs U V W) A) (act (reducedLegs U' V' W') A))
    (hb : Proportional (act (reducedLegs U V W) B) (act (reducedLegs U' V' W') B)) :
    Proportional U U' ∧ Proportional V V' ∧ Proportional W W' := by
  rw [A_matrix,act_P0,act_P0] at ha
  rw [B_matrix,act_P1,act_P1] at hb
  simp only [reducedLegs,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Matrix.cons_val_fin_one,mul_one,one_mul] at ha hb
  have haf := proportional_matching_factors 0 _ _ _ _
    (by simpa using hU) (by simp [Matrix.det_mul,hV,hW]) ha
  have hbf := proportional_matching_factors 1 _ _ _ _
    (by simpa using hV) (by simp [Matrix.det_mul,hU,hW]) hb
  have hu : Proportional U U' := by simpa only [Matrix.transpose_transpose] using haf.1.transpose
  have hv : Proportional V V' := by simpa only [Matrix.transpose_transpose] using hbf.1.transpose
  have hw : Proportional W W' := by
    have hh := haf.2.trans (hv.mul_right W'.transpose).symm
    have hh' := (proportional_cancel_left V _ _ hV).mp hh
    simpa only [Matrix.transpose_transpose] using hh'.transpose
  exact ⟨hu,hv,hw⟩

end
end Holant.Certificates.RainbowOrbit
