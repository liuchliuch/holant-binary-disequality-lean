import Holant.Proofs.Tetrahedral.DeterminantPreservers.Rulings
import Holant.Certificates.TetrahedralPreservers.NormalFormTransport


noncomputable section
namespace Holant.LocalDrafts.TetrahedralCompletion.DeterminantPreservers
open scoped Matrix
variable {K : Type*} [Field K]

def normalizedMap (T : Mat K →ₗ[K] Mat K) (U V : Mat K) : Mat K →ₗ[K] Mat K where
  toFun X := U⁻¹*T X*V⁻¹
  map_add' X Y := by rw [map_add,Matrix.mul_add,Matrix.add_mul]
  map_smul' c X := by rw [map_smul,Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]

theorem normalized_frame_image (U V : Mat K) (hU : U.det ≠ 0) (hV : V.det ≠ 0)
    (X : Mat K) : U⁻¹*(U*X*V)*V⁻¹=X := by
  rw [Matrix.mul_assoc U X V,
    Matrix.nonsing_inv_mul_cancel_left U (X*V) (isUnit_iff_ne_zero.mpr hU),
    Matrix.mul_nonsing_inv_cancel_right V X (isUnit_iff_ne_zero.mpr hV)]

theorem recover_normalized (T : Mat K →ₗ[K] Mat K) (U V : Mat K)
    (hU : U.det ≠ 0) (hV : V.det ≠ 0) (X : Mat K) :
    U*normalizedMap T U V X*V=T X := by
  change U*(U⁻¹*T X*V⁻¹)*V=T X
  rw [Matrix.mul_assoc U⁻¹ (T X) V⁻¹,
    Matrix.mul_nonsing_inv_cancel_left U (T X*V⁻¹) (isUnit_iff_ne_zero.mpr hU),
    Matrix.nonsing_inv_mul_cancel_right V (T X) (isUnit_iff_ne_zero.mpr hV)]

namespace Source

/-- Sole generic source theorem. Every factor and the transpose branch
are produced from the original four matrix-unit images. The hypotheses
are exactly an actual injective linear map and its nonzero determinant
multiplier, never a rank-one-preserver or sandwich decomposition premise. -/
theorem top (T : Mat K →ₗ[K] Mat K) (κ : K) (hκ : κ ≠ 0)
    (hT : Function.Injective T) (hdet : ∀ X : Mat K, (T X).det=κ*X.det) :
    ∃ L R : Mat K, L.det ≠ 0 ∧ R.det ≠ 0 ∧
      ((∀ X : Mat K, T X=L*X*R) ∨ (∀ X : Mat K, T X=L*X.transpose*R)) := by
  let P := T (matrixUnit false false)
  let Q := T (matrixUnit true true)
  have hP : P.det=0 := by simpa [P] using hdet (matrixUnit false false)
  have hQ : Q.det=0 := by simpa [Q] using hdet (matrixUnit true true)
  have hPn : P ≠ 0 := by
    intro h
    apply matrixUnit_ne_zero (K := K) false false
    apply hT
    simpa [P] using h
  have hQn : Q ≠ 0 := by
    intro h
    apply matrixUnit_ne_zero (K := K) true true
    apply hT
    simpa [Q] using h
  obtain ⟨u,v,_,_,hPe⟩ := singular_factor P hP hPn
  obtain ⟨s,t,_,_,hQe⟩ := singular_factor Q hQ hQn
  let U := columns u s
  let V := rows v t
  have hUV : U*V=T 1 := by
    change columns u s*rows v t=T 1
    rw [columns_rows,←hPe,←hQe]
    change T (matrixUnit false false)+T (matrixUnit true true)=T 1
    rw [←map_add,diagonal_units]
  have hprod : U.det*V.det=κ := by
    have h := congrArg Matrix.det hUV
    rw [Matrix.det_mul,hdet] at h
    simpa using h
  have hUVn : U.det*V.det ≠ 0 := by rw [hprod]; exact hκ
  obtain ⟨hU,hV⟩ := mul_ne_zero_iff.mp hUVn
  have h00 : U*matrixUnit false false*V=T (matrixUnit false false) := by
    change columns u s*matrixUnit false false*rows v t=P
    rw [columns_unit_rows]
    exact hPe.symm
  have h11 : U*matrixUnit true true*V=T (matrixUnit true true) := by
    change columns u s*matrixUnit true true*rows v t=Q
    rw [columns_unit_rows]
    exact hQe.symm
  let S := normalizedMap T U V
  have hS0 : S (matrixUnit false false)=matrixUnit false false := by
    change U⁻¹*T (matrixUnit false false)*V⁻¹=matrixUnit false false
    rw [←h00]
    exact normalized_frame_image U V hU hV _
  have hS1 : S (matrixUnit true true)=matrixUnit true true := by
    change U⁻¹*T (matrixUnit true true)*V⁻¹=matrixUnit true true
    rw [←h11]
    exact normalized_frame_image U V hU hV _
  have hSd : ∀ X : Mat K, (S X).det=X.det := by
    intro X
    have h := congrArg Matrix.det (recover_normalized T U V hU hV X)
    simp only [Matrix.det_mul] at h
    rw [hdet] at h
    have he : κ*(S X).det=κ*X.det := by
      calc
        κ*(S X).det=U.det*(S X).det*V.det := by rw [←hprod]; ring
        _=κ*X.det := h
    exact mul_left_cancel₀ hκ he
  obtain ⟨a,ha,hS | hS⟩ := normalized_rulings S hS0 hS1 hSd
  · refine ⟨U*diagonalScale a,diagonalScale a⁻¹*V,?_,?_,Or.inl ?_⟩
    · rw [Matrix.det_mul,det_diagonalScale]
      exact mul_ne_zero hU ha
    · rw [Matrix.det_mul,det_diagonalScale]
      exact mul_ne_zero (inv_ne_zero ha) hV
    · intro X
      have h := (recover_normalized T U V hU hV X).symm
      change T X=U*S X*V at h
      rw [hS X] at h
      simpa only [Matrix.mul_assoc] using h
  · refine ⟨U*diagonalScale a,diagonalScale a⁻¹*V,?_,?_,Or.inr ?_⟩
    · rw [Matrix.det_mul,det_diagonalScale]
      exact mul_ne_zero hU ha
    · rw [Matrix.det_mul,det_diagonalScale]
      exact mul_ne_zero (inv_ne_zero ha) hV
    · intro X
      have h := (recover_normalized T U V hU hV X).symm
      change T X=U*S X*V at h
      rw [hS X] at h
      simpa only [Matrix.mul_assoc] using h

open Holant.Certificates.TetrahedralPreservers Holant.Certificates.PlatonicIncidence

/-- The exact existing quaternion chart, without replacing its determinant
by a Hermitian norm. This is a coefficient map, not a binary resource. -/
def coefficientMap (A : End) : Mat ℂ →ₗ[ℂ] Mat ℂ :=
  coordinates.symm.toLinearMap.comp (A.mulVecLin.comp coordinates.toLinearMap)

theorem coefficientMap_injective (A : End) (hA : Function.Injective A.mulVecLin) :
    Function.Injective (coefficientMap A) := by
  intro X Y h
  apply coordinates.injective
  apply hA
  exact coordinates.symm.injective h

/-- Actual coefficient corollary for the saved q4 consumer. The multiplier
and determinant equality must be produced from its actual root geometry;
the left/right matrices are the generic theorem's outputs over complex
coefficients. No original-field physical realization is asserted. -/
theorem coefficient_top (A : End) (κ : ℂ) (hκ : κ ≠ 0)
    (hA : Function.Injective A.mulVecLin)
    (hdet : ∀ X : Mat ℂ, (coefficientMap A X).det=κ*X.det) :
    ∃ L R : Mat ℂ, L.det ≠ 0 ∧ R.det ≠ 0 ∧
      (A=sandwich L R ∨ A=transposeSandwich L R) := by
  have hcoord (r : V) : coordinates (assemble r) = r := coordinates.apply_symm_apply r
  obtain ⟨L,R,hL,hR,h | h⟩ := top (coefficientMap A) κ hκ (coefficientMap_injective A hA) hdet
  · refine ⟨L,R,hL,hR,Or.inl ?_⟩
    apply matrix_ext_action
    intro r
    have he := congrArg coordinates (h (assemble r))
    change coordinates (coordinates.symm (A *ᵥ coordinates (assemble r)))=coordinates (L*assemble r*R) at he
    rw [coordinates.apply_symm_apply,hcoord] at he
    simpa only [sandwich_action] using he
  · refine ⟨L,R,hL,hR,Or.inr ?_⟩
    apply matrix_ext_action
    intro r
    have he := congrArg coordinates (h (assemble r))
    change coordinates (coordinates.symm (A *ᵥ coordinates (assemble r)))=
      coordinates (L*(assemble r).transpose*R) at he
    rw [coordinates.apply_symm_apply,hcoord] at he
    simpa only [transposeSandwich_action] using he

end Source
end Holant.LocalDrafts.TetrahedralCompletion.DeterminantPreservers
end
