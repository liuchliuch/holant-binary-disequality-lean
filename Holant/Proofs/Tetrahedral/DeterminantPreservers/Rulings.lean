import Holant.Proofs.Tetrahedral.DeterminantPreservers.Basis


namespace Holant.LocalDrafts.TetrahedralCompletion.DeterminantPreservers
open scoped Matrix
variable {K : Type*} [Field K]

/-- The concrete two-ruling intersection at the two fixed diagonal axes.
The product-zero conclusion is the union of the two actual cross rulings. -/
theorem segre_at_diagonal_axes (P : Mat K) (hP : P.det=0)
    (h0 : (matrixUnit false false+P).det=0)
    (h1 : (matrixUnit true true+P).det=0) :
    ∃ a b : K, P=a • matrixUnit false true+b • matrixUnit true false ∧ a*b=0 := by
  simp [det_bool,matrixUnit] at hP h0 h1
  have hd : P true true=0 := by linear_combination h0-hP
  have ha : P false false=0 := by linear_combination h1-hP
  refine ⟨P false true,P true false,?_,?_⟩
  · ext i j
    cases i <;> cases j <;> simp [matrixUnit,ha,hd]
  · rw [ha,hd] at hP
    simpa only [zero_mul,mul_zero,zero_sub,neg_eq_zero,eq_comm] using hP

/-- Complete normalized determinant-preserver classification, with the
nonzero scaling and choice of ruling produced by the original images. -/
theorem normalized_rulings (S : Mat K →ₗ[K] Mat K)
    (h0 : S (matrixUnit false false)=matrixUnit false false)
    (h1 : S (matrixUnit true true)=matrixUnit true true)
    (hdet : ∀ X : Mat K, (S X).det=X.det) :
    ∃ a : K, a ≠ 0 ∧
      ((∀ X : Mat K, S X=diagonalScale a*X*diagonalScale a⁻¹) ∨
       (∀ X : Mat K, S X=diagonalScale a*X.transpose*diagonalScale a⁻¹)) := by
  let P := S (matrixUnit false true)
  let Q := S (matrixUnit true false)
  have hP : P.det=0 := by simpa [P] using hdet (matrixUnit false true)
  have hQ : Q.det=0 := by simpa [Q] using hdet (matrixUnit true false)
  have hP0 : (matrixUnit false false+P).det=0 := by
    have h := hdet (matrixUnit false false+matrixUnit false true)
    rw [map_add,h0] at h
    simpa [det_bool,matrixUnit,P] using h
  have hP1 : (matrixUnit true true+P).det=0 := by
    have h := hdet (matrixUnit true true+matrixUnit false true)
    rw [map_add,h1] at h
    simpa [det_bool,matrixUnit,P] using h
  have hQ0 : (matrixUnit false false+Q).det=0 := by
    have h := hdet (matrixUnit false false+matrixUnit true false)
    rw [map_add,h0] at h
    simpa [det_bool,matrixUnit,Q] using h
  have hQ1 : (matrixUnit true true+Q).det=0 := by
    have h := hdet (matrixUnit true true+matrixUnit true false)
    rw [map_add,h1] at h
    simpa [det_bool,matrixUnit,Q] using h
  obtain ⟨a,b,hPe,hab⟩ := segre_at_diagonal_axes P hP hP0 hP1
  obtain ⟨c,d,hQe,hcd⟩ := segre_at_diagonal_axes Q hQ hQ0 hQ1
  change S (matrixUnit false true)=_ at hPe
  change S (matrixUnit true false)=_ at hQe
  have hcross : a*d+b*c=1 := by
    have h := hdet (matrixUnit false true+matrixUnit true false)
    rw [map_add,hPe,hQe] at h
    simp [det_bool,matrixUnit] at h
    first | linear_combination h-hab-hcd | linear_combination -h-hab-hcd
  by_cases ha : a ≠ 0
  · have hb : b=0 := (mul_eq_zero.mp hab).resolve_left ha
    have had : a*d=1 := by simpa [hb] using hcross
    have hd : d ≠ 0 := by
      intro h
      rw [h,mul_zero] at had
      exact zero_ne_one had
    have hc : c=0 := (mul_eq_zero.mp hcd).resolve_right hd
    have hdi : d=a⁻¹ := by
      apply mul_left_cancel₀ ha
      rw [had,mul_inv_cancel₀ ha]
    refine ⟨a,ha,Or.inl ?_⟩
    intro X
    have he := congrArg S (basis_expansion X)
    simp only [map_add,map_smul,h0,h1,hPe,hQe,hb,hc,hdi,
      zero_smul,zero_add,add_zero] at he
    rw [he]
    ext i j
    cases i <;> cases j <;>
      simp [diagonalScale,matrixUnit,Matrix.mul_apply] <;>
      field_simp [ha] <;> ring
  · have ha0 : a=0 := not_ne_iff.mp ha
    have hbc : b*c=1 := by simpa [ha0] using hcross
    have hb : b ≠ 0 := by
      intro h
      rw [h,zero_mul] at hbc
      exact zero_ne_one hbc
    have hc : c ≠ 0 := by
      intro h
      rw [h,mul_zero] at hbc
      exact zero_ne_one hbc
    have hd : d=0 := (mul_eq_zero.mp hcd).resolve_left hc
    have hbi : b=c⁻¹ := by
      apply mul_left_cancel₀ hc
      rw [show c*b=1 from by simpa only [mul_comm] using hbc,mul_inv_cancel₀ hc]
    refine ⟨c,hc,Or.inr ?_⟩
    intro X
    have he := congrArg S (basis_expansion X)
    simp only [map_add,map_smul,h0,h1,hPe,hQe,ha0,hd,hbi,
      zero_smul,zero_add,add_zero] at he
    rw [he]
    ext i j
    cases i <;> cases j <;>
      simp [diagonalScale,matrixUnit,Matrix.mul_apply,Matrix.transpose_apply] <;>
      field_simp [hc] <;> ring

end Holant.LocalDrafts.TetrahedralCompletion.DeterminantPreservers
