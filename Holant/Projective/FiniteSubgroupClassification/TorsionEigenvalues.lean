import Holant.Projective.BoundedTorsion.Eigenratio
import Holant.Projective.BoundedTorsion.FiniteTrace
import Holant.Projective.BoundedTorsion.PGL
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Nonidentity elements of finite order in the genuine projective group have
two distinct nonzero characteristic roots. In characteristic zero the only
finite-order projective class with a repeated root is the identity. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section

/-- The two-by-two trace identity, independent of diagonalizability. -/
theorem trace_square (T : Binary (K := ℂ)) :
    Matrix.trace (T * T) = Matrix.trace T ^ 2 - 2 * Matrix.det T := by
  have hd : Matrix.det T = T false false * T true true - T false true * T true false := by
    rw [← Matrix.det_reindex_self finTwoEquiv.symm T, Matrix.det_fin_two]
    rfl
  rw [hd]
  simp [Matrix.trace, Matrix.mul_apply]
  ring

/-- Repeated characteristic roots of a projectively finite nonsingular matrix
force the matrix itself to be scalar. -/
theorem scalar_of_repeated_roots {T : Binary (K := ℂ)}
    (hT : ProjectivelyFinite T) {a : ℂ} (ha : a ≠ 0)
    (htr : Matrix.trace T = a + a) (hdet : Matrix.det T = a * a) :
    T = a • (1 : Binary) := by
  let S : Binary (K := ℂ) := a⁻¹ • T
  have hSdet : Matrix.det S = 1 := by
    simp [S, Matrix.det_smul, hdet]
    field_simp
  have hStr : Matrix.trace S = 2 := by
    simp only [S, Matrix.trace_smul, htr]
    change a⁻¹ * (a + a) = 2
    field_simp
    ring
  have hS : S = 1 := eq_one_of_power_traces
    ((hT.smul (inv_ne_zero ha)).isOfFinOrder_of_det_one hSdet) hStr (by
      rw [trace_square, hStr, hSdet]; norm_num)
  calc
    T = a • S := by simp [S, smul_smul, ha]
    _ = a • (1 : Binary) := by rw [hS]

/-- The characteristic roots of a nonidentity finite-order projective class
are distinct. These are roots of the actual representative, not chosen model data. -/
theorem exists_distinct_eigenpair (g : Matrix.GeneralLinearGroup Bool ℂ)
    (hfin : IsOfFinOrder (pglMk ℂ g)) (hne : pglMk ℂ g ≠ 1) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      Matrix.trace (g : Binary (K := ℂ)) = a + b ∧ Matrix.det (g : Binary (K := ℂ)) = a * b ∧
      a ∈ spectrum ℂ (g : Binary (K := ℂ)) ∧ b ∈ spectrum ℂ (g : Binary (K := ℂ)) := by
  obtain ⟨a, b, htr, hdet, hae, hbe⟩ := exists_eigenpair (g : Binary (K := ℂ))
  have hab0 : a * b ≠ 0 := hdet ▸ g.det_ne_zero
  have ha := (mul_ne_zero_iff.mp hab0).1
  have hb := (mul_ne_zero_iff.mp hab0).2
  refine ⟨a, b, ha, hb, ?_, htr, hdet, hae, hbe⟩
  intro hab
  subst b
  have hscalar := scalar_of_repeated_roots
    ((isOfFinOrder_pglMk_iff g).mp hfin) ha htr hdet
  apply hne
  change pglMk ℂ g = pglMk ℂ 1
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  exact projectiveClass_eq_iff.mpr ⟨a, ha, hscalar⟩

end
end Holant.Projective.FiniteSubgroupClassification
