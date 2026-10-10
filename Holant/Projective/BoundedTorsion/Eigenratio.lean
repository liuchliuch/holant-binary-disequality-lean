import Holant.Projective.BoundedTorsion.CyclotomicDegree
import Holant.Projective.BoundedTorsion.Group
import Holant.Projective.BoundedTorsion.DeterminantOne
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-! Torsion eigenratios and the trace/determinant invariant of literal transfer
matrices.  Characteristic roots and spectral power mapping avoid assuming a
diagonalizing basis or a bounded projective order. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Polynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [Field E]

def traceRatio (T : Binary (K := E)) : E := Matrix.trace T ^ 2 / Matrix.det T - 2

theorem exists_eigenpair [IsAlgClosed E] (T : Binary (K := E)) :
    ∃ a b : E, Matrix.trace T = a + b ∧ Matrix.det T = a * b ∧
      a ∈ spectrum E T ∧ b ∈ spectrum E T := by
  have hc : T.charpoly.roots.card = 2 := by
    rw [← (IsAlgClosed.splits T.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim]
    simp
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hc
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.trace_eq_sum_roots_charpoly, hab]
    simp
  · rw [Matrix.det_eq_prod_roots_charpoly, hab]
    simp
  · apply Matrix.mem_spectrum_of_isRoot_charpoly
    exact (Polynomial.mem_roots T.charpoly_monic.ne_zero).mp (by simp [hab])
  · apply Matrix.mem_spectrum_of_isRoot_charpoly
    exact (Polynomial.mem_roots T.charpoly_monic.ne_zero).mp (by simp [hab])

theorem eigenvalue_pow_of_scalar_pow {T : Binary (K := E)} {a c : E} {r : ℕ}
    (ha : a ∈ spectrum E T) (hT : T ^ r = c • (1 : Binary)) : a ^ r = c := by
  have h := spectrum.pow_mem_pow T r ha
  rw [hT, ← Algebra.algebraMap_eq_smul_one, spectrum.scalar_eq] at h
  exact h

/-- The eigenratio has finite order even when the characteristic roots repeat.
No assertion that this equals the projective order is needed for finite traces. -/
theorem exists_torsion_eigenratio [IsAlgClosed E] {T : Binary (K := E)}
    (hdet : Matrix.det T ≠ 0) (hT : ProjectivelyFinite T) :
    ∃ ζ : E, IsOfFinOrder ζ ∧ ζ + ζ⁻¹ = traceRatio T := by
  obtain ⟨a, b, htr, hdetab, ha, hb⟩ := exists_eigenpair T
  have ha0 : a ≠ 0 := (mul_ne_zero_iff.mp (hdetab ▸ hdet)).1
  have hb0 : b ≠ 0 := (mul_ne_zero_iff.mp (hdetab ▸ hdet)).2
  obtain ⟨r, hr, c, hc, hp⟩ := hT
  have hap := eigenvalue_pow_of_scalar_pow ha hp
  have hbp := eigenvalue_pow_of_scalar_pow hb hp
  refine ⟨a / b, isOfFinOrder_iff_pow_eq_one.mpr ⟨r, hr, ?_⟩, ?_⟩
  · rw [div_pow, hap, hbp, div_self hc]
  · dsimp [traceRatio]
    rw [htr, hdetab]
    field_simp
    ring

theorem traceRatio_map {L : Type*} [Field L] (f : L →+* E) (T : Binary (K := L)) :
    traceRatio (T.map f) = f (traceRatio T) := by
  simp only [traceRatio, ← AddMonoidHom.map_trace f T,
    ← show f (Matrix.det T) = Matrix.det (T.map f) from RingHom.map_det f T,
    map_sub, map_div₀, map_pow, map_ofNat]

variable {L : Type*} [Field L] [CharZero E] [IsAlgClosed E]
  [Algebra ℚ L] [Algebra L E] [Algebra ℚ E] [IsScalarTower ℚ L E]
  [FiniteDimensional ℚ L]

/-- Every torsion transfer has an eigenratio in one fixed finite root set,
with that exponent proved from the number-field degree. -/
theorem exists_bounded_eigenratio {T : Binary (K := L)}
    (hdet : Matrix.det T ≠ 0) (hT : ProjectivelyFinite T) :
    ∃ ζ : E, ζ ^ torsionExponent (Module.finrank ℚ L) = 1 ∧
      ζ + ζ⁻¹ = algebraMap L E (traceRatio T) := by
  have hdet' : Matrix.det (T.map (algebraMap L E)) ≠ 0 := by
    rw [← show algebraMap L E (Matrix.det T) = Matrix.det (T.map (algebraMap L E)) from
      RingHom.map_det (algebraMap L E) T]
    exact (map_ne_zero (algebraMap L E)).mpr hdet
  obtain ⟨ζ, hζ, hs⟩ := exists_torsion_eigenratio hdet' (hT.map (algebraMap L E))
  rw [traceRatio_map] at hs
  refine ⟨ζ, ?_, hs⟩
  apply pow_torsionExponent hζ
  exact totient_le_twice_degree_of_add_inv hζ.orderOf_pos (IsPrimitiveRoot.orderOf ζ) hs

end
end Holant.Projective.BoundedTorsion
