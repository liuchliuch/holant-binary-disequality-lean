import Holant.Projective.BoundedTorsion.Group
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Determinant-one representatives of a projective matrix group over an
algebraically closed extension.  These lemmas separate the elementary lifting
step from trace arithmetic and from the finite-trace group criterion. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {L E : Type*} [Field L] [Field E]

/-- All determinant-one scalar representatives of matrices from `G`. -/
def determinantOneLifts (f : L →+* E) (G : Set (Binary (K := L))) :
    Set (Binary (K := E)) :=
  {U | Matrix.det U = 1 ∧ ∃ T ∈ G, ∃ c : E, c ≠ 0 ∧ U = c • T.map f}

/-- The determinant-one representatives are multiplicatively closed. -/
theorem determinantOneLifts_mul_mem (f : L →+* E) {G : Set (Binary (K := L))}
    (hmul : ∀ T ∈ G, ∀ V ∈ G, T * V ∈ G)
    {U V : Binary (K := E)} (hU : U ∈ determinantOneLifts f G)
    (hV : V ∈ determinantOneLifts f G) : U * V ∈ determinantOneLifts f G := by
  obtain ⟨hdU, T, hT, c, hc, rfl⟩ := hU
  obtain ⟨hdV, W, hW, d, hd, rfl⟩ := hV
  refine ⟨by rw [Matrix.det_mul, hdU, hdV, one_mul], T * W, hmul T hT W hW,
    c * d, mul_ne_zero hc hd, ?_⟩
  rw [Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Projective finite order is preserved by a coefficient-field embedding. -/
theorem ProjectivelyFinite.map {T : Binary (K := L)} (hT : ProjectivelyFinite T)
    (f : L →+* E) : ProjectivelyFinite (T.map f) := by
  obtain ⟨r, hr, c, hc, hp⟩ := hT
  refine ⟨r, hr, f c, ?_, ?_⟩
  · exact fun h => hc (f.injective (by simpa using h))
  · rw [← Matrix.map_pow, hp]
    ext i j
    cases i <;> cases j <;> simp

/-- A determinant-one projective torsion matrix has ordinary finite order.
Squaring the scalar power removes its possible sign. -/
theorem ProjectivelyFinite.isOfFinOrder_of_det_one {T : Binary (K := E)}
    (hT : ProjectivelyFinite T) (hdet : Matrix.det T = 1) : IsOfFinOrder T := by
  obtain ⟨r, hr, c, _, hp⟩ := hT
  have hc : c ^ 2 = 1 := by
    have h := congrArg Matrix.det hp
    simpa [Matrix.det_pow, hdet, Matrix.det_smul] using h.symm
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨r * 2, Nat.mul_pos hr (by decide), ?_⟩
  rw [pow_mul, hp, smul_pow, hc]
  simp

/-- Projective torsion lifts to ordinary torsion inside determinant one. -/
theorem determinantOneLifts_isOfFinOrder (f : L →+* E) {G : Set (Binary (K := L))}
    (htorsion : ∀ T ∈ G, ProjectivelyFinite T)
    {U : Binary (K := E)} (hU : U ∈ determinantOneLifts f G) : IsOfFinOrder U := by
  obtain ⟨hdU, T, hT, c, hc, rfl⟩ := hU
  exact (((htorsion T hT).map f).smul hc).isOfFinOrder_of_det_one hdU

/-- A nonsingular matrix admits a nonzero determinant-normalizing scalar over
an algebraically closed field. -/
theorem exists_det_one_smul_map [IsAlgClosed E] (f : L →+* E)
    {T : Binary (K := L)} (hT : Matrix.det T ≠ 0) :
    ∃ c : E, c ≠ 0 ∧ Matrix.det (c • T.map f) = 1 := by
  have hd : Matrix.det (T.map f) ≠ 0 := by
    change Matrix.det (f.mapMatrix T) ≠ 0
    rw [← f.map_det]
    exact fun h => hT (f.injective (by simpa using h))
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((Matrix.det (T.map f))⁻¹) (by decide : 0 < 2)
  have hc0 : c ≠ 0 := by
    intro hz
    apply inv_ne_zero hd
    simpa [hz] using hc.symm
  refine ⟨c, hc0, ?_⟩
  rw [Matrix.det_smul]
  simpa [hc] using inv_mul_cancel₀ hd

/-- Every nonsingular source matrix has a determinant-one lift, with its exact
nonzero scalar witness retained. -/
theorem exists_mem_determinantOneLifts [IsAlgClosed E] (f : L →+* E)
    {G : Set (Binary (K := L))} {T : Binary (K := L)} (hT : T ∈ G)
    (hdet : Matrix.det T ≠ 0) :
    ∃ c : E, c ≠ 0 ∧ c • T.map f ∈ determinantOneLifts f G := by
  obtain ⟨c, hc, hd⟩ := exists_det_one_smul_map f hdet
  exact ⟨c, hc, hd, T, hT, c, hc, rfl⟩

end
end Holant.Projective.BoundedTorsion
