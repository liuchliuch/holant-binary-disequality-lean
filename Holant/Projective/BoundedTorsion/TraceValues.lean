import Holant.Projective.BoundedTorsion.Eigenratio

/-! Finitely many trace invariants, derived from the number field and torsion
hypotheses, rather than required as an extra source hypothesis. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Polynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [Field E]

theorem finite_power_fiber {n : ℕ} (hn : 0 < n) (c : E) :
    {z : E | z ^ n = c}.Finite := by
  have h := Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hn c)
  simpa only [Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, eval_C,
    sub_eq_zero] using h

theorem finite_square_preimage {S : Set E} (hS : S.Finite) :
    {z : E | z ^ 2 ∈ S}.Finite := by
  have h := hS.biUnion (fun c _ => finite_power_fiber (E := E) (by decide : 0 < 2) c)
  apply h.subset
  intro z hz
  exact Set.mem_iUnion.mpr ⟨z ^ 2, Set.mem_iUnion.mpr ⟨hz, rfl⟩⟩

theorem traceRatio_smul (T : Binary (K := E)) {c : E} (hc : c ≠ 0) :
    traceRatio (c • T) = traceRatio T := by
  simp only [traceRatio, Matrix.trace_smul, smul_eq_mul, Matrix.det_smul,
    Fintype.card_bool, mul_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

variable {L : Type*} [Field L] [CharZero E] [IsAlgClosed E]
  [Algebra ℚ L] [Algebra L E] [Algebra ℚ E] [IsScalarTower ℚ L E]
  [FiniteDimensional ℚ L]

include E in
theorem finite_traceRatio_image {G : Set (Binary (K := L))}
    (hdet : ∀ T ∈ G, Matrix.det T ≠ 0)
    (htorsion : ∀ T ∈ G, ProjectivelyFinite T) :
    (traceRatio '' G).Finite := by
  let e := torsionExponent (Module.finrank ℚ L)
  have hz : {z : E | z ^ e = 1}.Finite := finite_power_fiber (torsionExponent_pos _) 1
  have hs := hz.image (fun z : E => z + z⁻¹)
  have himage : (algebraMap L E '' (traceRatio '' G)).Finite := by
    apply hs.subset
    rintro _ ⟨_, ⟨T, hT, rfl⟩, rfl⟩
    obtain ⟨z, hz, he⟩ := exists_bounded_eigenratio (E := E) (hdet T hT) (htorsion T hT)
    exact ⟨z, hz, he⟩
  exact himage.of_finite_image (algebraMap L E).injective.injOn

/-- Any family of determinant-one scalar lifts of number-field torsion
matrices has finitely many traces.  The lift witnesses retain their scalars. -/
theorem finite_trace_image_of_lifts {G : Set (Binary (K := L))}
    (hdet : ∀ T ∈ G, Matrix.det T ≠ 0)
    (htorsion : ∀ T ∈ G, ProjectivelyFinite T)
    {S : Set (Binary (K := E))}
    (hlift : ∀ U ∈ S, Matrix.det U = 1 ∧ ∃ T ∈ G, ∃ c : E,
      c ≠ 0 ∧ U = c • T.map (algebraMap L E)) :
    (Matrix.trace '' S).Finite := by
  have hf := (finite_traceRatio_image (E := E) hdet htorsion).image
    (fun x : L => algebraMap L E x + 2)
  apply (finite_square_preimage hf).subset
  rintro _ ⟨U, hU, rfl⟩
  obtain ⟨hd, T, hT, c, hc, he⟩ := hlift U hU
  refine ⟨traceRatio T, ⟨T, hT, rfl⟩, ?_⟩
  have hr : traceRatio U = algebraMap L E (traceRatio T) := by
    rw [he, traceRatio_smul _ hc, traceRatio_map]
  simp only [traceRatio, hd, div_one] at hr
  exact sub_eq_iff_eq_add.mp hr |>.symm

end
end Holant.Projective.BoundedTorsion
