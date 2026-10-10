import Holant.Projective.BoundedTorsion.TraceValues
import Mathlib.Data.Set.Card

/-! Quantitative bounds for the trace sets of number-field torsion matrices. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Polynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [Field E]

/-- A nonconstant power equation has at most its exponent many solutions. -/
theorem ncard_power_fiber_le {n : ℕ} (hn : 0 < n) (c : E) :
    {z : E | z ^ n = c}.ncard ≤ n := by
  classical
  have hset : {z : E | z ^ n = c} =
      (((X : E[X]) ^ n - C c).roots.toFinset : Set E) := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hn c),
      Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero]
  rw [hset, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots_X_pow_sub_C hn c)

/-- Taking square roots increases the size of a finite set by at most two. -/
theorem ncard_square_preimage_le {S : Set E} (hS : S.Finite) :
    {z : E | z ^ 2 ∈ S}.ncard ≤ 2 * S.ncard := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | @insert c S hc hS ih =>
    have hset : {z : E | z ^ 2 ∈ insert c S} =
        {z : E | z ^ 2 = c} ∪ {z : E | z ^ 2 ∈ S} := by
      ext z
      simp
    rw [hset]
    calc
      _ ≤ {z : E | z ^ 2 = c}.ncard + {z : E | z ^ 2 ∈ S}.ncard :=
        Set.ncard_union_le _ _
      _ ≤ 2 + 2 * S.ncard :=
        Nat.add_le_add (ncard_power_fiber_le (by decide : 0 < 2) c) ih
      _ = 2 * (insert c S).ncard := by
        rw [Set.ncard_insert_of_notMem hc hS]
        omega

variable {L : Type*} [Field L] [CharZero E] [IsAlgClosed E]
  [Algebra ℚ L] [Algebra L E] [Algebra ℚ E] [IsScalarTower ℚ L E]
  [FiniteDimensional ℚ L]

include E in
/-- The trace/determinant invariant has at most the common torsion exponent
many values over a number field. -/
theorem ncard_traceRatio_image_le {G : Set (Binary (K := L))}
    (hdet : ∀ T ∈ G, Matrix.det T ≠ 0)
    (htorsion : ∀ T ∈ G, ProjectivelyFinite T) :
    (traceRatio '' G).ncard ≤ torsionExponent (Module.finrank ℚ L) := by
  let e := torsionExponent (Module.finrank ℚ L)
  have hz : {z : E | z ^ e = 1}.Finite := finite_power_fiber (torsionExponent_pos _) 1
  have hsub : algebraMap L E '' (traceRatio '' G) ⊆
      (fun z : E => z + z⁻¹) '' {z : E | z ^ e = 1} := by
    rintro _ ⟨_, ⟨T, hT, rfl⟩, rfl⟩
    obtain ⟨z, hz, he⟩ := exists_bounded_eigenratio (E := E) (hdet T hT) (htorsion T hT)
    exact ⟨z, hz, he⟩
  rw [← Set.ncard_image_of_injective (traceRatio '' G) (algebraMap L E).injective]
  exact (Set.ncard_le_ncard hsub (hz.image _)).trans <|
    (Set.ncard_image_le hz).trans (ncard_power_fiber_le (torsionExponent_pos _) (1 : E))

/-- Determinant-one scalar lifts of number-field torsion matrices have at most
twice the common torsion exponent many trace values. -/
theorem ncard_trace_image_of_lifts_le {G : Set (Binary (K := L))}
    (hdet : ∀ T ∈ G, Matrix.det T ≠ 0)
    (htorsion : ∀ T ∈ G, ProjectivelyFinite T)
    {S : Set (Binary (K := E))}
    (hlift : ∀ U ∈ S, Matrix.det U = 1 ∧ ∃ T ∈ G, ∃ c : E,
      c ≠ 0 ∧ U = c • T.map (algebraMap L E)) :
    (Matrix.trace '' S).ncard ≤ 2 * torsionExponent (Module.finrank ℚ L) := by
  let A := (fun x : L => algebraMap L E x + 2) '' (traceRatio '' G)
  have hA : A.Finite := (finite_traceRatio_image (E := E) hdet htorsion).image _
  have hsub : Matrix.trace '' S ⊆ {z : E | z ^ 2 ∈ A} := by
    rintro _ ⟨U, hU, rfl⟩
    obtain ⟨hd, T, hT, c, hc, he⟩ := hlift U hU
    refine ⟨traceRatio T, ⟨T, hT, rfl⟩, ?_⟩
    have hr : traceRatio U = algebraMap L E (traceRatio T) := by
      rw [he, traceRatio_smul _ hc, traceRatio_map]
    simp only [traceRatio, hd, div_one] at hr
    exact sub_eq_iff_eq_add.mp hr |>.symm
  calc
    _ ≤ {z : E | z ^ 2 ∈ A}.ncard :=
      Set.ncard_le_ncard hsub (finite_square_preimage hA)
    _ ≤ 2 * A.ncard := ncard_square_preimage_le hA
    _ ≤ 2 * (traceRatio '' G).ncard :=
      Nat.mul_le_mul_left 2 (Set.ncard_image_le (finite_traceRatio_image (E := E) hdet htorsion))
    _ ≤ 2 * torsionExponent (Module.finrank ℚ L) :=
      Nat.mul_le_mul_left 2 (ncard_traceRatio_image_le (E := E) hdet htorsion)

end
end Holant.Projective.BoundedTorsion
