import Holant.Projective.BoundedTorsion.FiniteTrace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Set.Card

/-! Quantitative form of the two-dimensional finite-trace argument.
The trace tuple has at most four coordinates, giving a fourth-power bound. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The trace-coordinate injection bounds a faithful torsion group by the
fourth power of the number of its trace values. -/
theorem card_le_trace_range_pow_four {G : Type*} [Group G]
    (ρ : G →* Binary (K := K)) (hρ : Function.Injective ρ)
    (htorsion : ∀ g, IsOfFinOrder (ρ g))
    (htrace : (Set.range (fun g => Matrix.trace (ρ g))).Finite) :
    Nat.card G ≤ (Set.range (fun g => Matrix.trace (ρ g))).ncard ^ 4 := by
  classical
  obtain ⟨f, hf, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range ρ)
  let R := Set.range (fun g => Matrix.trace (ρ g))
  let : Fintype R := htrace.fintype
  let tuple : G → (Fin (Module.finrank K (Submodule.span K (Set.range ρ))) → R) :=
    fun g i => ⟨Matrix.trace (ρ g * f i), by
      obtain ⟨a, ha⟩ := hf i
      exact ⟨g * a, by simp only [map_mul, ha]⟩⟩
  have hinj : Function.Injective tuple := by
    intro g h he
    apply eq_of_trace_right_translates ρ hρ htorsion
    intro a
    rw [map_mul, map_mul]
    apply trace_mul_eq_of_mem_span (S := Set.range f)
    · rintro B ⟨i, rfl⟩
      exact congrArg Subtype.val (congrFun he i)
    · rw [hspan]
      exact Submodule.subset_span ⟨a, rfl⟩
  have hdim : Module.finrank K (Submodule.span K (Set.range ρ)) ≤ 4 := by
    have h := Submodule.finrank_le (Submodule.span K (Set.range ρ))
    simpa [Binary, Module.finrank_matrix] using h
  have hR : 1 ≤ R.ncard := by
    apply (Set.ncard_pos htrace).mpr
    exact ⟨Matrix.trace (ρ 1), ⟨1, rfl⟩⟩
  calc
    Nat.card G ≤ Nat.card (Fin (Module.finrank K (Submodule.span K (Set.range ρ))) → R) :=
      Nat.card_le_card_of_injective tuple hinj
    _ = R.ncard ^ Module.finrank K (Submodule.span K (Set.range ρ)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    _ ≤ R.ncard ^ 4 := Nat.pow_le_pow_right hR hdim

/-- Quantitative finite trace criterion for a torsion matrix submonoid. -/
theorem card_submonoid_le_trace_range_pow_four (S : Submonoid (Binary (K := K)))
    (htorsion : ∀ T : S, IsOfFinOrder (T : Binary (K := K)))
    (htrace : (Set.range (fun T : S => Matrix.trace (T : Binary (K := K)))).Finite) :
    Nat.card S ≤ (Set.range (fun T : S => Matrix.trace (T : Binary (K := K)))).ncard ^ 4 := by
  have ht : ∀ T : S, IsOfFinOrder T := by
    intro T
    obtain ⟨n, hn, hp⟩ := (htorsion T).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext hp⟩
  let : Group S := groupOfIsUnit (fun T => (ht T).isUnit)
  exact card_le_trace_range_pow_four S.subtype Subtype.val_injective htorsion htrace

/-- The quantitative finite trace criterion includes an empty matrix set. -/
theorem ncard_matrix_set_le_trace_image_pow_four {S : Set (Binary (K := K))}
    (hmul : ∀ U ∈ S, ∀ V ∈ S, U * V ∈ S)
    (htorsion : ∀ T ∈ S, IsOfFinOrder T)
    (htrace : (Matrix.trace '' S).Finite) :
    S.ncard ≤ (Matrix.trace '' S).ncard ^ 4 := by
  classical
  by_cases hne : S.Nonempty
  · have hone : (1 : Binary (K := K)) ∈ S := by
      obtain ⟨T, hT⟩ := hne
      obtain ⟨n, hn, hp⟩ := (htorsion T hT).exists_pow_eq_one
      rw [← hp]
      exact positive_power_mem hmul hT hn
    let M : Submonoid (Binary (K := K)) :=
      { carrier := S, one_mem' := hone, mul_mem' := fun hU hV => hmul _ hU _ hV }
    have he : Set.range (fun T : M => Matrix.trace (T : Binary (K := K))) =
        Matrix.trace '' S := by
      ext x
      constructor
      · rintro ⟨T, rfl⟩
        exact ⟨T, T.property, rfl⟩
      · rintro ⟨T, hT, rfl⟩
        exact ⟨⟨T, hT⟩, rfl⟩
    have h := card_submonoid_le_trace_range_pow_four M
      (fun T => htorsion T T.property) (he ▸ htrace)
    rw [he] at h
    exact h
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

end
end Holant.Projective.BoundedTorsion
