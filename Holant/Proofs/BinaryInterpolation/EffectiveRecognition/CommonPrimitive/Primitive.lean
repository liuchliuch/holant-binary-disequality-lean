import Holant.Algebraic.FiniteFamilyField
import Holant.Proofs.AlgebraicRecognition.CommonFieldCheck
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Perfect


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
open Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Polynomial PowerArithmetic
open scoped BigOperators IntermediateField
noncomputable section

/-- Any positive-degree monic polynomial has exactly the existing companion
relation format; its coefficients, not an arithmetic oracle, are the data. -/
theorem monic_relation (p : ℚ[X]) (hp : p.Monic) (hd : 0 < p.natDegree) :
    ∃ (d : ℕ) (c : Vector d), PowerArithmetic.polynomial c = p := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  refine ⟨d, fun i => -p.coeff i.val, ?_⟩
  have he := p.as_sum_range_C_mul_X_pow
  rw [hd, Finset.sum_range_succ] at he
  have hl : p.coeff (d + 1) = 1 := by
    simpa only [hd] using hp.coeff_natDegree
  simp only [hl, C_1, one_mul] at he
  unfold PowerArithmetic.polynomial
  simp only [map_neg, neg_mul, Finset.sum_neg_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i) (d + 1)]
  rw [sub_neg_eq_add, add_comm]
  exact he.symm

theorem aeval_mem (L : IntermediateField ℚ ℂ) {θ : ℂ} (hθ : θ ∈ L) (p : ℚ[X]) :
    Polynomial.aeval θ p ∈ L := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using L.add_mem hp hq
  | monomial n a =>
    simpa using L.mul_mem (L.algebraMap_mem a) (L.toSubalgebra.pow_mem hθ n)

/-- All specified conjugates lie in one actual embedded finite extension.
The primitive generator belongs to, and generates, that same extension. -/
theorem tuple_primitive {ι : Type*} [Finite ι] (z : ι → ℂ)
    (hz : ∀ i, IsAlgebraic ℚ (z i)) :
    ∃ θ : ℂ, IsAlgebraic ℚ θ ∧ θ ∈ familyField z ∧
      familyField z = ℚ⟮θ⟯ ∧
      ∃ (d : ℕ) (c : Vector d) (e : ι → RationalPolynomialCode),
        PowerArithmetic.polynomial c = minpoly ℚ θ ∧
        (PowerArithmetic.polynomial c).Monic ∧
        (PowerArithmetic.polynomial c).Separable ∧
        (∀ i, Polynomial.aeval θ (e i).polynomial = z i) ∧
        (∀ i, decode θ (CommonFieldCheck.reduce c (e i)) = z i) := by
  classical
  let L := familyField z
  letI : FiniteDimensional ℚ L := familyField_finiteDimensional z hz
  let b : PowerBasis ℚ L := Field.powerBasisOfFiniteOfSeparable ℚ L
  let θ : ℂ := L.val b.gen
  have hθ : IsIntegral ℚ θ := b.isIntegral_gen.map L.val
  have hp : ∀ i, ∃ p : ℚ[X], Polynomial.aeval θ p = z i := by
    intro i
    obtain ⟨p, he⟩ := b.exists_eq_aeval' (fieldCoefficient z i)
    refine ⟨p, ?_⟩
    have h := congrArg L.val he
    simpa only [θ, Polynomial.aeval_algHom_apply, fieldCoefficient,
      IntermediateField.val_mk] using h.symm
  choose p hp using hp
  have he : ∀ i, ∃ e : RationalPolynomialCode, e.polynomial = p i :=
    fun i => RationalPolynomialCode.exists_code (p i)
  choose e he using he
  have hev : ∀ i, Polynomial.aeval θ (e i).polynomial = z i := by
    intro i; rw [he, hp]
  have hfield : familyField z = ℚ⟮θ⟯ := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro w ⟨i, rfl⟩
      rw [← hev i]
      exact aeval_mem _ (IntermediateField.subset_adjoin ℚ {θ} (by simp)) _
    · apply IntermediateField.adjoin_le_iff.mpr
      intro w hw
      have hw' : w = θ := Set.mem_singleton_iff.mp hw
      subst w
      exact b.gen.property
  obtain ⟨d, c, hc⟩ := monic_relation (minpoly ℚ θ) (minpoly.monic hθ) (minpoly.natDegree_pos hθ)
  have hr : θ ^ (d + 1) = decode θ c :=
    relation_of_root θ c (by rw [hc]; exact minpoly.aeval ℚ θ)
  refine ⟨θ, hθ.isAlgebraic, b.gen.property, hfield, d, c, e, hc, ?_, ?_, hev, ?_⟩
  · rw [hc]; exact minpoly.monic hθ
  · rw [hc]; exact (minpoly.irreducible hθ).separable
  · intro i
    rw [CommonFieldCheck.decode_reduce θ c hr, hev]

/-- Split the single tuple only after adjoining both families. In particular,
the witness is never silently required to live in the original coefficient field. -/
theorem coefficient_witness_primitive {m n : ℕ}
    (w : Fin m → AlgebraicComplex) (y : Fin n → AlgebraicComplex) :
    ∃ (θ : ℂ) (d : ℕ) (c : Vector d)
      (e : Fin m → RationalPolynomialCode) (x : Fin n → Vector d),
      IsAlgebraic ℚ θ ∧ PowerArithmetic.polynomial c = minpoly ℚ θ ∧
      (PowerArithmetic.polynomial c).Separable ∧
      (∀ i, Polynomial.aeval θ (e i).polynomial = (w i : ℂ)) ∧
      (∀ j, decode θ (x j) = (y j : ℂ)) := by
  let z : (Fin m ⊕ Fin n) → ℂ := Sum.elim (fun i => (w i : ℂ)) (fun j => (y j : ℂ))
  have hz : ∀ i, IsAlgebraic ℚ (z i) := by
    intro i
    cases i with
    | inl i => exact (w i).property.isAlgebraic
    | inr j => exact (y j).property.isAlgebraic
  obtain ⟨θ, hθ, _, _, d, c, e, hc, _, hs, he, hx⟩ := tuple_primitive z hz
  exact ⟨θ, d, c, fun i => e (.inl i), fun j => CommonFieldCheck.reduce c (e (.inr j)),
    hθ, hc, hs, fun i => he (.inl i), fun j => hx (.inr j)⟩

end
end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
