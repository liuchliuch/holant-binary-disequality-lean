import Holant.Proofs.FiniteGroups.Stabilization.FieldExtension
import Holant.Projective.FiniteSubgroupClassification.FixedPoints
import Holant.Projective.BoundedTorsion.TraceValues
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Basic


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates.MatchingContractionClosure
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem traceRatio_conj (V U : Matrix.GeneralLinearGroup Bool ℂ) :
    traceRatio ((V * U * V⁻¹ : Matrix.GeneralLinearGroup Bool ℂ) : Mat) = traceRatio (U : Mat) := by
  have ht : Matrix.trace ((V * U * V⁻¹ : Matrix.GeneralLinearGroup Bool ℂ) : Mat) =
      Matrix.trace (U : Mat) := Matrix.trace_units_conj V U
  have hd : Matrix.det ((V * U * V⁻¹ : Matrix.GeneralLinearGroup Bool ℂ) : Mat) =
      Matrix.det (U : Mat) := by
    change ((Matrix.GeneralLinearGroup.det (V * U * V⁻¹) : ℂˣ) : ℂ) =
      ((Matrix.GeneralLinearGroup.det U : ℂˣ) : ℂ)
    congr 1
    simp [map_mul, map_inv, mul_comm, mul_left_comm]
  simp only [traceRatio, ht, hd]

theorem traceRatio_diagonal (a : ℂˣ) :
    traceRatio ((diagonalGL a 1 : Matrix.GeneralLinearGroup Bool ℂ) : Mat) =
      (a : ℂ) + (a : ℂ)⁻¹ := by
  have hd : Matrix.det ((diagonalGL a 1 : Matrix.GeneralLinearGroup Bool ℂ) : Mat) = (a : ℂ) := by
    rw [← Matrix.det_reindex_self finTwoEquiv.symm _, Matrix.det_fin_two]
    change (a : ℂ) * 1 - 0 * 0 = (a : ℂ)
    ring
  have ht : Matrix.trace ((diagonalGL a 1 : Matrix.GeneralLinearGroup Bool ℂ) : Mat) = (a : ℂ) + 1 := by
    simp [diagonalGL, Matrix.trace, diagonal, add_comm]
  rw [traceRatio, hd, ht]
  field_simp [a.ne_zero]
  <;> ring

theorem traceRatio_of_conjugate_torus (U : Matrix.GeneralLinearGroup Bool ℂ)
    (g : PGL2 ℂ) (a : ℂˣ) (he : g * pglMk ℂ U * g⁻¹ = torusHom a) :
    traceRatio (U : Mat) = (a : ℂ) + (a : ℂ)⁻¹ := by
  induction g using Quotient.inductionOn with
  | h V =>
    have he' : pglMk ℂ (V * U * V⁻¹) = pglMk ℂ (diagonalGL a 1) := by
      rw [map_mul, map_mul, map_inv]
      exact he
    obtain ⟨c, hc, hm⟩ := projectiveClass_eq_iff.mp
      (pglMk_eq_iff_projectiveClass_eq.mp he')
    calc
      traceRatio (U : Mat) = traceRatio ((V * U * V⁻¹ : Matrix.GeneralLinearGroup Bool ℂ) : Mat) :=
        (traceRatio_conj V U).symm
      _ = traceRatio (c • ((diagonalGL a 1 : Matrix.GeneralLinearGroup Bool ℂ) : Mat)) := congrArg _ hm
      _ = traceRatio ((diagonalGL a 1 : Matrix.GeneralLinearGroup Bool ℂ) : Mat) := traceRatio_smul _ hc
      _ = (a : ℂ) + (a : ℂ)⁻¹ := traceRatio_diagonal a

variable {L : Type*} [Field L] [NumberField L]

theorem torus_ratio_descends (ι : L →ₐ[ℚ] ℂ) (q : PGL2 L)
    (g : PGL2 ℂ) (a : ℂˣ)
    (he : g * pglExtend ι.toRingHom q * g⁻¹ = torusHom a) :
    ∃ s : L, (a : ℂ) + (a : ℂ)⁻¹ = ι s := by
  induction q using Quotient.inductionOn with
  | h U =>
    refine ⟨traceRatio (U : Binary), ?_⟩
    change g * pglExtend ι.toRingHom (pglMk L U) * g⁻¹ = torusHom a at he
    rw [pglExtend_mk] at he
    have ht := traceRatio_of_conjugate_torus (Matrix.GeneralLinearGroup.map ι.toRingHom U) g a he
    have hm : ((Matrix.GeneralLinearGroup.map ι.toRingHom U :
        Matrix.GeneralLinearGroup Bool ℂ) : Mat) = (U : Binary (K := L)).map ι.toRingHom := by
      ext i j
      rfl
    rw [hm] at ht
    have hmap := Holant.Projective.BoundedTorsion.traceRatio_map (E := ℂ)
      ι.toRingHom (U : Binary (K := L))
    exact ht.symm.trans hmap

/-- The embedding is a genuine algebra embedding, not an element-order
bound premise.  Its existence is supplied in ExactGroupBound. -/
theorem projective_order_dvd_sourceExponent (ι : L →ₐ[ℚ] ℂ) (q : PGL2 L)
    (hq : IsOfFinOrder q) : orderOf q ∣ torsionExponent (Module.finrank ℚ L) := by
  letI : Algebra L ℂ := ι.toRingHom.toAlgebra
  letI : IsScalarTower ℚ L ℂ := IsScalarTower.of_algebraMap_eq (fun x => (ι.commutes x).symm)
  let qC := pglExtend ι.toRingHom q
  have hf : IsOfFinOrder qC := (pglExtend ι.toRingHom).isOfFinOrder hq
  have ho : orderOf qC = orderOf q := pglExtend_order ι.toRingHom q
  by_cases h1 : qC = 1
  · have horder : orderOf q = 1 := by simpa [h1] using ho.symm
    rw [horder]
    exact one_dvd _
  · obtain ⟨g, a, _, he⟩ := exists_conjugate_torus hf h1
    have haorder : orderOf (a : ℂ) = orderOf q := by
      rw [orderOf_units, ← orderOf_injective torusHom torusHom_injective, ← he]
      exact ((MulAut.conj g).orderOf_eq qC).trans ho
    have hpos : 0 < orderOf (a : ℂ) := haorder.symm ▸ hq.orderOf_pos
    obtain ⟨s, hs⟩ := torus_ratio_descends ι q g a he
    rw [← haorder]
    exact eigenratio_order_dvd_exponent hpos (IsPrimitiveRoot.orderOf (a : ℂ))
      (show (a : ℂ) + (a : ℂ)⁻¹ = algebraMap L ℂ s from hs)

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
