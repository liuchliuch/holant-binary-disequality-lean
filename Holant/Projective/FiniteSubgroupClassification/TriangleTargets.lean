import Holant.Projective.FiniteSubgroupClassification.TriangleConjugacy
import Holant.Projective.FiniteSubgroupClassification.DihedralConjugacy

/-! The four normalized trace targets occur in the source's actual golden
icosahedral matrix family. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

def triangleTargetIndex (large negative : Bool) : Fin 60 :=
  if large then if negative then 26 else 24 else if negative then 37 else 36

def triangleTargetGL (large negative : Bool) : GL2C :=
  Matrix.GeneralLinearGroup.scalar Bool (Units.mk0 (1 / 2 : ℂ) (by norm_num)) *
    representativeGL .icosahedral (triangleTargetIndex large negative)

theorem triangleTargetGL_val (large negative : Bool) :
    (triangleTargetGL large negative : Mat) =
      (1 / 2 : ℂ) • representative .icosahedral (triangleTargetIndex large negative) := by
  change (Matrix.scalar Bool (1 / 2 : ℂ)) * _ = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  rfl

def triangleTargetDelta (large negative : Bool) : ℂ :=
  if negative then -(Complex.I * (if large then phiC else tauC))
  else Complex.I * (if large then phiC else tauC)

theorem triangleTarget_entries (large negative : Bool) :
    (triangleTargetGL large negative) false false = (1 + triangleTargetDelta large negative) / 2 ∧
    (triangleTargetGL large negative) true true = (1 - triangleTargetDelta large negative) / 2 ∧
    (triangleTargetGL large negative) false true = (if large then tauC else Complex.I * phiC) / 2 ∧
    (triangleTargetGL large negative) true false = (if large then -tauC else Complex.I * phiC) / 2 := by
  change (triangleTargetGL large negative : Mat) false false = _ ∧
    (triangleTargetGL large negative : Mat) true true = _ ∧
    (triangleTargetGL large negative : Mat) false true = _ ∧
    (triangleTargetGL large negative : Mat) true false = _
  rw [triangleTargetGL_val]
  cases large <;> cases negative <;>
    norm_num [Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,triangleTargetIndex, triangleTargetDelta, representative, raw, icosahedralRaw,
      goldenMatrix, GoldenInt.eval, quaternion, quaternionBasis, Q0, Q1, Q2, Q3,
      Holant.Signature.equality, phiC, tauC] <;>
    norm_num [Pi.smul_apply, smul_eq_mul, quaternion, quaternionBasis, Q0, Q1, Q2, Q3,
      Holant.Signature.equality] <;> simp <;> ring <;> simp

theorem triangleTarget_trace (large negative : Bool) :
    Matrix.trace (triangleTargetGL large negative : Mat) = 1 := by
  have he := triangleTarget_entries large negative
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_bool]
  rw [he.1, he.2.1]
  ring

theorem triangleTarget_det (large negative : Bool) :
    Matrix.det (triangleTargetGL large negative : Mat) = 1 := by
  have he := triangleTarget_entries large negative
  rw [det_bool_formula, he.1, he.2.1, he.2.2.1, he.2.2.2]
  cases large <;> cases negative <;> simp only [triangleTargetDelta, Bool.false_eq_true, ↓reduceIte]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals linear_combination golden_pair_sum_sq / 4

theorem triangleTarget_upper_ne_zero (large negative : Bool) :
    (triangleTargetGL large negative) false true ≠ 0 := by
  rw [(triangleTarget_entries large negative).2.2.1]
  apply div_ne_zero _ (by norm_num)
  cases large
  · exact mul_ne_zero Complex.I_ne_zero phiC_ne_zero
  · exact tauC_ne_zero

theorem triangleTarget_delta (large negative : Bool) :
    (triangleTargetGL large negative) false false - (triangleTargetGL large negative) true true =
      triangleTargetDelta large negative := by
  rw [(triangleTarget_entries large negative).1, (triangleTarget_entries large negative).2.1]
  ring

theorem triangleTarget_mem_icosahedral (large negative : Bool) :
    pglMk ℂ (triangleTargetGL large negative) ∈ modelPGL .icosahedral := by
  have he : pglMk ℂ (triangleTargetGL large negative) =
      pglMk ℂ (representativeGL .icosahedral (triangleTargetIndex large negative)) :=
    pglMk_eq_iff_projectiveClass_eq.mpr
      (projectiveClass_eq_iff.mpr ⟨(1 / 2 : ℂ), by norm_num, triangleTargetGL_val large negative⟩)
  rw [he]
  exact (indexedPGL .icosahedral (triangleTargetIndex large negative)).property

/-- Every normalized `(Z,B)` triangle pair is sent into the actual source I
by a diagonal conjugator preserving Z. -/
theorem normalized_triangle_conjugate_into_icosahedral (U : GL2C)
    (ht : Matrix.trace (U : Mat) = 1) (hd : Matrix.det (U : Mat) = 1)
    (h5 : orderOf (zClass * pglMk ℂ U) = 5) :
    ∃ t : ℂˣ, torusHom t * pglMk ℂ U * (torusHom t)⁻¹ ∈ modelPGL .icosahedral := by
  have hroots := triangle_delta_roots (normalized_triangle_delta U ht hd h5)
  have hu := (normalized_triangle_offdiagonal U ht hd h5).1
  have hcase (large negative : Bool)
      (he : U false false - U true true = triangleTargetDelta large negative) :
      ∃ t : ℂˣ, torusHom t * pglMk ℂ U * (torusHom t)⁻¹ ∈ modelPGL .icosahedral := by
    obtain ⟨t, ht⟩ := diagonal_conjugate_of_trace_det_delta U (triangleTargetGL large negative)
      ht (triangleTarget_trace large negative) hd (triangleTarget_det large negative)
      (he.trans (triangleTarget_delta large negative).symm) hu (triangleTarget_upper_ne_zero large negative)
    refine ⟨t, ?_⟩
    rw [ht]
    exact triangleTarget_mem_icosahedral large negative
  rcases hroots with h | h | h | h
  · exact hcase true false h
  · exact hcase true true h
  · exact hcase false false h
  · exact hcase false true h

/-- Actual simultaneous inclusion of every projective `(2,3,5)` pair into I. -/
theorem triangle_pair_conjugate_into_icosahedral {a b : PGL2 ℂ}
    (ha : orderOf a = 2) (hb : orderOf b = 3) (hab : orderOf (a * b) = 5) :
    ∃ g : PGL2 ℂ, g * a * g⁻¹ = zClass ∧ g * b * g⁻¹ ∈ modelPGL .icosahedral := by
  obtain ⟨g, hg⟩ := involution_conjugate_z ha
  let b' := (MulAut.conj g) b
  have hb' : orderOf b' = 3 := (MulAut.conj g).orderOf_eq b |>.trans hb
  have hab' : orderOf (zClass * b') = 5 := by
    rw [← hg]
    change orderOf ((MulAut.conj g) a * (MulAut.conj g) b) = 5
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact hab
  obtain ⟨U, hU, ht, hd⟩ := exists_trace_one_rep_of_order_three b' hb'
  obtain ⟨t, htI⟩ := normalized_triangle_conjugate_into_icosahedral U ht hd (by simpa only [hU] using hab')
  refine ⟨torusHom t * g, ?_, ?_⟩
  · calc
      _ = torusHom t * (g * a * g⁻¹) * (torusHom t)⁻¹ := by group
      _ = zClass := by rw [hg, (torus_commute_z t).eq]; simp [mul_assoc]
  · have he : (torusHom t * g) * b * (torusHom t * g)⁻¹ =
        torusHom t * pglMk ℂ U * (torusHom t)⁻¹ := by
      rw [hU]
      dsimp [b']
      group
    rw [he]
    exact htI

end
end Holant.Projective.FiniteSubgroupClassification
