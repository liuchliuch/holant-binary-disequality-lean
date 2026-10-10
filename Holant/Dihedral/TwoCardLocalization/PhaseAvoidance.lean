import Holant.Dihedral.CompatibleCoefficientLine.Interface
import Holant.Projective.RootPolygon

/-! A genuine finite-grid choice for the parity/parity fusion case. The two
exceptional roots are excluded by a degree-two polynomial, including m=3. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Polynomial

/-- A nonzero quadratic cannot vanish on the full source root grid. -/
theorem phase_square_avoid {m : ℕ} (hm : 3 ≤ m) (a b : Scalar) (ha : a ≠ 0) :
    ∃ t : {t : Scalar // Roots m t}, a*t.val^2 ≠ b := by
  classical
  by_contra hn
  push_neg at hn
  let p : ℂ[X] := C (a:ℂ)*X^2-C (b:ℂ)
  have hdeg : p.natDegree ≤ m := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_X_pow_le _ 2).trans (by omega)
    · simp
  have hvanish (z : ℂ) (hz : z^m=1) : p.eval z=0 := by
    let t : Scalar := Holant.Projective.CyclicPhasePencil.algebraicRoot (by omega) z hz
    have ht : Roots m t := Holant.Projective.CyclicPhasePencil.algebraicRoot_pow (by omega) z hz
    have he : a*t^2=b := hn ⟨t,ht⟩
    have he' : (a:ℂ)*z^2=(b:ℂ) := by
      change (a:ℂ)*(t:ℂ)^2=(b:ℂ)
      exact_mod_cast he
    simp [p,he']
  have hc := Holant.Projective.root_polygon_interior_coeff (by omega) p hdeg hvanish
    (k:=2) (by omega) (by omega)
  have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  apply ha'
  simpa [p] using hc

/-- Literal normalized-weight ratio from the source three-factor fusion. -/
theorem opposite_parity_weight_ratio (α : Bool) (a₀ a₁ b₀ b₁ t : Scalar)
    (ha₁ : a₁ ≠ 0) (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) (ht : t ≠ 0) :
    (a₀*exponent α t*exponent α b₀)/(a₁*exponent (!α) t*exponent (!α) b₁) =
      if α then (a₀/(a₁*b₀*b₁))*(t⁻¹)^2 else (a₀*b₀*b₁/a₁)*t^2 := by
  cases α <;> simp only [exponent,Bool.not_false,Bool.not_true,Bool.false_eq_true,reduceCtorEq,ite_true,ite_false] <;>
    field_simp [ha₁,hb₀,hb₁,ht] <;> ring

/-- The selected phase keeps the two normalized fused coefficient lines apart.
No unequal-ratio conclusion is supplied as an assumption. -/
theorem opposite_parity_weights_distinct {m : ℕ} (hm : 3 ≤ m)
    (α : Bool) (a₀ a₁ b₀ b₁ : Scalar)
    (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) :
    ∃ t : {t : Scalar // Roots m t},
      a₀*exponent α t.val*exponent α b₀ ≠ a₁*exponent (!α) t.val*exponent (!α) b₁ := by
  cases α
  · obtain ⟨t,ht⟩ := phase_square_avoid hm (a₀*b₀*b₁) a₁ (mul_ne_zero (mul_ne_zero ha₀ hb₀) hb₁)
    refine ⟨t,?_⟩
    simp only [exponent,Bool.not_false,Bool.false_eq_true,reduceCtorEq,ite_true,ite_false]
    intro he
    apply ht
    have ht0 := t.property.ne_zero (by omega : 0<m)
    field_simp [ht0,hb₁] at he
    linear_combination he
  · obtain ⟨t,ht⟩ := phase_square_avoid hm (a₁*b₁*b₀) a₀ (mul_ne_zero (mul_ne_zero ha₁ hb₁) hb₀)
    refine ⟨t,?_⟩
    simp only [exponent,Bool.not_true,Bool.false_eq_true,reduceCtorEq,ite_true,ite_false]
    intro he
    apply ht
    have ht0 := t.property.ne_zero (by omega : 0<m)
    field_simp [ht0,hb₀] at he
    linear_combination -he

end Holant.Dihedral.TwoCardLocalization
