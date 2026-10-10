import Holant.Tractable.TwoTranslate.Phase
import Holant.Tractable.TwoTranslate.Support

/-!
Manuscript Lemma 2.7, `lem:affine-two-translate-closure`.

The original finite GF(2) support systems and even-mixed Z/4 quadratics are
retained. A kernel translation uses the four exact derivative residue cases.
A non-kernel translation uses a detecting row to construct an affine projection
and a finite system for the union of the two disjoint support cosets. The result
includes the zero signature, inconsistent support systems, and arity zero.
-/
namespace Holant.Tractable
noncomputable section
open AffinePhase TwoTranslate

/-- The affine class is closed under summing a signature with any Boolean
translate, without any nonvanishing or positive-arity hypothesis. -/
theorem Affine.two_translate {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Affine f) (w : Fin n → Bool) :
    Affine (fun x => f x + f (AffinePhase.xor x w)) := by
  classical
  rcases hf with rfl | ⟨s, hs, S, Q, rfl⟩
  · left
    funext x
    simp
  · by_cases hw : ∀ r, rowDot (S.matrix r) w = 0
    · convert ((affine_phase_two_translate Q w).scale s).restrict S using 1
      funext x
      have ht := holds_translate_iff S w x hw
      by_cases hx : S.Holds x
      · have hxw := ht.mpr hx
        simp [affineFormula, hx, hxw, mul_add]
      · have hxw : ¬ S.Holds (xor x w) := fun h => hx (ht.mp h)
        simp [affineFormula, hx, hxw]
    · obtain ⟨r, hr⟩ := exists_detecting_row S w hw
      have hp : IsAffineMap (projection S w r) := by
        intro x y
        rw [projection_affine, AffinePhase.xor_assoc]
      convert ((affine_quadratic_precompose Q (projection S w r) hp).scale s).restrict
        (saturationSystem S w r) using 1
      funext x
      rw [sum_eq_projected S w r hr (affineFormula s S Q)
        (by intro y hy; simp [affineFormula, hy]) x]
      by_cases hx : (saturationSystem S w r).Holds x
      · have hpx := (saturation_holds_projection S w x r).mp hx
        simp [hx, affineFormula, hpx]
      · simp [hx]

/-- Source-labelled main-path statement of Lemma 2.7. -/
theorem affine_two_translate_closure {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Affine f) (w : Fin n → Bool) :
    Affine (fun x => f x + f (AffinePhase.xor x w)) :=
  hf.two_translate w

end
end Holant.Tractable
