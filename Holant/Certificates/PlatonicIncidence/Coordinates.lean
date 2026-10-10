import Holant.Certificates.RainbowOrbit.GroupRepresentatives
import Mathlib.NumberTheory.Real.GoldenRatio

/-! Exact coordinate bridge for A.19/A.20. Integer golden-ratio certificates
are interpreted in the actual complex matrix space, not an abstract incidence
model. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Mat := Matrix Bool Bool ℂ
abbrev Coord := Fin 4 → ℂ

def assemble (v : Coord) : Mat := fun a b =>
  v 0*Q0 a b+v 1*Q1 a b+v 2*Q2 a b+v 3*Q3 a b

theorem coefficient_assemble (v : Coord) : quaternionCoefficient (assemble v)=v := by
  funext i
  fin_cases i <;>
    simp [quaternionCoefficient,assemble,Q0,Q1,Q2,Q3,Holant.Signature.equality] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem assemble_coefficient (U : Mat) : assemble (quaternionCoefficient U)=U := by
  ext a b
  cases a <;> cases b <;>
    simp [quaternionCoefficient,assemble,Q0,Q1,Q2,Q3,Holant.Signature.equality] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

def coordinates : Mat ≃ₗ[ℂ] Coord where
  toFun := quaternionCoefficient
  invFun := assemble
  left_inv := assemble_coefficient
  right_inv := coefficient_assemble
  map_add' U V := by
    funext i
    fin_cases i <;> simp [quaternionCoefficient] <;> ring
  map_smul' c U := by
    funext i
    exact quaternionCoefficient_smul c U i

@[simp] theorem coordinates_apply (U : Mat) (i : Fin 4) :
    coordinates U i=quaternionCoefficient U i := rfl

@[simp] theorem coordinates_golden (v : GoldenVector) (i : Fin 4) :
    coordinates (goldenMatrix v) i=(GoldenInt.eval (v i) : ℂ) :=
  quaternionCoefficient_quaternion _ _

@[simp] theorem coordinates_one (i : Fin 4) :
    coordinates (1 : Mat) i=if i=0 then 1 else 0 := by
  fin_cases i <;> norm_num [coordinates_apply,quaternionCoefficient,Matrix.one_apply]

/-- Faithfulness is proved from irrationality of the literal golden ratio. -/
theorem golden_eval_zero_iff (u : GoldenInt) : GoldenInt.eval u=0 ↔ u=GoldenInt.zero := by
  constructor
  · intro h
    have hb : u.b=0 := by
      by_contra hb
      have hi : Irrational MatchingProductBridge.goldenRatio := by
        exact Real.goldenRatio_irrational
      apply hi.ne_rational (-u.a) u.b
      apply (eq_div_iff (Int.cast_ne_zero.mpr hb)).mpr
      dsimp [GoldenInt.eval] at h
      push_cast
      linarith
    have ha : u.a=0 := by
      simpa [GoldenInt.eval,hb] using h
    cases u
    simp_all [GoldenInt.zero]
  · rintro rfl
    exact GoldenInt.eval_zero

@[simp] theorem complex_golden_zero_iff (u : GoldenInt) :
    (GoldenInt.eval u : ℂ)=0 ↔ u=GoldenInt.zero := by
  rw [Complex.ofReal_eq_zero,golden_eval_zero_iff]

end
end Holant.Certificates.PlatonicIncidence
