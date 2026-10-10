import Holant.Certificates.PlatonicIncidence.Coordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The finite secant predicate is equivalent to membership in the literal
complex span of identity and a source matrix. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- All imaginary-coordinate 2x2 minors, computed in Z[phi]. -/
def baseSecant (g : PlatonicModel) (j : Fin (size g)) : Finset (Fin (size g)) :=
  Finset.univ.filter fun k => ∀a b : Fin 3,
    goldenCross (raw g j) (raw g k) a.succ b.succ=GoldenInt.zero

theorem nonidentity_coordinate (g : PlatonicModel) (j : Fin (size g))
    (hj : j≠identityIndex g) : ∃a : Fin 3,coordinates (representative g j) a.succ≠0 := by
  by_contra hn
  push_neg at hn
  have he : representative g j=coordinates (representative g j) 0 • (1 : Mat) := by
    apply coordinates.injective
    funext a
    rw [map_smul]
    simp only [Pi.smul_apply,smul_eq_mul,coordinates_one]
    by_cases ha : a=0
    · subst a
      simp only [ite_true,mul_one]
    · obtain ⟨a,rfl⟩ := Fin.eq_succ_of_ne_zero ha
      simpa only [Fin.succ_ne_zero,ite_false,mul_zero] using hn a
  rw [←representative_identity g] at he
  exact hj (projectively_injective g j (identityIndex g) _ he)

theorem mem_identity_span_iff (U V : Mat)
    (hU : ∃a : Fin 3,coordinates U a.succ≠0) :
    V∈Submodule.span ℂ ({(1 : Mat),U} : Set Mat) ↔
      ∀a b : Fin 3,coordinates U a.succ*coordinates V b.succ=
        coordinates U b.succ*coordinates V a.succ := by
  constructor
  · intro h
    obtain ⟨c,d,h⟩ := Submodule.mem_span_pair.mp h
    have hh := congrArg coordinates h
    simp only [map_add,map_smul] at hh
    intro a b
    have ha := congrFun hh a.succ
    have hb := congrFun hh b.succ
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,coordinates_one,Fin.succ_ne_zero,
      if_false,mul_zero,zero_add] at ha hb
    rw [←ha,←hb]
    ring
  · intro h
    obtain ⟨a,ha⟩ := hU
    let d := coordinates V a.succ/coordinates U a.succ
    let c := coordinates V 0-d*coordinates U 0
    apply Submodule.mem_span_pair.mpr
    refine ⟨c,d,?_⟩
    apply coordinates.injective
    rw [map_add,map_smul,map_smul]
    funext b
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,coordinates_one]
    by_cases hb : b=0
    · subst b
      simp [c]
    · obtain ⟨b,rfl⟩ := Fin.eq_succ_of_ne_zero hb
      simp only [Fin.succ_ne_zero,if_false,mul_zero,zero_add]
      dsimp [d]
      apply (mul_left_cancel₀ ha)
      calc
        coordinates U a.succ*(coordinates V a.succ/coordinates U a.succ*coordinates U b.succ)
            =coordinates U b.succ*coordinates V a.succ := by field_simp
        _=coordinates U a.succ*coordinates V b.succ := (h a b).symm

theorem baseSecant_iff (g : PlatonicModel) (j k : Fin (size g))
    (hj : j≠identityIndex g) :
    k∈baseSecant g j ↔ representative g k∈Submodule.span ℂ
      ({(1 : Mat),representative g j} : Set Mat) := by
  rw [mem_identity_span_iff _ _ (nonidentity_coordinate g j hj)]
  simp only [baseSecant,Finset.mem_filter,Finset.mem_univ,true_and]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro b
  rw [←complex_golden_zero_iff]
  simp only [goldenCross,GoldenInt.eval_sub,GoldenInt.eval_mul,Complex.ofReal_sub,
    Complex.ofReal_mul,coordinates_golden,representative,sub_eq_zero]

end
end Holant.Certificates.PlatonicIncidence
