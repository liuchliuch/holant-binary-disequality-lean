import Holant.Signature
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Ordinary dependence of two coordinate tensors, including either zero
vector, and its exact complex-conjugation/real-line characterization. -/
namespace Holant.Pauli.ProjectiveDetermination
noncomputable section
open scoped ComplexConjugate
variable {K α : Type*} [Field K]

/-- Ordinary dependence, with zero cards explicitly included. -/
def Dependent (u v : α → K) : Prop := u = 0 ∨ ∃ c : K, v = fun x => c*u x

def wedge (u v : α → K) (x y : α) : K := u x*v y-v x*u y

theorem dependent_iff_wedge_zero (u v : α → K) : Dependent u v ↔ ∀ x y, wedge u v x y = 0 := by
  classical
  constructor
  · rintro (rfl | ⟨c,rfl⟩) x y
    · simp [wedge]
    · simp only [wedge]; ring
  · intro h
    by_cases hu : u = 0
    · exact Or.inl hu
    · obtain ⟨x,hx⟩ : ∃ x, u x ≠ 0 := by
        by_contra hn
        push_neg at hn
        exact hu (funext hn)
      refine Or.inr ⟨v x/u x,?_⟩
      funext y
      have hxy : u x*v y = v x*u y := sub_eq_zero.mp (h x y)
      calc
        v y = (v x*u y)/u x := (eq_div_iff hx).mpr (by simpa only [mul_comm] using hxy)
        _ = (v x/u x)*u y := by ring

theorem Dependent.symm {u v : α → K} (h : Dependent u v) : Dependent v u := by
  rw [dependent_iff_wedge_zero] at h ⊢
  intro x y
  unfold wedge
  have hh := h x y
  unfold wedge at hh
  exact sub_eq_zero.mpr (sub_eq_zero.mp hh).symm

/-- Equivalent to a nontrivial two-term linear relation, including the zero pair. -/
theorem dependent_iff_relation (u v : α → K) :
    Dependent u v ↔ ∃ a b : K, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ x, a*u x+b*v x = 0 := by
  constructor
  · rintro (rfl | ⟨c,rfl⟩)
    · exact ⟨1,0,Or.inl one_ne_zero,by simp⟩
    · refine ⟨-c,1,Or.inr one_ne_zero,?_⟩
      intro x; ring
  · rintro ⟨a,b,hab,h⟩
    rw [dependent_iff_wedge_zero]
    by_cases hb : b = 0
    · have ha : a ≠ 0 := hab.resolve_right (not_not_intro hb)
      have hu : ∀ x, u x = 0 := by
        intro x
        have hx := h x
        simpa [hb,ha] using hx
      intro x y; simp [wedge,hu]
    · intro x y
      apply (mul_eq_zero.mp (show b*wedge u v x y = 0 from ?_)).resolve_left hb
      have hx := h x
      have hy := h y
      unfold wedge
      calc
        b*(u x*v y-v x*u y) = u x*(a*u y+b*v y)-u y*(a*u x+b*v x) := by ring
        _ = 0 := by rw [hx,hy]; ring

/-- This also represents the zero vector, using scalar1 and the zero real vector. -/
def IsRealLine (u : α → ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∃ r : α → ℝ, u = fun x => c*(r x : ℂ)

theorem realLine_iff_conjugate_dependent (u : α → ℂ) :
    IsRealLine u ↔ Dependent u (fun x => conj (u x)) := by
  classical
  constructor
  · rintro ⟨c,hc,r,rfl⟩
    rw [dependent_iff_wedge_zero]
    intro x y
    simp only [wedge,map_mul,Complex.conj_ofReal]
    ring
  · intro h
    rw [dependent_iff_wedge_zero] at h
    by_cases hu : u = 0
    · refine ⟨1,one_ne_zero,fun _ => 0,?_⟩
      funext y
      simp [hu]
    · obtain ⟨x,hx⟩ : ∃ x, u x ≠ 0 := by
        by_contra hn
        push_neg at hn
        exact hu (funext hn)
      have hreal (y : α) : conj (u y/u x) = u y/u x := by
        rw [map_div₀]
        apply (div_eq_div_iff (by simpa using hx) hx).mpr
        have hh := sub_eq_zero.mp (h x y)
        simpa only [mul_comm] using hh
      refine ⟨u x,hx,fun y => (u y/u x).re,?_⟩
      funext y
      have hr : ((u y/u x).re : ℂ) = u y/u x := (Complex.conj_eq_iff_re).mp (hreal y)
      rw [hr]
      field_simp

end
end Holant.Pauli.ProjectiveDetermination
