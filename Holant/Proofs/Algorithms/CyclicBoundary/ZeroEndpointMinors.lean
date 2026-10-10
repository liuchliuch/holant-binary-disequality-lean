import Holant.Projective.CyclicQuaternary.Coordinates


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointMinors
open Holant.Projective.CyclicQuaternary
noncomputable section

def minor (x y z : ℂ) : ℂ := (y-z)^2-x^2

/-- Direct polynomial proof, retaining the zero solution as well. -/
theorem simultaneous_zero (x y z : ℂ)
    (h₁ : minor x y z = 0) (h₂ : minor y z x = 0) (h₃ : minor z x y = 0) :
    (x = y ∧ z = 0) ∨ (x = z ∧ y = 0) ∨ (y = z ∧ x = 0) := by
  unfold minor at h₁ h₂ h₃
  have hz : z*(z-x-y) = 0 := by
    linear_combination (1/2:ℂ)*h₁ + (1/2:ℂ)*h₂
  rcases mul_eq_zero.mp hz with hz | hz
  · left
    refine ⟨?_,hz⟩
    rw [hz, zero_pow (by decide : 2 ≠ 0), sub_zero] at h₃
    exact sub_eq_zero.mp (mul_self_eq_zero.mp (by simpa only [pow_two] using h₃))
  · have he : z = x+y := by linear_combination hz
    rw [he] at h₃
    have hxy : x*y = 0 := by linear_combination (-1/4:ℂ)*h₃
    rcases mul_eq_zero.mp hxy with hx | hy
    · right; right
      exact ⟨by simpa [hx] using he.symm,hx⟩
    · right; left
      exact ⟨by simpa [hy] using he.symm,hy⟩

theorem nonzero_minor_or_line (x y z : ℂ) :
    minor x y z ≠ 0 ∨ minor y z x ≠ 0 ∨ minor z x y ≠ 0 ∨
      (x = y ∧ z = 0) ∨ (x = z ∧ y = 0) ∨ (y = z ∧ x = 0) := by
  by_cases h₁ : minor x y z = 0
  · by_cases h₂ : minor y z x = 0
    · by_cases h₃ : minor z x y = 0
      · exact Or.inr (Or.inr (Or.inr (simultaneous_zero x y z h₁ h₂ h₃)))
      · exact Or.inr (Or.inr (Or.inl h₃))
    · exact Or.inr (Or.inl h₂)
  · exact Or.inl h₁

def leftFactor (r₁ r₂ a₂ : ℂ) : Signature ℂ 2 := fun x =>
  if x 0 then (if x 1 then 0 else r₁) else (if x 1 then a₂*r₂ else 0)

def rightFactor (r₁ r₂ : ℂ) : Signature ℂ 2 := fun x =>
  if x 0 then (if x 1 then 0 else 1) else (if x 1 then r₂/r₁ else 0)

/-- Literal source coordinate table after the indicated permutation of the
three complement blocks. The proof works at the original four ordered ports. -/
theorem factor_identity (r₁ r₂ a₁ a₂ : ℂ) (hr : r₁ ≠ 0)
    (h : a₁*r₁^2 = a₂*r₂^2) :
    ofCoordinates 0 0 ![(r₁,a₁*r₁),(r₂,a₂*r₂),(0,0)] =
      fun w => leftFactor r₁ r₂ a₂ ![w 0,w 3] * rightFactor r₁ r₂ ![w 1,w 2] := by
  funext w
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [ofCoordinates, leftFactor, rightFactor, h0, h1, h2, h3]
  all_goals field_simp [hr]
  all_goals first | exact h | ring | linear_combination h | linear_combination -h

theorem leftFactor_nonzero (r₁ r₂ a₂ : ℂ) (hr : r₁ ≠ 0) : leftFactor r₁ r₂ a₂ ≠ 0 := by
  intro h
  have he := congrFun h ![true,false]
  exact hr (by simpa [leftFactor] using he)

theorem rightFactor_nonzero (r₁ r₂ : ℂ) : rightFactor r₁ r₂ ≠ 0 := by
  intro h
  have he := congrFun h ![true,false]
  simpa [rightFactor] using he

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointMinors
