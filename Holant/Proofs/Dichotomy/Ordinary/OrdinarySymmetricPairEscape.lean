import Holant.Proofs.Hardness.DenseTwoCoefficientEscape

/-! Exact finite two-copy escape for a symmetric paired interaction.
The step is its actual matrix-square ratio, not an interpolated gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinarySymmetricPairEscape
open Holant
namespace E
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseTwoCoefficientEscape
  (InfiniteOrder infinite_of_norm_ne_one)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false

def step (r : ℂ) : ℂ := 2*r/(1+r^2)

theorem two_unit_norms (r : ℂ) (unit : ‖r‖=1) (output : ‖step r‖=1) : r^2=1 := by
  have denominator : ‖1+r^2‖=2 := by
    have h := output
    rw [step,norm_div,norm_mul,unit] at h
    norm_num at h
    exact (div_eq_one_iff_eq (by
      intro zero
      rw [zero,div_zero] at h
      norm_num at h)).mp h |>.symm
  have base : (r^2).re*(r^2).re+(r^2).im*(r^2).im=1 := by
    have h := Complex.normSq_eq_norm_sq (r^2)
    simpa [Complex.normSq_apply,norm_pow,unit,pow_two] using h
  have shifted : (1+(r^2).re)*(1+(r^2).re)+(r^2).im*(r^2).im=4 := by
    have h := Complex.normSq_eq_norm_sq (1+r^2)
    rw [denominator] at h
    norm_num [Complex.normSq_apply,pow_two] at h ⊢
    exact h
  have real : (r^2).re=1 := by nlinarith
  have imag : (r^2).im=0 := by
    apply mul_self_eq_zero.mp
    nlinarith
  apply Complex.ext <;> simp [real,imag]

theorem escape (r : ℂ) (square_not_one : r^2≠1) (square_not_neg_one : r^2≠-1) :
    E.InfiniteOrder r ∨ (1+r^2≠0 ∧ E.InfiniteOrder (step r)) := by
  by_cases unit : ‖r‖=1
  · right
    refine ⟨?_,E.infinite_of_norm_ne_one ?_⟩
    · intro zero
      apply square_not_neg_one
      linear_combination zero
    · intro output
      exact square_not_one (two_unit_norms r unit output)
  · exact Or.inl (E.infinite_of_norm_ne_one unit)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinarySymmetricPairEscape
end
