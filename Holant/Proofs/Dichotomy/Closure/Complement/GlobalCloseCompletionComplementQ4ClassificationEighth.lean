import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationAlgebra

/-! The exceptional eighth-root entry ratio escapes after one actual series
square. Its new squared ratio is 2, proved over the original coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationEighth
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem escape (a b : K) (ha : a≠0) (hb : b≠0) (fourth : a^4≠b^4) (eighth : a^8=b^8) :
    2*a*b≠0 ∧ a^2+b^2≠0 ∧ (2*a*b)^8≠(a^2+b^2)^8 := by
  have pair : (a^4-b^4)*(a^4+b^4)=0 := by linear_combination eighth
  have sum : a^4+b^4=0 := (mul_eq_zero.mp pair).resolve_left (sub_ne_zero.mpr fourth)
  have hn : a^2+b^2≠0 := by
    intro zero
    apply fourth
    linear_combination (a^2-b^2)*zero
  refine ⟨mul_ne_zero (mul_ne_zero (by norm_num) ha) hb,hn,?_⟩
  have ratio : (2*a*b)^2=2*(a^2+b^2)^2 := by linear_combination -2*sum
  have powered : (2*a*b)^8=16*(a^2+b^2)^8 := by
    calc
      _=((2*a*b)^2)^4 := by ring
      _=(2*(a^2+b^2)^2)^4 := by rw [ratio]
      _=_ := by ring
  intro same
  have zero : (15:K)*(a^2+b^2)^8=0 := by linear_combination same-powered
  exact mul_ne_zero (by norm_num : (15:K)≠0) (pow_ne_zero _ hn) zero

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationEighth
end
