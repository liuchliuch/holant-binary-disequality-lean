import Holant.Proofs.Hardness.PositiveDynamicGraphFilter
import Holant.Proofs.Hardness.NuComplexDynamicSeparation

/-! The accepted original-q sequence and difference identity are reused unchanged.
Complex ν-dominant norm-cone estimates prove the denominator in the original field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.NuComplexDynamicGraphFilter
namespace Q
export ExactTwoChainQueries (Input)
export PositiveDynamicQueries (count)
end Q
namespace G
export ThreeModeGraphEvaluation (sourceValue)
end G
namespace A
export ThreeModeAnnihilator (denominator differenceFilter)
end A
namespace D
export PositiveDynamicSeparation (lam mu nu)
end D
variable {K : Type} [Field K] [CharZero K] (a b c : K)
variable (params : NuComplexDynamicParameters.Data)
abbrev roots := PositiveDynamicGraphFilter.roots a b c params.realParams
abbrev queryValue := PositiveDynamicGraphFilter.queryValue a b c params.realParams

theorem difference_identity (r : Q.Input) :
    A.differenceFilter (roots a b c params r) (queryValue a b c params r) 0=
      G.sourceValue a b c r*A.denominator (Q.count r)
        (D.lam a b (params.length (Q.count r))) (D.mu a b c (params.length (Q.count r)))
        (D.nu a b c (params.length (Q.count r))) :=
  PositiveDynamicGraphFilter.difference_identity a b c params.realParams r

variable (σ : K→+*ℂ) (ha : σ a=params.a) (hb : σ b=params.b) (hc : σ c=params.c)
include ha hb hc in
theorem recovery (r : Q.Input) :
    A.differenceFilter (roots a b c params r) (queryValue a b c params r) 0/
      A.denominator (Q.count r) (D.lam a b (params.length (Q.count r)))
        (D.mu a b c (params.length (Q.count r))) (D.nu a b c (params.length (Q.count r)))=
      G.sourceValue a b c r := by
  rw [difference_identity,mul_div_cancel_right₀ _
    (NuComplexDynamicSeparation.denominator_nonzero σ a b c params ha hb hc (Q.count r))]
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.NuComplexDynamicGraphFilter
