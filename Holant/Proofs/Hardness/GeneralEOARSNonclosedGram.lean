import Holant.Proofs.Hardness.GeneralEOARSNonclosedSupport
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Equality in the finite complex Gram inequality forces the two support
fibres to agree. This supplies the free-pair branch of the mating split. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedGram
open Holant
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

def rowMass (u : ι → ℂ) : ℝ := ∑ i, ‖u i‖ ^ 2
def rowInner (u v : ι → ℂ) : ℂ := ∑ i, u i * star (v i)

theorem saturated (u v : ι → ℂ) (b : ℝ) (hb : 0 < b)
    (hu : rowMass u = b) (hv : rowMass v = b) (hc : ‖rowInner u v‖ = b) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ i, u i = c * v i := by
  let U : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  let V : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hU : ‖U‖ ^ 2 = b := (EuclideanSpace.norm_sq_eq U).trans hu
  have hV : ‖V‖ ^ 2 = b := (EuclideanSpace.norm_sq_eq V).trans hv
  have U0 : U ≠ 0 := by intro h; simp [h] at hU; linarith
  have V0 : V ≠ 0 := by intro h; simp [h] at hV; linarith
  have UV : ‖U‖ = ‖V‖ := by nlinarith [norm_nonneg U,norm_nonneg V]
  have hin : inner ℂ V U = rowInner u v := by
    simp [PiLp.inner_apply,RCLike.inner_apply,rowInner,U,V]
  have sat : ‖inner ℂ V U‖ = ‖V‖ * ‖U‖ := by
    rw [hin,hc,UV]
    nlinarith
  obtain ⟨c,hc,he⟩ := (norm_inner_eq_norm_iff V0 U0).mp sat
  exact ⟨c,hc,fun i => congrArg (fun z : EuclideanSpace ℂ ι => z i) he⟩

theorem saturated_support (u v : ι → ℂ) (b : ℝ) (hb : 0 < b)
    (hu : rowMass u = b) (hv : rowMass v = b) (hc : ‖rowInner u v‖ = b) :
    ∀ i, u i ≠ 0 ↔ v i ≠ 0 := by
  obtain ⟨c,hc,h⟩ := saturated u v b hb hu hv hc
  intro i
  rw [h i]
  simp only [ne_eq,mul_eq_zero,not_or,hc,not_false_eq_true,true_and]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedGram
