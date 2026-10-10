import Holant.ReedMuller.CharacterFlat.LinearLift

/-! On a two-point internal fibre the character either survives everywhere
with the same factor two, or cancels on every feasible boundary word. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem lift_mem_pair_projection (D : BinaryCode (n+2)) (hd : pairWord n∈D)
    (a : BinaryVector (n+2)) (eta b0 : ZMod 2) (x0 : BinaryVector n)
    (h0 : lift eta b0 x0-a∈D) (b : ZMod 2) (x : BinaryVector n) :
    lift eta b x-a∈D ↔ x-x0∈equalProjection D := by
  rw [lift_mem_translate D a eta b0 x0 h0]
  constructor
  · intro h
    exact ⟨b-b0,h⟩
  · rintro ⟨r,hr⟩
    exact (prepend_mem_iff D (x-x0) r hr (b-b0)).mpr (Or.inr hd)

/-- Complete sign/cancellation formula, including the actual nonzero scalar
when the fibre character is trivial. No subset of the support is discarded. -/
theorem close_with_pair (D : BinaryCode (n+2)) (hd : pairWord n∈D)
    (a : BinaryVector (n+2)) (ell : Character (n+2)) (c : ℂ)
    (eta b0 : ZMod 2) (x0 : BinaryVector n) (h0 : lift eta b0 x0-a∈D) :
    closeValue eta (value c a D ell)=
      if ell (pairWord n)=0 then
        value (2*c*sign (ell (lift eta 0 0))) x0 (equalProjection D) (ell.comp tailEmbedding)
      else 0 := by
  funext x
  simp only [closeValue,ite_apply,Pi.zero_apply]
  simp only [value,lift_mem_pair_projection D hd a eta b0 x0 h0]
  by_cases hx : x-x0∈equalProjection D
  · simp only [hx,ite_true]
    rw [←Finset.mul_sum,sign_sum_lift]
    split_ifs <;> ring
  · simp [hx]

theorem double_scalar_nonzero (c : ℂ) (hc : c≠0) (ell : Character (n+2)) (eta : ZMod 2) :
    2*c*sign (ell (lift eta 0 (0 : BinaryVector n)))≠0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) hc) (sign_nonzero _)

end
end Holant.ReedMuller.CharacterFlat
