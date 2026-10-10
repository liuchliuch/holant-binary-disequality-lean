import Holant.ReedMuller.CoefficientAtlas.Physical

/-! Source Lemma7.11 with original physical I/X cards, inverse Walsh coordinates,
actual Reed–Muller support, and exact output scalar. -/
namespace Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.LowArity
noncomputable section
set_option backward.isDefEq.respectTransparency false

instance codeMembershipDecidable (x : BinaryVector 8) : Decidable (x∈code) := by
  change Decidable (∃ a : Param,evaluate a=x)
  infer_instance

theorem support_word_iff_code (x : Point → Bool) :
    (∃ a : Param,word a=x) ↔ vector x∈code := by
  change (∃ a : Param,word a=x) ↔ ∃ a : Param,evaluate a=vector x
  simp only [word_eq_iff_evaluate]

theorem sign_eq_pow (z : ZMod 2) :
    (sign (G := ℂˣ) (-1) z:ℂ)=(-1:ℂ)^z.val := by
  fin_cases z
  · change (1:ℂ)=(-1:ℂ)^0
    simp
  · change (-1:ℂ)=(-1:ℂ)^1
    simp

/-- Full current Lemma7.11. The proof needs only the one-step part of the
proper physical I/X deck, so no additional retained-state or coefficient
normalization premise is imposed. -/
theorem source_rm_coefficient_atlas (f : Signature ℂ 8)
    (hsupport : SupportRM (walsh f)) (hdeck : PhysicalDeck f) :
    ∃ c : ℂˣ, ∃ w : BinaryVector 8,
      (∀ z, walsh f z=if vector z∈code then
        (c:ℂ)*(-1:ℂ)^(dot w (vector z)).val else 0) ∧
      f=(fun x => if vector x+w∈code then 16*(c:ℂ) else 0) ∧
      (16:ℂ)*(c:ℂ)≠0 := by
  classical
  obtain ⟨c,w,hc⟩ := coefficients_character (walsh f) hsupport (plusCards_of_physical f hdeck)
  refine ⟨c,w,?_,?_,mul_ne_zero (by norm_num) c.ne_zero⟩
  · intro z
    simpa only [support_word_iff_code,sign_eq_pow] using hc z
  · have H := character_fourier (walsh f) hsupport c w hc
    rw [physical_of_walsh] at H
    exact H

end
end Holant.ReedMuller.CoefficientAtlas
