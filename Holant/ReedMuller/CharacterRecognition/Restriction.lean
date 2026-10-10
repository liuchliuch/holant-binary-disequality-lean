import Holant.ReedMuller.CharacterRecognition.Source

/-! Character-flatness supplies literal coefficient characters under affine
coordinate maps whenever the mapped points really lie on the support. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {r n : ℕ}

/-- Restrict an actual character-flat signature through affine coordinates,
keeping a recorded nonzero scalar and the exterior Bell sign character.
The support assumption is about actual nonzero signature values. -/
theorem character_of_CFlat_restriction (f : Signature ℂ n) (hf : CFlat f)
    (P : Word r → Prop) (x₀ : Word r) (hx₀ : P x₀)
    (p : BinaryVector r →ₗ[ZMod 2] BinaryVector n) (z : BinaryVector n)
    (s : ℂ) (hs : s≠0) (mu : Character r)
    (hn : ∀ x,P x → f (wordVector (z+p (vectorWord x)))≠0) :
    ∃ c : ℂ,c≠0 ∧ ∃ ell : Character r,∀ x,P x →
      s*sign (mu (vectorWord x))*f (wordVector (z+p (vectorWord x)))=
        c*sign (ell (vectorWord x)) := by
  classical
  rcases hf with hz|⟨c,a,D,ell,hD,hf⟩
  · have hh := hn x₀ hx₀
    simp [hz] at hh
  refine ⟨s*(c : ℂ)*sign (ell z),mul_ne_zero (mul_ne_zero hs c.ne_zero) (sign_nonzero _),
    mu+ell.comp p,?_⟩
  intro x hx
  have hh := hn x hx
  rw [hf] at hh ⊢
  have hmem : z+p (vectorWord x)-a∈D := by
    exact (value_nonzero_iff c c.ne_zero a D ell _).mp (by
      simpa only [signature,vector_word] using hh)
  change s*sign (mu (vectorWord x))*
    (if vectorWord (wordVector (z+p (vectorWord x)))-a∈D then
      (c : ℂ)*sign (ell (vectorWord (wordVector (z+p (vectorWord x))))) else 0)=_
  rw [vector_word,if_pos hmem]
  simp only [map_add,sign_add,LinearMap.add_apply,LinearMap.comp_apply]
  ring

end
end Holant.ReedMuller.CharacterRecognition
