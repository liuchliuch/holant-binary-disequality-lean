import Holant.ReedMuller.AffinePatching.ReconstructionSupport

/-! Reconstruct the source affine class from its actual support and its phase
identities on fully supported cubes, allowing all repeated directions. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

/-- Affine Boolean maps carry a cube to a cube with their linear directions. -/
theorem affineMap_cubeWords (p : Word m → Word n) (hp : IsAffineMap p)
    (z u v w : Word m) (i : Fin 8) :
    p (cubeWords z u v w i) = cubeWords (p z)
      (xor (p u) (p (origin m))) (xor (p v) (p (origin m)))
      (xor (p w) (p (origin m))) i := by
  unfold IsAffineMap at hp
  fin_cases i <;> dsimp [cubeWords] <;> simp only [hp]

/-- The eight-term multiplicative ratio is preserved under an affine Boolean
pullback, with no injectivity or nonzero assumption. -/
theorem thirdRatio_affineMap (f : Signature AlgebraicComplex n)
    (p : Word m → Word n) (hp : IsAffineMap p) (z u v w : Word m) :
    thirdRatio (fun x => f (p x)) z u v w = thirdRatio f (p z)
      (xor (p u) (p (origin m))) (xor (p v) (p (origin m)))
      (xor (p w) (p (origin m))) := by
  unfold IsAffineMap at hp
  simp only [thirdRatio, hp]

/-- A ternary-closed support and trivial third ratios on every fully supported
cube reconstruct a genuine finite affine system and an even-mixed quadratic
phase. The zero signature and all arities are included. -/
theorem affine_of_support_ternary_of_supported_cube
    (f : Signature AlgebraicComplex n)
    (ht : ∀ x y z : Word n, f x ≠ 0 → f y ≠ 0 → f z ≠ 0 →
      f (xor (xor x y) z) ≠ 0)
    (hc : ∀ z u v w : Word n, (∀ i, f (cubeWords z u v w i) ≠ 0) →
      thirdRatio f z u v w = 1) : Affine f := by
  classical
  by_cases hf : f = 0
  · exact Or.inl hf
  have hex : ∃ a, f a ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  obtain ⟨a, ha⟩ := hex
  obtain ⟨S, p, hp, hpn, hpf, hS⟩ := exists_support_retraction f a ha ht
  have hg : Affine (fun x => f (p x)) := by
    apply affine_of_thirdTrivial hpn
    intro z u v w
    rw [thirdRatio_affineMap f p hp]
    apply hc
    intro i
    rw [← affineMap_cubeWords p hp z u v w i]
    exact hpn _
  convert hg.restrict S using 1
  funext x
  by_cases hx : f x ≠ 0
  · simp only [ite_eq_left ((hS x).mpr hx), hpf x hx]
  · simp only [ite_eq_right (mt (hS x).mp hx)]
    exact not_ne_iff.mp hx

/-- The source affine class is characterized by closure of the actual support
and phase cancellation on supported cubes. -/
theorem affine_iff_support_ternary_and_supported_cube
    (f : Signature AlgebraicComplex n) : Affine f ↔
    (∀ x y z : Word n, f x ≠ 0 → f y ≠ 0 → f z ≠ 0 →
      f (xor (xor x y) z) ≠ 0) ∧
    (∀ z u v w : Word n, (∀ i, f (cubeWords z u v w i) ≠ 0) →
      thirdRatio f z u v w = 1) := by
  constructor
  · intro hf
    exact ⟨affine_support_ternary f hf, affine_supported_cube f hf⟩
  · rintro ⟨ht, hc⟩
    exact affine_of_support_ternary_of_supported_cube f ht hc

end
end Holant.ReedMuller.AffinePatching
