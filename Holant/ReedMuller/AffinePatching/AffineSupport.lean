import Holant.ReedMuller.AffinePatching.WalshTranslation

/-! Genuine affine support closure and phase identities on supported cubes.
No nowhere-zero premise is imposed outside the inspected cube. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 theorem affine_support_ternary (f : Signature AlgebraicComplex n) (hf : Affine f)
    (x y z : Word n) (hx : f x≠0) (hy : f y≠0) (hz : f z≠0) :
    f (AffinePhase.xor (AffinePhase.xor x y) z)≠0 := by
  rcases hf with rfl | ⟨c,hc,S,Q,rfl⟩
  · exact False.elim (hx rfl)
  have hm (t : Word n) (ht : affineFormula c S Q t≠0) : S.Holds t := by
    by_contra h
    exact ht (by simp [affineFormula,h])
  have hS : S.Holds (AffinePhase.xor (AffinePhase.xor x y) z) := by
    intro r
    change rowDot (S.matrix r) (AffinePhase.xor (AffinePhase.xor x y) z)=S.rhs r
    rw [rowDot_xor,rowDot_xor]
    have hx' : rowDot (S.matrix r) x=S.rhs r := hm x hx r
    have hy' : rowDot (S.matrix r) y=S.rhs r := hm y hy r
    have hz' : rowDot (S.matrix r) z=S.rhs r := hm z hz r
    rw [hx',hy',hz']
    have h : ∀ a : ZMod 2,a+a+a=a := by decide
    exact h _
  simp only [affineFormula,if_pos hS]
  exact mul_ne_zero hc (fourthRootPhase_ne_zero _)

def cubeWords (z u v w : Word n) : Fin 8 → Word n :=
  ![z,AffinePhase.xor z u,AffinePhase.xor z v,AffinePhase.xor z w,
    AffinePhase.xor (AffinePhase.xor z u) v,AffinePhase.xor (AffinePhase.xor z u) w,
    AffinePhase.xor (AffinePhase.xor z v) w,
    AffinePhase.xor (AffinePhase.xor (AffinePhase.xor z u) v) w]

 theorem affine_supported_cube (f : Signature AlgebraicComplex n) (hf : Affine f)
    (z u v w : Word n) (hn : ∀ i,f (cubeWords z u v w i)≠0) :
    thirdRatio f z u v w=1 := by
  rcases hf with rfl | ⟨c,hc,S,Q,rfl⟩
  · exact False.elim (hn 0 rfl)
  have hs : ∀ i,S.Holds (cubeWords z u v w i) := by
    intro i
    by_contra h
    exact hn i (by simp [affineFormula,h])
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  have h4 := hs 4
  have h5 := hs 5
  have h6 := hs 6
  have h7 := hs 7
  change S.Holds z at h0
  change S.Holds (AffinePhase.xor z u) at h1
  change S.Holds (AffinePhase.xor z v) at h2
  change S.Holds (AffinePhase.xor z w) at h3
  change S.Holds (AffinePhase.xor (AffinePhase.xor z u) v) at h4
  change S.Holds (AffinePhase.xor (AffinePhase.xor z u) w) at h5
  change S.Holds (AffinePhase.xor (AffinePhase.xor z v) w) at h6
  change S.Holds (AffinePhase.xor (AffinePhase.xor (AffinePhase.xor z u) v) w) at h7
  unfold thirdRatio
  apply (div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero (mul_ne_zero (hn 4) (hn 5)) (hn 6)) (hn 0))).mpr
  change affineFormula c S Q (AffinePhase.xor (AffinePhase.xor (AffinePhase.xor z u) v) w)*
    affineFormula c S Q (AffinePhase.xor z u)*affineFormula c S Q (AffinePhase.xor z v)*
    affineFormula c S Q (AffinePhase.xor z w)=
    affineFormula c S Q (AffinePhase.xor (AffinePhase.xor z u) v)*
    affineFormula c S Q (AffinePhase.xor (AffinePhase.xor z u) w)*
    affineFormula c S Q (AffinePhase.xor (AffinePhase.xor z v) w)*affineFormula c S Q z
  simp only [affineFormula,if_pos h0,if_pos h1,if_pos h2,if_pos h3,if_pos h4,if_pos h5,if_pos h6,if_pos h7]
  have H := quadratic_phase_cross Q z u v w
  linear_combination c^4*H

end
end Holant.ReedMuller.AffinePatching
