import Holant.ReedMuller.AffinePatching.BooleanLinear

/-! Three supported words fit in an actual accessible annihilating hyperplane,
so local affine supports force genuine global ternary affine closure. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 def HyperplaneAffine (F : Signature AlgebraicComplex n) : Prop :=
  ∀ v : BinaryVector n,Accessible v → Affine (hyperplaneMask (wordVector v) F)

 theorem global_support_ternary (hn : 6≤n) (F : Signature AlgebraicComplex n)
    (hF : HyperplaneAffine F) (x y z : Word n)
    (hx : F x≠0) (hy : F y≠0) (hz : F z≠0) :
    F (AffinePhase.xor (AffinePhase.xor x y) z)≠0 := by
  obtain ⟨v,hv,hw⟩ := exists_accessible_orthogonal (k:=3) hn ![vectorWord x,vectorWord y,vectorWord z]
  have hxv : binaryDot x (wordVector v)=0 := by
    rw [binaryDot_vector,vector_word,dot_comm]
    exact hw 0
  have hyv : binaryDot y (wordVector v)=0 := by
    rw [binaryDot_vector,vector_word,dot_comm]
    exact hw 1
  have hzv : binaryDot z (wordVector v)=0 := by
    rw [binaryDot_vector,vector_word,dot_comm]
    exact hw 2
  have hx' : hyperplaneMask (wordVector v) F x≠0 := by simpa [hyperplaneMask,hxv] using hx
  have hy' : hyperplaneMask (wordVector v) F y≠0 := by simpa [hyperplaneMask,hyv] using hy
  have hz' : hyperplaneMask (wordVector v) F z≠0 := by simpa [hyperplaneMask,hzv] using hz
  have H := affine_support_ternary _ (hF v hv) x y z hx' hy' hz'
  intro h
  exact H (by simp [hyperplaneMask,h])

end
end Holant.ReedMuller.AffinePatching
