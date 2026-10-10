import Holant.ReedMuller.AffinePatching.CommonHyperplane
import Holant.ReedMuller.AffinePatching.AffineSupport

/-! Faithful Boolean/F2 transport for actual affine coordinate maps. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

 theorem vector_xor (x y : Word n) : vectorWord (AffinePhase.xor x y)=vectorWord x+vectorWord y := by
  funext i
  exact bitValue_xor (x i) (y i)

@[simp] theorem vector_origin : vectorWord (origin n)=(0:BinaryVector n) := by
  funext i;rfl

 theorem vector_injective : Function.Injective (vectorWord (n:=n)) := by
  intro x y h
  have H := congrArg wordVector h
  simpa using H

 theorem word_add (x y : BinaryVector n) : wordVector (x+y)=AffinePhase.xor (wordVector x) (wordVector y) := by
  apply vector_injective
  simp only [vector_word,vector_xor]

 theorem binaryDot_vector (x y : Word n) : binaryDot x y=dot (vectorWord x) (vectorWord y) := rfl

 def affineBoolean (a : BinaryVector n) (L : BinaryVector m →ₗ[ZMod 2] BinaryVector n) : Word m → Word n :=
  fun x => wordVector (a+L (vectorWord x))

 theorem affineBoolean_isAffine (a : BinaryVector n) (L : BinaryVector m →ₗ[ZMod 2] BinaryVector n) :
    IsAffineMap (affineBoolean a L) := by
  intro x y
  apply vector_injective
  simp only [affineBoolean,vector_word,vector_xor,vector_origin,map_add,map_zero,add_zero]
  funext i
  exact (show ∀ a b c : ZMod 2,a+(b+c)=(a+b)+((a+c)+a) from by decide) _ _ _

 theorem affineBoolean_subtract (a : BinaryVector n) (L : BinaryVector m →ₗ[ZMod 2] BinaryVector n)
    (x y : Word m) :
    affineBoolean a L (AffinePhase.xor x y)=
      AffinePhase.xor (affineBoolean a L x) (wordVector (L (vectorWord y))) := by
  apply vector_injective
  simp only [affineBoolean,vector_word,vector_xor,map_add]
  exact add_assoc _ _ _ |>.symm

end
end Holant.ReedMuller.AffinePatching
