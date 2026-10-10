import Holant.Certificates.OctahedralSeparator.Field
import Holant.Tractable.AffinePhase.Roots

/-! The exact Q(sqrt2,i) checker lands in the actual algebraic-complex field,
not merely in complex numbers. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable
open Holant.Certificates.OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def algebraicEmbed (z : Scalar) : AlgebraicComplex :=
  (z.re.re : AlgebraicComplex)+(z.im.re : AlgebraicComplex)*sqrtTwo+
    ((z.re.im : AlgebraicComplex)+(z.im.im : AlgebraicComplex)*sqrtTwo)*imaginaryUnit

 theorem coe_algebraicEmbed (z : Scalar) : (algebraicEmbed z : ℂ)=embed z := by
  have hz : z=coeff z.re.re z.im.re z.re.im z.im.im := by cases z; rfl
  conv_rhs => rw [hz]
  rw [embed_coeff]
  rfl

 theorem algebraicEmbed_injective : Function.Injective algebraicEmbed := by
  intro z w h
  apply embed_injective
  simpa only [coe_algebraicEmbed] using congrArg (fun x : AlgebraicComplex => (x : ℂ)) h

 @[simp] theorem algebraicEmbed_zero : algebraicEmbed 0=0 := by
  apply Subtype.ext
  simp [coe_algebraicEmbed,embed_zero]
 @[simp] theorem algebraicEmbed_one : algebraicEmbed 1=1 := by
  apply Subtype.ext
  simp [coe_algebraicEmbed,embed_one]
 @[simp] theorem algebraicEmbed_add (z w : Scalar) : algebraicEmbed (z+w)=algebraicEmbed z+algebraicEmbed w := by
  apply Subtype.ext
  simp [coe_algebraicEmbed,embed_add]
 @[simp] theorem algebraicEmbed_mul (z w : Scalar) : algebraicEmbed (z*w)=algebraicEmbed z*algebraicEmbed w := by
  apply Subtype.ext
  simp [coe_algebraicEmbed,embed_mul]

 def algebraicEmbedding : Scalar →+* AlgebraicComplex where
  toFun := algebraicEmbed
  map_zero' := algebraicEmbed_zero
  map_one' := algebraicEmbed_one
  map_add' := algebraicEmbed_add
  map_mul' := algebraicEmbed_mul

 @[simp] theorem algebraicEmbed_neg (z : Scalar) : algebraicEmbed (-z)= -algebraicEmbed z := map_neg algebraicEmbedding z
 @[simp] theorem algebraicEmbed_sub (z w : Scalar) : algebraicEmbed (z-w)=algebraicEmbed z-algebraicEmbed w := map_sub algebraicEmbedding z w
 @[simp] theorem algebraicEmbed_pow (z : Scalar) (n : ℕ) : algebraicEmbed (z^n)=(algebraicEmbed z)^n := map_pow algebraicEmbedding z n
 @[simp] theorem algebraicEmbed_inv (z : Scalar) : algebraicEmbed z⁻¹=(algebraicEmbed z)⁻¹ := map_inv₀ algebraicEmbedding z
 @[simp] theorem algebraicEmbed_div (z w : Scalar) : algebraicEmbed (z/w)=algebraicEmbed z/algebraicEmbed w := map_div₀ algebraicEmbedding z w

 theorem algebraicEmbed_ne_zero {z : Scalar} (hz : z≠0) : algebraicEmbed z≠0 := by
  intro h
  exact hz (algebraicEmbed_injective (h.trans algebraicEmbed_zero.symm))

 @[simp] theorem algebraicEmbed_root : algebraicEmbed root=sqrtTwo := by
  simp [algebraicEmbed,root,coeff]
 @[simp] theorem algebraicEmbed_imag : algebraicEmbed imag=imaginaryUnit := by
  simp [algebraicEmbed,imag,coeff]

 def rawZetaEight : Scalar := (1+imag)/root

 @[simp] theorem algebraicEmbed_zeta : algebraicEmbed rawZetaEight=zetaEight := by
  simp [rawZetaEight,zetaEight]

 def algebraicMatrix (U : Bool → Bool → Scalar) : Matrix Bool Bool AlgebraicComplex := fun a b => algebraicEmbed (U a b)

 theorem algebraicMatrix_injective : Function.Injective algebraicMatrix := by
  intro U V h
  funext a b
  exact algebraicEmbed_injective (congrFun (congrFun h a) b)

end
end Holant.Certificates.AffineEndpoint
