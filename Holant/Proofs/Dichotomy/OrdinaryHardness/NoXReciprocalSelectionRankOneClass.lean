import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneOdd
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneMinimal

/-! The unsigned marginal keeps the exact Affine/alpha-Affine distinction.
Its possible factor two is proved nonzero and never discarded physically. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneClass
open Holant Holant.Tractable
namespace R
export NoXReciprocalSelectionRankOneOdd (resource value)
export NoXReciprocalSelectionRankOnePins (minor)
export NoXReciprocalSelectionRankOne (ports)
export NoXSeparateSignedProjection (signedCount)
end R
namespace M
export NoXReciprocalSelectionRankOneMarginal (scale scale_ne_zero)
end M
namespace O
export OrdinaryNegativeRankOneMinimal (unary unary_affine unary_alpha)
end O
namespace U
export OrdinaryNegativeXUniversalResource (AlphaResource AffineResource)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s n : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (pins : Fin (b j.val)→Bool ⊕ Fin n) (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (x y : Fin n→Bool)
variable (odd : Odd (R.signedCount (R.ports x y) 0 false))
variable (even : Even (R.signedCount (R.ports x y) 0 true))
variable (support : ∀z,R.minor H j pins z≠0→z=x ∨ z=y)
variable (hx : R.minor H j pins x≠0) (hy : R.minor H j pins y≠0)

def leftValue : AlgebraicComplex := (M.scale (K:=K) x y : AlgebraicComplex)*(R.minor H j pins x : AlgebraicComplex)
def rightValue : AlgebraicComplex := (M.scale (K:=K) x y : AlgebraicComplex)*(R.minor H j pins y : AlgebraicComplex)

include support in
theorem ambient_eq : (R.resource H j p0 p1 h0 h1 pins pure x y odd even).ambient H=
    O.unary (leftValue H j pins x y) (rightValue H j pins x y) := by
  funext z
  change ((R.resource H j p0 p1 h0 h1 pins pure x y odd even).signature H z : AlgebraicComplex)=_
  rw [R.value H j p0 p1 h0 h1 pins pure x y odd even support]
  cases hz:z 0 <;> simp [O.unary,leftValue,rightValue,hz]

include hx in
theorem left_nonzero : leftValue H j pins x y≠0 :=
  mul_ne_zero (fun h=>M.scale_ne_zero (K:=K) x y (Subtype.ext h)) (fun h=>hx (Subtype.ext h))
include hy in
theorem right_nonzero : rightValue H j pins x y≠0 :=
  mul_ne_zero (fun h=>M.scale_ne_zero (K:=K) x y (Subtype.ext h)) (fun h=>hy (Subtype.ext h))

include support hx hy in
theorem full (z : Fin 1→Bool) : (R.resource H j p0 p1 h0 h1 pins pure x y odd even).ambient H z≠0 := by
  rw [ambient_eq H j p0 p1 h0 h1 pins pure x y odd even support]
  cases hz:z 0
  · simpa [O.unary,hz] using left_nonzero H j pins x y hx
  · simpa [O.unary,hz] using right_nonzero H j pins x y hy

def alpha (phase : (R.minor H j pins x : AlgebraicComplex)^4= -(R.minor H j pins y : AlgebraicComplex)^4) :
    U.AlphaResource H .one where
  toOddResource := R.resource H j p0 p1 h0 h1 pins pure x y odd even
  alpha := by
    rw [ambient_eq H j p0 p1 h0 h1 pins pure x y odd even support]
    apply O.unary_alpha _ _ (left_nonzero H j pins x y hx)
    simp only [leftValue,rightValue,mul_pow,phase,mul_neg]
  full := full H j p0 p1 h0 h1 pins pure x y odd even support hx hy

def affine (phase : (R.minor H j pins x : AlgebraicComplex)^4=(R.minor H j pins y : AlgebraicComplex)^4) :
    U.AffineResource H .one where
  toOddResource := R.resource H j p0 p1 h0 h1 pins pure x y odd even
  affine := by
    rw [ambient_eq H j p0 p1 h0 h1 pins pure x y odd even support]
    apply O.unary_affine _ _ (left_nonzero H j pins x y hx)
    simp only [leftValue,rightValue,mul_pow,phase]
  full := full H j p0 p1 h0 h1 pins pure x y odd even support hx hy


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneClass
end
