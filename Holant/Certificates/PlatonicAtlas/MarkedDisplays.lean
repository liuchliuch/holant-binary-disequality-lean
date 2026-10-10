import Holant.Certificates.PlatonicAtlas.Spanning
import Holant.Certificates.RainbowOrbit.SourceInterface

/-! Literal A.19 O-prime orientation factors. The coefficient similarity is
analytic; actual physical generators remain the separately verified resources. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
open Holant.Certificates.OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def primeOrientationScale : ℂ := embed (coeff 0 2 0 (-2))
 def primeOrientationInverseScale : ℂ := embed (coeff 0 (1/8) 0 (1/8))

 theorem primeOrientationScale_nonzero : primeOrientationScale≠0 :=
  embed_ne_zero (by decide +kernel)
 theorem primeOrientationInverseScale_nonzero : primeOrientationInverseScale≠0 :=
  embed_ne_zero (by decide +kernel)
 theorem primeOrientation_scales : primeOrientationScale*primeOrientationInverseScale=1 := by
  have h : coeff 0 2 0 (-2)*coeff 0 (1/8) 0 (1/8)=(1 : Scalar) := by decide +kernel
  exact (embed_mul _ _).symm.trans ((congrArg embed h).trans embed_one)

 theorem prime_markS : markS 1=primeOrientationScale • physicalX := by
  have h : sMatrix 1=ms (coeff 0 2 0 (-2)) flip := by decide +kernel
  change complexMatrix (conjugator 1)*(complexMatrix (conjugator 1)).transpose=_
  rw [←complexMatrix_mt,←complexMatrix_mm]
  change complexMatrix (sMatrix 1)=_
  rw [h,complexMatrix_ms,complexMatrix_flip]
  rfl

 theorem prime_markSinv : markSinv 1=primeOrientationInverseScale • physicalX := by
  have h : sInverse 1=ms (coeff 0 (1/8) 0 (1/8)) flip := by decide +kernel
  change (complexMatrix (conjugator 1))⁻¹.transpose*(complexMatrix (conjugator 1))⁻¹=_
  rw [←complexMatrix_inverseConjugator,←complexMatrix_mt,←complexMatrix_mm]
  change complexMatrix (sInverse 1)=_
  rw [h,complexMatrix_ms,complexMatrix_flip]
  rfl

 theorem prime_transport_P0 (U V : BinaryMatrix) :
    act (markLegs 1) (P0 U V)=P0 (complexTheta 1 U) (complexTheta 1 V) := mark_P0 1 U V

 theorem prime_transport_P1 (U V : BinaryMatrix) :
    Proportional (act (markLegs 1) (P1 U V))
      (P1 (complexTheta 1 (U*physicalX)) (complexTheta 1 (physicalX*V))) := by
  rw [mark_P1,prime_markS,prime_markSinv,Matrix.mul_smul,Matrix.smul_mul,
    complexTheta_smul,complexTheta_smul]
  exact matching_proportional 1 ⟨_,primeOrientationInverseScale_nonzero,rfl⟩
    ⟨_,primeOrientationScale_nonzero,rfl⟩

 theorem prime_transport_P2 (U V : BinaryMatrix) :
    Proportional (act (markLegs 1) (P2 U V))
      (P2 (complexTheta 1 U) (complexTheta 1 (physicalX*V*physicalX))) := by
  rw [mark_P2,prime_markS,prime_markSinv,Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul,primeOrientation_scales,one_smul]
  exact Proportional.refl _

 theorem marked_sourceAxes_actual (f : Form) (i : Fin 4) :
    Direction f (thetaEquiv f (sourceAxes i)) :=
  (direction_iff_source_conjugate f _).mpr ⟨sourceAxes i,sourceAxes_actual .octahedral i,rfl⟩

 theorem marked_sourceAxes_span (f : Form) :
    Submodule.span ℂ (Set.range (fun i => thetaEquiv f (sourceAxes i)))=⊤ :=
  transported_sourceAxes_span (thetaEquiv f)

 theorem external_generators_physical (F : FourTensor) (j : Fin 4) (i : Fin 12) :
    Gadget.Realizes (physicalFamily F {U | External.Direction U}) .disequality
      (act (physicalSingleLeg j (External.representative i)) F) :=
  singlePhysical_realizes_of_source_mem F {U | External.Direction U} j _ (external_physical_source_mem i).1

end
end Holant.Certificates.PlatonicAtlas
