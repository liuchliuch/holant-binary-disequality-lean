import Holant.Certificates.AffineEndpoint.FastTransformData
import Holant.Certificates.AffineEndpoint.FastSupportChecks
import Holant.Certificates.AffineEndpoint.FastPhaseBridge
import Holant.Certificates.AffineEndpoint.FastWitnessChecker

/-! Equality of the optimized digit evaluator and the actual original ordered
integer tensor sum, for every intrinsic phase code. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase SupportCatalog
open Holant.Certificates.OctahedralSeparator IntegerValues
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem fastResidue_eq (c : InputCode) (x : Fin 16) :
    fastResidue c.1 c.2.val x=inputResidue c x := by
  apply Fin.ext
  change DigitPhaseRuntime.exponent (fastSupportDimension c.1) c.2.val (fastSupportCoordinates c.1 x).val=_
  rw [fastSupportDimension_eq]
  exact (fastPhaseExponent_correct (supportDim c.1) (supportDim_le_four c.1) c.2
    (fastSupportCoordinates c.1 x)).symm.trans
    (congrArg (fun y => ((phaseQuadratic (phaseDecode (supportDim c.1) c.2)).eval y).val)
      (funext (fastSupportCoordinates_eq c.1 x)))

 theorem fastIntegerInput_eq (c : InputCode) (x : Fin 16) :
    fastIntegerInput c.1 c.2.val x=integerInput c x := by
  simp only [fastIntegerInput,integerInput,fastSupportMask_mem,fastResidue_eq]

 theorem fastIntegerTerm_eq (c : InputCode) (k : Fin 18) (x y : Fin 16) :
    fastIntegerTerm c.1 c.2.val k x y=integerTerm c k x y := by
  simp only [fastIntegerTerm,integerTerm,fastSupportMask_mem,fastResidue_eq]

 theorem fastIntegerOutput_eq (c : InputCode) (k : Fin 18) (x : Fin 16) :
    fastIntegerOutput c.1 c.2.val k x=integerOutput c k x := by
  unfold fastIntegerOutput integerOutput
  congr 1
  apply congrArg List.ofFn
  funext y
  exact fastIntegerTerm_eq c k x y

 theorem fastWitnessCheck_iff (c : InputCode) (k : Fin 18) (w : Nat) :
    FastWitnessCheck c.1 c.2.val k w ↔ WitnessCheck c k w := by
  simp only [FastWitnessCheck,WitnessCheck,fastIntegerOutput_eq,fastIntegerInput_eq]

end Holant.Certificates.AffineEndpoint
