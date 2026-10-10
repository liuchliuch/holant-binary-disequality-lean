import Holant.Certificates.AffineEndpoint.InputModel
import Holant.Certificates.AffineEndpoint.IntegerValues
import Holant.Certificates.AffineEndpoint.CoreTensorData

/-! Direct finite sums of the original ordered four-fold core action. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase SupportCatalog
open Holant.Certificates.OctahedralSeparator
open IntegerValues
set_option maxRecDepth 100000

 def inputResidue (c : InputCode) (x : Fin 16) : Fin 4 :=
  ⟨((phaseQuadratic (phaseDecode (supportDim c.1) c.2)).eval
    (supportCoordinates c.1 (codeWord x))).val,ZMod.val_lt _⟩

 def integerInput (c : InputCode) (x : Fin 16) : Coeff :=
  if x∈(supportRows c.1).codes then rotate one (inputResidue c x) else zero

 def integerTerm (c : InputCode) (k : Fin 18) (x y : Fin 16) : Coeff :=
  if y∈(supportRows c.1).codes then rotate (coreTensorRows k x y) (inputResidue c y) else zero

 def integerOutput (c : InputCode) (k : Fin 18) (x : Fin 16) : Coeff :=
  IntegerValues.sum (List.ofFn (integerTerm c k x))

end Holant.Certificates.AffineEndpoint
