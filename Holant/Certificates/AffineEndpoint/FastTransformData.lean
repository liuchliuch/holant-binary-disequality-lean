import Holant.Certificates.AffineEndpoint.FastSupportData
import Holant.Certificates.AffineEndpoint.DigitPhaseRuntime
import Holant.Certificates.AffineEndpoint.IntegerTransformData

/-! Optimized integer evaluation candidates. The semantic equality to the
actual tensor action is established in FastTransform, after the digit bridge. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Certificates.OctahedralSeparator IntegerValues

 def fastResidue (s : SupportCatalog.SupportIndex) (c : Nat) (x : Fin 16) : Fin 4 :=
  ⟨DigitPhaseRuntime.exponent (fastSupportDimension s) c (fastSupportCoordinates s x).val,
    DigitPhaseRuntime.exponent_lt _ _ _⟩

 def fastIntegerInput (s : SupportCatalog.SupportIndex) (c : Nat) (x : Fin 16) : Coeff :=
  if (fastSupportMask s).testBit x.val then rotate one (fastResidue s c x) else zero

 def fastIntegerTerm (s : SupportCatalog.SupportIndex) (c : Nat) (k : Fin 18) (x y : Fin 16) : Coeff :=
  if (fastSupportMask s).testBit y.val then rotate (coreTensorRows k x y) (fastResidue s c y) else zero

 def fastIntegerOutput (s : SupportCatalog.SupportIndex) (c : Nat) (k : Fin 18) (x : Fin 16) : Coeff :=
  IntegerValues.sum (List.ofFn (fastIntegerTerm s c k x))

end Holant.Certificates.AffineEndpoint
