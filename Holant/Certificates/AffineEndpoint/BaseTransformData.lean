import Holant.Certificates.AffineEndpoint.BaseTensorData
import Holant.Certificates.AffineEndpoint.FastTransformData
namespace Holant.Certificates.AffineEndpoint
open IntegerValues
 def baseIntegerTerm (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) (x y : Fin 16) : Coeff :=
  if (fastSupportMask s).testBit y.val then rotate (baseTensor b x y) (fastResidue s c y) else zero
 def baseIntegerOutput (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) (x : Fin 16) : Coeff :=
  IntegerValues.sum (List.ofFn (baseIntegerTerm s c b x))
end Holant.Certificates.AffineEndpoint
