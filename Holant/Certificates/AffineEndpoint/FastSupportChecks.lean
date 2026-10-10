import Holant.Certificates.AffineEndpoint.FastSupportFinite
namespace Holant.Certificates.AffineEndpoint
open Holant.Tractable.AffinePhase SupportCatalog
set_option backward.isDefEq.respectTransparency false
 theorem fastSupportCoordinates_eq (s : SupportIndex) (x : Fin 16) (j : Fin (supportDim s)) :
    (fastSupportCoordinates s x).val.testBit j.val=supportCoordinates s (codeWord x) j := by
  simp only [fastSupportCoordinates,fastSupportLinear_eq,fastSupportOrigin_eq]
  exact (fastLinearCoordinates_eq (supportLinearIndex s) (codeXor (supportRows s).originCode x) j).trans
    (by rw [codeWord_codeXor]; rfl)
 theorem fastSupportMask_mem (s : SupportIndex) (x : Fin 16) :
    (fastSupportMask s).testBit x.val=true ↔ x∈(supportRows s).codes := by
  rw [fastSupportMask_eq]
  exact support_mask_membership s x
end Holant.Certificates.AffineEndpoint
