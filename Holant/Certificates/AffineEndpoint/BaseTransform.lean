import Holant.Certificates.AffineEndpoint.BaseTensor
import Holant.Certificates.AffineEndpoint.BaseWitnessChecker
import Holant.Certificates.AffineEndpoint.FastTransform
import Holant.Certificates.AffineEndpoint.WitnessSoundness
namespace Holant.Certificates.AffineEndpoint
set_option backward.isDefEq.respectTransparency false

 theorem baseIntegerOutput_eq (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) (x : Fin 16) :
    baseIntegerOutput s c b x=fastIntegerOutput s c (baseCore b) x := by
  unfold baseIntegerOutput fastIntegerOutput
  congr 1
  apply congrArg List.ofFn
  funext y
  simp only [baseIntegerTerm,fastIntegerTerm,baseTensor_eq]

 theorem baseWitnessCheck_iff (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) (w : Nat) :
    BaseWitnessCheck s c b w ↔ FastWitnessCheck s c (baseCore b) w := by
  simp only [BaseWitnessCheck,FastWitnessCheck,baseIntegerOutput_eq]

 theorem baseWitnessCheck_sound (c : InputCode) (b : Bool) (w : Nat)
    (hw : BaseWitnessCheck c.1 c.2.val b w)
    (hg : Holant.EightVertex.ProductAnchor.EndpointEven (Holant.Signature.coordinateAction
      (fun _ => coreMatrix (numberedCore (baseCore b))) (inputSignature c))) :
    EndpointNormalForm (Holant.Signature.coordinateAction
      (fun _ => coreMatrix (numberedCore (baseCore b))) (inputSignature c)) :=
  witnessCheck_core_normal_form c (baseCore b) w
    ((fastWitnessCheck_iff c (baseCore b) w).mp ((baseWitnessCheck_iff _ _ _ _).mp hw)) hg

end Holant.Certificates.AffineEndpoint
