import Holant.Certificates.AffineEndpoint.CoreAffine
import Holant.Certificates.AffineEndpoint.ScaledInputs
import Holant.Certificates.AffineEndpoint.OutputComplement

/-! Structural assembly of the literal eighteen cores from the two finite
base certificates. The final source theorem instantiates the coverage argument
with BaseCertificate.all_base_inputs. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem core_normal_form_of_base_coverage
    (hcovered : ∀b : Bool,∀c : InputCode,∃w,BaseWitnessCheck c.1 c.2.val b w)
    (k : CoreIndex) (f : Signature AlgebraicComplex 4) (hf : Affine f) (hn : f≠0)
    (hg : EndpointEven (coreAction k f)) : EndpointNormalForm (coreAction k f) := by
  rcases coreAction_affine_or_base k hf with ha|⟨b,j,c,he⟩
  · exact affine_endpoint_normal_form _ ha hg
  · have ht := phaseTwist_affine j hf
    have htn := phaseTwist_ne_zero j hn
    rw [he] at hg ⊢
    cases c
    · exact base_family_normal_form b (hcovered b) (phaseTwist j f) ht htn hg
    · apply (endpointNormalForm_complement_iff _).mpr
      exact base_family_normal_form b (hcovered b) (phaseTwist j f) ht htn
        ((endpointEven_complement_iff _).mp hg)

end
end Holant.Certificates.AffineEndpoint
