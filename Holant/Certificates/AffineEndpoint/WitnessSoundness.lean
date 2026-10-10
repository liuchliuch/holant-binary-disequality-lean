import Holant.Certificates.AffineEndpoint.CoefficientWitness
import Holant.Certificates.AffineEndpoint.IntegerTransform

/-! Every accepted integer witness proves the actual algebraic-complex normal
form of the original four-fold tensor action. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.OctahedralSeparator IntegerValues
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

 theorem clearedOutput_code (c : InputCode) (k : Fin 18) (x : Fin 16) :
    alg (integerOutput c k x)=clearedOutput c k (codeWord x) := by
  simp only [clearedOutput,wordCode_codeWord]

 theorem witnessCheck_sound (c : InputCode) (k : Fin 18) (w : Nat)
    (hw : WitnessCheck c k w) (hg : EndpointEven (clearedOutput c k)) :
    EndpointNormalForm (clearedOutput c k) := by
  exact coefficientWitness_sound (integerOutput c k) (fun r => integerInput (referenceInput r))
    (fun r x => integerInput_alg (referenceInput r) x) w hw hg

 theorem endpointEven_scale_iff (g : Signature AlgebraicComplex 4) (a : AlgebraicComplex) (ha : a≠0) :
    EndpointEven (a • g) ↔ EndpointEven g := by
  constructor
  · rintro ⟨h0,h1,ho⟩
    refine ⟨?_,?_,?_⟩
    · exact fun hz => h0 (by change a*g (fun _ => false)=0; rw [hz,mul_zero])
    · exact fun hz => h1 (by change a*g (fun _ => true)=0; rw [hz,mul_zero])
    · intro x hx
      exact (mul_eq_zero.mp (ho x hx)).resolve_left ha
  · rintro ⟨h0,h1,ho⟩
    exact ⟨mul_ne_zero ha h0,mul_ne_zero ha h1,fun x hx => by change a*g x=0; rw [ho x hx,mul_zero]⟩

 theorem witnessCheck_core_normal_form (c : InputCode) (k : Fin 18) (w : Nat)
    (hw : WitnessCheck c k w)
    (hg : EndpointEven (Signature.coordinateAction (fun _ => coreMatrix (numberedCore k)) (inputSignature c))) :
    EndpointNormalForm (Signature.coordinateAction (fun _ => coreMatrix (numberedCore k)) (inputSignature c)) := by
  have ha : algebraicEmbed (coreClearingScale k)^4≠0 :=
    pow_ne_zero 4 (algebraicEmbed_ne_zero (coreClearingScale_ne_zero k))
  have hg' : EndpointEven (clearedOutput c k) := by
    rw [clearedOutput_eq,endpointEven_scale_iff _ _ ha]
    exact hg
  have h := witnessCheck_sound c k w hw hg'
  rw [clearedOutput_eq] at h
  exact (endpointNormalForm_scale_iff _ _ ha).mp h

end
end Holant.Certificates.AffineEndpoint
