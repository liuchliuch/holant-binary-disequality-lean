import Holant.Certificates.AffineEndpoint.IntegerTransformData
import Holant.Certificates.AffineEndpoint.CoreTensorChecks
import Holant.Certificates.AffineEndpoint.Cores
import Holant.Certificates.AffineEndpoint.ActionWordCodes

namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase SupportCatalog
open Holant.Certificates.OctahedralSeparator IntegerValues
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

 theorem code_mem_support (s : SupportIndex) (x : Fin 16) :
    codeWord x∈supportWords s ↔ x∈(supportRows s).codes := by
  simp [supportWords,decodeSupport,Finset.mem_map,codeWord_injective.eq_iff]

 theorem integerInput_eval (c : InputCode) (x : Fin 16) :
    IntegerCoefficient.eval (integerInput c x)=rawInputSignature c (codeWord x) := by
  simp only [integerInput,rawInputSignature,code_mem_support]
  split_ifs <;> simp [eval_zero,eval_rotate,eval_one,inputResidue]

 theorem integerInput_alg (c : InputCode) (x : Fin 16) :
    alg (integerInput c x)=inputSignature c (codeWord x) := by
  rw [alg,integerInput_eval,algebraicEmbed_rawInputSignature]

 theorem integerTerm_eval (c : InputCode) (k : Fin 18) (x y : Fin 16) :
    IntegerCoefficient.eval (integerTerm c k x y)=coreClearingScale k^4*
      ((∏j : Fin 4,coreRaw (numberedCore k) (codeWord x j) (codeWord y j))*rawInputSignature c (codeWord y)) := by
  simp only [integerTerm,rawInputSignature,code_mem_support]
  split_ifs <;> simp [eval_zero,eval_rotate,coreTensorRows_correct,inputResidue,mul_assoc]

 theorem integerOutput_eval (c : InputCode) (k : Fin 18) (x : Fin 16) :
    IntegerCoefficient.eval (integerOutput c k x)=coreClearingScale k^4*
      Signature.coordinateAction (fun _ => coreRaw (numberedCore k)) (rawInputSignature c) (codeWord x) := by
  rw [coordinateAction_wordCodes,integerOutput,eval_sum,List.map_ofFn,List.sum_ofFn]
  change (∑y : Fin 16,IntegerCoefficient.eval (integerTerm c k x y))=_
  simp_rw [integerTerm_eval]
  rw [←Finset.mul_sum]

 theorem algebraicTensor_action {n : ℕ} (L : Fin n → Bool → Bool → Scalar) (f : Signature Scalar n) :
    (fun x => algebraicEmbed (Signature.coordinateAction L f x))=
      Signature.coordinateAction (fun j => algebraicMatrix (L j)) (fun x => algebraicEmbed (f x)) := by
  funext x
  change algebraicEmbedding (∑y,(∏j,L j (x j) (y j))*f y)=_
  simp only [map_sum,map_mul,map_prod]
  rfl

 def clearedOutput (c : InputCode) (k : Fin 18) : Signature AlgebraicComplex 4 :=
  fun x => alg (integerOutput c k (wordCode x))

 theorem clearedOutput_eq (c : InputCode) (k : Fin 18) :
    clearedOutput c k=algebraicEmbed (coreClearingScale k)^4 •
      Signature.coordinateAction (fun _ => coreMatrix (numberedCore k)) (inputSignature c) := by
  have he := algebraicTensor_action (fun _ : Fin 4 => coreRaw (numberedCore k)) (rawInputSignature c)
  funext x
  simp only [clearedOutput,alg,integerOutput_eval,codeWord_wordCode,algebraicEmbed_mul,algebraicEmbed_pow,
    Pi.smul_apply,smul_eq_mul]
  congr 1
  simpa only [coreMatrix,algebraicEmbed_rawInputSignature] using congrFun he x

end
end Holant.Certificates.AffineEndpoint
