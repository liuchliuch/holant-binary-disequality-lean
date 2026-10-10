import Holant.Proofs.Hardness.EOQuaternarySparseFourStageAccess
import Holant.Proofs.Hardness.ComplexSelfdualData

/-! The selected cancellation-free two-copy tensor is generated in the
original coefficient field; the original oracle and its answer codec remain exact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseFourData
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature fieldSignature_eq_zero presentation targetEncoding targetValue)
end O
namespace N
export EOQuaternarySparseFourLocal (mask index Applicable output output_eo output_five)
end N
namespace F
export GeneratedSignatureField (ambient algebraic source)
end F
namespace V
export RealDenseSignTwistStageAccess (value)
end V
set_option backward.isDefEq.respectTransparency false
variable (M : Signature ℂ 4)
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'

theorem field_mask : N.mask (O.fieldSignature M)=N.mask M := by
  classical
  funext i
  simp only [N.mask,FiveSupportEOOrdering.middleCoeff,ne_eq,O.fieldSignature_eq_zero]

theorem field_index : N.index (O.fieldSignature M)=N.index M := by
  unfold N.index
  rw [field_mask]

theorem field_applicable (hs : N.Applicable M) : N.Applicable (O.fieldSignature M) := by
  unfold N.Applicable
  rw [field_mask]
  exact hs

def generated : Signature (O.field M) 4 := N.output (O.fieldSignature M) (N.index (O.fieldSignature M))
def output : Signature ℂ 4 := F.ambient M (generated M)

theorem output_eq : output M=N.output M (N.index M) := by
  unfold output generated
  rw [field_index]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp only [F.ambient,N.output,EOQuaternarySparseFourLocal.oriented,
    Tensor.reindex_apply,entries,table,h0,h1,h2,h3]
  all_goals rfl

theorem output_eo : DenseEOUnitLocal.EOSupport (output M) := by
  rw [output_eq]
  exact N.output_eo M _

theorem output_five (hs : N.Applicable M) : FiveSupportEOOrdering.ExactlyFive (output M) := by
  rw [output_eq]
  exact N.output_five M hs

variable (halg : ∀x,IsAlgebraic ℚ (M x)) (he : DenseEOUnitLocal.EOSupport M) (hs : N.Applicable M)

def stageSource : LengthControlledOracleReduction O.targetEncoding (O.presentation M halg).encoding
    O.targetEncoding (O.presentation M halg).encoding (V.value (generated M)) (O.targetValue M halg) := by
  have r := EOQuaternarySparseFourStageAccess.source (O.presentation M halg)
    (O.fieldSignature M) (DenseEOPairedSource.field_eo M he) (field_applicable M hs)
  have ht : V.value (O.fieldSignature M)=O.targetValue M halg :=
    funext (ComplexSelfdualData.target_value M halg)
  rw [ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseFourData
