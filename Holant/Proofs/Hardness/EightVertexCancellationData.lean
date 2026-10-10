import Holant.Proofs.Hardness.EightVertexCancellationStageAccess
import Holant.Proofs.Hardness.ComplexSelfdualData

/-! The generated cancellation tensor lies in the original coefficient field.
The ambient singleton source is connected through a genuine field retraction,
then through the exact two-copy original-label substitution programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCancellationData
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature fieldSignature_eq_zero presentation TargetInput targetEncoding targetValue)
end O
namespace N
export EightVertexCancellationLocal (Applicable output output_eo output_middle_or_five)
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

def generated : Signature (O.field M) 4 := N.output (O.fieldSignature M)
def output : Signature ℂ 4 := F.ambient M (generated M)

theorem output_eq : output M=N.output M := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp only [output,generated,F.ambient,N.output,entries,table,chainEntries,h0,h1,h2,h3]
  all_goals rfl

theorem output_eo (h : N.Applicable M) : DenseEOUnitLocal.EOSupport (output M) := by
  rw [output_eq]
  exact N.output_eo M h.cancel

theorem output_middle_or_five (h : N.Applicable M) :
    DenseEOUnitLocal.NonzeroMiddle (output M) ∨ FiveSupportEOOrdering.ExactlyFive (output M) := by
  rw [output_eq]
  exact N.output_middle_or_five M h

theorem field_even (he : EvenSupport M) : EvenSupport (O.fieldSignature M) := by
  intro x hx
  exact (O.fieldSignature_eq_zero M x).mpr (he x hx)

variable (halg : ∀x,IsAlgebraic ℚ (M x)) (he : EvenSupport M)

def stageSource : LengthControlledOracleReduction O.targetEncoding (O.presentation M halg).encoding
    O.targetEncoding (O.presentation M halg).encoding (V.value (generated M)) (O.targetValue M halg) := by
  have r := EightVertexCancellationStageAccess.source (O.presentation M halg)
    (O.fieldSignature M) (field_even M he)
  have ht : V.value (O.fieldSignature M)=O.targetValue M halg :=
    funext (ComplexSelfdualData.target_value M halg)
  rw [ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCancellationData
