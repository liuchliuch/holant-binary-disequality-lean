import Holant.Proofs.Hardness.ComplexNonselfdualFourStageAccess
import Holant.Proofs.Hardness.ComplexNonselfdualChoice
import Holant.Proofs.Hardness.ComplexSelfdualData

/-! Every dense EO tensor has a successful one of three literal four-copy
orders. All generated values remain in the ORIGINAL coefficient field. The
separate ambient field presentation is connected by GeneratedSignatureField. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualData
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature presentation TargetInput targetEncoding targetValue)
end O
namespace C
export ComplexNonselfdualFourCopy
  (output output_eo output_middle output_opposite isolated pairSum isolated_values pairSum_values)
end C
namespace F
export GeneratedSignatureField (ambient algebraic source)
end F
namespace V
export RealDenseSignTwistStageAccess (value)
end V
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K]

def choice (M : Signature K 4) : Fin 3 :=
  ComplexNonselfdualChoice.selectedIndex ((entries M).b*(entries M).y)
    ((entries M).c*(entries M).z) ((entries M).d*(entries M).w)

theorem selected_good [CharZero K] (M : Signature K 4) (hm : DenseEOUnitLocal.NonzeroMiddle M) :
    C.pairSum M (choice M)≠0 ∧
      C.isolated M (choice M)^2+C.pairSum M (choice M)^2≠0 := by
  rw [C.isolated_values,C.pairSum_values]
  exact ComplexNonselfdualChoice.selected_good _ _ _
    (mul_ne_zero hm.1 hm.2.2.2.2.2) (mul_ne_zero hm.2.1 hm.2.2.2.2.1)
    (mul_ne_zero hm.2.2.1 hm.2.2.2.1)

theorem selected_applicable [CharZero K] (M : Signature K 4)
    (hm : DenseEOUnitLocal.NonzeroMiddle M) :
    ComplexSelfdualData.Applicable (C.output M (choice M)) := by
  have hh := selected_good M hm
  have hn := C.output_middle M hm (choice M) hh.1 hh.2
  have ho := C.output_opposite M (choice M)
  exact ⟨C.output_eo M (choice M),ho.1,ho.2.1,ho.2.2,hn.1,hn.2.2.1,hn.2.1⟩

variable (M : Signature ℂ 4)
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'

def generated : Signature (O.field M) 4 := C.output (O.fieldSignature M) (choice M)
def output : Signature ℂ 4 := F.ambient M (generated M)

theorem output_eq : output M=C.output M (choice M) := by
  unfold output generated F.ambient
  generalize choice M=i
  funext x
  fin_cases i <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp only [C.output,ComplexNonselfdualFourCopy.middle,
    ComplexNonselfdualFourCopy.oriented,ComplexNonselfdualFourCopy.order,
    ComplexNonselfdualCompression.compressed,Tensor.reindex_apply,entries,table,h0,h1,h2,h3]
  all_goals rfl

theorem output_applicable (hm : DenseEOUnitLocal.NonzeroMiddle M) :
    ComplexSelfdualData.Applicable (output M) := by
  rw [output_eq]
  exact selected_applicable M hm

variable (halg : ∀x,IsAlgebraic ℚ (M x)) (he : DenseEOUnitLocal.EOSupport M)

def stageSource : LengthControlledOracleReduction O.targetEncoding (O.presentation M halg).encoding
    O.targetEncoding (O.presentation M halg).encoding (V.value (generated M)) (O.targetValue M halg) := by
  have r := ComplexNonselfdualFourStageAccess.source (O.presentation M halg)
    (O.fieldSignature M) (choice M) (DenseEOPairedSource.field_eo M he)
  have ht : V.value (O.fieldSignature M)=O.targetValue M halg :=
    funext (ComplexSelfdualData.target_value M halg)
  rw [ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualData
