import Holant.Proofs.Hardness.ComplexFiveSupportStageAccess
import Holant.Proofs.Hardness.ComplexSelfdualData
import Holant.Proofs.Hardness.GeneralGeometricCapSource

/-! Each generated signature stays in the original input's coefficient field.
The independently generated field is joined only by the checked answer map. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexFiveSupportData
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature presentation TargetInput targetEncoding targetValue)
end O
namespace N
export ComplexFiveSupportLocal (output output_eo first last alpha beta gamma selected_first_middle
  selected_last_middle cancellation_cap)
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

def generated (k : Fin 3) : Signature (O.field M) 4 :=
  N.output (O.fieldSignature M) (FiveSupportEOOrdering.missingIndex M) k

def output (k : Fin 3) : Signature ℂ 4 := F.ambient M (generated M k)

theorem output_eq (k : Fin 3) : output M k=N.output M (FiveSupportEOOrdering.missingIndex M) k := by
  funext x
  fin_cases k
  · rfl
  · cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
    all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',output,generated,F.ambient,N.output,N.first,ComplexFiveSupportLocal.oriented,
      ComplexNonselfdualCompression.compressed,Tensor.reindex_apply,entries,table,h0,h1,h2,h3]
    all_goals rfl
  · cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
    all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',output,generated,F.ambient,N.output,N.first,N.last,ComplexFiveSupportLocal.oriented,
      ComplexNonselfdualCompression.compressed,Tensor.reindex_apply,entries,table,h0,h1,h2,h3]
    all_goals rfl

variable (he : DenseEOUnitLocal.EOSupport M) (hm : FiveSupportEOOrdering.ExactlyFive M)

include he in
theorem output_eo (k : Fin 3) : DenseEOUnitLocal.EOSupport (output M k) := by
  rw [output_eq]
  exact N.output_eo M he _ k

include he hm in
theorem first_applicable (h : N.beta M^2+N.gamma M^2=0) :
    GeneralGeometricCapSource.Applicable (output M 1) := by
  rw [output_eq]
  exact ⟨N.output_eo M he _ 1,N.selected_first_middle M hm,N.cancellation_cap M hm h⟩

include hm in
theorem last_middle (h : N.beta M^2+N.gamma M^2≠0) :
    DenseEOUnitLocal.NonzeroMiddle (output M 2) := by
  rw [output_eq]
  exact N.selected_last_middle M hm h

variable (halg : ∀x,IsAlgebraic ℚ (M x))

def stageSource (k : Fin 3) : LengthControlledOracleReduction O.targetEncoding (O.presentation M halg).encoding
    O.targetEncoding (O.presentation M halg).encoding (V.value (generated M k)) (O.targetValue M halg) := by
  have r := ComplexFiveSupportStageAccess.source (O.presentation M halg)
    (O.fieldSignature M) (FiveSupportEOOrdering.missingIndex M) k (DenseEOPairedSource.field_eo M he)
  have ht : V.value (O.fieldSignature M)=O.targetValue M halg :=
    funext (ComplexSelfdualData.target_value M halg)
  rw [ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexFiveSupportData
