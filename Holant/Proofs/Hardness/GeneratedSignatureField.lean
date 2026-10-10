import Holant.Proofs.Hardness.RealDenseExceptionalOriginalData
import Holant.Proofs.Hardness.RealDenseSelfdualStageAccess
import Holant.Proofs.Algorithms.FieldTransport

/-! A generated signature can have a strictly smaller coefficient field than
the original input. This adapter derives the actual subfield inclusion and
uses a rational-matrix answer retraction. The graph query is literally the
identity; neither the fields nor their independently chosen codecs are equated. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneratedSignatureField
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose Holant.LocalDrafts.MainChain
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (coefficient coefficient_algebraic field fieldSignature presentation tables
   TargetInput targetEncoding targetValue target_value_exact)
end O
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels tables evaluate)
end V
set_option backward.isDefEq.respectTransparency false
variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (M x))
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
variable (N : Signature (O.field M) 4)

def ambient : Signature L 4 := fun x=>(N x : L)
local instance generatedAlgebra : Algebra ℚ (O.field (ambient M N)) :=
  (O.field (ambient M N)).algebra'

include halg in
theorem algebraic : ∀x,IsAlgebraic ℚ (ambient M N x) := by
  letI := familyField_finiteDimensional (O.coefficient M) (O.coefficient_algebraic M halg)
  intro x
  exact (Algebra.IsAlgebraic.isAlgebraic (R:=ℚ) (N x)).algHom (O.field M).val

theorem field_le : O.field (ambient M N)≤O.field M := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i,rfl⟩
  cases i with
  | inl i => exact (N i.2).property
  | inr i =>
      rcases i with ⟨i,u,v⟩
      cases u <;> cases v <;> first | exact (O.field M).zero_mem | exact (O.field M).one_mem

def embedding : O.field (ambient M N)→ₐ[ℚ] O.field M :=
  IntermediateField.inclusion (field_le M N)

theorem embedding_value (x : O.field (ambient M N)) :
    (embedding M N x : L)=x := IntermediateField.coe_inclusion (field_le M N) x

theorem value_exact (r : O.TargetInput) :
    V.value N r=embedding M N (O.targetValue (ambient M N) (algebraic M halg N) r) := by
  apply Subtype.ext
  rw [embedding_value,O.target_value_exact]
  change ((O.field M).subtype
    ((r.val.realize r.property (V.signatures N) V.kernels).denote Fin.elim0))=_
  rw [←Network.denote_map (O.field M).subtype]
  apply congrFun (Network.denote_congr (r.val.shape r.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x; rfl
  · intro e x y; cases x <;> cases y <;> rfl

def answer := (embedding M N).toLinearMap.leftInverse

def answerComputes : Computes (O.presentation M halg).encoding
    (O.presentation (ambient M N) (algebraic M halg N)).encoding (answer M N) :=
  FieldCodec.retractComputes (O.presentation (ambient M N) (algebraic M halg N))
    (O.presentation M halg) (embedding M N)

/-- Actual one-query answer recoding to the original pre-normalization field. -/
def source : LengthControlledOracleReduction O.targetEncoding
    (O.presentation (ambient M N) (algebraic M halg N)).encoding
    O.targetEncoding (O.presentation M halg).encoding
    (O.targetValue (ambient M N) (algebraic M halg N)) (V.value N) := by
  have r := FieldTransport.fromOriginal
    (O.presentation (ambient M N) (algebraic M halg N)) (O.presentation M halg)
    (embedding M N) O.targetEncoding (O.targetValue (ambient M N) (algebraic M halg N))
    ((O.tables (ambient M N) (algebraic M halg N)).outputBound
      (O.presentation (ambient M N) (algebraic M halg N)))
  have hv : (fun r=>embedding M N (O.targetValue (ambient M N) (algebraic M halg N) r))=V.value N :=
    funext fun r=>(value_exact M halg N r).symm
  rw [hv] at r
  exact r

theorem answer_exact (r : O.TargetInput) :
    answer M N (V.value N r)=O.targetValue (ambient M N) (algebraic M halg N) r := by
  rw [value_exact M halg N]
  exact FieldCodec.retract_embedding (embedding M N) _

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneratedSignatureField
