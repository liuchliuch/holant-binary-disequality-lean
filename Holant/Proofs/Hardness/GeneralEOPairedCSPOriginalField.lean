import Holant.Proofs.Hardness.GeneralEOPairedCSPClosed
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget
import Holant.Proofs.Algorithms.FieldCodec

/-! A real rational-linear adapter from the literal original-family answer
codec to the compiler's working coefficient presentation. Presentations are
not identified, even though the additional X coefficients are rational. The
query word and the entire original graph remain unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPOriginalField
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables originalValue target_exact)
end O
namespace W
export GeneralEOPairedCSPField (field signatures signature_value covers)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
local instance workingAlgebra : Algebra ℚ (W.field G) := (W.field G).algebra'

abbrev presentation := GeneralEOPairedCSPField.presentation G (GeneralEOPairedCSPClosed.algebraic G)
abbrev targetValue := GeneralEOPairedCSPField.targetValue G (GeneralEOPairedCSPClosed.algebraic G)

theorem field_le : O.originalField G≤W.field G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  exact coefficient_mem_familyField (GeneralEOPairedCSPField.coefficient G) (.inl ⟨i,x⟩)

def embedding : O.originalField G→ₐ[ℚ]W.field G := IntermediateField.inclusion (field_le G)

@[simp] theorem embedding_value (x : O.originalField G) :
    (embedding G x : AlgebraicComplex)=x := IntermediateField.coe_inclusion (field_le G) x

/-- The actual finite rational-matrix programme changes answer coordinates;
no equality of basis choices or encoded field words is presumed. -/
def answerComputes : Computes (O.originalPresentation G).encoding (presentation G).encoding (embedding G) :=
  Holant.LocalDrafts.MainChain.FieldCodec.computes (O.originalPresentation G) (presentation G)
    (embedding G).toLinearMap

theorem target_value (q : GeneralEOPairedCSPRecords.TargetInput (s:=s) (arity:=arity)) :
    targetValue G q=embedding G (O.originalValue G q) := by
  apply Subtype.ext
  rw [GeneralEOPairedCSPField.target_value_exact,embedding_value,O.target_exact]

/-- Any working-field original-graph oracle call can be replaced by the
literal pre-existing original coefficient codec, via a real one-query adapter. -/
def targetTransport : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 arity) (presentation G).encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
    (targetValue G) (O.originalValue G) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
    (identityComputes (RawClosedNetwork.validatedEncoding s 1 arity)) (answerComputes G)
    ((O.originalTables G).outputBound (O.originalPresentation G))
    (targetValue G) (target_value G)

/-- Convert the original oracle's answer, then perform the actual unused-bit
correction in the working field. Empty answer batches map to zero. -/
def post : Computes
    (OracleBatch.contextEncoding (O.originalPresentation G).encoding GeneralEOPairedCSPRaw.unary)
    (presentation G).encoding
    (fun a : List (O.originalField G)×ℕ=>embedding G (a.1.getD 0 0)*(2:W.field G)^a.2) := by
  let power : Computes (pairEncoding (presentation G).encoding GeneralEOPairedCSPRaw.unary)
      (presentation G).encoding (fun a : W.field G×ℕ=>a.1*(2:W.field G)^a.2) :=
    congrComputes (ScalarPower.multiplyPower (presentation G)
      ((presentation G).decode.symm (2:W.field G))) (fun _=>by simp)
  let answer := ((Wiring.firstComputes (framedListEncoding (O.originalPresentation G).encoding)
    GeneralEOPairedCSPRaw.unary).andThen
      (FixedGadgetSubstitution.Compiler.getDComputes (O.originalPresentation G).encoding 0 0)).andThen
        (answerComputes G)
  exact (pairComputes answer
    (Wiring.secondComputes (framedListEncoding (O.originalPresentation G).encoding)
      GeneralEOPairedCSPRaw.unary)).andThen power

theorem answer_primitive_bound (x : O.originalField G) :
    primitiveCost (answerComputes G).machine ((answerComputes G).outputs x).steps
      (some (initList (answerComputes G).machine.computer ((O.originalPresentation G).encoding.encode x)))≤
      (primitivePolynomial (answerComputes G)).eval ((O.originalPresentation G).encoding.encode x).length :=
  computes_primitive_cost (answerComputes G) x

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPOriginalField
