import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTargetCore
import Holant.Proofs.Reductions.GeneralExtraction.GeneralCommonField
import Holant.Proofs.Algorithms.TableFieldTransport


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
open Holant.Tractable
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open GeneralPowerExposure
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

variable (f : Signature AlgebraicComplex (arity s)) (P : PowerMacro G f)

theorem field_le : originalField G ≤ GeneralCommonField.field G f P := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i,rfl⟩
  exact coefficient_mem_familyField (GeneralCommonField.coefficient G f P) (.inl i)

def embedding : originalField G →ₐ[ℚ] GeneralCommonField.field G f P :=
  IntermediateField.inclusion (field_le G f P)

theorem mapped_tables :
    TableFieldTransport.mapTables (originalPresentation G) (GeneralCommonField.presentation G f P)
      (embedding G f P) (originalTables G) =
      GeneralFieldReduction.targetTables (GeneralCommonField.presentation G f P)
        (GeneralCommonField.original G f P) := by
  unfold TableFieldTransport.mapTables originalTables GeneralFieldReduction.targetTables
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables
  congr 1
  · funext i x
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · funext i a b
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    cases a <;> cases b <;> simp [Signature.disequality]

def targetTransport : LengthControlledOracleReduction
    (GeneralFieldReduction.queryEncoding (s:=s) (arity:=arity)) (GeneralCommonField.presentation G f P).encoding
    (GeneralFieldReduction.queryEncoding (s:=s) (arity:=arity)) (originalPresentation G).encoding
    (GeneralCommonField.targetValue G f P) (originalValue G) := by
  have h := TableFieldTransport.toOriginal (originalPresentation G) (GeneralCommonField.presentation G f P)
    (embedding G f P) (originalTables G)
  rw [mapped_tables G f P] at h
  exact h

/-- The full one-factor machine now uses the ORIGINAL coefficient codec
at its oracle end. This is real program composition, not an encoding claim. -/
def reduction : PolyTimeOracleReduction
    (GeneralFieldReduction.inputEncoding (s:=s) (arity:=arity)) (GeneralCommonField.presentation G f P).encoding
    (GeneralFieldReduction.queryEncoding (s:=s) (arity:=arity)) (originalPresentation G).encoding
    (GeneralCommonField.sourceValue G f P) (originalValue G) :=
  (GeneralCommonField.controlled G f P).compose (targetTransport G f P).reduction

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
