import Holant.Proofs.Reductions.FactorSaturation.WholeForest
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Proofs.Algorithms.FieldCodec


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FactorSaturation.WholeForest
open Holant.Tractable
open Holant.Complexity Computability BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant.Complexity.UniversalPairReduction.Surgery
variable {s : ℕ} (D : Roots s)

def includeInput (r : ExactSignatureTables.Input s 1 (A D)) :
    ExactSignatureTables.Input (s+count D) 1 (A D) :=
  ⟨r.val, by
    have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
    apply (RawGrouping.wellFormed_iff_members _ _ _ _).mpr
    exact ⟨fun row hm => ⟨by have := (hr.1 row hm).1; omega, (hr.1 row hm).2⟩,hr.2⟩⟩

def includeComputes : Computes (oracleEncoding D) (inputEncoding D) (includeInput D) :=
  recode (identityComputes (oracleEncoding D)) id (fun _ => rfl) (fun _ => rfl)

theorem include_value (r : ExactSignatureTables.Input s 1 (A D)) :
    sourceValue D (includeInput D r) =
      CommonField.embedding D.signature D.nonzero D.identity (originalValue D r) := by
  apply Subtype.ext
  change (sourceValue D (includeInput D r) : AlgebraicComplex) = (originalValue D r : AlgebraicComplex)
  rw [source_value_exact, original_value_exact, Choice.denote_eq_evaluate, Choice.denote_eq_evaluate]
  unfold Choice.evaluate
  apply Finset.sum_congr rfl
  intro c _
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro row hm
  have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  have hi := (hr.1 row hm).1
  have hj : row.1 < s+count D := by omega
  simp only [Choice.rowValue, Choice.table, dif_pos hi, dif_pos hj]
  rfl

def reverseControlled : LengthControlledOracleReduction
    (oracleEncoding D) (originalPresentation D).encoding (inputEncoding D) (presentation D).encoding
    (originalValue D) (sourceValue D) :=
  controlledOneQueryOfEq (includeComputes D)
    (FieldCodec.retractComputes (originalPresentation D) (presentation D)
      (CommonField.embedding D.signature D.nonzero D.identity))
    ((sourceTables D).outputBound (presentation D)) (originalValue D) (fun r => by
      change originalValue D r = (CommonField.embedding D.signature D.nonzero D.identity).toLinearMap.leftInverse (sourceValue D (includeInput D r))
      rw [include_value]
      exact (FieldCodec.retract_embedding (CommonField.embedding D.signature D.nonzero D.identity)
        (originalValue D r)).symm)

theorem equivalent :
    OracleReducible (inputEncoding D) (presentation D).encoding
      (oracleEncoding D) (originalPresentation D).encoding (sourceValue D) (originalValue D) ∧
    OracleReducible (oracleEncoding D) (originalPresentation D).encoding
      (inputEncoding D) (presentation D).encoding (originalValue D) (sourceValue D) :=
  ⟨⟨reduction D⟩,⟨(reverseControlled D).reduction⟩⟩

end Holant.LocalDrafts.Hardness.FactorSaturation.WholeForest
