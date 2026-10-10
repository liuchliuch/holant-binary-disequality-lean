import Holant.Proofs.Reductions.FactorSaturation.Reverse


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FactorSaturation.OriginalCodec
open Holant.Tractable
open Holant.Algebraic Holant.Complexity Computability BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant.Complexity.UniversalPairReduction.Surgery
variable {s : ℕ}

def rootLookup (roots : Fin s → AnySignature AlgebraicComplex) (i : ℕ) : AnySignature AlgebraicComplex :=
  if hi : i < s then roots ⟨i,hi⟩ else ⟨0,0⟩
def rootArity (roots : Fin s → AnySignature AlgebraicComplex) (i : ℕ) := (rootLookup roots i).1
def rootTable (roots : Fin s → AnySignature AlgebraicComplex) (i : Fin s) :
    Signature AlgebraicComplex (rootArity roots i.val) := (rootLookup roots i.val).2

@[simp] theorem rootLookup_old (roots : Fin s → AnySignature AlgebraicComplex) (i : Fin s) :
    rootLookup roots i.val = roots i := by simp [rootLookup,i.isLt]

variable (D : WholeForest.Roots s)
abbrev encoding := RawClosedNetwork.validatedEncoding s 1 (rootArity D.signature)
abbrev field := GeneralOriginalTarget.originalField (rootTable D.signature)
abbrev presentation := GeneralOriginalTarget.originalPresentation (rootTable D.signature)
abbrev value := GeneralOriginalTarget.originalValue (rootTable D.signature)

theorem lookup_agrees (i : Fin s) :
    lookup D.signature D.nonzero i.val = rootLookup D.signature i.val := by simp
theorem arity_agrees (i : Fin s) : WholeForest.A D i.val = rootArity D.signature i.val :=
  congrArg Sigma.fst (lookup_agrees D i)

def query (r : ExactSignatureTables.Input s 1 (WholeForest.A D)) :
    ExactSignatureTables.Input s 1 (rootArity D.signature) :=
  ⟨r.val, by
    have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
    apply (RawGrouping.wellFormed_iff_members _ _ _ _).mpr
    refine ⟨?_,hr.2⟩
    intro row hm
    exact ⟨(hr.1 row hm).1, (hr.1 row hm).2.trans (arity_agrees D ⟨row.1,(hr.1 row hm).1⟩)⟩⟩

def back (r : ExactSignatureTables.Input s 1 (rootArity D.signature)) :
    ExactSignatureTables.Input s 1 (WholeForest.A D) :=
  ⟨r.val, by
    have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
    apply (RawGrouping.wellFormed_iff_members _ _ _ _).mpr
    refine ⟨?_,hr.2⟩
    intro row hm
    exact ⟨(hr.1 row hm).1, (hr.1 row hm).2.trans (arity_agrees D ⟨row.1,(hr.1 row hm).1⟩).symm⟩⟩

def queryComputes : Computes (WholeForest.oracleEncoding D) (encoding D) (query D) :=
  recode (identityComputes (WholeForest.oracleEncoding D)) id (fun _ => rfl) (fun _ => rfl)
def backComputes : Computes (encoding D) (WholeForest.oracleEncoding D) (back D) :=
  recode (identityComputes (encoding D)) id (fun _ => rfl) (fun _ => rfl)

theorem original_field_le : field D ≤ WholeForest.field D := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  have hc : ∀ y : Fin (lookup D.signature D.nonzero i.val).1 → Bool,
      (lookup D.signature D.nonzero i.val).2 y ∈ WholeForest.field D :=
    fun y => CommonField.vertex_covered D.signature D.nonzero D.identity
      ⟨i.val,by have := i.isLt; omega⟩ y
  rw [lookup_agrees D i] at hc
  exact hc x

def embedding : field D →ₐ[ℚ] WholeForest.field D := IntermediateField.inclusion (original_field_le D)

theorem ambient_value (r : ExactSignatureTables.Input s 1 (WholeForest.A D)) :
    (WholeForest.originalValue D r : AlgebraicComplex) = (value D (query D r) : AlgebraicComplex) := by
  rw [WholeForest.original_value_exact, GeneralOriginalTarget.target_exact,
    Choice.denote_eq_evaluate, Choice.denote_eq_evaluate]
  unfold Choice.evaluate
  apply Finset.sum_congr rfl
  intro c _
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro row hm
  have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  have hi := (hr.1 row hm).1
  unfold Choice.rowValue Choice.table
  simp only [dif_pos hi]
  exact congrArg (fun f : AnySignature AlgebraicComplex =>
    f.2 (fun j => (row.2.map (Choice.bit (Choice.extend c))).getD j.val false))
      (lookup_agrees D ⟨row.1,hi⟩)

theorem embedded_value (r : ExactSignatureTables.Input s 1 (WholeForest.A D)) :
    CommonField.embedding D.signature D.nonzero D.identity (WholeForest.originalValue D r) =
      embedding D (value D (query D r)) := Subtype.ext (ambient_value D r)

def correction : field D → GeneralOriginalTarget.originalField (WholeForest.originalFamily D) :=
  fun z => (CommonField.embedding D.signature D.nonzero D.identity).toLinearMap.leftInverse (embedding D z)

def correctionComputes : Computes (presentation D).encoding (WholeForest.originalPresentation D).encoding
    (correction D) :=
  (FieldCodec.computes (presentation D) (WholeForest.presentation D) (embedding D).toLinearMap).andThen
    (FieldCodec.retractComputes (WholeForest.originalPresentation D) (WholeForest.presentation D)
      (CommonField.embedding D.signature D.nonzero D.identity))

/-- Translate to the ROOT-ONLY oracle presentation using a real mapper and
two rational linear machines. The graph value proves the retraction domain. -/
def transport : LengthControlledOracleReduction
    (WholeForest.oracleEncoding D) (WholeForest.originalPresentation D).encoding
    (encoding D) (presentation D).encoding (WholeForest.originalValue D) (value D) :=
  controlledOneQueryOfEq (queryComputes D) (correctionComputes D)
    ((GeneralOriginalTarget.originalTables (rootTable D.signature)).outputBound (presentation D))
    (WholeForest.originalValue D) (fun r => by
      unfold correction
      rw [← embedded_value D r]
      exact (FieldCodec.retract_embedding (CommonField.embedding D.signature D.nonzero D.identity)
        (WholeForest.originalValue D r)).symm)

/-- Final forest reducer with a terminal codec depending only on D.signature. -/
def reduction : PolyTimeOracleReduction
    (WholeForest.inputEncoding D) (WholeForest.presentation D).encoding
    (encoding D) (presentation D).encoding (WholeForest.sourceValue D) (value D) :=
  PrefixMachine.withTerminal (CommonField.table D.signature D.nonzero D.identity) (WholeForest.presentation D)
    ((CommonField.originalTransport D.signature D.nonzero D.identity).compose (transport D).reduction)
    (WholeForest.chain D)

def includeInput (r : ExactSignatureTables.Input s 1 (rootArity D.signature)) :=
  WholeForest.includeInput D (back D r)
def includeComputes : Computes (encoding D) (WholeForest.inputEncoding D) (includeInput D) :=
  (backComputes D).andThen (WholeForest.includeComputes D)

theorem include_value (r : ExactSignatureTables.Input s 1 (rootArity D.signature)) :
    WholeForest.sourceValue D (includeInput D r) = embedding D (value D r) := by
  rw [includeInput,WholeForest.include_value,embedded_value]
  rfl

def reverse : LengthControlledOracleReduction
    (encoding D) (presentation D).encoding
    (WholeForest.inputEncoding D) (WholeForest.presentation D).encoding
    (value D) (WholeForest.sourceValue D) :=
  controlledOneQueryOfEq (includeComputes D)
    (FieldCodec.retractComputes (presentation D) (WholeForest.presentation D) (embedding D))
    ((WholeForest.sourceTables D).outputBound (WholeForest.presentation D)) (value D)
    (fun r => by
      change value D r = (embedding D).toLinearMap.leftInverse (WholeForest.sourceValue D (includeInput D r))
      rw [include_value]
      exact (FieldCodec.retract_embedding (embedding D) (value D r)).symm)

theorem equivalent :
    OracleReducible (WholeForest.inputEncoding D) (WholeForest.presentation D).encoding
      (encoding D) (presentation D).encoding (WholeForest.sourceValue D) (value D) ∧
    OracleReducible (encoding D) (presentation D).encoding
      (WholeForest.inputEncoding D) (WholeForest.presentation D).encoding (value D) (WholeForest.sourceValue D) :=
  ⟨⟨reduction D⟩,⟨(reverse D).reduction⟩⟩

/-- End-to-end cost, INCLUDING the independent root-codec adapter. -/
theorem run_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (encoding D) (presentation D).encoding (value D) oracle)
    (r : ExactSignatureTables.Input (s+WholeForest.count D) 1 (WholeForest.A D)) :
    ∃ n ≤ (reduction D).time.eval ((WholeForest.inputEncoding D).encode r).length,
      (fun c => c.bind ((reduction D).machine.step oracle))^[n]
        (some ((reduction D).machine.init ((WholeForest.inputEncoding D).encode r))) =
        some ((reduction D).machine.output ((WholeForest.presentation D).encoding.encode (WholeForest.sourceValue D r))) ∧
      OracleBatch.primitiveCount (reduction D).machine oracle
        ((reduction D).machine.init ((WholeForest.inputEncoding D).encode r)) n ≤
        (reduction D).machine.primitiveBudget * (reduction D).time.eval ((WholeForest.inputEncoding D).encode r).length := by
  let run := (reduction D).correct oracle ho r
  refine ⟨run.steps,run.steps_le_m,run.evals_in_steps,?_⟩
  exact (OracleBatch.primitiveCount_le (reduction D).machine oracle
    ((reduction D).machine.init ((WholeForest.inputEncoding D).encode r)) run.steps).trans
      (Nat.mul_le_mul_left (reduction D).machine.primitiveBudget run.steps_le_m)

end Holant.LocalDrafts.Hardness.FactorSaturation.OriginalCodec
