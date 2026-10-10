import Holant.Proofs.Reductions.FactorSaturation.CommonField


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FactorSaturation.WholeForest
open Holant.Tractable
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction

/-- This is the declared root-preprocessing boundary. Zero signatures must
be handled by the root zero branch and nullary coefficients by an actual
scalar restoration program outside this endpoint. They are not discarded here. -/
structure Roots (s : ℕ) where
  signature : Fin s → AnySignature AlgebraicComplex
  nonzero : ∀ i, (signature i).2 ≠ 0
  positive : ∀ i, 0 < (signature i).1
  identity : RetainsIdentity (Set.range signature)

variable {s : ℕ} (D : Roots s)
abbrev count := addedCount D.signature D.nonzero
abbrev A := arity D.signature D.nonzero
abbrev originalFamily := original D.signature D.nonzero
abbrev outputFamily := augmented D.signature D.nonzero
abbrev field := CommonField.field D.signature D.nonzero D.identity
abbrev presentation := CommonField.presentation D.signature D.nonzero D.identity
abbrev originalPresentation := GeneralOriginalTarget.originalPresentation (originalFamily D)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+count D) 1 (A D)
abbrev oracleEncoding := RawClosedNetwork.validatedEncoding s 1 (A D)

def sourceTables := GeneralFieldReduction.targetTables (presentation D)
  (CommonField.smallAugmented D.signature D.nonzero D.identity)
def sourceValue := (sourceTables D).evaluate (presentation D)
abbrev originalValue := GeneralOriginalTarget.originalValue (originalFamily D)

def chain := PrefixMachine.chain (CommonField.table D.signature D.nonzero D.identity)
  (CommonField.macro D.signature D.nonzero D.identity) (count D) le_rfl

/-- All layer programs are constructed by the existing actual controlled
extraction compiler and inliner; final field conversion is also inlined. -/
def reduction : PolyTimeOracleReduction (inputEncoding D) (presentation D).encoding
    (oracleEncoding D) (originalPresentation D).encoding (sourceValue D) (originalValue D) :=
  PrefixMachine.withTerminal (CommonField.table D.signature D.nonzero D.identity) (presentation D)
    (CommonField.originalTransport D.signature D.nonzero D.identity).reduction (chain D)

theorem source_value_exact (r : ExactSignatureTables.Input (s+count D) 1 (A D)) :
    (sourceValue D r : AlgebraicComplex) =
      (r.val.realize r.property (outputFamily D) (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [sourceValue, sourceTables, GeneralFieldReduction.targetTables, FieldReduction.target_evaluate]
  change (field D).subtype _ = _
  rw [← Network.denote_map]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact CommonField.table_exact D.signature D.nonzero D.identity _
      (r.val.signatureLabel r.property v).isLt x
  · funext e a b
    cases a <;> cases b <;> rfl

theorem original_value_exact (r : ExactSignatureTables.Input s 1 (A D)) :
    (originalValue D r : AlgebraicComplex) =
      (r.val.realize r.property (originalFamily D) (fun _ => Signature.disequality)).denote Fin.elim0 :=
  GeneralOriginalTarget.target_exact (originalFamily D) r

theorem original_labels :
    Set.range (fun i => (⟨A D i.val, originalFamily D i⟩ : AnySignature AlgebraicComplex)) =
      Set.range D.signature := original_family D.signature D.nonzero

theorem output_labels :
    Set.range (fun i => (⟨A D i.val, outputFamily D i⟩ : AnySignature AlgebraicComplex)) =
      Set.range D.signature ∪ Set.range (entry D.signature D.nonzero) :=
  augmented_family D.signature D.nonzero

theorem output_saturated : FactorSaturated
    (Set.range (fun i => (⟨A D i.val, outputFamily D i⟩ : AnySignature AlgebraicComplex))) :=
  saturated D.signature D.nonzero

theorem output_finite :
    (Set.range (fun i => (⟨A D i.val, outputFamily D i⟩ : AnySignature AlgebraicComplex))).Finite :=
  finite_augmented D.signature D.nonzero

theorem retains_original : Set.range D.signature ⊆
    Set.range (fun i => (⟨A D i.val, outputFamily D i⟩ : AnySignature AlgebraicComplex)) := by
  rw [output_labels]
  exact Set.subset_union_left

theorem output_preprocessed (f : AnySignature AlgebraicComplex)
    (hf : f ∈ Set.range (fun i => (⟨A D i.val, outputFamily D i⟩ : AnySignature AlgebraicComplex))) :
    0 < f.1 ∧ f.2 ≠ 0 := by
  rw [output_labels] at hf
  rcases hf with ⟨i,rfl⟩ | ⟨j,rfl⟩
  · exact ⟨D.positive i,D.nonzero i⟩
  · exact ⟨entry_positive D.signature D.nonzero D.positive j,entry_nonzero D.signature D.nonzero j⟩

theorem run_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (oracleEncoding D) (originalPresentation D).encoding (originalValue D) oracle)
    (r : ExactSignatureTables.Input (s+count D) 1 (A D)) :
    ∃ n ≤ (reduction D).time.eval ((inputEncoding D).encode r).length,
      (fun c => c.bind ((reduction D).machine.step oracle))^[n]
        (some ((reduction D).machine.init ((inputEncoding D).encode r))) =
        some ((reduction D).machine.output ((presentation D).encoding.encode (sourceValue D r))) ∧
      OracleBatch.primitiveCount (reduction D).machine oracle
        ((reduction D).machine.init ((inputEncoding D).encode r)) n ≤
        (reduction D).machine.primitiveBudget * (reduction D).time.eval ((inputEncoding D).encode r).length := by
  let run := (reduction D).correct oracle ho r
  refine ⟨run.steps,run.steps_le_m,run.evals_in_steps,?_⟩
  exact (OracleBatch.primitiveCount_le (reduction D).machine oracle
    ((reduction D).machine.init ((inputEncoding D).encode r)) run.steps).trans
      (Nat.mul_le_mul_left (reduction D).machine.primitiveBudget run.steps_le_m)

end Holant.LocalDrafts.Hardness.FactorSaturation.WholeForest
