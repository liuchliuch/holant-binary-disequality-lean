import Holant.Proofs.BinaryInterpolation.PhysicalQueries
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Batch
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Bounds
import Holant.Complexity.OracleBatch.ReductionTrace
import Holant.Complexity.EncodedHolantOutputSize


namespace Holant.LocalDrafts.BinaryInterpolation.EncodedBatch
open Turing Computability Holant.Algebraic
open Holant.Complexity Holant.Complexity.BinaryCompose
open Holant.Complexity.FixedFieldMachines
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation
open Holant.OneHot.StackProgram
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {s b : ℕ} (arity : ℕ → ℕ) (g : Template)
variable (hg : g.WellFormed s b arity) (hbinary : g.boundary = 2) (edge : Fin b)

abbrev Source := PhysicalQueries.Source (s:=s) (b:=b) arity g
abbrev sourceEncoding := RawClosedNetwork.validatedEncoding (s+1) b
  (PhysicalQueries.A (s:=s) arity g)
abbrev queryEncoding := RawClosedNetwork.validatedEncoding s b arity
abbrev contextEncoding := codeEncoding WeightCompiler.labels

def queries (r : Source (s:=s) (b:=b) arity g) :=
  Chains.Compiler.Batch.samples (s+1) b (PhysicalQueries.A (s:=s) arity g) s
    (Chains.Compiler.OriginalFamily.value arity g hg hbinary edge) r

def queriesComputes : Computes (sourceEncoding (s:=s) (b:=b) arity g)
    (framedListEncoding (queryEncoding (s:=s) (b:=b) arity))
    (queries arity g hg hbinary edge) :=
  Chains.Compiler.Batch.samplesComputes (s+1) b (PhysicalQueries.A (s:=s) arity g) s
    (queryEncoding (s:=s) (b:=b) arity)
    (Chains.Compiler.OriginalFamily.value arity g hg hbinary edge)
    (Chains.Compiler.OriginalFamily.computes arity g hg hbinary edge)

@[simp] theorem query_count (r : Source (s:=s) (b:=b) arity g) :
    (queries arity g hg hbinary edge r).length = occurrences s r.val+1 :=
  Chains.Compiler.Batch.samples_length _ _ _ _ _ r

def context (geometric : Bool) (r : Source (s:=s) (b:=b) arity g) : Code (Fin 4) :=
  WeightCompiler.reference geometric (occurrences s r.val)

def contextComputes (geometric : Bool) : Computes (sourceEncoding (s:=s) (b:=b) arity g)
    contextEncoding (context (s:=s) (b:=b) arity g geometric) :=
  (FixedGadgetSubstitution.Compiler.occurrencesComputes (s+1) b
    (PhysicalQueries.A (s:=s) arity g) s).andThen (WeightCompiler.computes geometric)

def preprocess (geometric : Bool) (r : Source (s:=s) (b:=b) arity g) :=
  (queries arity g hg hbinary edge r, context (s:=s) (b:=b) arity g geometric r)

def preprocessComputes (geometric : Bool) :
    Computes (sourceEncoding (s:=s) (b:=b) arity g)
      (OracleBatch.contextEncoding (queryEncoding (s:=s) (b:=b) arity) contextEncoding)
      (preprocess arity g hg hbinary edge geometric) :=
  pairComputes (queriesComputes arity g hg hbinary edge)
    (contextComputes (s:=s) (b:=b) arity g geometric)

/-- Runtime is charged to the original graph, before either query expansion
or bytecode generation. There is one finite program for every value of m. -/
theorem preprocessing_steps (geometric : Bool) (r : Source (s:=s) (b:=b) arity g) :
    ((preprocessComputes arity g hg hbinary edge geometric).outputs r).steps ≤
      (preprocessComputes arity g hg hbinary edge geometric).time.eval
        ((sourceEncoding (s:=s) (b:=b) arity g).encode r).length :=
  ((preprocessComputes arity g hg hbinary edge geometric).outputs r).steps_le_m

theorem preprocessing_primitive_cost (geometric : Bool)
    (r : Source (s:=s) (b:=b) arity g) :
    primitiveCost (preprocessComputes arity g hg hbinary edge geometric).machine
      ((preprocessComputes arity g hg hbinary edge geometric).outputs r).steps
      (some (initList (preprocessComputes arity g hg hbinary edge geometric).machine.computer
        ((sourceEncoding (s:=s) (b:=b) arity g).encode r))) ≤
      (primitivePolynomial (preprocessComputes arity g hg hbinary edge geometric)).eval
        ((sourceEncoding (s:=s) (b:=b) arity g).encode r).length :=
  computes_primitive_cost (preprocessComputes arity g hg hbinary edge geometric) r

/-- Explicit quartic bound for all generated weight bytes in original input
length, including every instruction frame and the final terminator. -/
theorem context_bytes (geometric : Bool) (r : Source (s:=s) (b:=b) arity g) :
    (contextEncoding.encode (context (s:=s) (b:=b) arity g geometric r)).length ≤
      WeightCompiler.quartic.eval ((sourceEncoding (s:=s) (b:=b) arity g).encode r).length :=
  (WeightCompiler.quartic_output_bound geometric (occurrences s r.val)).trans
    (natPolynomial_eval_mono WeightCompiler.quartic (occurrences_le_input_length s r.val))

/-- Fixed macro constants are explicit: at most 2 V m² additional vertices
per query once m≥1. Removing the original marked vertices only improves it. -/
theorem quadratic_vertices (r : Source (s:=s) (b:=b) arity g)
    (hm : 1 ≤ occurrences s r.val) (i : Fin (occurrences s r.val+1)) :
    (Chains.Compiler.OriginalFamily.value arity g hg hbinary edge ⟨r,i⟩).val.vertices.length -
      r.val.vertices.length ≤ 2*g.vertices.length*(occurrences s r.val)^2 := by
  have h := Chains.Compiler.OriginalFamily.added_vertices_le arity g hg hbinary edge ⟨r,i⟩
  have h₁ : occurrences s r.val+1 ≤ 2*occurrences s r.val := by omega
  have h₂ := Nat.mul_le_mul_left g.vertices.length
    (Nat.mul_le_mul_right (occurrences s r.val) h₁)
  nlinarith

theorem cubic_vertices (r : Source (s:=s) (b:=b) arity g)
    (hm : 1 ≤ occurrences s r.val) :
    (∑ i : Fin (occurrences s r.val+1),
      ((Chains.Compiler.OriginalFamily.value arity g hg hbinary edge ⟨r,i⟩).val.vertices.length -
        r.val.vertices.length)) ≤ 4*g.vertices.length*(occurrences s r.val)^3 := by
  calc
    _ ≤ ∑ _i : Fin (occurrences s r.val+1),
        2*g.vertices.length*(occurrences s r.val)^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact quadratic_vertices arity g hg hbinary edge r hm i
    _ ≤ 4*g.vertices.length*(occurrences s r.val)^3 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h₁ : occurrences s r.val+1 ≤ 2*occurrences s r.val := by omega
      have h₂ := Nat.mul_le_mul_right (2*g.vertices.length*(occurrences s r.val)^2) h₁
      nlinarith

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s b arity)

/-- This reduction only collects the actual faithfully encoded Γ answers and
the computed interpolation program. It does not claim to have evaluated it. -/
def collect (geometric : Bool) : PolyTimeOracleReduction
    (sourceEncoding (s:=s) (b:=b) arity g)
    (OracleBatch.contextEncoding F.encoding contextEncoding)
    (queryEncoding (s:=s) (b:=b) arity) F.encoding
    (fun r => OracleBatch.answers (T.evaluate F)
      (preprocess arity g hg hbinary edge geometric r)) (T.evaluate F) :=
  OracleBatch.reduction (preprocessComputes arity g hg hbinary edge geometric)
    (identityComputes (OracleBatch.contextEncoding F.encoding contextEncoding)) (T.outputBound F)

/-- Exact oracle-call count of the actual finite caller, not merely a bound on
a semantic list. Every original-Γ answer keeps its canonical fixed-field word. -/
theorem collect_query_count (geometric : Bool) (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (b:=b) arity) F.encoding (T.evaluate F) oracle)
    (r : Source (s:=s) (b:=b) arity g) :
    ∃ time ≤ (collect arity g hg hbinary edge F T geometric).time.eval
        ((sourceEncoding (s:=s) (b:=b) arity g).encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount
        (collect arity g hg hbinary edge F T geometric).machine oracle
        ((collect arity g hg hbinary edge F T geometric).machine.init
          ((sourceEncoding (s:=s) (b:=b) arity g).encode r)) time = occurrences s r.val+1 := by
  exact OracleBatch.reduction_query_count_succ
    (preprocessComputes arity g hg hbinary edge geometric)
    (identityComputes (OracleBatch.contextEncoding F.encoding contextEncoding)) (T.outputBound F)
    oracle ho (fun r => occurrences s r.val) (query_count arity g hg hbinary edge) r

theorem collected_bytes (geometric : Bool) (r : Source (s:=s) (b:=b) arity g) :
    ((OracleBatch.contextEncoding F.encoding contextEncoding).encode
      (OracleBatch.answers (T.evaluate F) (preprocess arity g hg hbinary edge geometric r))).length ≤
    (OracleBatch.decoderBound (preprocessComputes arity g hg hbinary edge geometric)
      (T.outputBound F)).eval ((sourceEncoding (s:=s) (b:=b) arity g).encode r).length :=
  OracleBatch.decoder_length_le (preprocessComputes arity g hg hbinary edge geometric)
    (T.outputBound F) r

end
end Holant.LocalDrafts.BinaryInterpolation.EncodedBatch
