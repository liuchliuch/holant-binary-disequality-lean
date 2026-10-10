import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.MatchingSum
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Source
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
local instance : Fintype Bool := Bool.fintype

/-- The sole source takes the original circuit, not a supplied CNF or
correctness receipt. Boundedness and all circuit occurrences are produced by
the delivered circuit-to-graph-to-CNF frontend. -/
def input (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) : Input :=
  ⟨DualRail.VerifierInput.Source.input c,DualRail.VerifierInput.Source.bounded c⟩
def frontend : Computes Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding encoding input :=
  recode DualRail.VerifierInput.Source.computes id (fun _ => rfl) (fun _ => rfl)
def computes : Computes Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding
    WeightedMatchingInterpolation.encoding (fun c => graph (input c)) :=
  frontend.andThen Programs.computes
theorem circuit_cut_count (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    cutValue (input c)=2^(occurrences (input c).val).length*
      (Holant.LocalDrafts.CountingHardness.CircuitInstance.value c : ℤ) := by
  rw [cut_count]
  simp only [input]
  rw [DualRail.VerifierInput.Source.count]
theorem circuit_full_cut_count (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    fullCutValue (input c)=2^(occurrences (input c).val).length*
      (Holant.LocalDrafts.CountingHardness.CircuitInstance.value c : ℤ) := by
  rw [full_cut_count]
  simp only [input]
  rw [DualRail.VerifierInput.Source.count]

def emptyFormula (n : ℕ) : Input := ⟨(n,[]),by simp [DualRail.VerifierInput.Bounded]⟩
theorem empty_formula_count (n : ℕ) : fullCutValue (emptyFormula n)=(2 : ℤ)^n := by
  rw [full_cut_count]
  simp [emptyFormula,occurrences,DualRail.VerifierInput.value,DualRail.VerifierInput.accepts,
    DualRail.VerifierInput.formulaEval,Holant.Complexity.countAccepted,
    Fintype.card_fun]
theorem empty_graph : (graph (emptyFormula 0)).val=(0,[]) := rfl

abbrev machine := computes.machine
def time := computes.time
def storagePolynomial : Polynomial ℕ := Polynomial.X+time*Polynomial.C machine.primitiveBudget
def execution (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    TM2OutputsInTime machine.computer
      (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c)
      (some (WeightedMatchingInterpolation.encoding.encode (graph (input c))))
      (time.eval (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c).length) := computes.outputs c
theorem primitive_bound (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    primitiveCost machine (execution c).steps
      (some (initList machine.computer (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c)))≤
      (primitivePolynomial computes).eval (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c).length :=
  computes_primitive_cost computes c
theorem bytes (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    (WeightedMatchingInterpolation.encoding.encode (graph (input c))).length≤
      computes.outputBound.bound.eval (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c).length :=
  computes.outputBound.length_le c
theorem prefix_storage (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) (t : ℕ)
    (cfg : machine.Config)
    (hr : (fun z=>z.bind machine.computer.step)^[t]
      (some (initList machine.computer (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c)))=some cfg)
    (ht : t≤time.eval (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c).length) :
    stackSize cfg.stk≤storagePolynomial.eval
      (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c).length := by
  have h := machine.run_size_le _ _ _ hr
  rw [Machine.size_init] at h
  simp only [storagePolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _)

/-- Actual downstream query compiler, with the SAME original signed graph
as intermediate input. This consumes the delivered polynomial interpolation;
it is not an assertion that the graph's signed partition already counts CNF.
-/
def sampleComputes : Computes Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding
    (framedListEncoding WeightedMatchingInterpolation.unitEncoding)
    (fun c => WeightedMatchingInterpolation.queries (graph (input c))) :=
  computes.andThen WeightedMatchingInterpolation.Queries.computes
theorem sample_count (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    (WeightedMatchingInterpolation.queries (graph (input c))).length=vertexCount (input c).val+1 := by
  simp [WeightedMatchingInterpolation.queries,graph,raw]
theorem sample_recovery (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    WeightedMatchingInterpolation.recover (vertexCount (input c).val)
      ((WeightedMatchingInterpolation.queries (graph (input c))).map WeightedMatchingInterpolation.unitValue)=
      WeightedMatchingInterpolation.signedValue (graph (input c)) :=
  WeightedMatchingInterpolation.recovery (graph (input c))

abbrev answerField := WeightedMatchingInterpolation.Source.rationalField
def graphPartition (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) : ℚ :=
  WeightedMatchingInterpolation.signedValue (graph (input c))
theorem graphPartition_actual_sum (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    graphPartition c=
      ((∑ s : MatchingSum.Selection (MatchingSum.keyGraph (input c)),
        MatchingSum.segmentWeight (input c) s 1*MatchingSum.segmentWeight (input c) s 2 : ℤ) : ℚ) := by
  rw [graphPartition,← WeightedMatchingInterpolation.signed_integer,
    MatchingSum.integer_segment_sum]
theorem graphPartition_count (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    graphPartition c=(2 : ℚ)^(occurrences (input c).val).length*
      (Holant.LocalDrafts.CountingHardness.CircuitInstance.value c : ℚ) := by
  rw [graphPartition,← WeightedMatchingInterpolation.signed_integer,
    MatchingSum.integer_graph,circuit_full_cut_count]
  push_cast <;> rfl
theorem original_matching_words (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c))) (side : Bool)
    (r : Fin (vertexCount (input c).val)) :
    (MatchingSum.rowWord (input c)
      (MatchingSum.toSelection (MatchingSum.keyGraph (input c))
        (MatchingSum.keyMatchingEquiv (input c) m)) side r.val).count true=1 :=
  MatchingSum.rowWord_one _ _ _ _
def originalSelection (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c))) :
    MatchingSum.Selection (MatchingSum.keyGraph (input c)) :=
  MatchingSum.toSelection (MatchingSum.keyGraph (input c)) (MatchingSum.keyMatchingEquiv (input c) m)

/-- The first completed component of the actual global matching fibre:
the remaining variable matching, with incoming/outgoing occupations extracted
from the SAME original matching. Neither a layout nor local validity is input.
-/
def originalRemaining (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c))) :
    RemainingMatching (input c)
      (MatchingSum.variableIncoming (input c) (originalSelection c m))
      (MatchingSum.variableOutgoing (input c) (originalSelection c m)) :=
  MatchingSum.remainingCapture (input c) (originalSelection c m)

/-- Clause cycles and XOR completions are captured from the same original
edge-index matching. Their two-sided exact-one laws are produced internally;
all four connector bits and every signed local choice remain present. -/
def originalClause (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c)))
    (i : Fin (input c).val.2.length) :
    Cycle.Matching
      (boundary (input c) i.val (MatchingSum.clauseIncoming (input c) (originalSelection c m)))
      (boundary (input c) i.val (MatchingSum.clauseOutgoing (input c) (originalSelection c m))) :=
  MatchingSum.clauseMatchingCapture (input c) (originalSelection c m) i
def originalXor (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c)))
    (j : Fin (occurrences (input c).val).length) :
    {cs : List ValiantXor.Vertex // cs∈ValiantXor.actualCompletions
      (MatchingSum.actualXorWord (input c) (originalSelection c m) j)} :=
  MatchingSum.xorCompletionCapture (input c) (originalSelection c m) j
theorem original_xor_edges (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c)))
    (j : Fin (occurrences (input c).val).length) :
    ValiantXor.completionEdges (MatchingSum.actualXorWord (input c) (originalSelection c m) j)
      (originalXor c m j).val=MatchingSum.xorEdgesCapture (input c) (originalSelection c m) j :=
  MatchingSum.xor_completion_edges (input c) (originalSelection c m) j
def originalJoint (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c))) : MatchingSum.Joint (input c) :=
  MatchingSum.capture (input c) (originalSelection c m)
theorem original_merge (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c))) :
    MatchingSum.mergeIDs (input c) (originalJoint c m)=
      MatchingSum.selectedIDs (input c) (originalSelection c m) :=
  MatchingSum.merge_capture (input c) (originalSelection c m)
theorem original_typed_merge (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c))) :
    MatchingSum.typedMerge (input c) (originalJoint c m)=(originalSelection c m).val :=
  MatchingSum.typed_merge_capture (input c) (originalSelection c m)
theorem original_xor_weight (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c)))
    (j : Fin (occurrences (input c).val).length) :
    ValiantXor.completionWeight (MatchingSum.actualXorWord (input c) (originalSelection c m) j)
      (originalXor c m j).val=MatchingSum.xorSelectedWeight (input c) (originalSelection c m) j :=
  MatchingSum.xor_completion_weight (input c) (originalSelection c m) j
theorem original_xor_raw_weight (c : Holant.LocalDrafts.CountingHardness.CircuitInstance)
    (m : WeightedMatchingInterpolation.Matching (graph (input c)))
    (j : Fin (occurrences (input c).val).length) :
    ValiantXor.completionWeight (MatchingSum.actualXorWord (input c) (originalSelection c m) j)
      (originalXor c m j).val=
      ∏ e∈MatchingSum.xorSelected (input c) (originalSelection c m) j,
        if (MatchingSum.record (input c) (2,j.val,e.val,false)).2 then (-1 : ℤ) else 1 :=
  MatchingSum.xor_completion_raw_weight (input c) (originalSelection c m) j
def pre : Computes Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding
    (pairEncoding WeightedMatchingInterpolation.encoding encodingBoolBool)
    (fun c=>(graph (input c),false)) := pairComputes computes
  (constantComputes Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding encodingBoolBool false)
def post : Computes (pairEncoding answerField.encoding encodingBoolBool) answerField.encoding
    (fun p : ℚ×Bool=>p.1) := Wiring.firstComputes answerField.encoding encodingBoolBool
attribute [local irreducible] pre post computes WeightedMatchingInterpolation.Source.source
  WeightedMatchingInterpolation.signedValue graph input

private def signedOutput : PolynomialOutputBound WeightedMatchingInterpolation.encoding
    answerField.encoding WeightedMatchingInterpolation.signedValue :=
  WeightedMatchingInterpolation.Source.source.sourceOutputBound
attribute [local irreducible] signedOutput

private theorem compiler_identity (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    graphPartition c=(fun p : ℚ×Bool=>p.1) (WeightedMatchingInterpolation.signedValue (graph (input c)),false) := by
  simp only [graphPartition]

def compilerControlled : LengthControlledOracleReduction
    Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding answerField.encoding
    WeightedMatchingInterpolation.encoding answerField.encoding
      graphPartition WeightedMatchingInterpolation.signedValue :=
  Holant.LocalDrafts.Hardness.ControlledCap.controlledContextOfEq pre post
    signedOutput graphPartition compiler_identity

/-- Actual, fully installed circuit-bytes -> signed graph -> UNIT multigraph
machine. Its output is the graph's signed partition; graphPartition_count
derives the original occurrence scalar from the complete local signed sum.
The rational codec is the delivered singleton presentation and is not
identified with the original M field.
-/
def source : LengthControlledOracleReduction
    Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding answerField.encoding
    WeightedMatchingInterpolation.unitEncoding answerField.encoding
      graphPartition WeightedMatchingInterpolation.unitValue :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.composeControlled
    compilerControlled WeightedMatchingInterpolation.Source.source
theorem source_reduction : source.reduction=
    compilerControlled.compose WeightedMatchingInterpolation.Source.source.reduction := rfl
theorem source_machine : source.reduction.machine=
    (compilerControlled.compose WeightedMatchingInterpolation.Source.source.reduction).machine := rfl
theorem source_time : source.reduction.time=
    (compilerControlled.compose WeightedMatchingInterpolation.Source.source.reduction).time := rfl
theorem source_query_bound : source.queryBound=
    WeightedMatchingInterpolation.Source.source.queryBound.comp compilerControlled.queryBound := rfl
theorem source_answer_codec : source.targetOutput=WeightedMatchingInterpolation.Source.source.targetOutput := rfl

/-- The actual input-derived occurrence counter is run on the actual CNF
frontend output. It is a unary tape programme, not a semantic exponent input.
-/
def scalarExponent : Computes Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding
    UnaryBinary.unaryEncoding (fun c => (occurrences (input c).val).length) :=
  frontend.andThen Programs.occurrenceCount
def correctedPartition (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) : ℚ :=
  graphPartition c*((2 : ℚ)⁻¹)^(occurrences (input c).val).length
theorem circuit_count (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    correctedPartition c=(Holant.LocalDrafts.CountingHardness.CircuitInstance.value c : ℚ) := by
  rw [correctedPartition,graphPartition_count]
  calc
    _ = (Holant.LocalDrafts.CountingHardness.CircuitInstance.value c : ℚ)*
        ((2 : ℚ)^(occurrences (input c).val).length*
          ((2 : ℚ)⁻¹)^(occurrences (input c).val).length) := by ring
    _ = _ := by rw [← mul_pow]; norm_num
def correctedPre : Computes Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding
    (pairEncoding WeightedMatchingInterpolation.encoding UnaryBinary.unaryEncoding)
    (fun c=>(graph (input c),(occurrences (input c).val).length)) := pairComputes computes scalarExponent
def correctedPost : Computes (pairEncoding answerField.encoding UnaryBinary.unaryEncoding) answerField.encoding
    (fun p : ℚ×ℕ=>p.1*((2 : ℚ)⁻¹)^p.2) := ScalarPower.correction answerField (2 : ℚ)
attribute [local irreducible] correctedPre correctedPost

private theorem corrected_identity (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) :
    correctedPartition c=(fun p : ℚ×ℕ=>p.1*((2 : ℚ)⁻¹)^p.2)
      (WeightedMatchingInterpolation.signedValue (graph (input c)),(occurrences (input c).val).length) := by
  simp only [correctedPartition,graphPartition]

def correctedCompilerControlled : LengthControlledOracleReduction
    Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding answerField.encoding
    WeightedMatchingInterpolation.encoding answerField.encoding
      correctedPartition WeightedMatchingInterpolation.signedValue :=
  Holant.LocalDrafts.Hardness.ControlledCap.controlledContextOfEq correctedPre correctedPost
    signedOutput correctedPartition corrected_identity

/-- The same physical scalar correction and shared-parameter interpolation.
Its original value name remains correctedPartition; circuit_count now
derives its equality to the actual circuit count. The fixed inverse 1/2 is
compiled by the old field programme, with no free matching unary gadget.
-/
def correctedSource : LengthControlledOracleReduction
    Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding answerField.encoding
    WeightedMatchingInterpolation.unitEncoding answerField.encoding
      correctedPartition WeightedMatchingInterpolation.unitValue :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.composeControlled
    correctedCompilerControlled WeightedMatchingInterpolation.Source.source
theorem correctedSource_reduction : correctedSource.reduction=
    correctedCompilerControlled.compose WeightedMatchingInterpolation.Source.source.reduction := rfl
theorem correctedSource_machine : correctedSource.reduction.machine=
    (correctedCompilerControlled.compose WeightedMatchingInterpolation.Source.source.reduction).machine := rfl
theorem correctedSource_time : correctedSource.reduction.time=
    (correctedCompilerControlled.compose WeightedMatchingInterpolation.Source.source.reduction).time := rfl
theorem correctedSource_query_bound : correctedSource.queryBound=
    WeightedMatchingInterpolation.Source.source.queryBound.comp correctedCompilerControlled.queryBound := rfl

/-- Actual counting consumer. All programme/clock/query/answer fields are
the saved correctedSource fields; only correctness consumes the derived
whole signed matching law and its internally computed occurrence scalar. -/
def circuitSource : LengthControlledOracleReduction
    Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding answerField.encoding
    WeightedMatchingInterpolation.unitEncoding answerField.encoding
      (fun c => (Holant.LocalDrafts.CountingHardness.CircuitInstance.value c : ℚ))
      WeightedMatchingInterpolation.unitValue where
  reduction := {
    machine := correctedSource.reduction.machine
    time := correctedSource.reduction.time
    correct := by
      intro oracle ho c
      simpa only [circuit_count] using correctedSource.reduction.correct oracle ho c
  }
  targetOutput := correctedSource.targetOutput
  queryBound := correctedSource.queryBound
  safeQuery := correctedSource.safeQuery
theorem circuitSource_machine : circuitSource.reduction.machine=correctedSource.reduction.machine := rfl
theorem circuitSource_time : circuitSource.reduction.time=correctedSource.reduction.time := rfl
theorem circuitSource_query_bound : circuitSource.queryBound=correctedSource.queryBound := rfl
theorem circuitSource_answer_codec : circuitSource.targetOutput=correctedSource.targetOutput := rfl

theorem source_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle WeightedMatchingInterpolation.unitEncoding answerField.encoding
      WeightedMatchingInterpolation.unitValue oracle)
    (c : Holant.LocalDrafts.CountingHardness.CircuitInstance) (t : ℕ) (cfg : source.reduction.machine.Cfg)
    (ht : t≤source.reduction.time.eval
      (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c).length)
    (hr : source.reduction.machine.run oracle
      (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c) t=some cfg) :
    stackSize cfg.stk≤source.sourceOutputPolynomial.eval
      (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c).length := by
  have h := source.run_stackSize_le oracle ho c t cfg hr
  exact h.trans (by
    simpa only [LengthControlledOracleReduction.sourceOutputPolynomial,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right (source.reduction.machine.primitiveBudget+
        (source.targetOutput.bound.comp source.queryBound).eval
          (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c).length) ht)
        (Holant.LocalDrafts.CountingHardness.CircuitInstance.encoding.encode c).length)

end
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Source
