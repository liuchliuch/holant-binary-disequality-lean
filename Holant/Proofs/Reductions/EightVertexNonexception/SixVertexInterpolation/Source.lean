import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.Core


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.Source
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation
open Holant.Complexity.BinaryInterpolation.Chains
open Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Holant.Complexity.GraphPreprocessing
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t))

/-- Use the original intermediate field algebra already used by Core and F. -/
local instance originalFieldAlgebra : Algebra ℚ (Original.field M) :=
  (Original.field M).algebra'

private theorem original_input_bytes (r : Input M halg) :
    (Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.inputEncoding (data M halg)).encode r =
      inputEncoding.encode r := rfl

def queries (r : Input M halg) : List Original.TargetInput :=
  Compiler.Batch.samples 3 1 (PQ.A (s:=2) baseArity loopTemplate) 2 sampleQuery r

/-- Each physical sample is already expanded to the original M/native-X
oracle; there is no intermediate oracle for q or a presumed hard signature. -/
def queriesComputes : Computes inputEncoding
    (framedListEncoding Original.targetEncoding) (queries M halg) :=
  Compiler.Batch.samplesComputes 3 1 (PQ.A (s:=2) baseArity loopTemplate) 2
    Original.targetEncoding sampleQuery sampleQueryComputes

theorem query_count (r : Input M halg) :
    (queries M halg r).length = occurrences 2 r.val+1 :=
  Compiler.Batch.samples_length _ _ _ _ _ r

theorem query_bytes (r : Input M halg) :
    ((framedListEncoding Original.targetEncoding).encode (queries M halg r)).length ≤
      (queriesComputes M halg).outputBound.bound.eval (inputEncoding.encode r).length :=
  (queriesComputes M halg).outputBound.length_le r

theorem answers_order (r : Input M halg) :
    (queries M halg r).map (Original.targetValue M halg) =
      List.ofFn (MC.values (data M halg) r) := by
  simp only [queries,Compiler.Batch.samples,List.map_map,Function.comp_def]
  simp_rw [sampleQuery_value M halg]
  simpa only [Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.queries,
    Holant.LocalDrafts.BinaryInterpolation.EncodedBatch.queries,Compiler.Batch.samples,
    List.map_map,Function.comp_def,data] using MC.answer_order (data M halg) r

def preprocessing (r : Input M halg) :=
  (queries M halg r,WeightCompiler.reference true (occurrences 2 r.val))

def pre : Computes inputEncoding
    (OracleBatch.contextEncoding Original.targetEncoding MC.codeEncoding)
    (preprocessing M halg) :=
  pairComputes (queriesComputes M halg)
    (Holant.LocalDrafts.BinaryInterpolation.EncodedBatch.contextComputes
      (s:=2) (b:=1) baseArity loopTemplate true)

theorem answered_eq (r : Input M halg) :
    OracleBatch.answers (Original.targetValue M halg) (preprocessing M halg r) =
      MC.answered (data M halg) r := by
  apply Prod.ext
  · exact answers_order M halg r
  · rfl

def weightGood : Bool := by
  classical
  exact if decide (u M halg = 0) then false else
    if decide (v M halg = 0) then false else
      if decide (u M halg = v M halg) then false else true

theorem weightGood_correct : weightGood M halg = true ↔
    u M halg ≠ 0 ∧ v M halg ≠ 0 ∧ u M halg ≠ v M halg := by
  classical
  by_cases hu : u M halg = 0 <;> by_cases hv : v M halg = 0 <;>
    by_cases huv : u M halg = v M halg <;> simp [weightGood,hu,hv,huv]

def equalConstantComputes (x y : Original.field M) :
    Computes inputEncoding encodingBoolBool (fun _ : Input M halg => decide (x=y)) := by
  classical
  exact (pairComputes (constantComputes inputEncoding (F M halg).encoding x)
    (constantComputes inputEncoding (F M halg).encoding y)).andThen
      (equalComputes (F M halg).encoding)

/-- Only canonical words for the actual q-derived weights are compared.
All three equality tests are the existing physical WordCompare program. -/
def weightGoodComputes : Computes inputEncoding encodingBoolBool
    (fun _ : Input M halg => weightGood M halg) := by
  classical
  exact ifComputes (equalConstantComputes M halg (u M halg) 0)
    (constantComputes inputEncoding encodingBoolBool false)
    (ifComputes (equalConstantComputes M halg (v M halg) 0)
      (constantComputes inputEncoding encodingBoolBool false)
      (ifComputes (equalConstantComputes M halg (u M halg) (v M halg))
        (constantComputes inputEncoding encodingBoolBool false)
        (constantComputes inputEncoding encodingBoolBool true)))

def countEqual (k : ℕ) (r : Input M halg) : Bool := decide (occurrences 2 r.val = k)
def countEqualComputes (k : ℕ) : Computes inputEncoding encodingBoolBool (countEqual M halg k) :=
  (pairComputes (FixedGadgetSubstitution.Compiler.occurrencesComputes 3 1
    (PQ.A (s:=2) baseArity loopTemplate) 2)
    (constantComputes inputEncoding UnaryBinary.unaryEncoding k)).andThen
      (equalComputes UnaryBinary.unaryEncoding)

def smallCount (r : Input M halg) : Bool := if countEqual M halg 0 r then true else countEqual M halg 1 r
def smallCountComputes : Computes inputEncoding encodingBoolBool (smallCount M halg) :=
  ifComputes (countEqualComputes M halg 0)
    (constantComputes inputEncoding encodingBoolBool true) (countEqualComputes M halg 1)

theorem smallCount_correct (r : Input M halg) :
    smallCount M halg r = true ↔ occurrences 2 r.val ≤ 1 := by
  by_cases h₀ : occurrences 2 r.val = 0 <;> by_cases h₁ : occurrences 2 r.val = 1 <;>
    simp [smallCount,countEqual,h₀,h₁] <;> omega

def branch (r : Input M halg) : Bool :=
  if Original.branch M then
    if smallCount M halg r then weightGood M halg else false
  else false

/-- The original eight field words, the original graph's actual label stream,
and the concrete two weights are all produced internally. No certificate of
node separation or successful interpolation is part of the input encoding. -/
def branchComputes : Computes inputEncoding encodingBoolBool (branch M halg) :=
  ifComputes
    ((constantComputes inputEncoding (framedListEncoding (F M halg).encoding)
      (BranchTest.entriesList (Original.fieldSignature M))).andThen
        (Original.branchComputes M halg))
    (ifComputes (smallCountComputes M halg) (weightGoodComputes M halg)
      (constantComputes inputEncoding encodingBoolBool false))
    (constantComputes inputEncoding encodingBoolBool false)

theorem branch_correct (r : Input M halg) : branch M halg r = true ↔
    SparseCase M ∧ occurrences 2 r.val ≤ 1 ∧
      u M halg ≠ 0 ∧ v M halg ≠ 0 ∧ u M halg ≠ v M halg := by
  by_cases hₛ : Original.branch M = true
  · have hs := (Original.branch_correct M).mp hₛ
    by_cases hsmall : smallCount M halg r = true
    · have hc := (smallCount_correct M halg r).mp hsmall
      simpa [branch,hₛ,hsmall,hs,hc] using weightGood_correct M halg
    · have hc : ¬ occurrences 2 r.val ≤ 1 := fun h => hsmall ((smallCount_correct M halg r).mpr h)
      have hf := Bool.eq_false_iff.mpr hsmall
      simp [branch,hₛ,hf,hc]
  · have hs : ¬ SparseCase M := fun h => hₛ ((Original.branch_correct M).mpr h)
    have hf := Bool.eq_false_iff.mpr hₛ
    simp [branch,hf,hs]

theorem branch_coefficients (hM : EvenSupport M) (r : Input M halg) :
    branch M halg r = true ↔ SparseCase M ∧ occurrences 2 r.val ≤ 1 ∧
      sparseU (entries M) ≠ 0 ∧ sparseV (entries M) ≠ 0 ∧
        sparseU (entries M) ≠ sparseV (entries M) := by
  rw [branch_correct]
  by_cases hs : SparseCase M
  · have hzero (z : Original.field M) : z ≠ 0 ↔ (z : L) ≠ 0 := by
      constructor
      · intro h hz
        exact h (Subtype.ext hz)
      · intro h hz
        exact h (congrArg (fun z : Original.field M => (z : L)) hz)
    have he : u M halg ≠ v M halg ↔ (u M halg : L) ≠ (v M halg : L) := by
      constructor
      · intro h hz
        exact h (Subtype.ext hz)
      · intro h hz
        exact h (congrArg (fun z : Original.field M => (z : L)) hz)
    simp only [hzero,he,u_exact M halg hM hs,v_exact M halg hM hs]
  · simp [hs]

/-- The recognizer's success proves the actual finite denominator nonzero;
it is no longer a caller-supplied Lagrange premise. -/
theorem branch_denominator (r : Input M halg) (hb : branch M halg r = true) :
    (MC.resultPair (data M halg) r).2 ≠ 0 := by
  obtain ⟨_,hm,hu,hv,huv⟩ := (branch_correct M halg r).mp hb
  apply commonDenominator_ne_zero
  intro i
  apply queryDenominator_ne_zero
  · change Function.Injective (fun i : Fin (occurrences 2 r.val+1) =>
      (u M halg / v M halg)^(i.val+1))
    exact first_nodes_injective (u M halg) (v M halg) hu hv huv (occurrences 2 r.val) hm
  · intro j
    exact pow_ne_zero _ hv

/-- A concrete, internally checked pin-interpolation producer from the same
M, actual q, original graph, field and byte programs. Its scope is explicit:
this branch has at most one marked binary occurrence, not arbitrary pin use. -/
theorem branch_recovery (hM : EvenSupport M) (r : Input M halg)
    (hb : branch M halg r = true) :
    MC.interpolatedValue (data M halg) r = targetPinValue M halg r := by
  obtain ⟨hs,_,_,hv,_⟩ := (branch_correct M halg r).mp hb
  exact recovery_if_denominator M halg hM hs r hv (branch_denominator M halg r hb)

def branch_outputs (r : Input M halg) :
    TM2OutputsInTime (branchComputes M halg).machine.computer (inputEncoding.encode r)
      (some (encodingBoolBool.encode (branch M halg r)))
      ((branchComputes M halg).time.eval (inputEncoding.encode r).length) :=
  (branchComputes M halg).outputs r

theorem branch_primitive_bound (r : Input M halg) :
    primitiveCost (branchComputes M halg).machine ((branchComputes M halg).outputs r).steps
      (some (initList (branchComputes M halg).machine.computer (inputEncoding.encode r))) ≤
      (primitivePolynomial (branchComputes M halg)).eval (inputEncoding.encode r).length :=
  computes_primitive_cost (branchComputes M halg) r

/-- A non-literal coefficient branch. Its weights are those of the same q
self-loop; neither the tensor nor the original M is replaced or normalized. -/
def doubling : Bool :=
  if Original.branch M then
    if decide (v M halg=0) then false else decide (u M halg=2*v M halg)
  else false

def doublingComputes : Computes inputEncoding encodingBoolBool
    (fun _ : Input M halg => doubling M halg) :=
  ifComputes
    ((constantComputes inputEncoding (framedListEncoding (F M halg).encoding)
      (BranchTest.entriesList (Original.fieldSignature M))).andThen
        (Original.branchComputes M halg))
    (ifComputes (equalConstantComputes M halg (v M halg) 0)
      (constantComputes inputEncoding encodingBoolBool false)
      ((pairComputes
        (constantComputes inputEncoding (F M halg).encoding (u M halg))
        ((pairComputes
          (constantComputes inputEncoding (F M halg).encoding (2 : Original.field M))
          (constantComputes inputEncoding (F M halg).encoding (v M halg))).andThen
            (Holant.OneHot.StackProgram.Machine.fieldProviders (F M halg)).mul)).andThen
              (equalComputes (F M halg).encoding)))
    (constantComputes inputEncoding encodingBoolBool false)

theorem doubling_correct : doubling M halg = true ↔
    SparseCase M ∧ v M halg ≠ 0 ∧ u M halg = 2*v M halg := by
  have hs := Original.branch_correct M
  cases hb : Original.branch M <;> by_cases hv : v M halg=0 <;>
    by_cases hu : u M halg=2*v M halg <;> simp_all [doubling]

theorem doubling_coefficients (hM : EvenSupport M) : doubling M halg = true ↔
    SparseCase M ∧ sparseV (entries M) ≠ 0 ∧
      sparseU (entries M) = 2*sparseV (entries M) := by
  rw [doubling_correct]
  by_cases hs : SparseCase M
  · have hzero : v M halg ≠ 0 ↔ (v M halg : L) ≠ 0 := by
      constructor
      · intro h hz
        exact h (Subtype.ext hz)
      · intro h hz
        exact h (congrArg (fun z : Original.field M => (z : L)) hz)
    have he : u M halg = 2*v M halg ↔ (u M halg : L) = 2*(v M halg : L) := by
      constructor
      · intro h
        exact congrArg (fun z : Original.field M => (z : L)) h
      · intro h
        exact Subtype.ext h
    simp only [hzero,he,u_exact M halg hM hs,v_exact M halg hM hs]
  · simp [hs]

def doubling_outputs (r : Input M halg) :
    TM2OutputsInTime (doublingComputes M halg).machine.computer (inputEncoding.encode r)
      (some (encodingBoolBool.encode (doubling M halg)))
      ((doublingComputes M halg).time.eval (inputEncoding.encode r).length) :=
  (doublingComputes M halg).outputs r

theorem doubling_primitive_bound (r : Input M halg) :
    primitiveCost (doublingComputes M halg).machine ((doublingComputes M halg).outputs r).steps
      (some (initList (doublingComputes M halg).machine.computer (inputEncoding.encode r))) ≤
      (primitivePolynomial (doublingComputes M halg)).eval (inputEncoding.encode r).length :=
  computes_primitive_cost (doublingComputes M halg) r

namespace Checked

namespace Cap
export Holant.LocalDrafts.BinaryInterpolation.MachineCapstone
  (reorder interpreterTime interpreter_outputs answered_length)
end Cap

abbrev outputEncoding := pairEncoding encodingBoolBool (F M halg).encoding

/-- Read the second actual interpreter stack cell, rather than supplying a
normalizer as advice. The re-encoding is byte-for-byte the same stack codec. -/
def denominatorComputes : Computes (DivisionStack.encoding (F M halg))
    (F M halg).encoding (fun p : Original.field M × Original.field M => p.2) :=
  recode (FixedGadgetSubstitution.Compiler.getDComputes (F M halg).encoding 1 0)
    (fun p => [p.1,p.2]) (fun _ => rfl) (fun _ => rfl)

def denominatorZeroComputes : Computes (DivisionStack.encoding (F M halg))
    encodingBoolBool (fun p : Original.field M × Original.field M => decide (p.2=0)) :=
  (pairComputes (denominatorComputes M halg)
    (constantComputes (DivisionStack.encoding (F M halg)) (F M halg).encoding 0)).andThen
      (equalComputes (F M halg).encoding)

def fixedGood : Bool :=
  if Original.branch M then if decide (v M halg=0) then false else true else false

def fixedGoodComputes : Computes (DivisionStack.encoding (F M halg)) encodingBoolBool
    (fun _ : Original.field M × Original.field M => fixedGood M halg) :=
  ifComputes
    ((constantComputes (DivisionStack.encoding (F M halg))
      (framedListEncoding (F M halg).encoding)
      (BranchTest.entriesList (Original.fieldSignature M))).andThen
        (Original.branchComputes M halg))
    (ifComputes
      ((pairComputes
        (constantComputes (DivisionStack.encoding (F M halg)) (F M halg).encoding (v M halg))
        (constantComputes (DivisionStack.encoding (F M halg)) (F M halg).encoding 0)).andThen
          (equalComputes (F M halg).encoding))
      (constantComputes (DivisionStack.encoding (F M halg)) encodingBoolBool false)
      (constantComputes (DivisionStack.encoding (F M halg)) encodingBoolBool true))
    (constantComputes (DivisionStack.encoding (F M halg)) encodingBoolBool false)

def flag (p : Original.field M × Original.field M) : Bool :=
  if fixedGood M halg then if decide (p.2=0) then false else true else false

def flagComputes : Computes (DivisionStack.encoding (F M halg)) encodingBoolBool (flag M halg) :=
  ifComputes (fixedGoodComputes M halg)
    (ifComputes (denominatorZeroComputes M halg)
      (constantComputes (DivisionStack.encoding (F M halg)) encodingBoolBool false)
      (constantComputes (DivisionStack.encoding (F M halg)) encodingBoolBool true))
    (constantComputes (DivisionStack.encoding (F M halg)) encodingBoolBool false)

theorem flag_correct (p : Original.field M × Original.field M) :
    flag M halg p = true ↔ SparseCase M ∧ v M halg ≠ 0 ∧ p.2 ≠ 0 := by
  have hs := Original.branch_correct M
  cases hb : Original.branch M <;> by_cases hv : v M halg=0 <;> by_cases hd : p.2=0 <;>
    simp_all [flag,fixedGood]

/-- This actual pair program keeps the original faithful quotient word and
emits a checked success bit. A false bit retains every failed branch; its
quotient is never identified with the pin target. -/
def finishComputes : Computes (DivisionStack.encoding (F M halg)) (outputEncoding M halg)
    (fun p : Original.field M × Original.field M => (flag M halg p,p.1/p.2)) :=
  pairComputes (flagComputes M halg) (DivisionStack.computes (F M halg))

def value (r : Input M halg) : Bool × Original.field M :=
  (flag M halg (MC.resultPair (data M halg) r),MC.interpolatedValue (data M halg) r)

abbrev arithmetic := (MC.interpreter (data M halg)).compose (finishComputes M halg).machine
abbrev post := (Cap.reorder (F:=F M halg)).machine.compose (arithmetic M halg)
abbrev machine := OracleBatch.machine (pre M halg).machine (post M halg)

def arithmeticTime : Polynomial ℕ :=
  Cap.interpreterTime (data M halg) + 8*MC.widthPolynomial (data M halg) + 12 +
    (finishComputes M halg).time.comp (4*MC.widthPolynomial (data M halg)+5)
def postTime : Polynomial ℕ :=
  (Cap.reorder (F:=F M halg)).time.comp (MC.transcriptBound (data M halg)) +
    6*MC.transcriptBound (data M halg)+4+arithmeticTime M halg
def timePolynomial : Polynomial ℕ :=
  (pre M halg).time + 16*((pre M halg).outputBound.bound+MC.transcriptBound (data M halg)+1) +
    postTime M halg

def arithmetic_outputs (r : Input M halg) :
    TM2OutputsInTime (arithmetic M halg).computer
      ((pairEncoding MC.codeEncoding
        (Holant.OneHot.StackProgram.stackEncoding (F M halg).encoding)).encode
        (WeightCompiler.reference true (occurrences 2 r.val),List.ofFn (MC.values (data M halg) r)))
      (some ((outputEncoding M halg).encode (value M halg r)))
      ((arithmeticTime M halg).eval (inputEncoding.encode r).length) := by
  let first := Cap.interpreter_outputs (data M halg) r
  let last := (finishComputes M halg).outputs (MC.resultPair (data M halg) r)
  let all := BinaryCompose.Machine.compose_correct (MC.interpreter (data M halg))
    (finishComputes M halg).machine _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  have hs := MC.result_length (data M halg) r
  have hd := natPolynomial_eval_mono (finishComputes M halg).time hs
  simp only [original_input_bytes] at ht hs hd
  simp only [arithmeticTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_comp]
  omega

def post_outputs (r : Input M halg) :
    TM2OutputsInTime (post M halg).computer
      ((OracleBatch.contextEncoding (F M halg).encoding MC.codeEncoding).encode
        (OracleBatch.answers (Original.targetValue M halg) (preprocessing M halg r)))
      (some ((outputEncoding M halg).encode (value M halg r)))
      ((postTime M halg).eval (inputEncoding.encode r).length) := by
  rw [answered_eq]
  let first := (Cap.reorder (F:=F M halg)).outputs (MC.answered (data M halg) r)
  let last := arithmetic_outputs M halg r
  let all := BinaryCompose.Machine.compose_correct (Cap.reorder (F:=F M halg)).machine
    (arithmetic M halg) _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  dsimp only [MC.answered,Prod.fst,Prod.snd] at ht
  have hs := (Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.component_lengths
    (data M halg) r).2.2
  have hr := natPolynomial_eval_mono (Cap.reorder (F:=F M halg)).time
    (Cap.answered_length (data M halg) r)
  dsimp only [MC.answered] at hr
  simp only [original_input_bytes] at ht hs hr
  simp only [postTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_comp]
  omega

/-- Same ordered original-M query transcript, now with a physically checked
denominator flag for every actual m. No successful finite-query combination
is silently promoted to an all-size hardness reduction. -/
theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding
      (Original.targetValue M halg) oracle) (r : Input M halg) :
    ∃ t ≤ (timePolynomial M halg).eval (inputEncoding.encode r).length,
      OracleBatch.RunsTrace (machine M halg) oracle
        ((machine M halg).init (inputEncoding.encode r))
        ((machine M halg).output ((outputEncoding M halg).encode (value M halg r))) t
        ((queries M halg r).map Original.targetEncoding.encode) := by
  have hm := OracleBatch.oracle_encoded_list oracle ho (queries M halg r)
  have ha := (pre M halg).outputs r
  have hb := post_outputs M halg r
  rw [OracleBatch.context_encode] at hb
  have hb' : TM2OutputsInTime (post M halg).computer
      (OracleBatch.word (((queries M halg r).map Original.targetEncoding.encode).map oracle)
        (MC.codeEncoding.encode (WeightCompiler.reference true (occurrences 2 r.val))))
      (some ((outputEncoding M halg).encode (value M halg r)))
      ((postTime M halg).eval (inputEncoding.encode r).length) := by
    simp only [OracleBatch.answers,preprocessing] at hb
    rw [hm]
    exact hb
  have ha' : TM2OutputsInTime (pre M halg).machine.computer (inputEncoding.encode r)
      (some (OracleBatch.word ((queries M halg r).map Original.targetEncoding.encode)
        (MC.codeEncoding.encode (WeightCompiler.reference true (occurrences 2 r.val)))))
      ((pre M halg).time.eval (inputEncoding.encode r).length) := by
    simpa only [preprocessing,OracleBatch.context_encode] using ha
  have hr := OracleBatch.run_trace (pre M halg).machine (post M halg) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,hr⟩
  have ht₁ := ha'.steps_le_m
  have ht₂ := hb'.steps_le_m
  have hp := (pre M halg).outputBound.length_le r
  have hd := Cap.answered_length (data M halg) r
  rw [← answered_eq,OracleBatch.context_encode] at hd
  simp only [OracleBatch.answers,preprocessing] at hd
  have hdq : (OracleBatch.word
      (((queries M halg r).map Original.targetEncoding.encode).map oracle)
      (MC.codeEncoding.encode (WeightCompiler.reference true (occurrences 2 r.val)))).length ≤
      (MC.transcriptBound (data M halg)).eval (inputEncoding.encode r).length := by
    simpa only [hm,original_input_bytes] using hd
  rw [OracleBatch.context_encode] at hp
  simp only [preprocessing] at hp
  have hh := OracleBatch.overhead_le oracle ((queries M halg r).map Original.targetEncoding.encode)
    (MC.codeEncoding.encode (WeightCompiler.reference true (occurrences 2 r.val)))
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_one]
  omega

def reduction : PolyTimeOracleReduction inputEncoding (outputEncoding M halg)
    Original.targetEncoding (F M halg).encoding (value M halg) (Original.targetValue M halg) where
  machine := machine M halg
  time := timePolynomial M halg
  correct oracle ho r := by
    let h := execution M halg oracle ho r
    exact {
      steps := h.choose
      evals_in_steps := h.choose_spec.2.run
      steps_le_m := h.choose_spec.1 }

theorem success_recovery (hM : EvenSupport M) (r : Input M halg)
    (h : (value M halg r).1 = true) : (value M halg r).2 = targetPinValue M halg r := by
  obtain ⟨hs,hv,hd⟩ := (flag_correct M halg (MC.resultPair (data M halg) r)).mp h
  exact recovery_if_denominator M halg hM hs r hv hd

/-- The checked bit has precisely a finite coefficient-power condition at
this original graph's computed m. It does not test or assume infinite order. -/
theorem success_condition (r : Input M halg) : (value M halg r).1 = true ↔
    SparseCase M ∧ v M halg ≠ 0 ∧ Function.Injective
      (fun i : Fin (occurrences 2 r.val+1) => (u M halg/v M halg)^(i.val+1)) := by
  constructor
  · intro h
    obtain ⟨hs,hv,hd⟩ := (flag_correct M halg (MC.resultPair (data M halg) r)).mp h
    refine ⟨hs,hv,?_⟩
    exact nodes_injective_of_denominator _ _ hd
  · rintro ⟨hs,hv,hn⟩
    apply (flag_correct M halg (MC.resultPair (data M halg) r)).mpr
    refine ⟨hs,hv,?_⟩
    apply commonDenominator_ne_zero
    intro i
    apply queryDenominator_ne_zero
    · exact hn
    · intro j
      exact pow_ne_zero _ hv

theorem first_branch_success (r : Input M halg) (hb : branch M halg r = true) :
    (value M halg r).1 = true := by
  obtain ⟨hs,_,_,hv,_⟩ := (branch_correct M halg r).mp hb
  exact (flag_correct M halg (MC.resultPair (data M halg) r)).mpr
    ⟨hs,hv,branch_denominator M halg r hb⟩

/-- All-size separation is a theorem of this actual coefficient branch.
The original rational algebra produces characteristic zero, not a new input. -/
theorem doubling_success (hb : doubling M halg = true) (r : Input M halg) :
    (value M halg r).1 = true := by
  obtain ⟨hs,hv,hu⟩ := (doubling_correct M halg).mp hb
  apply (success_condition M halg r).mpr
  refine ⟨hs,hv,?_⟩
  have hr : u M halg/v M halg = (2 : Original.field M) := (div_eq_iff hv).mpr hu
  rw [hr]
  letI : CharZero (Original.field M) := algebraRat.charZero (Original.field M)
  exact doubling_nodes_injective (occurrences 2 r.val)

theorem doubling_recovery (hM : EvenSupport M) (hb : doubling M halg = true)
    (r : Input M halg) : MC.interpolatedValue (data M halg) r = targetPinValue M halg r :=
  success_recovery M halg hM r (doubling_success M halg hb r)

/-- Direct machine endpoint for the proved first-degree branch. Its premise
is the actual coefficient/label-stream Boolean test, not a tensor equation,
oracle reduction, successful output or hardness promise. -/
theorem pin_execution (hM : EvenSupport M) (r : Input M halg)
    (hb : branch M halg r = true) (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding
      (Original.targetValue M halg) oracle) :
    ∃ t ≤ (timePolynomial M halg).eval (inputEncoding.encode r).length,
      OracleBatch.RunsTrace (machine M halg) oracle
        ((machine M halg).init (inputEncoding.encode r))
        ((machine M halg).output ((outputEncoding M halg).encode
          (true,targetPinValue M halg r))) t
        ((queries M halg r).map Original.targetEncoding.encode) := by
  obtain ⟨t,ht,hr⟩ := execution M halg oracle ho r
  have hs := first_branch_success M halg r hb
  have hv := success_recovery M halg hM r hs
  have he : value M halg r = (true,targetPinValue M halg r) := Prod.ext hs hv
  rw [he] at hr
  exact ⟨t,ht,hr⟩

theorem zero_failure (r : Input M halg)
    (hd : (MC.resultPair (data M halg) r).2 = 0) :
    value M halg r = (false,0) := by
  apply Prod.ext
  · simp [value,flag,hd]
  · exact zero_denominator M halg r hd

theorem exact_calls_and_primitive (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding
      (Original.targetValue M halg) oracle) (r : Input M halg) :
    ∃ t ≤ (timePolynomial M halg).eval (inputEncoding.encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount (machine M halg) oracle
        ((machine M halg).init (inputEncoding.encode r)) t = occurrences 2 r.val+1 ∧
      OracleBatch.primitiveCount (machine M halg) oracle
        ((machine M halg).init (inputEncoding.encode r)) t ≤
        (Polynomial.C (machine M halg).primitiveBudget * timePolynomial M halg).eval
          (inputEncoding.encode r).length := by
  obtain ⟨t,ht,hr⟩ := execution M halg oracle ho r
  refine ⟨t,ht,?_,?_⟩
  · simpa only [List.length_map,query_count] using hr.count
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
        Nat.mul_le_mul_left (machine M halg).primitiveBudget ht)

end Checked

namespace Pin

abbrev machine := OracleBatch.machine (pre M halg).machine (MC.post (data M halg))
def timePolynomial : Polynomial ℕ :=
  (pre M halg).time +
    16*((pre M halg).outputBound.bound+MC.transcriptBound (data M halg)+1) +
      MC.postTime (data M halg)

/-- On the internally tested doubling branch, this is actual ordinary
M/native-X access for arbitrarily many marked pin occurrences. The output
keeps precisely the old original-field word, without the optional check bit. -/
theorem execution (hM : EvenSupport M) (hbranch : doubling M halg = true)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding
      (Original.targetValue M halg) oracle) (r : Input M halg) :
    ∃ t ≤ (timePolynomial M halg).eval (inputEncoding.encode r).length,
      OracleBatch.RunsTrace (machine M halg) oracle
        ((machine M halg).init (inputEncoding.encode r))
        ((machine M halg).output ((F M halg).encoding.encode (targetPinValue M halg r))) t
        ((queries M halg r).map Original.targetEncoding.encode) := by
  have hm := OracleBatch.oracle_encoded_list oracle ho (queries M halg r)
  have ha := (pre M halg).outputs r
  have hb := MC.post_outputs (data M halg) r
  rw [← answered_eq,OracleBatch.context_encode,Checked.doubling_recovery M halg hM hbranch r] at hb
  have hb' : TM2OutputsInTime (MC.post (data M halg)).computer
      (OracleBatch.word (((queries M halg r).map Original.targetEncoding.encode).map oracle)
        (MC.codeEncoding.encode (WeightCompiler.reference true (occurrences 2 r.val))))
      (some ((F M halg).encoding.encode (targetPinValue M halg r)))
      ((MC.postTime (data M halg)).eval (inputEncoding.encode r).length) := by
    simp only [OracleBatch.answers,preprocessing] at hb
    rw [hm]
    exact hb
  have ha' : TM2OutputsInTime (pre M halg).machine.computer (inputEncoding.encode r)
      (some (OracleBatch.word ((queries M halg r).map Original.targetEncoding.encode)
        (MC.codeEncoding.encode (WeightCompiler.reference true (occurrences 2 r.val)))))
      ((pre M halg).time.eval (inputEncoding.encode r).length) := by
    simpa only [preprocessing,OracleBatch.context_encode] using ha
  have hr := OracleBatch.run_trace (pre M halg).machine (MC.post (data M halg)) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,hr⟩
  have ht₁ := ha'.steps_le_m
  have ht₂ := hb'.steps_le_m
  have hp := (pre M halg).outputBound.length_le r
  have hd := Checked.Cap.answered_length (data M halg) r
  rw [← answered_eq,OracleBatch.context_encode] at hd
  simp only [OracleBatch.answers,preprocessing] at hd
  have hdq : (OracleBatch.word
      (((queries M halg r).map Original.targetEncoding.encode).map oracle)
      (MC.codeEncoding.encode (WeightCompiler.reference true (occurrences 2 r.val)))).length ≤
      (MC.transcriptBound (data M halg)).eval (inputEncoding.encode r).length := by
    simpa only [hm,original_input_bytes] using hd
  rw [OracleBatch.context_encode] at hp
  simp only [preprocessing] at hp
  have hh := OracleBatch.overhead_le oracle ((queries M halg r).map Original.targetEncoding.encode)
    (MC.codeEncoding.encode (WeightCompiler.reference true (occurrences 2 r.val)))
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_one]
  omega

/-- This is a reduction of the *actual literal pin Holant function*, not of
an unproved hard source or an interpolation expression selected by fiat. -/
def reduction (hM : EvenSupport M) (hbranch : doubling M halg = true) :
    PolyTimeOracleReduction inputEncoding (F M halg).encoding
      Original.targetEncoding (F M halg).encoding
      (targetPinValue M halg) (Original.targetValue M halg) where
  machine := machine M halg
  time := timePolynomial M halg
  correct oracle ho r := by
    let h := execution M halg hM hbranch oracle ho r
    exact {
      steps := h.choose
      evals_in_steps := h.choose_spec.2.run
      steps_le_m := h.choose_spec.1 }

theorem exact_calls_and_primitive (hM : EvenSupport M) (hbranch : doubling M halg = true)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding
      (Original.targetValue M halg) oracle) (r : Input M halg) :
    ∃ t ≤ (timePolynomial M halg).eval (inputEncoding.encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount (machine M halg) oracle
        ((machine M halg).init (inputEncoding.encode r)) t = occurrences 2 r.val+1 ∧
      OracleBatch.primitiveCount (machine M halg) oracle
        ((machine M halg).init (inputEncoding.encode r)) t ≤
        (Polynomial.C (machine M halg).primitiveBudget * timePolynomial M halg).eval
          (inputEncoding.encode r).length := by
  obtain ⟨t,ht,hr⟩ := execution M halg hM hbranch oracle ho r
  refine ⟨t,ht,?_,?_⟩
  · simpa only [List.length_map,query_count] using hr.count
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
        Nat.mul_le_mul_left (machine M halg).primitiveBudget ht)

end Pin

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.Source
