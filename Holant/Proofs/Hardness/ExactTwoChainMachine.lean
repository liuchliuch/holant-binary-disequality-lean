import Holant.Proofs.Hardness.ExactTwoChainQueries
import Holant.Proofs.BinaryInterpolation.OracleAnswerBounds
import Holant.Complexity.BinaryInterpolation.DivisionStack

/-! The physical four-port interpolation programme. This replays the accepted
variable-code field interpreter on the genuinely different all-occurrence
EXACT2 chain query compiler. Bounds are proved from those emitted query bytes;
no arbitrary code runtime or externally supplied transcript is assumed. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainMachine
open Turing Computability Holant.Algebraic
open Holant.LocalDrafts.BinaryInterpolation
namespace Q
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding queries queriesComputes preprocessing pre code query_count sample)
end Q
open Holant.Complexity Holant.Complexity.BinaryCompose
open Holant.Complexity.FixedGadgetSubstitution Holant.Complexity.FixedFieldMachines
open Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

structure Data (F : FixedField K n) (T : ExactSignatureTables n 1 1 Q.arity) where
  gamma : K
  rho : K
  geometric : Bool

variable {F : FixedField K n} {T : ExactSignatureTables n 1 1 Q.arity} (d : Data F T)

abbrev Input (_d : Data F T) := Q.Input
abbrev inputEncoding (_d : Data F T) := Q.sourceEncoding
abbrev queryEncoding := Q.targetEncoding
abbrev codeEncoding := Holant.OneHot.StackProgram.codeEncoding WeightCompiler.labels
abbrev answerEncoding := OracleBatch.contextEncoding F.encoding codeEncoding
abbrev queries (_d : Data F T) := Q.queries
abbrev preprocessing (d : Data F T) (r : Q.Input) := (Q.queries r,WeightCompiler.reference d.geometric (occurrences 1 r.val))
abbrev pre (d : Data F T) : Computes Q.sourceEncoding
    (OracleBatch.contextEncoding Q.targetEncoding codeEncoding) (preprocessing d) :=
  pairComputes Q.queriesComputes
    ((FixedGadgetSubstitution.Compiler.occurrencesComputes 2 1 Q.arity 1).andThen
      (WeightCompiler.computes d.geometric))
abbrev count (_d : Data F T) (r : Q.Input) := occurrences 1 r.val
abbrev code (d : Data F T) (r : Q.Input) := WeightCompiler.reference d.geometric (count d r)

def values (r : Input d) (i : Fin (count d r+1)) : K := T.evaluate F (Q.sample ⟨r,i⟩)

def denominator (r : Input d) :=
  queryDenominator (WeightFormulas.nodes d.geometric d.rho (count d r))
    (WeightFormulas.scales d.gamma (count d r))

def resultPair (r : Input d) : K × K :=
  (commonNumerator (denominator d r) (values d r), commonDenominator (denominator d r))

def interpolatedValue (r : Input d) : K := (resultPair d r).1/(resultPair d r).2

theorem answer_order (r : Input d) : (queries d r).map (T.evaluate F) = List.ofFn (values d r) := by
  simp only [queries,Q.queries,Chains.Compiler.Batch.samples,List.map_map,List.ofFn_eq_map,values,Function.comp_def]
  rfl

def answered (r : Input d) : List K × Code (Fin 4) := (List.ofFn (values d r), code d r)

theorem answered_eq (r : Input d) :
    OracleBatch.answers (T.evaluate F) (preprocessing d r) = answered d r := by
  apply Prod.ext
  · exact answer_order d r
  · rfl

/-- The existing pair machines physically swap the framed code and answer
stack. No parser, stack permutation or oracle data is hidden in a callback. -/
def reorder : Computes (answerEncoding (F:=F))
    (pairEncoding codeEncoding (stackEncoding F.encoding))
    (fun z : List K × Code (Fin 4) => (z.2,z.1)) :=
  Wiring.swapComputes (framedListEncoding F.encoding) codeEncoding

abbrev literalCoordinates := fun a => F.decode.symm (WeightFormulas.coefficients d.gamma d.rho a)
abbrev literals := RingFormulaMachine.literals F (literalCoordinates d)
abbrev labelBound := RingFormulaMachine.labelBound WeightCompiler.labels
abbrev interpreter := StackInputInterpreter.machine (Kernels.machine (literals d) (fieldProviders F))
  WeightCompiler.labels labelBound
abbrev arithmetic := (interpreter d).compose (DivisionStack.computes F).machine
abbrev post := (reorder (F:=F)).machine.compose (arithmetic d)
abbrev machine := OracleBatch.machine (pre d).machine (post d)

abbrev base := OracleAnswerBounds.coordinates F T d.gamma d.rho
def answerBudget (_d : Data F T) : Polynomial ℕ := 2*Q.queriesComputes.outputBound.bound
abbrev transcriptBound := OracleBatch.decoderBound (pre d) (T.outputBound F)

/-- A single structural polynomial dominates both the degree/summand budget
and the height of the actual generated stack run. -/
def structuralPolynomial : Polynomial ℕ :=
  (Polynomial.X+1)*(answerBudget d+WeightCompiler.quartic+1)+WeightCompiler.quartic+Polynomial.X+1

def widthPolynomial : Polynomial ℕ :=
  (RingFormulaMachine.widthPolynomial F (base d)).comp (structuralPolynomial d)

def instructionPolynomial : Polynomial ℕ :=
  let W := widthPolynomial d
  let H := structuralPolynomial d
  let P := fieldProviders F
  P.add.time.comp (3*W+1)+P.mul.time.comp (3*W+1)+14*W+18+
    (2*W+4)*Polynomial.C (2^18)+3+Polynomial.C (2*(labelBound+6))+
    4*((2*W+2)*H+1)+9

def interpreterTime : Polynomial ℕ :=
  4*transcriptBound d+6+WeightCompiler.quartic*instructionPolynomial d

def arithmeticTime : Polynomial ℕ := interpreterTime d+8*widthPolynomial d+12+
  (DivisionStack.computes F).time.comp (4*widthPolynomial d+5)

def postTime : Polynomial ℕ :=
  (reorder (F:=F)).time.comp (transcriptBound d)+6*transcriptBound d+4+arithmeticTime d

def timePolynomial : Polynomial ℕ :=
  (pre d).time+16*((pre d).outputBound.bound+transcriptBound d+1)+postTime d

@[simp] theorem width_eval (N : ℕ) : (widthPolynomial d).eval N =
    ArithmeticSize.bitBound F (base d) ((structuralPolynomial d).eval N) := by
  simp [widthPolynomial]

@[simp] theorem instruction_eval (N : ℕ) : (instructionPolynomial d).eval N =
    Interpreter.instructionBound labelBound F.encoding (fieldProviders F)
      ((widthPolynomial d).eval N) ((structuralPolynomial d).eval N) := by
  simp [instructionPolynomial, Interpreter.instructionBound, Kernels.timeBound]

theorem weight_le_quartic (m : ℕ) : WeightFormulas.weightSize m ≤ WeightCompiler.quartic.eval m := by
  rw [WeightCompiler.quartic_eval]
  unfold WeightCompiler.codeBound
  nlinarith

theorem code_length_bound (r : Input d) :
    (code d r).length ≤ WeightCompiler.quartic.eval ((inputEncoding d).encode r).length := by
  have h := WeightCompiler.reference_length_le d.geometric (count d r)
  have hc : WeightCompiler.codeBound (count d r) ≤ WeightCompiler.quartic.eval (count d r) := by
    rw [WeightCompiler.quartic_eval]
    omega
  exact h.trans (hc.trans (natPolynomial_eval_mono WeightCompiler.quartic
    (occurrences_le_input_length 1 r.val)))

theorem structural_bounds (r : Input d) :
    let N := ((inputEncoding d).encode r).length
    let Q := (structuralPolynomial d).eval N
    1 ≤ Q ∧ (answerBudget d).eval N ≤ Q ∧
      PostprocessBounds.budget (count d r) ((answerBudget d).eval N) ≤ Q ∧
      count d r+1+(code d r).length ≤ Q := by
  dsimp only
  have hm := occurrences_le_input_length 1 r.val
  have hw := (weight_le_quartic (count d r)).trans
    (natPolynomial_eval_mono WeightCompiler.quartic hm)
  have hc := code_length_bound d r
  change WeightFormulas.weightSize (count d r) ≤
    WeightCompiler.quartic.eval ((inputEncoding d).encode r).length at hw
  change count d r ≤ ((inputEncoding d).encode r).length at hm
  simp only [structuralPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one, PostprocessBounds.budget]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · have hh := Nat.mul_le_mul (Nat.add_le_add_right hm 1)
      (Nat.add_le_add_right (Nat.add_le_add_left hw
        ((answerBudget d).eval ((inputEncoding d).encode r).length)) 1)
    nlinarith
  · nlinarith

theorem answered_length (r : Input d) :
    ((answerEncoding (F:=F)).encode (answered d r)).length ≤
      (transcriptBound d).eval ((inputEncoding d).encode r).length := by
  rw [← answered_eq]
  exact OracleBatch.decoder_length_le (pre d) (T.outputBound F) r

theorem component_lengths (r : Input d) :
    let L := (transcriptBound d).eval ((inputEncoding d).encode r).length
    (codeEncoding.encode (code d r)).length ≤ L ∧
      ((stackEncoding F.encoding).encode (List.ofFn (values d r))).length ≤ L ∧
      ((pairEncoding codeEncoding (stackEncoding F.encoding)).encode
        (code d r,List.ofFn (values d r))).length ≤ 3*L+1 := by
  have h := answered_length d r
  change ((pairEncoding (stackEncoding F.encoding) codeEncoding).encode
    (List.ofFn (values d r),code d r)).length ≤ _ at h
  rw [pairEncoding_length] at h
  dsimp only [Prod.fst, Prod.snd] at h
  dsimp only
  rw [pairEncoding_length]
  dsimp only [Prod.fst, Prod.snd]
  omega

/-- Every emitted original-q answer is bounded from the actual four-port
query bytes, rather than the old binary-chain graph-size formula. -/
theorem sample_answers_bound (r : Input d) (i : Fin (count d r+1)) :
    ArithmeticSize.Bound (fun a=>F.decode (base d a))
      ((answerBudget d).eval ((inputEncoding d).encode r).length) (values d r i) := by
  have hq : Q.sample ⟨r,i⟩∈queries d r := by
    unfold queries Q.queries Chains.Compiler.Batch.samples
    exact List.mem_map.mpr ⟨i,by simp,rfl⟩
  have hmember := OracleBatch.member_length_le
    ((queries d r).map queryEncoding.encode) (queryEncoding.encode (Q.sample ⟨r,i⟩))
    (List.mem_map.mpr ⟨_,hq,rfl⟩)
  have hlist := Q.queriesComputes.outputBound.length_le r
  rw [OracleBatch.list_encode] at hlist
  change (OracleBatch.listWord ((queries d r).map queryEncoding.encode)).length≤
    Q.queriesComputes.outputBound.bound.eval ((inputEncoding d).encode r).length at hlist
  have hsize := (Q.sample ⟨r,i⟩).val.counts_le_encoded_length
  apply (OracleAnswerBounds.answer_bound F T d.gamma d.rho (Q.sample ⟨r,i⟩)).mono (.inl 3)
    (OracleAnswerBounds.decode_unit F T d.gamma d.rho)
  simp only [answerBudget,Polynomial.eval_mul,Polynomial.eval_ofNat]
  change (Q.sample ⟨r,i⟩).val.vertices.length+(Q.sample ⟨r,i⟩).val.edges.length≤
    (queryEncoding.encode (Q.sample ⟨r,i⟩)).length at hsize
  omega

/-- Every stack boundary, including the final numerator and denominator,
has width certified from the original graph's length and the true Γ answers. -/
theorem certified (r : Input d) :
    let N := ((inputEncoding d).encode r).length
    Certified F.encoding (RingFormulaMachine.coefficients F (literalCoordinates d))
      ((widthPolynomial d).eval N) ((structuralPolynomial d).eval N)
      (code d r) (List.ofFn (values d r)) [(resultPair d r).1,(resultPair d r).2]
      (PostprocessBounds.trace d.gamma d.rho d.geometric (count d r) (values d r)) := by
  dsimp only
  let N := ((inputEncoding d).encode r).length
  let Q := (structuralPolynomial d).eval N
  let Y := (answerBudget d).eval N
  have hq := structural_bounds d r
  have hu := OracleAnswerBounds.decode_unit F T d.gamma d.rho
  have hy := sample_answers_bound d r
  have hl := OracleAnswerBounds.literal_bound F T d.gamma d.rho
  have hcoeff : RingFormulaMachine.coefficients F (literalCoordinates d) =
      WeightFormulas.coefficients d.gamma d.rho := by
    funext a
    exact F.decode.apply_symm_apply _
  rw [hcoeff, width_eval]
  apply certified_of_run F.encoding (WeightFormulas.coefficients d.gamma d.rho)
    (ArithmeticSize.bitBound F (base d) Q) Q
  · intro a
    exact ((hl a).mono (.inl 3) hu hq.1).encoded_length_le F (base d)
  · exact (ArithmeticSize.Bound.zero (.inl 3) Q).encoded_length_le F (base d)
  · exact (ArithmeticSize.Bound.one.mono (.inl 3) hu (Nat.zero_le Q)).encoded_length_le F (base d)
  · exact PostprocessBounds.reference_run d.gamma d.rho d.geometric (count d r) (values d r)
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact ((hy i).mono (.inl 3) hu hq.2.1).encoded_length_le F (base d)
  · intro x hx
    have ht := PostprocessBounds.trace_bound F (base d) (.inl 3) hu d.gamma d.rho hl
      d.geometric (count d r) Y (values d r) hy x hx
    exact (ht.mono (.inl 3) hu hq.2.2.1).encoded_length_le F (base d)
  · simpa using hq.2.2.2

theorem result_length (r : Input d) :
    ((DivisionStack.encoding F).encode (resultPair d r)).length ≤
      4*(widthPolynomial d).eval ((inputEncoding d).encode r).length+5 := by
  have h := (certified d r).output_width
  have h₁ := h (resultPair d r).1 (by simp)
  have h₂ := h (resultPair d r).2 (by simp)
  rw [DivisionStack.encoding_length]
  omega

def interpreter_outputs (r : Input d) :
    TM2OutputsInTime (interpreter d).computer
      ((pairEncoding codeEncoding (stackEncoding F.encoding)).encode
        (code d r,List.ofFn (values d r)))
      (some ((DivisionStack.encoding F).encode (resultPair d r)))
      ((interpreterTime d).eval ((inputEncoding d).encode r).length) := by
  let hex := StackInputInterpreter.execute WeightCompiler.labels labelBound F.encoding _
    (literals d) (fieldProviders F) (RingFormulaMachine.label_le WeightCompiler.labels) (certified d r)
  let t := hex.choose
  have ht := hex.choose_spec.1
  have hr := hex.choose_spec.2
  refine { steps := t, evals_in_steps := hr, steps_le_m := ?_ }
  have hlen := component_lengths d r
  have hcode := hlen.1
  change ((StackProgram.codeEncoding WeightCompiler.labels).encode (code d r)).length ≤ _ at hcode
  have hc := code_length_bound d r
  have hm := Nat.mul_le_mul_right
    ((instructionPolynomial d).eval ((inputEncoding d).encode r).length) hc
  rw [instruction_eval] at hm
  simp only [interpreterTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, instruction_eval]
  omega

def arithmetic_outputs (r : Input d) :
    TM2OutputsInTime (arithmetic d).computer
      ((pairEncoding codeEncoding (stackEncoding F.encoding)).encode
        (code d r,List.ofFn (values d r)))
      (some (F.encoding.encode (interpolatedValue d r)))
      ((arithmeticTime d).eval ((inputEncoding d).encode r).length) := by
  let first := interpreter_outputs d r
  let last := (DivisionStack.computes F).outputs (resultPair d r)
  let all := BinaryCompose.Machine.compose_correct (interpreter d) (DivisionStack.computes F).machine
    _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  have hs := result_length d r
  have hd := natPolynomial_eval_mono (DivisionStack.computes F).time hs
  simp only [arithmeticTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_comp]
  omega

def post_outputs (r : Input d) :
    TM2OutputsInTime (post d).computer ((answerEncoding (F:=F)).encode (answered d r))
      (some (F.encoding.encode (interpolatedValue d r)))
      ((postTime d).eval ((inputEncoding d).encode r).length) := by
  let first := (reorder (F:=F)).outputs (answered d r)
  let last := arithmetic_outputs d r
  let all := BinaryCompose.Machine.compose_correct (reorder (F:=F)).machine (arithmetic d)
    _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  dsimp only [answered, Prod.fst, Prod.snd] at ht
  have hs := (component_lengths d r).2.2
  have hr := natPolynomial_eval_mono (reorder (F:=F)).time (answered_length d r)
  dsimp only [answered] at hr
  simp only [postTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_comp]
  omega

/-- A concrete bounded execution and the exact ordered Γ-query transcript.
Pre/post machines make no oracle calls; the collector makes precisely these. -/
theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle queryEncoding F.encoding (T.evaluate F) oracle)
    (r : Input d) :
    ∃ t ≤ (timePolynomial d).eval ((inputEncoding d).encode r).length,
      OracleBatch.RunsTrace (machine d) oracle
        ((machine d).init ((inputEncoding d).encode r))
        ((machine d).output (F.encoding.encode (interpolatedValue d r))) t
        ((queries d r).map queryEncoding.encode) := by
  have hm := OracleBatch.oracle_encoded_list oracle ho (queries d r)
  have ha := (pre d).outputs r
  have hb := post_outputs d r
  rw [← answered_eq, OracleBatch.context_encode] at hb
  have hb' : TM2OutputsInTime (post d).computer
      (OracleBatch.word (((queries d r).map queryEncoding.encode).map oracle)
        (codeEncoding.encode (code d r)))
      (some (F.encoding.encode (interpolatedValue d r)))
      ((postTime d).eval ((inputEncoding d).encode r).length) := by
    simp only [OracleBatch.answers] at hb
    rw [hm]
    exact hb
  have ha' : TM2OutputsInTime (pre d).machine.computer ((inputEncoding d).encode r)
      (some (OracleBatch.word ((queries d r).map queryEncoding.encode)
        (codeEncoding.encode (code d r)))) ((pre d).time.eval ((inputEncoding d).encode r).length) := by
    simp only [OracleBatch.context_encode] at ha
    exact ha
  have run := OracleBatch.run_trace (pre d).machine (post d) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,run⟩
  have ht₁ := ha'.steps_le_m
  have ht₂ := hb'.steps_le_m
  have hp := (pre d).outputBound.length_le r
  have hd := answered_length d r
  have hh := OracleBatch.overhead_le oracle
    ((queries d r).map queryEncoding.encode)
    (codeEncoding.encode (code d r))
  rw [OracleBatch.context_encode] at hp
  change (OracleBatch.word
    ((queries d r).map queryEncoding.encode)
    (codeEncoding.encode (code d r))).length ≤
    (pre d).outputBound.bound.eval ((inputEncoding d).encode r).length at hp
  rw [← answered_eq, OracleBatch.context_encode] at hd
  simp only [OracleBatch.answers] at hd
  change (OracleBatch.word
    (((queries d r).map (T.evaluate F)).map F.encoding.encode)
    (codeEncoding.encode (code d r))).length ≤
    (transcriptBound d).eval ((inputEncoding d).encode r).length at hd
  have hdq : (OracleBatch.word
      (((queries d r).map queryEncoding.encode).map oracle)
      (codeEncoding.encode (code d r))).length ≤
      (transcriptBound d).eval ((inputEncoding d).encode r).length := by
    simpa only [hm] using hd
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  omega

/-- This is the full actual finite-machine reduction to the original Γ oracle.
Its source function is explicit interpolation of actual emitted queries. The
source-paper identification is supplied separately by FieldSource.recovery. -/
def reduction : PolyTimeOracleReduction (inputEncoding d) F.encoding
    queryEncoding F.encoding (interpolatedValue d) (T.evaluate F) where
  machine := machine d
  time := timePolynomial d
  correct oracle ho r := by
    let hex := execution d oracle ho r
    exact {
      steps := hex.choose
      evals_in_steps := hex.choose_spec.2.run
      steps_le_m := hex.choose_spec.1 }

theorem exact_calls_and_primitive (oracle : List Bool → List Bool)
    (ho : RepresentsOracle queryEncoding F.encoding (T.evaluate F) oracle)
    (r : Input d) :
    ∃ t ≤ (timePolynomial d).eval ((inputEncoding d).encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount (machine d) oracle
        ((machine d).init ((inputEncoding d).encode r)) t = count d r+1 ∧
      OracleBatch.primitiveCount (machine d) oracle
        ((machine d).init ((inputEncoding d).encode r)) t ≤
        (Polynomial.C (machine d).primitiveBudget * timePolynomial d).eval
          ((inputEncoding d).encode r).length := by
  obtain ⟨t,ht,hr⟩ := execution d oracle ho r
  refine ⟨t,ht,?_,?_⟩
  · simpa only [List.length_map, queries, Q.query_count] using hr.count
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [Polynomial.eval_mul, Polynomial.eval_C] using
        Nat.mul_le_mul_left (machine d).primitiveBudget ht)

end
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainMachine
