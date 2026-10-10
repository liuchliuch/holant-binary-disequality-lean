import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Postprocess
import Holant.Complexity.OracleBatch.ReductionTrace
import Holant.Proofs.Algorithms.TraceQueryControl


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Source
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {d : ℕ} (F : FixedField ℚ d)

abbrev codeEncoding := Holant.OneHot.StackProgram.codeEncoding WeightCompiler.labels
abbrev answerEncoding := OracleBatch.contextEncoding F.encoding codeEncoding
def pre : Computes encoding (OracleBatch.contextEncoding unitEncoding codeEncoding)
    (fun g : Input => (queries g,Postprocess.reference g.val.1)) :=
  pairComputes Queries.computes (Queries.size.andThen Postprocess.computes)

/-- Output-size bound for EVERY actual unit multigraph, including empty and
no-matching graphs. Count is bounded from its real edge-selection functions.
-/
def targetOutput : PolynomialOutputBound unitEncoding F.encoding unitValue where
  bound := (RingFormulaMachine.widthPolynomial F (Postprocess.coordinates F)).comp (Polynomial.X^2)
  length_le g := by
    have h := (Postprocess.count_bound F (unitCount g) ((unitEncoding.encode g).length^2)
      (unit_answer_bound g)).encoded_length_le F (Postprocess.coordinates F)
    simpa only [unitValue,Polynomial.eval_comp,Polynomial.eval_pow,Polynomial.eval_X,
      RingFormulaMachine.width_eval] using h

def values (g : Input) (i : Fin (g.val.1+1)) : ℚ := unitValue (query g i.val)
def answered (g : Input) : List ℚ × Code (Fin 4) := (List.ofFn (values g),Postprocess.reference g.val.1)
theorem answer_order (g : Input) : (queries g).map unitValue=List.ofFn (values g) := by
  simp only [queries,List.map_map,List.ofFn_eq_map,values,Function.comp_def]
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.map_map,Function.comp_def]
  rfl
theorem answered_eq (g : Input) : OracleBatch.answers unitValue (queries g,Postprocess.reference g.val.1)=answered g := by
  exact Prod.ext (answer_order g) rfl

def reorder : Computes (answerEncoding F) (pairEncoding codeEncoding (stackEncoding F.encoding))
    (fun z : List ℚ × Code (Fin 4) => (z.2,z.1)) :=
  Wiring.swapComputes (framedListEncoding F.encoding) codeEncoding
def arithmetic := (Postprocess.interpreter F).compose (DivisionStack.computes F).machine
def post := (reorder F).machine.compose (arithmetic F)
def machine := OracleBatch.machine pre.machine (post F)
def transcriptBound := OracleBatch.decoderBound pre (targetOutput F)
def structuralPolynomial := Postprocess.structuralPolynomial answerBudget
def widthPolynomial := (RingFormulaMachine.widthPolynomial F (Postprocess.coordinates F)).comp structuralPolynomial
def heightPolynomial : Polynomial ℕ := Polynomial.X+1+pre.outputBound.bound
def instructionPolynomial : Polynomial ℕ :=
  let W := widthPolynomial F
  let H := heightPolynomial
  let P := fieldProviders F
  P.add.time.comp (3*W+1)+P.mul.time.comp (3*W+1)+14*W+18+
    (2*W+4)*Polynomial.C (2^18)+3+Polynomial.C (2*(RingFormulaMachine.labelBound WeightCompiler.labels+6))+
    4*((2*W+2)*H+1)+9
def interpreterTime : Polynomial ℕ :=
  4*transcriptBound F+6+pre.outputBound.bound*instructionPolynomial F
def arithmeticTime : Polynomial ℕ := interpreterTime F+8*widthPolynomial F+12+
  (DivisionStack.computes F).time.comp (4*widthPolynomial F+5)
def postTime : Polynomial ℕ :=
  (reorder F).time.comp (transcriptBound F)+6*transcriptBound F+4+arithmeticTime F
def timePolynomial : Polynomial ℕ :=
  pre.time+16*(pre.outputBound.bound+transcriptBound F+1)+postTime F

theorem instruction_eval (N : ℕ) : (instructionPolynomial F).eval N=
    Interpreter.instructionBound (RingFormulaMachine.labelBound WeightCompiler.labels)
      F.encoding (fieldProviders F) ((widthPolynomial F).eval N) (heightPolynomial.eval N) := by
  simp [instructionPolynomial,Interpreter.instructionBound,Kernels.timeBound]

theorem sample_bound (g : Input) (i : Fin (g.val.1+1)) :
    ArithmeticSize.Bound (fun b => F.decode (Postprocess.coordinates F b))
      (answerBudget.eval (encoding.encode g).length) (values g i) :=
  Postprocess.count_bound F _ _ (sample_count_bound g i)

theorem code_bytes (g : Input) : (codeEncoding.encode (Postprocess.reference g.val.1)).length≤
    pre.outputBound.bound.eval (encoding.encode g).length := by
  have h := pre.outputBound.length_le g
  simp only [answerEncoding,OracleBatch.contextEncoding,answered,pairEncoding_length] at h
  omega
theorem code_length (g : Input) : (Postprocess.reference g.val.1).length≤
    pre.outputBound.bound.eval (encoding.encode g).length := by
  have h := framedListEncoding_length_lower (opEncoding WeightCompiler.labels) (Postprocess.reference g.val.1)
  change 2*(Postprocess.reference g.val.1).length+1≤(codeEncoding.encode (Postprocess.reference g.val.1)).length at h
  exact (by omega : (Postprocess.reference g.val.1).length≤(codeEncoding.encode (Postprocess.reference g.val.1)).length).trans (code_bytes g)

private theorem widen {A V : Type} [CommSemiring V] {e : Encoding V Bool} {c : A → V}
    {W H W' H' : ℕ} {code : Code A} {s out trace : List V}
    (h : Certified e c W H code s out trace) (hw : W≤W') (hh : H≤H') :
    Certified e c W' H' code s out trace := by
  induction h with
  | nil s width height => exact .nil s (fun x hx => (width x hx).trans hw) (height.trans hh)
  | cons op code s mid out event trace exec width height next ih =>
    exact .cons op code s mid out event trace exec (fun x hx => (width x hx).trans hw) (height.trans hh) ih

def certified (g : Input) :
    Certified F.encoding (RingFormulaMachine.coefficients F (Postprocess.coordinates F))
      ((widthPolynomial F).eval (encoding.encode g).length)
      (heightPolynomial.eval (encoding.encode g).length)
      (Postprocess.reference g.val.1) (List.ofFn (values g))
      [(Postprocess.resultPair g.val.1 (values g)).1,(Postprocess.resultPair g.val.1 (values g)).2]
      (Postprocess.trace g.val.1 (values g)) := by
  let N := (encoding.encode g).length
  let Y := answerBudget.eval N
  have hn := (input_counts g).1
  have hs : Postprocess.structural g.val.1 Y≤structuralPolynomial.eval N := by
    simpa only [structuralPolynomial,Postprocess.structural_eval,Polynomial.eval_C,Y] using
      natPolynomial_eval_mono (Postprocess.structuralPolynomial (Polynomial.C Y)) hn
  apply widen (Postprocess.certified F g.val.1 Y (values g) (sample_bound F g))
  · change ArithmeticSize.bitBound F (Postprocess.coordinates F) (Postprocess.structural g.val.1 Y)≤_
    simpa only [widthPolynomial,Polynomial.eval_comp,RingFormulaMachine.width_eval] using
      natPolynomial_eval_mono (RingFormulaMachine.widthPolynomial F (Postprocess.coordinates F)) hs
  · have hc := code_length g
    simp only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    omega

theorem result_bytes (g : Input) :
    ((DivisionStack.encoding F).encode (Postprocess.resultPair g.val.1 (values g))).length≤
      4*(widthPolynomial F).eval (encoding.encode g).length+5 := by
  have h := (certified F g).output_width
  have h1 := h (Postprocess.resultPair g.val.1 (values g)).1 (by simp)
  have h2 := h (Postprocess.resultPair g.val.1 (values g)).2 (by simp)
  rw [DivisionStack.encoding_length]
  omega

theorem answered_bytes (g : Input) : ((answerEncoding F).encode (answered g)).length≤
    (transcriptBound F).eval (encoding.encode g).length := by
  simpa only [answered_eq,answerEncoding,transcriptBound] using OracleBatch.decoder_length_le pre (targetOutput F) g

theorem component_bytes (g : Input) :
    let L := (transcriptBound F).eval (encoding.encode g).length
    (codeEncoding.encode (Postprocess.reference g.val.1)).length≤L ∧
      ((stackEncoding F.encoding).encode (List.ofFn (values g))).length≤L ∧
      ((pairEncoding codeEncoding (stackEncoding F.encoding)).encode
        (Postprocess.reference g.val.1,List.ofFn (values g))).length≤3*L+1 := by
  have h := answered_bytes F g
  simp only [answerEncoding,OracleBatch.contextEncoding,answered,pairEncoding_length] at h
  dsimp only
  rw [pairEncoding_length]
  simp only [stackEncoding]
  omega

def interpreter_outputs (g : Input) : TM2OutputsInTime (Postprocess.interpreter F).computer
    ((pairEncoding codeEncoding (stackEncoding F.encoding)).encode
      (Postprocess.reference g.val.1,List.ofFn (values g)))
    (some ((DivisionStack.encoding F).encode (Postprocess.resultPair g.val.1 (values g))))
    ((interpreterTime F).eval (encoding.encode g).length) := by
  have execution := StackInputInterpreter.execute WeightCompiler.labels
    (RingFormulaMachine.labelBound WeightCompiler.labels) F.encoding _
    (RingFormulaMachine.literals F (Postprocess.coordinates F)) (fieldProviders F)
    (RingFormulaMachine.label_le WeightCompiler.labels) (certified F g)
  let t := Classical.choose execution
  have ht := (Classical.choose_spec execution).1
  have hr := (Classical.choose_spec execution).2
  refine { steps := t, evals_in_steps := hr, steps_le_m := ?_ }
  have hlen := component_bytes F g
  change t ≤ _ at ht
  dsimp only [codeEncoding] at hlen
  have hc := code_length g
  have hm := Nat.mul_le_mul_right ((instructionPolynomial F).eval (encoding.encode g).length) hc
  rw [instruction_eval] at hm
  simp only [interpreterTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,instruction_eval]
  omega

theorem result_signed (g : Input) :
    (Postprocess.resultPair g.val.1 (values g)).1/(Postprocess.resultPair g.val.1 (values g)).2=signedValue g := by
  rw [Postprocess.result_value,← answer_order]
  exact recovery g

def arithmetic_outputs (g : Input) : TM2OutputsInTime (arithmetic F).computer
    ((pairEncoding codeEncoding (stackEncoding F.encoding)).encode
      (Postprocess.reference g.val.1,List.ofFn (values g)))
    (some (F.encoding.encode (signedValue g))) ((arithmeticTime F).eval (encoding.encode g).length) := by
  let first := interpreter_outputs F g
  let last := (DivisionStack.computes F).outputs (Postprocess.resultPair g.val.1 (values g))
  have all := BinaryCompose.Machine.compose_correct (Postprocess.interpreter F)
    (DivisionStack.computes F).machine _ _ _ _ _ first last
  rw [result_signed] at all
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  have hl := result_bytes F g
  have hd := natPolynomial_eval_mono (DivisionStack.computes F).time hl
  simp only [arithmeticTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

def post_outputs (g : Input) : TM2OutputsInTime (post F).computer
    ((answerEncoding F).encode (answered g)) (some (F.encoding.encode (signedValue g)))
      ((postTime F).eval (encoding.encode g).length) := by
  let first := (reorder F).outputs (answered g)
  let last := arithmetic_outputs F g
  have all := BinaryCompose.Machine.compose_correct (reorder F).machine (arithmetic F) _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  have hl := component_bytes F g
  have hd := natPolynomial_eval_mono (reorder F).time (answered_bytes F g)
  have hlast := last.steps_le_m
  simp only [answered] at ht hd
  simp only [postTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle unitEncoding F.encoding unitValue oracle) (g : Input) :
    ∃ t≤(timePolynomial F).eval (encoding.encode g).length,
      OracleBatch.RunsTrace (machine F) oracle ((machine F).init (encoding.encode g))
        ((machine F).output (F.encoding.encode (signedValue g))) t ((queries g).map unitEncoding.encode) := by
  have hm := OracleBatch.oracle_encoded_list oracle ho (queries g)
  have ha := pre.outputs g
  have hb := post_outputs F g
  have ha' : TM2OutputsInTime pre.machine.computer (encoding.encode g)
      (some (OracleBatch.word ((queries g).map unitEncoding.encode) (codeEncoding.encode (Postprocess.reference g.val.1))))
      (pre.time.eval (encoding.encode g).length) := by simpa only [OracleBatch.context_encode] using ha
  have hb' : TM2OutputsInTime (post F).computer
      (OracleBatch.word (((queries g).map unitEncoding.encode).map oracle) (codeEncoding.encode (Postprocess.reference g.val.1)))
      (some (F.encoding.encode (signedValue g))) ((postTime F).eval (encoding.encode g).length) := by
    simpa only [OracleBatch.context_encode,answered,← answer_order,hm] using hb
  have trace := OracleBatch.run_trace pre.machine (post F) oracle (encoding.encode g)
    ((queries g).map unitEncoding.encode) (codeEncoding.encode (Postprocess.reference g.val.1))
    (F.encoding.encode (signedValue g)) ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,trace⟩
  have hp := pre.outputBound.length_le g
  have hd := OracleBatch.decoder_length_le pre (targetOutput F) g
  have hc := OracleBatch.overhead_le oracle ((queries g).map unitEncoding.encode)
    (codeEncoding.encode (Postprocess.reference g.val.1))
  have hat := ha'.steps_le_m
  have hbt := hb'.steps_le_m
  rw [OracleBatch.context_encode] at hp
  simp only [OracleBatch.context_encode,OracleBatch.answers] at hd
  simp only [OracleBatch.overhead,hm] at hc
  have hdq : (OracleBatch.word (((queries g).map unitEncoding.encode).map oracle)
      (codeEncoding.encode (Postprocess.reference g.val.1))).length ≤
      (transcriptBound F).eval (encoding.encode g).length := by
    simpa only [hm,transcriptBound] using hd
  dsimp only at hp
  change _ ≤ (transcriptBound F).eval (encoding.encode g).length at hd
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

def reduction : PolyTimeOracleReduction encoding F.encoding unitEncoding F.encoding signedValue unitValue where
  machine := machine F
  time := timePolynomial F
  correct oracle ho g :=
    let h := execution F oracle ho g
    { steps := h.choose, evals_in_steps := h.choose_spec.2.run, steps_le_m := h.choose_spec.1 }

def controlled : LengthControlledOracleReduction encoding F.encoding unitEncoding F.encoding signedValue unitValue where
  reduction := reduction F
  targetOutput := targetOutput F
  queryBound := pre.outputBound.bound
  safeQuery oracle ho g t c hr hq := by
    obtain ⟨_,_,trace⟩ := execution F oracle ho g
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member trace t c hr hq
    obtain ⟨q,_,he⟩ := List.mem_map.mp hm
    refine ⟨q,he.symm,?_⟩
    exact (OracleBatch.member_length_le _ _ hm).trans (OracleBatch.query_context_length_le pre g).1

theorem exact_calls (oracle : List Bool → List Bool)
    (ho : RepresentsOracle unitEncoding F.encoding unitValue oracle) (g : Input) :
    ∃ t≤(timePolynomial F).eval (encoding.encode g).length,
      UniversalPairReduction.ThreeQuery.queryCount (machine F) oracle ((machine F).init (encoding.encode g)) t=g.val.1+1 ∧
      OracleBatch.primitiveCount (machine F) oracle ((machine F).init (encoding.encode g)) t≤
        (Polynomial.C (machine F).primitiveBudget*timePolynomial F).eval (encoding.encode g).length := by
  obtain ⟨t,ht,trace⟩ := execution F oracle ho g
  refine ⟨t,ht,?_,?_⟩
  · simpa only [List.length_map,number_queries] using trace.count
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [Polynomial.eval_mul,Polynomial.eval_C] using Nat.mul_le_mul_left (machine F).primitiveBudget ht)

theorem same_machine : (controlled F).reduction.machine=machine F := rfl
theorem same_time : (controlled F).reduction.time=timePolynomial F := rfl

private theorem singleton_decode_one :
    (Module.Basis.singleton (Fin 1) ℚ).equivFun.symm (fun _ => 1)=(1 : ℚ) := by
  have h : (Module.Basis.singleton (Fin 1) ℚ).equivFun (1 : ℚ)=(fun _ => 1) := by
    funext i
    simp [Module.Basis.equivFun_apply]
  rw [← h]
  exact LinearEquiv.symm_apply_apply _ _

/-- A literal rational codec presentation, with unit and multiplication
tables both [1]. This is manufactured here; it is not a caller input. -/
def rationalField : FixedField ℚ 1 where
  basis := Module.Basis.singleton (Fin 1) ℚ
  unitCode := fun _ => 1
  mulTable := fun _ _ _ => 1
  unit_spec := singleton_decode_one
  mul_spec i j := by simpa only [Module.Basis.singleton_apply,one_mul] using singleton_decode_one

/-- Sole entry, with no field presentation, polynomial, correct-answer,
normalization, or reduction in the input. The source and target answer codecs
are this one fixed rational presentation; the target is a UNIT MULTIGRAPH.
-/
def source : LengthControlledOracleReduction encoding rationalField.encoding
    unitEncoding rationalField.encoding signedValue unitValue := controlled rationalField

theorem source_machine : source.reduction.machine=machine rationalField := rfl
theorem source_time : source.reduction.time=timePolynomial rationalField := rfl

theorem source_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle unitEncoding rationalField.encoding unitValue oracle)
    (g : Input) (t : ℕ) (c : source.reduction.machine.Cfg)
    (ht : t≤source.reduction.time.eval (encoding.encode g).length)
    (hr : source.reduction.machine.run oracle (encoding.encode g) t=some c) :
    stackSize c.stk≤source.sourceOutputPolynomial.eval (encoding.encode g).length := by
  have h := source.run_stackSize_le oracle ho g t c hr
  exact h.trans (by
    simpa only [LengthControlledOracleReduction.sourceOutputPolynomial,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right (source.reduction.machine.primitiveBudget+
        (source.targetOutput.bound.comp source.queryBound).eval (encoding.encode g).length) ht)
          (encoding.encode g).length)

theorem source_output_bytes (g : Input) : (rationalField.encoding.encode (signedValue g)).length≤
    source.sourceOutputBound.bound.eval (encoding.encode g).length := source.sourceOutputBound.length_le g

end
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Source
