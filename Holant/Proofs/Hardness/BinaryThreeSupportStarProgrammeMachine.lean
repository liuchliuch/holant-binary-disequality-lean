import Holant.Proofs.Hardness.BinaryThreeSupportStarProgrammeMachineBase

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarMachine
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open Holant.Complexity.BinaryInterpolation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ} (F : FixedField K n)

theorem answered_length (r : C.Raw) :
    ((answerEncoding F).encode (answered (K:=K) r)).length≤
      (transcriptBound F).eval (C.encoding.encode r).length := by
  rw [←answered_eq]
  exact OracleBatch.decoder_length_le pre (outputBound F) r

theorem component_lengths (r : C.Raw) :
    let L := (transcriptBound F).eval (C.encoding.encode r).length
    (codeEncoding.encode (code r)).length≤L ∧
      ((stackEncoding F.encoding).encode (List.ofFn (values r))).length≤L ∧
      ((pairEncoding codeEncoding (stackEncoding F.encoding)).encode
        (code r,List.ofFn (values r))).length≤3*L+1 := by
  have h := answered_length F r
  change ((pairEncoding (stackEncoding F.encoding) codeEncoding).encode
    (List.ofFn (values r),code r)).length≤_ at h
  rw [pairEncoding_length] at h
  dsimp only [Prod.fst,Prod.snd] at h
  dsimp only
  rw [pairEncoding_length]
  dsimp only [Prod.fst,Prod.snd]
  omega

theorem certified (r : C.Raw) :
    let N := (C.encoding.encode r).length
    Certified F.encoding (RingFormulaMachine.coefficients F (literalCoordinates F))
      ((widthPolynomial F).eval N) (structuralPolynomial.eval N)
      (code r) (List.ofFn (values r)) [(resultPair r).1,(resultPair r).2]
      (P.trace (count r) (values r)) := by
  dsimp only
  let N := (C.encoding.encode r).length
  let B := structuralPolynomial.eval N
  let Y := answerBudget.eval N
  have hq := structural_bounds r
  have hu := decoded_unit F
  have hy := sample_answers_bound F r
  have hl := literal_bound F
  have hcoeff : RingFormulaMachine.coefficients F (literalCoordinates F)=P.coefficients (K:=K) := by
    funext a
    exact F.decode.apply_symm_apply _
  rw [hcoeff,width_eval]
  apply certified_of_run F.encoding P.coefficients (ArithmeticSize.bitBound F (base F) B) B
  · intro a
    exact ((hl a).mono (.inl 4) hu hq.1).encoded_length_le F (base F)
  · exact (ArithmeticSize.Bound.zero (.inl 4) B).encoded_length_le F (base F)
  · exact (ArithmeticSize.Bound.one.mono (.inl 4) hu (Nat.zero_le B)).encoded_length_le F (base F)
  · exact P.reference_run (count r) (values r)
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact ((hy i).mono (.inl 4) hu hq.2.1).encoded_length_le F (base F)
  · intro x hx
    have ht := P.trace_bound F (base F) (.inl 4) hu hl (count r) Y (values r) hy x hx
    exact (ht.mono (.inl 4) hu hq.2.2.1).encoded_length_le F (base F)
  · simpa using hq.2.2.2

theorem result_length (r : C.Raw) :
    ((DivisionStack.encoding F).encode (resultPair r)).length ≤
      4*(widthPolynomial F).eval ((C.encoding).encode r).length+5 := by
  have h := (certified F r).output_width
  have h₁ := h (resultPair r).1 (by simp)
  have h₂ := h (resultPair r).2 (by simp)
  rw [DivisionStack.encoding_length]
  omega

def interpreter_outputs (r : C.Raw) :
    TM2OutputsInTime (interpreter F).computer
      ((pairEncoding codeEncoding (stackEncoding F.encoding)).encode
        (code r,List.ofFn (values r)))
      (some ((DivisionStack.encoding F).encode (resultPair r)))
      ((interpreterTime F).eval ((C.encoding).encode r).length) := by
  let hex := StackInputInterpreter.execute WeightCompiler.labels labelBound F.encoding _
    (literals F) (fieldProviders F) (RingFormulaMachine.label_le WeightCompiler.labels) (certified F r)
  let t := hex.choose
  have ht := hex.choose_spec.1
  have hr := hex.choose_spec.2
  refine { steps := t, evals_in_steps := hr, steps_le_m := ?_ }
  have hlen := component_lengths F r
  have hcode := hlen.1
  change ((StackProgram.codeEncoding WeightCompiler.labels).encode (code r)).length ≤ _ at hcode
  have hc := code_length_bound r
  have hm := Nat.mul_le_mul_right
    ((instructionPolynomial F).eval ((C.encoding).encode r).length) hc
  rw [instruction_eval] at hm
  simp only [interpreterTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, instruction_eval]
  omega

def arithmetic_outputs (r : C.Raw) :
    TM2OutputsInTime (arithmetic F).computer
      ((pairEncoding codeEncoding (stackEncoding F.encoding)).encode
        (code r,List.ofFn (values r)))
      (some (F.encoding.encode (interpolatedValue r)))
      ((arithmeticTime F).eval ((C.encoding).encode r).length) := by
  let first := interpreter_outputs F r
  let last := (DivisionStack.computes F).outputs (resultPair r)
  let all := BinaryCompose.Machine.compose_correct (interpreter F) (DivisionStack.computes F).machine
    _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  have hs := result_length F r
  have hd := natPolynomial_eval_mono (DivisionStack.computes F).time hs
  simp only [arithmeticTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_comp]
  omega

def post_outputs (r : C.Raw) :
    TM2OutputsInTime (post F).computer ((answerEncoding F).encode (answered r))
      (some (F.encoding.encode (interpolatedValue r)))
      ((postTime F).eval ((C.encoding).encode r).length) := by
  let first := (reorder F).outputs (answered r)
  let last := arithmetic_outputs F r
  let all := BinaryCompose.Machine.compose_correct (reorder F).machine (arithmetic F)
    _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  dsimp only [answered, Prod.fst, Prod.snd] at ht
  have hs := (component_lengths F r).2.2
  have hr := natPolynomial_eval_mono (reorder F).time (answered_length F r)
  dsimp only [answered] at hr
  simp only [postTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_comp]
  omega

/-- A concrete bounded execution and the exact ordered Γ-query transcript.
Pre/post machines make no oracle calls; the collector makes precisely these. -/
theorem execution_agree (oracle : List Bool → List Bool) (r : C.Raw)
    (ho : ∀q∈Q.queries r,oracle (C.encoding.encode q)=F.encoding.encode (targetValue q)) :
    ∃ t ≤ (timePolynomial F).eval ((C.encoding).encode r).length,
      OracleBatch.RunsTrace (machine F) oracle
        ((machine F).init ((C.encoding).encode r))
        ((machine F).output (F.encoding.encode (interpolatedValue r))) t
        ((Q.queries r).map C.encoding.encode) := by
  have hm : ((Q.queries r).map C.encoding.encode).map oracle=
      ((Q.queries r).map targetValue).map F.encoding.encode := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro q hq
    exact ho q hq
  have ha := (pre).outputs r
  have hb := post_outputs F r
  rw [← answered_eq, OracleBatch.context_encode] at hb
  have hb' : TM2OutputsInTime (post F).computer
      (OracleBatch.word (((Q.queries r).map C.encoding.encode).map oracle)
        (codeEncoding.encode (code r)))
      (some (F.encoding.encode (interpolatedValue r)))
      ((postTime F).eval ((C.encoding).encode r).length) := by
    simp only [OracleBatch.answers] at hb
    rw [hm]
    exact hb
  have ha' : TM2OutputsInTime (pre).machine.computer ((C.encoding).encode r)
      (some (OracleBatch.word ((Q.queries r).map C.encoding.encode)
        (codeEncoding.encode (code r)))) ((pre).time.eval ((C.encoding).encode r).length) := by
    simp only [OracleBatch.context_encode] at ha
    exact ha
  have run := OracleBatch.run_trace (pre).machine (post F) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,run⟩
  have ht₁ := ha'.steps_le_m
  have ht₂ := hb'.steps_le_m
  have hp := (pre).outputBound.length_le r
  have hd := answered_length F r
  have hh := OracleBatch.overhead_le oracle
    ((Q.queries r).map C.encoding.encode)
    (codeEncoding.encode (code r))
  rw [OracleBatch.context_encode] at hp
  change (OracleBatch.word
    ((Q.queries r).map C.encoding.encode)
    (codeEncoding.encode (code r))).length ≤
    (pre).outputBound.bound.eval ((C.encoding).encode r).length at hp
  rw [← answered_eq, OracleBatch.context_encode] at hd
  simp only [OracleBatch.answers] at hd
  change (OracleBatch.word
    (((Q.queries r).map (targetValue)).map F.encoding.encode)
    (codeEncoding.encode (code r))).length ≤
    (transcriptBound F).eval ((C.encoding).encode r).length at hd
  have hdq : (OracleBatch.word
      (((Q.queries r).map C.encoding.encode).map oracle)
      (codeEncoding.encode (code r))).length ≤
      (transcriptBound F).eval ((C.encoding).encode r).length := by
    simpa only [hm] using hd
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  omega

theorem execution (oracle : List Bool→List Bool)
    (ho : RepresentsOracle C.encoding F.encoding targetValue oracle) (r : C.Raw) :
    ∃t≤(timePolynomial F).eval (C.encoding.encode r).length,
      OracleBatch.RunsTrace (machine F) oracle ((machine F).init (C.encoding.encode r))
        ((machine F).output (F.encoding.encode (interpolatedValue r))) t
        ((Q.queries r).map C.encoding.encode) :=
  execution_agree F oracle r (fun q _=>ho q)

/-- The actual finite-machine reduction to the unsigned NAND2 graph oracle.
Its source function is explicit interpolation of actual emitted queries;
`interpolatedValue_eq` identifies it with the signed graph sum. -/
def reduction : PolyTimeOracleReduction (C.encoding) F.encoding
    C.encoding F.encoding (interpolatedValue (K:=K)) (targetValue) where
  machine := machine F
  time := timePolynomial F
  correct oracle ho r := by
    let hex := execution F oracle ho r
    exact {
      steps := hex.choose
      evals_in_steps := hex.choose_spec.2.run
      steps_le_m := hex.choose_spec.1 }


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarMachine
