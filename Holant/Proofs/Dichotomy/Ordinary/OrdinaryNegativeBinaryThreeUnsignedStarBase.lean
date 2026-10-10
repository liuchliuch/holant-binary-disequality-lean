import Holant.Proofs.Hardness.BinaryThreeSupportStarProgrammeBounds
import Holant.Proofs.Hardness.BinaryCSPProgrammeValue
import Holant.Complexity.OracleBatch.ReductionTrace
import Holant.Complexity.BinaryInterpolation.DivisionStack

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeBinaryThreeUnsignedStarMachine
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open Holant.Complexity.BinaryInterpolation
open scoped BigOperators
namespace Q
export BinaryCSPProgrammeStars (queries queriesComputes expand)
end Q
namespace C
export BinaryCSPProgrammeCore (Raw encoding signCountComputes)
end C
namespace V
export BinaryCSPProgrammeValue (value coordinates base decode_coordinates base_unit base_minus
  answer_bound counts_le_bytes targetOutput)
end V
namespace P
export BinaryThreeSupportStarProgramme (reference computes quartic quartic_eval weightSize codeBound
  resultPair trace reference_run trace_bound budget coefficients reference_length_le)
end P
namespace G
export BinaryThreeSupportGates (implication)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ} (F : FixedField K n)

abbrev codeEncoding := Holant.OneHot.StackProgram.codeEncoding WeightCompiler.labels
abbrev answerEncoding := OracleBatch.contextEncoding F.encoding codeEncoding
def targetValue : C.Raw→K := V.value (G.implication (K:=K))
def count (r : C.Raw) : ℕ := r.signs.length
def code (r : C.Raw) := P.reference (count r)
def values (r : C.Raw) (i : Fin (count r+1)) : K := targetValue (Q.expand r i.val)
def resultPair (r : C.Raw) : K×K := P.resultPair (count r) (values r)
def interpolatedValue (r : C.Raw) : K := (resultPair r).1/(resultPair r).2
def preprocessing (r : C.Raw) := (Q.queries r,code r)
def pre : Computes C.encoding (OracleBatch.contextEncoding C.encoding codeEncoding) preprocessing :=
  pairComputes Q.queriesComputes (C.signCountComputes.andThen P.computes)
def answered (r : C.Raw) : List K×Holant.OneHot.StackProgram.Code (Fin 4) :=
  (List.ofFn (values r),code r)

theorem answer_order (r : C.Raw) : (Q.queries r).map targetValue=List.ofFn (values (K:=K) r) := by
  apply List.ext_getElem
  · simp [Q.queries,count]
  · intro i hi hj
    simp only [Q.queries,List.getElem_map,List.getElem_range,List.getElem_ofFn,values]

theorem answered_eq (r : C.Raw) : OracleBatch.answers targetValue (preprocessing r)=answered (K:=K) r := by
  apply Prod.ext
  · exact answer_order r
  · rfl

def reorder : Computes (answerEncoding F) (pairEncoding codeEncoding (stackEncoding F.encoding))
    (fun z : List K×Holant.OneHot.StackProgram.Code (Fin 4)=>(z.2,z.1)) :=
  Wiring.swapComputes (framedListEncoding F.encoding) codeEncoding
abbrev literalCoordinates := fun i : Fin 4=>F.decode.symm (P.coefficients (K:=K) i)
abbrev literals := RingFormulaMachine.literals F (literalCoordinates F)
abbrev labelBound := RingFormulaMachine.labelBound WeightCompiler.labels
abbrev interpreter := StackInputInterpreter.machine (Kernels.machine (literals F) (fieldProviders F))
  WeightCompiler.labels labelBound
abbrev arithmetic := (interpreter F).compose (DivisionStack.computes F).machine
abbrev post := (reorder F).machine.compose (arithmetic F)
abbrev machine := OracleBatch.machine pre.machine (post F)
abbrev base := V.coordinates F 1 2 (-1) (G.implication (K:=K))
abbrev outputBound := V.targetOutput F 1 2 (-1) (G.implication (K:=K))
abbrev transcriptBound := OracleBatch.decoderBound pre (outputBound F)
def answerBudget : Polynomial ℕ := 2*Q.queriesComputes.outputBound.bound
def structuralPolynomial : Polynomial ℕ :=
  (Polynomial.X+1)*(answerBudget+P.quartic+1)+P.quartic+Polynomial.X+1
def widthPolynomial : Polynomial ℕ := (RingFormulaMachine.widthPolynomial F (base F)).comp structuralPolynomial
def instructionPolynomial : Polynomial ℕ :=
  let W := widthPolynomial F
  let H := structuralPolynomial
  let A := fieldProviders F
  A.add.time.comp (3*W+1)+A.mul.time.comp (3*W+1)+14*W+18+
    (2*W+4)*Polynomial.C (2^18)+3+Polynomial.C (2*(labelBound+6))+4*((2*W+2)*H+1)+9
def interpreterTime : Polynomial ℕ := 4*transcriptBound F+6+P.quartic*instructionPolynomial F
def arithmeticTime : Polynomial ℕ := interpreterTime F+8*widthPolynomial F+12+
  (DivisionStack.computes F).time.comp (4*widthPolynomial F+5)
def postTime : Polynomial ℕ := (reorder F).time.comp (transcriptBound F)+6*transcriptBound F+4+arithmeticTime F
def timePolynomial : Polynomial ℕ := pre.time+16*(pre.outputBound.bound+transcriptBound F+1)+postTime F

@[simp] theorem width_eval (N : ℕ) : (widthPolynomial F).eval N=
    ArithmeticSize.bitBound F (base F) (structuralPolynomial.eval N) := by simp [widthPolynomial]
@[simp] theorem instruction_eval (N : ℕ) : (instructionPolynomial F).eval N=
    Interpreter.instructionBound labelBound F.encoding (fieldProviders F)
      ((widthPolynomial F).eval N) (structuralPolynomial.eval N) := by
  simp [instructionPolynomial,Interpreter.instructionBound,Kernels.timeBound]

theorem count_le_input_length (r : C.Raw) : count r≤(C.encoding.encode r).length := by
  have h := OracleBatch.list_length_le (r.signs.map encodingNatBool.encode)
  rw [←OracleBatch.list_encode] at h
  simp only [List.length_map] at h
  change r.signs.length≤(BinaryCSPProgrammeCore.signsEncoding.encode r.signs).length at h
  change r.signs.length≤(BinaryCSPProgrammeCore.fieldsEncoding.encode r.fields).length
  simp only [BinaryCSPProgrammeCore.fieldsEncoding,pairEncoding_length,BinaryCSPProgrammeCore.Raw.fields]
  omega

theorem code_length_bound (r : C.Raw) : (code r).length≤P.quartic.eval (C.encoding.encode r).length := by
  have h := P.reference_length_le (count r)
  have hq : P.codeBound (count r)≤P.quartic.eval (count r) := by rw [P.quartic_eval]; omega
  exact h.trans (hq.trans (natPolynomial_eval_mono P.quartic (count_le_input_length r)))

theorem structural_bounds (r : C.Raw) :
    let N := (C.encoding.encode r).length
    let B := structuralPolynomial.eval N
    1≤B ∧ answerBudget.eval N≤B ∧ P.budget (count r) (answerBudget.eval N)≤B ∧
      count r+1+(code r).length≤B := by
  dsimp only
  have hm := count_le_input_length r
  have hw : P.weightSize (count r)≤P.quartic.eval (count r) := by
    rw [P.quartic_eval]
    unfold P.codeBound
    nlinarith
  have hw' := hw.trans (natPolynomial_eval_mono P.quartic hm)
  have hc := code_length_bound r
  simp only [structuralPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_one,P.budget]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · have ht := Nat.mul_le_mul (Nat.add_le_add_right hm 1)
      (Nat.add_le_add_right (Nat.add_le_add_left hw' (answerBudget.eval (C.encoding.encode r).length)) 1)
    nlinarith
  · nlinarith

theorem decoded_unit : F.decode (base F (.inl 4))=1 := by simp only [base,V.decode_coordinates,V.base_unit]
theorem literal_bound (i : Fin 4) :
    ArithmeticSize.Bound (fun a=>F.decode (base F a)) 1 (P.coefficients (K:=K) i) := by
  have h (j : BinaryCSPProgrammeValue.Label) :=
    ArithmeticSize.Bound.coefficient (coeff:=fun a=>F.decode (base F a)) j
  fin_cases i
  · simpa [base,V.decode_coordinates,V.base,P.coefficients,BinaryCSPProgrammeValue.literals] using h (.inl 4)
  · simpa [base,V.decode_coordinates,V.base,P.coefficients,BinaryCSPProgrammeValue.literals] using h (.inl 5)
  · simpa [base,V.decode_coordinates,V.base,P.coefficients,BinaryCSPProgrammeValue.literals] using h (.inl 3)
  · simpa [base,V.decode_coordinates,V.base,P.coefficients,BinaryCSPProgrammeValue.literals] using h (.inl 4)

theorem sample_answers_bound (r : C.Raw) (i : Fin (count r+1)) :
    ArithmeticSize.Bound (fun a=>F.decode (base F a)) (answerBudget.eval (C.encoding.encode r).length)
      (values (K:=K) r i) := by
  have hq : Q.expand r i.val∈Q.queries r := List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩
  have hm := OracleBatch.member_length_le ((Q.queries r).map C.encoding.encode)
    (C.encoding.encode (Q.expand r i.val)) (List.mem_map.mpr ⟨_,hq,rfl⟩)
  have hl := Q.queriesComputes.outputBound.length_le r
  rw [OracleBatch.list_encode] at hl
  have hs := V.counts_le_bytes (Q.expand r i.val)
  have hb := V.answer_bound (1 : K) 2 (-1) G.implication (Q.expand r i.val)
  have hb' : ArithmeticSize.Bound (fun a=>F.decode (base F a))
      ((Q.expand r i.val).edges.length+(Q.expand r i.val).variables) (values r i) := by
    simpa only [base,V.decode_coordinates,values,targetValue] using hb
  apply hb'.mono (.inl 4) (decoded_unit F)
  simp only [answerBudget,Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeBinaryThreeUnsignedStarMachine
