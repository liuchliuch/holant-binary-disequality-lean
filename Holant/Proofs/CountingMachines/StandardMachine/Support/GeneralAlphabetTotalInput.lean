import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetTotalInputCore
import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetSharpWitness
import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Standard

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetTotalInput
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing BooleanOpcode Reverse.Staging
variable (m : BinaryMachine) (T : Polynomial ℕ) (acceptControl : m.core.σ → Bool)
local instance : Fintype (m.core.Γ m.core.k₀) := m.alphabets m.core.k₀


def parsedWord (bits : List Bool) : List (Γ m) := (Parser.parse m T acceptControl bits).getD []
def totalCount (bits : List Bool) : ℕ :=
  (Parser.parse m T acceptControl bits).elim 0
    (GeneralAlphabetSharpWitness.boundedCount m T acceptControl (encodingList (Γ m)))
def accepts (p : List Bool×List Bool) : Bool :=
  (Parser.parse m T acceptControl p.1).isSome &&
    BooleanInputWitness.paddedAccept (originalWitness m T acceptControl)
      (parsedWord m T acceptControl p.1,p.2)
def dataEncoding := FixedFieldMachines.pairEncoding Frame.wordEncoding Frame.wordEncoding

/-- One total physical parser, consumed by two ordinary tape projections. -/
def parsed : Computes dataEncoding BooleanInputWitness.Guard.outputEncoding
    (fun p => (Parser.parse m T acceptControl p.1).map (codeWord m T acceptControl)) :=
  (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding).andThen
    (Parser.computes m T acceptControl)

def safeInput : Computes dataEncoding
    (BooleanInputWitness.inputEncoding (originalWitness m T acceptControl))
    (fun p => parsedWord m T acceptControl p.1) :=
  recode ((parsed m T acceptControl).andThen BooleanInputWitness.Routing.Prefix.computes)
    id (fun _ => rfl) (fun p => by
      cases h : Parser.parse m T acceptControl p.1 <;>
        simp [parsedWord,input_code,h,Frame.wordEncoding])

def validFlag : Computes dataEncoding encodingBoolBool
    (fun p => (Parser.parse m T acceptControl p.1).isSome) :=
  congrComputes ((parsed m T acceptControl).andThen BooleanInputWitness.Routing.Flag.computes)
    (fun p => by simp only [Function.comp_apply,Option.isSome_map])

def samePayload : Computes dataEncoding
    (BooleanInputWitness.Frontend.dataEncoding (originalWitness m T acceptControl))
    (fun p => (parsedWord m T acceptControl p.1,p.2)) :=
  pairComputes (safeInput m T acceptControl)
    (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding)

/-- The original verifier receives the same decoded original Γ input. A
malformed received word feeds the safe empty original input but its independently
produced physical flag forces false, even when m accepts the empty input. -/
def computes : Computes dataEncoding encodingBoolBool (accepts m T acceptControl) :=
  (pairComputes (validFlag m T acceptControl)
    ((samePayload m T acceptControl).andThen
      (BooleanInputWitness.Frontend.computes (originalWitness m T acceptControl)))).andThen
    BooleanInputWitness.Frontend.conjunction

def time : Polynomial ℕ :=
  3*Polynomial.X+3+(computes m T acceptControl).time.comp (2*Polynomial.X+1)

/-- Reuse the generic finite standard tagged-input parser. Its actual machine
preserves the Bool⊕Bool alphabet and routes the received word and candidate
bits to the above ALL-input finite programme. -/
def taggedVerifier {f : List Bool × List Bool → Bool}
    (c : Computes dataEncoding encodingBoolBool f) : PolyTime (encodingProd (encodingList Bool) (encodingList Bool))
    (taggedBoolEncoding Bool) f where
  tm := Tagged.computer c.machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3*Polynomial.X+3+c.time.comp (2*Polynomial.X+1)
  outputsFun p := by
    let run := c.outputs p
    have ha := Tagged.parse_exact c.machine p.1 p.2
    have hb := Tagged.lift_run c.machine _ _ run.steps run.evals_in_steps
    rw [Tagged.lift_halt] at hb
    refine {
      steps := run.steps+(3*p.1.length+2*p.2.length+3)
      evals_in_steps := ?_
      steps_le_m := ?_ }
    · change (Tagged.stepper c.machine)^[run.steps+(3*p.1.length+2*p.2.length+3)]
        (some (initList (Tagged.computer c.machine)
          (List.map id ((encodingProd (encodingList Bool) (encodingList Bool)).encode p)))) =
        some (haltList (Tagged.computer c.machine)
          (List.map id ((taggedBoolEncoding Bool).encode (f p))))
      simp only [List.map_id]
      change (Tagged.stepper c.machine)^[run.steps+(3*p.1.length+2*p.2.length+3)]
        (some (initList (Tagged.computer c.machine) (p.1.map Sum.inl++p.2.map Sum.inr))) = _
      rw [Function.iterate_add_apply]
      exact (congrArg ((Tagged.stepper c.machine)^[run.steps]) ha).trans
        (by simpa [dataEncoding,FixedFieldMachines.pairEncoding,Frame.wordEncoding,
          encodingBoolBool,taggedBoolEncoding,encodeBool] using hb)
    · have hh : (dataEncoding.encode p).length≤2*(p.1.length+p.2.length)+1 := by
        simp only [dataEncoding,FixedFieldMachines.pairEncoding_length,Frame.wordEncoding,id_eq]; omega
      have ht := natPolynomial_eval_mono c.time hh
      have hs := run.steps_le_m
      have hn : ((encodingProd (encodingList Bool) (encodingList Bool)).encode p).length=p.1.length+p.2.length := by simp [encodingList]
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_one,hn]
      change run.steps+(3*p.1.length+2*p.2.length+3)≤
        3*(p.1.length+p.2.length)+3+c.time.eval (2*(p.1.length+p.2.length)+1)
      omega
  finiteAlphabets _ := inferInstanceAs (Fintype (Bool⊕Bool))

def verifier : PolyTime (encodingProd (encodingList Bool) (encodingList Bool))
    (taggedBoolEncoding Bool) (accepts m T acceptControl) :=
  taggedVerifier (computes m T acceptControl)

@[simp] theorem verifier_inputAlphabet : (verifier m T acceptControl).inputAlphabet = Equiv.refl (Bool⊕Bool) := rfl
@[simp] theorem verifier_outputAlphabet : (verifier m T acceptControl).outputAlphabet = Equiv.refl (Bool⊕Bool) := rfl
@[simp] theorem verifier_time : (verifier m T acceptControl).time = time m T acceptControl := rfl

/-- The input codec is identity on ALL Bool lists, including malformed words.
The witness polynomial remains 2*T; the OLD runtime clock is T(decoded N).
Extra bits at the larger received length are physically forced false. -/
def source : SharpPWitness (encodingList Bool) (totalCount m T acceptControl) where
  witnessLength := (originalWitness m T acceptControl).witnessLength
  accept := accepts m T acceptControl
  verifier := verifier m T acceptControl
  counts bits := by
    cases hp : Parser.parse m T acceptControl bits with
    | none => simp [totalCount,accepts,hp,witnessCount,countAccepted]
    | some word =>
        have he : (BooleanInputWitness.inputEncoding (originalWitness m T acceptControl)).encode word=bits :=
          (input_code m T acceptControl word).trans (Parser.parse_sound m T acceptControl bits word hp)
        have hc := BooleanInputWitness.padded_counts (originalWitness m T acceptControl) word
        rw [BooleanInputWitness.newLength,he] at hc
        simpa [totalCount,accepts,parsedWord,hp,originalWitness,encodingList] using hc

theorem inSharpP : InSharpP (encodingList Bool) (totalCount m T acceptControl) := ⟨source m T acceptControl⟩

theorem malformed_zero (bits : List Bool) (h : Parser.parse m T acceptControl bits=none) :
    totalCount m T acceptControl bits=0 := by simp [totalCount,h]
theorem malformed_rejected (bits witness : List Bool) (h : Parser.parse m T acceptControl bits=none) :
    accepts m T acceptControl (bits,witness)=false := by simp [accepts,h]
def malformed_outputs (bits witness : List Bool) (h : Parser.parse m T acceptControl bits=none) :
    TM2OutputsInTime (verifier m T acceptControl).tm
      (bits.map Sum.inl++witness.map Sum.inr) (some [Sum.inr false])
      ((time m T acceptControl).eval (bits.length+witness.length)) := by
  have ho := (verifier m T acceptControl).outputsFun (bits,witness)
  simpa [encodingProd,encodingList,taggedBoolEncoding,encodeBool,List.map_id,Equiv.refl,Equiv.symm,Function.comp_def,
    malformed_rejected m T acceptControl bits witness h] using ho

theorem legal_count (word : List (Γ m)) :
    totalCount m T acceptControl (codeWord m T acceptControl word) =
      GeneralAlphabetSharpWitness.boundedCount m T acceptControl (encodingList (Γ m)) word := by
  simp only [totalCount,Parser.parse_code,Option.elim_some]

theorem legal_native_count (word : List (Γ m)) :
    totalCount m T acceptControl (codeWord m T acceptControl word) =
      Fintype.card (GeneralAlphabetSharpWitness.NativePacketWitness m T acceptControl (encodingList (Γ m)) word) :=
  (legal_count m T acceptControl word).trans
    (GeneralAlphabetSharpWitness.native_count m T acceptControl (encodingList (Γ m)) word).symm

theorem original_clock (bits : List Bool) (word : List (Γ m))
    (h : Parser.parse m T acceptControl bits=some word) :
    GeneralAlphabetSharpWitness.clock m T (encodingList (Γ m)) word=T.eval word.length ∧
      word.length≤bits.length := by
  refine ⟨rfl,?_⟩
  have he := congrArg List.length (Parser.parse_sound m T acceptControl bits word h)
  have hw := Nat.mul_le_mul_right word.length (Nat.succ_le_of_lt (Parser.width_pos m T acceptControl))
  calc
    word.length≤Parser.width m T acceptControl*word.length := by simpa only [Nat.one_mul] using hw
    _=(codeWord m T acceptControl word).length := (Parser.code_length m T acceptControl word).symm
    _=bits.length := he

/-- The OLD counter is itself a real composition of the finite symbol reader
and unary polynomial programme; it sees N symbols and produces 2*T(N), even
when the received bit length is W*N. -/
def old_counter_outputs (bits : List Bool) (word : List (Γ m))
    (h : Parser.parse m T acceptControl bits=some word) :
    TM2OutputsInTime
      (BooleanInputWitness.Counter.oldWitnessComputes (originalWitness m T acceptControl)).machine.computer
      bits (some (List.replicate (2*T.eval word.length) true))
      ((BooleanInputWitness.Counter.oldWitnessComputes (originalWitness m T acceptControl)).time.eval bits.length) := by
  have he := (input_code m T acceptControl word).trans (Parser.parse_sound m T acceptControl bits word h)
  have ho := (BooleanInputWitness.Counter.oldWitnessComputes (originalWitness m T acceptControl)).outputs word
  rw [he] at ho
  simpa only [BooleanInputWitness.oldLength,originalWitness,GeneralAlphabetSharpWitness.source,
    encodingList,Polynomial.eval_mul,Polynomial.eval_ofNat,
    WitnessParameters.unary,UnaryBinary.unaryEncoding,id_eq] using ho

/-- This is the actual standard verifier table, with no split controls. -/
def execution : BinaryMachine where
  core := (verifier m T acceptControl).tm
  alternate := (verifier m T acceptControl).tm.m
  split _ := false
  alphabets := (verifier m T acceptControl).finiteAlphabets
local instance : Fintype (execution m T acceptControl).core.K := (execution m T acceptControl).core.kFin
local instance : Fintype (execution m T acceptControl).core.Λ := (execution m T acceptControl).core.ΛFin
local instance : Fintype (execution m T acceptControl).core.σ := (execution m T acceptControl).core.σFin
local instance (k : (execution m T acceptControl).core.K) : Fintype ((execution m T acceptControl).core.Γ k) :=
  (execution m T acceptControl).alphabets k

def capacityPolynomial : Polynomial ℕ := Polynomial.X+
  time m T acceptControl*Polynomial.C (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (verifier m T acceptControl).tm)
def primitivePolynomial : Polynomial ℕ := time m T acceptControl*
  Polynomial.C (execution m T acceptControl).primitiveBudget
def bitsPolynomial : Polynomial ℕ := Polynomial.C (execution m T acceptControl).controlBits+
  capacityPolynomial m T acceptControl*Polynomial.C (execution m T acceptControl).symbolWidths

def outputs (bits witness : List Bool) :
    TM2OutputsInTime (verifier m T acceptControl).tm
      (bits.map Sum.inl++witness.map Sum.inr)
      (some [Sum.inr (accepts m T acceptControl (bits,witness))])
      ((time m T acceptControl).eval (bits.length+witness.length)) := by
  simpa [encodingProd,encodingList,taggedBoolEncoding,encodeBool,List.map_id,Equiv.refl,Equiv.symm,Function.comp_def] using
    (verifier m T acceptControl).outputsFun (bits,witness)

/-- An observed early clean true halt cannot disagree with the internally
produced verdict. Both runs are transported to the same real held clock. -/
theorem physical_accepts_iff (bits witness : List Bool) :
    (∃ steps, (fun p => p.bind (verifier m T acceptControl).tm.step)^[steps]
      (some (initList (verifier m T acceptControl).tm (bits.map Sum.inl++witness.map Sum.inr)))=
      some (haltList (verifier m T acceptControl).tm [Sum.inr true])) ↔
      accepts m T acceptControl (bits,witness)=true := by
  constructor
  · rintro ⟨steps,hr⟩
    let ho := outputs m T acceptControl bits witness
    have ht : TM2OutputsInTime (verifier m T acceptControl).tm
        (bits.map Sum.inl++witness.map Sum.inr) (some [Sum.inr true]) (steps+ho.steps) :=
      { steps := steps, evals_in_steps := hr, steps_le_m := Nat.le_add_right _ _ }
    have hv : TM2OutputsInTime (verifier m T acceptControl).tm
        (bits.map Sum.inl++witness.map Sum.inr)
        (some [Sum.inr (accepts m T acceptControl (bits,witness))]) (steps+ho.steps) :=
      { steps := ho.steps, evals_in_steps := ho.evals_in_steps, steps_le_m := Nat.le_add_left _ _ }
    have he := (Holant.LocalDrafts.CountingHardness.VerifierRun.outputs_at_bound _ _ _ _ ht).symm.trans
      (Holant.LocalDrafts.CountingHardness.VerifierRun.outputs_at_bound _ _ _ _ hv)
    have hw := congrArg (fun c : (verifier m T acceptControl).tm.Cfg =>
      c.stk (verifier m T acceptControl).tm.k₁) he
    change ([Sum.inr true] : List (Bool⊕Bool)) = [Sum.inr (accepts m T acceptControl (bits,witness))] at hw
    exact (Sum.inr.inj (List.cons.inj hw).1).symm
  · intro h
    refine ⟨(outputs m T acceptControl bits witness).steps,?_⟩
    have ho := (outputs m T acceptControl bits witness).evals_in_steps
    change (fun p => p.bind (verifier m T acceptControl).tm.step)^[(outputs m T acceptControl bits witness).steps]
      (some (initList (verifier m T acceptControl).tm (bits.map Sum.inl++witness.map Sum.inr))) =
      some (haltList (verifier m T acceptControl).tm [Sum.inr (accepts m T acceptControl (bits,witness))]) at ho
    simpa only [h] using ho

theorem malformed_no_true (bits witness : List Bool)
    (h : Parser.parse m T acceptControl bits=none) :
    ¬∃ steps, (fun p => p.bind (verifier m T acceptControl).tm.step)^[steps]
      (some (initList (verifier m T acceptControl).tm (bits.map Sum.inl++witness.map Sum.inr)))=
      some (haltList (verifier m T acceptControl).tm [Sum.inr true]) := by
  rw [physical_accepts_iff,malformed_rejected m T acceptControl bits witness h]
  simp

/-- Every actual pre exists; full input/output timing produces its bounds
internally, even on malformed received words. -/
theorem actual_prefix (bits witness : List Bool) (j : ℕ)
    (hj : j≤(outputs m T acceptControl bits witness).steps) :
    ∃ next, (fun p => p.bind (verifier m T acceptControl).tm.step)^[j]
      (some (initList (verifier m T acceptControl).tm
        (bits.map Sum.inl++witness.map Sum.inr)))=some next ∧
      (∀ key, (next.stk key).length≤(capacityPolynomial m T acceptControl).eval (bits.length+witness.length)) ∧
      (execution m T acceptControl).primitiveCost j
        ([],initList (verifier m T acceptControl).tm (bits.map Sum.inl++witness.map Sum.inr))≤
          (primitivePolynomial m T acceptControl).eval (bits.length+witness.length) ∧
      (execution m T acceptControl).codedStorageBits next≤
        (bitsPolynomial m T acceptControl).eval (bits.length+witness.length) := by
  have whole := (outputs m T acceptControl bits witness).evals_in_steps
  change (fun p => p.bind (verifier m T acceptControl).tm.step)^[(outputs m T acceptControl bits witness).steps]
    (some (initList (verifier m T acceptControl).tm (bits.map Sum.inl++witness.map Sum.inr))) =
    some (haltList (verifier m T acceptControl).tm [Sum.inr (accepts m T acceptControl (bits,witness))]) at whole
  have he : ∃ next, (fun p => p.bind (verifier m T acceptControl).tm.step)^[j]
      (some (initList (verifier m T acceptControl).tm (bits.map Sum.inl++witness.map Sum.inr)))=some next := by
    cases hp : (fun p => p.bind (verifier m T acceptControl).tm.step)^[j]
      (some (initList (verifier m T acceptControl).tm (bits.map Sum.inl++witness.map Sum.inr))) with
    | some next => exact ⟨next,rfl⟩
    | none =>
        have hn : (fun p : Option (verifier m T acceptControl).tm.Cfg =>
            p.bind (verifier m T acceptControl).tm.step)^[
            (outputs m T acceptControl bits witness).steps-j] none=none :=
          Function.iterate_fixed (f := fun p : Option (verifier m T acceptControl).tm.Cfg =>
            p.bind (verifier m T acceptControl).tm.step) rfl _
        rw [show (outputs m T acceptControl bits witness).steps=
          ((outputs m T acceptControl bits witness).steps-j)+j by omega,
          Function.iterate_add_apply,hp,hn] at whole
        cases whole
  obtain ⟨next,hr⟩ := he
  have ht := hj.trans (outputs m T acceptControl bits witness).steps_le_m
  have hc : ∀ key, (next.stk key).length≤(capacityPolynomial m T acceptControl).eval (bits.length+witness.length) := by
    have hh := Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some (verifier m T acceptControl).tm j _ _ hr
    have hm := Nat.mul_le_mul_right (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (verifier m T acceptControl).tm) ht
    intro key
    have hs := Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound (verifier m T acceptControl).tm
      (bits.map Sum.inl++witness.map Sum.inr) j key
    rw [hh] at hs
    simp only [List.length_append,List.length_map] at hs
    exact hs.trans (by simpa [capacityPolynomial] using Nat.add_le_add_left hm (bits.length+witness.length))
  refine ⟨next,hr,hc,?_,?_⟩
  · exact ((execution m T acceptControl).primitiveCost_le j _).trans (by
      simpa [primitivePolynomial] using Nat.mul_le_mul_right (execution m T acceptControl).primitiveBudget ht)
  · exact ((execution m T acceptControl).codedStorageBits_le next).trans (by
      simpa [bitsPolynomial] using (execution m T acceptControl).storageBits_le next
        ((capacityPolynomial m T acceptControl).eval (bits.length+witness.length)) hc)

theorem step_none (c : (execution m T acceptControl).Config) :
    (execution m T acceptControl).step none c=some (Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (verifier m T acceptControl).tm c) := by
  cases hl : c.l <;> simp [execution,BinaryMachine.step,Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep,hl]

theorem none_trace (n : ℕ) (c : (execution m T acceptControl).Config) :
    (execution m T acceptControl).TraceValid (List.replicate n none) c
      ((Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (verifier m T acceptControl).tm)^[n] c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      refine ⟨Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (verifier m T acceptControl).tm c,step_none m T acceptControl c,?_⟩
      simpa only [Function.iterate_succ_apply] using ih (Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (verifier m T acceptControl).tm c)

/-- Parser, old-length polynomial evaluation, guard, same verifier, decoder,
cleanup and the advertised held padding all have one canonical None token. -/
theorem canonical_trace (bits witness : List Bool) :
    (execution m T acceptControl).TraceValid
      (List.replicate ((time m T acceptControl).eval (bits.length+witness.length)) none)
      (initList (verifier m T acceptControl).tm (bits.map Sum.inl++witness.map Sum.inr))
      (haltList (verifier m T acceptControl).tm [Sum.inr (accepts m T acceptControl (bits,witness))]) := by
  have h := none_trace m T acceptControl ((time m T acceptControl).eval (bits.length+witness.length))
    (initList (verifier m T acceptControl).tm (bits.map Sum.inl++witness.map Sum.inr))
  rw [Holant.LocalDrafts.CountingHardness.VerifierRun.outputs_at_bound _ _ _ _ (outputs m T acceptControl bits witness)] at h
  exact h

theorem token_unique (c d : (execution m T acceptControl).Config) (token : Option Bool)
    (h : (execution m T acceptControl).step token c=some d) : token=none := by
  cases hl : c.l with
  | none => exact GeneralAlphabetSharpWitness.halted_token_unique _ c d token hl h
  | some label => exact GeneralAlphabetSharpWitness.ordinary_token_unique _ label c d token hl rfl h

def fixedTimePolynomial : Polynomial ℕ := (time m T acceptControl).comp (Polynomial.X+2*T)
def fixedCapacityPolynomial : Polynomial ℕ := (capacityPolynomial m T acceptControl).comp (Polynomial.X+2*T)
def fixedPrimitivePolynomial : Polynomial ℕ := (primitivePolynomial m T acceptControl).comp (Polynomial.X+2*T)
def fixedBitsPolynomial : Polynomial ℕ := (bitsPolynomial m T acceptControl).comp (Polynomial.X+2*T)

theorem fixed_input_length (bits : List Bool) (witness : Fin ((2*T).eval bits.length) → Bool) :
    bits.length+(List.ofFn witness).length=(Polynomial.X+2*T).eval bits.length := by
  simp only [List.length_ofFn,Polynomial.eval_add,Polynomial.eval_X]

theorem fixed_time (bits : List Bool) (witness : Fin ((2*T).eval bits.length) → Bool) :
    (outputs m T acceptControl bits (List.ofFn witness)).steps≤
      (fixedTimePolynomial m T acceptControl).eval bits.length := by
  have h := (outputs m T acceptControl bits (List.ofFn witness)).steps_le_m
  calc
    _ ≤ (time m T acceptControl).eval (bits.length+(List.ofFn witness).length) := h
    _ = _ := by rw [fixed_input_length T bits witness]; simp only [fixedTimePolynomial,Polynomial.eval_comp]

theorem fixed_prefix (bits : List Bool) (witness : Fin ((2*T).eval bits.length) → Bool) (j : ℕ)
    (hj : j≤(outputs m T acceptControl bits (List.ofFn witness)).steps) :
    ∃ next, (fun p => p.bind (verifier m T acceptControl).tm.step)^[j]
      (some (initList (verifier m T acceptControl).tm
        (bits.map Sum.inl++(List.ofFn witness).map Sum.inr)))=some next ∧
      (∀ key, (next.stk key).length≤(fixedCapacityPolynomial m T acceptControl).eval bits.length) ∧
      (execution m T acceptControl).primitiveCost j
        ([],initList (verifier m T acceptControl).tm
          (bits.map Sum.inl++(List.ofFn witness).map Sum.inr))≤
          (fixedPrimitivePolynomial m T acceptControl).eval bits.length ∧
      (execution m T acceptControl).codedStorageBits next≤
        (fixedBitsPolynomial m T acceptControl).eval bits.length := by
  have h := actual_prefix m T acceptControl bits (List.ofFn witness) j hj
  rw [fixed_input_length T bits witness] at h
  simpa only [fixedCapacityPolynomial,fixedPrimitivePolynomial,fixedBitsPolynomial,Polynomial.eval_comp] using h

/-- A malformed serialization has no accepted candidate at ANY length. -/
theorem malformed_witness_count (bits : List Bool) (n : ℕ)
    (h : Parser.parse m T acceptControl bits=none) :
    witnessCount n (fun witness => accepts m T acceptControl (bits,witness))=0 := by
  simp [malformed_rejected m T acceptControl bits _ h,witnessCount,countAccepted]
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetTotalInput
