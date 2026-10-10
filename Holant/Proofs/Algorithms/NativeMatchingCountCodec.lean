import Holant.Proofs.Algorithms.NativeMatchingOriginalFieldSource
import Holant.Complexity.RationalArithmetic.ScalarMachines
import Holant.Complexity.IntegerArithmetic.Encoding
import Holant.Complexity.FixedFieldMachines.Vector
import Holant.Complexity.OracleBatch.PrimitiveCost


namespace Holant.LocalDrafts.MainChain.NativeMatchingCountCodec
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates

namespace Base
export _root_.Holant.LocalDrafts.MainChain.NativeMatchingOriginalFieldSource (Circuit rationalField source)
namespace Circuit
export Holant.LocalDrafts.CountingHardness.CircuitInstance (encoding value)
end Circuit
namespace Native
export _root_.Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.OriginalFieldMap (TargetInput targetEncoding targetValue)
end Native
end Base

namespace Sign
set_option backward.isDefEq.respectTransparency false

/-- One physical stack is both the input and output. The sign is consumed,
never left in the natural payload. Only the negative branch needs a loop. -/
def machine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Bool
  main := false
  State := Option Bool
  initial := none
  program
    | false => .pop () (fun _ bit => bit)
        (.branch (fun bit => bit.getD false)
          (.load (fun _ => none) (.goto (fun _ => true)))
          (.load (fun _ => none) .halt))
    | true => .pop () (fun _ bit => bit)
        (.branch Option.isSome
          (.load (fun _ => none) (.goto (fun _ => true)))
          (.load (fun _ => none) .halt))

def cfg (label : Option Bool) (word : List Bool) : machine.Config :=
  ⟨label, none, fun _ => word⟩

theorem cfg_init (word : List Bool) :
    cfg (some false) word = initList machine.computer word := by
  rw [machine.init_eq]
  unfold cfg wordTape
  congr 1

theorem cfg_halt (word : List Bool) :
    cfg none word = haltList machine.computer word := by
  rw [machine.halt_eq]
  unfold cfg wordTape
  congr 1

/-- The first instruction really pops the codec's parity bit. Empty input
is treated as the canonical positive zero, not as a missing free sign. -/
theorem step_start (word : List Bool) :
    machine.computer.step (cfg (some false) word) =
      some (cfg (if word.head?.getD false then some true else none) word.tail) := by
  cases word with
  | nil =>
    simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, Function.update_eq_const_of_subsingleton] <;> rfl
  | cons bit rest =>
    cases bit <;>
      simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, Function.update_eq_const_of_subsingleton] <;> rfl

theorem step_erase_cons (bit : Bool) (word : List Bool) :
    machine.computer.step (cfg (some true) (bit :: word)) =
      some (cfg (some true) word) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, Function.update_eq_const_of_subsingleton] <;> rfl

theorem step_erase_nil :
    machine.computer.step (cfg (some true) []) = some (cfg none []) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, Function.update_eq_const_of_subsingleton] <;> rfl

def Runs (start finish : machine.Config) (n : ℕ) : Prop :=
  (fun c => c.bind machine.computer.step)^[n] (some start) = some finish

theorem Runs.one {start finish : machine.Config}
    (h : machine.computer.step start = some finish) : Runs start finish 1 := h

theorem Runs.trans {a b c : machine.Config} {n m : ℕ}
    (h : Runs a b n) (h' : Runs b c m) : Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

/-- All negative payload bits and the final EOF test are charged. -/
theorem erase_exact (word : List Bool) :
    Runs (cfg (some true) word) (cfg none []) (word.length + 1) := by
  induction word with
  | nil => exact Runs.one step_erase_nil
  | cons bit word ih =>
    simpa [List.length_cons, Nat.add_assoc] using
      (Runs.one (step_erase_cons bit word)).trans ih

/-- Correctness for every integer, with no integrality/nonnegative premise.
The original integer codec head and tail producers determine the two cases. -/
def outputs (z : ℤ) :
    TM2OutputsInTime machine.computer (IntegerArithmetic.encoding.encode z)
      (some (encodingNatBool.encode z.toNat))
      ((IntegerArithmetic.encoding.encode z).length + 2) := by
  cases z with
  | ofNat n =>
    refine ⟨⟨1, ?_⟩, ?_⟩
    · change machine.computer.step
        (initList machine.computer (IntegerArithmetic.encoding.encode (n : ℤ))) =
          some (haltList machine.computer (encodingNatBool.encode (n : ℤ).toNat))
      rw [← cfg_init, ← cfg_halt, step_start,
        IntegerArithmetic.encoding_head, IntegerArithmetic.encoding_tail]
      rfl
    · change 1 ≤ _
      omega
  | negSucc n =>
    have first : machine.computer.step
        (cfg (some false) (IntegerArithmetic.encoding.encode (.negSucc n))) =
          some (cfg (some true) (encodeNat n)) := by
      rw [step_start, IntegerArithmetic.encoding_head, IntegerArithmetic.encoding_tail]
      rfl
    have run := (Runs.one first).trans (erase_exact (encodeNat n))
    refine ⟨⟨(encodeNat n).length + 2, ?_⟩, ?_⟩
    · change (fun c => c.bind machine.computer.step)^[(encodeNat n).length + 2]
        (some (initList machine.computer (IntegerArithmetic.encoding.encode (.negSucc n)))) =
          some (haltList machine.computer (encodingNatBool.encode (.negSucc n : ℤ).toNat))
      rw [← cfg_init, ← cfg_halt]
      change Runs (cfg (some false) (IntegerArithmetic.encoding.encode (.negSucc n)))
        (cfg none []) ((encodeNat n).length + 2)
      simpa only [Nat.add_assoc] using run
    · simp only [IntegerArithmetic.encoding_negSucc, List.length_cons]
      omega

noncomputable def computes :
    Computes IntegerArithmetic.encoding encodingNatBool Int.toNat where
  machine := machine
  time := Polynomial.X + 2
  outputs z := by
    simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat] using outputs z

theorem input_output_alias : machine.input = machine.output := rfl
theorem initial_register : machine.initial = none := rfl
theorem row_budget (label : Bool) : TM2Cost.budget (machine.program label) = 4 := by
  cases label <;> rfl

/-- Primitive cost is the interpreted syntax cost, not a free word operation. -/
theorem row_primitive (label : Bool) (state : Option Bool) (tapes : Unit → List Bool) :
    (TM2Cost.primitiveRun (machine.program label) state tapes).1 ≤ 4 := by
  simpa only [row_budget] using TM2Cost.primitiveRun_cost_le (machine.program label) state tapes

end Sign

noncomputable section

/-- The literal singleton basis has its sole coordinate equal to the rational
number. This equality justifies the parser's typed interface, not an opcode. -/
theorem singleton_coordinate (q : ℚ) : Base.rationalField.basis.equivFun q 0 = q := by
  simp [Base.rationalField, NativeMatchingOriginalFieldSource.rationalField,
    NativeCubicMatching.Source.F, NativeCubicMatching.Programs.F,
    WeightedMatchingInterpolation.Source.rationalField,
    Module.Basis.equivFun_apply]

/-- Consume the actual fixed-vector frame, including its empty-vector suffix. -/
def singletonComputes : Computes Base.rationalField.encoding rationalEncoding id :=
  congrComputes
    (recode (g := fun q : ℚ => Base.rationalField.basis.equivFun q 0)
      (headComputes 0) (fun q : ℚ => Base.rationalField.basis.equivFun q)
      (fun _ => rfl) (fun _ => rfl)) singleton_coordinate

theorem singleton_programme : singletonComputes.machine = (headComputes 0).machine := rfl
theorem singleton_clock : singletonComputes.time = (headComputes 0).time := rfl

/-- Sole ordinary answer program: frame parser, numerator parser, physical
parity pop/negative erase. Its `andThen` clocks include copying and clearing. -/
def computes : Computes Base.rationalField.encoding encodingNatBool (fun q : ℚ => q.num.toNat) :=
  congrComputes
    ((singletonComputes.andThen RationalArithmetic.numeratorComputes).andThen Sign.computes)
    (fun _ => rfl)

def decoderReceipt (q : ℚ) :
    TM2OutputsInTime computes.machine.computer (Base.rationalField.encoding.encode q)
      (some (encodingNatBool.encode q.num.toNat))
      (computes.time.eval (Base.rationalField.encoding.encode q).length) := computes.outputs q

@[simp] theorem nat_cast_num (n : ℕ) : (n : ℚ).num.toNat = n := by simp

/-- This consumes the actual circuit count; no desired count is machine data. -/
def circuitReceipt (c : Base.Circuit) :
    TM2OutputsInTime computes.machine.computer
      (Base.rationalField.encoding.encode (Base.Circuit.value c : ℚ))
      (some (encodingNatBool.encode (Base.Circuit.value c)))
      (computes.time.eval
        (Base.rationalField.encoding.encode (Base.Circuit.value c : ℚ)).length) := by
  simpa only [nat_cast_num] using decoderReceipt (Base.Circuit.value c : ℚ)

variable {L : Type} [Field L] [Algebra ℚ L] {d : ℕ} (F : FixedField L d)

/-- An actual one-query caller whose postprogramme is the decoder above.
Its intermediate-answer bound is produced by the existing circuit machine. -/
def caller : LengthControlledOracleReduction Base.Circuit.encoding encodingNatBool
    Base.Circuit.encoding Base.rationalField.encoding Base.Circuit.value
    (fun c => (Base.Circuit.value c : ℚ)) :=
  controlledOneQueryOfEq (identityComputes Base.Circuit.encoding) computes
    (Base.source F).sourceOutputBound Base.Circuit.value (fun c => (nat_cast_num _).symm)

/-- Unique final consumer: the real original-field callee is installed into
the caller by the existing finite inliner. The answer decoder is ordinary. -/
def source : LengthControlledOracleReduction Base.Circuit.encoding encodingNatBool
    Base.Native.targetEncoding F.encoding Base.Circuit.value Base.Native.targetValue :=
  (caller F).composeControlled (Base.source F)

theorem source_machine : (source F).reduction.machine =
    OracleCompose.machine (Base.source F).reduction.machine (caller F).reduction.machine := rfl

/-- The old callee time and actual query/answer copy-clear-return overhead are
all inside this installed polynomial, as is the ordinary decoder clock. -/
theorem source_time : (source F).reduction.time =
    (caller F).compositionTimePolynomial (Base.source F).reduction := rfl
theorem source_queryBound : (source F).queryBound =
    (Base.source F).queryBound.comp (caller F).queryBound := rfl
theorem source_targetOutput : (source F).targetOutput = (Base.source F).targetOutput := rfl

def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Base.Native.targetEncoding F.encoding Base.Native.targetValue oracle)
    (c : Base.Circuit) := (source F).reduction.correct oracle ho c

/-- Every external callback still receives original native query bytes and
returns original F bytes. No callback belongs to the ordinary answer decoder. -/
theorem query_origin (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Base.Native.targetEncoding F.encoding Base.Native.targetValue oracle)
    (c : Base.Circuit) (t : ℕ) (cfg : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (Base.Circuit.encoding.encode c) t = some cfg)
    (hq : (source F).reduction.machine.IsQuery cfg) :
    ∃ q : Base.Native.TargetInput,
      cfg.stk (source F).reduction.machine.queryStack = Base.Native.targetEncoding.encode q ∧
      (Base.Native.targetEncoding.encode q).length ≤
        (source F).queryBound.eval (Base.Circuit.encoding.encode c).length :=
  by
    obtain ⟨q,hq,hl⟩ := (source F).safeQuery oracle ho c t cfg hr hq
    exact ⟨q,hq,by simpa only [hq] using hl⟩

theorem internal_query_origin (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Base.Native.targetEncoding F.encoding Base.Native.targetValue oracle)
    (c : Base.Circuit) (t : ℕ) (cfg : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (Base.Circuit.encoding.encode c) t = some cfg)
    (hq : (source F).reduction.machine.IsQuery cfg) :
    LengthControlledOracleReduction.CompositionQueryOrigin
      (caller F) (Base.source F) oracle c cfg :=
  (caller F).composeControlled_query_origin (Base.source F) oracle ho c t cfg hr hq

theorem answer_length (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Base.Native.targetEncoding F.encoding Base.Native.targetValue oracle)
    (c : Base.Circuit) (t : ℕ) (cfg : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (Base.Circuit.encoding.encode c) t = some cfg)
    (hq : (source F).reduction.machine.IsQuery cfg) :
    (oracle (cfg.stk (source F).reduction.machine.queryStack)).length ≤
      ((source F).targetOutput.bound.comp (source F).queryBound).eval
        (Base.Circuit.encoding.encode c).length :=
  (source F).answer_length_le oracle ho c t cfg hr hq

/-- Full storage at any actual prefix, including stale original-field answers. -/
theorem prefix_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Base.Native.targetEncoding F.encoding Base.Native.targetValue oracle)
    (c : Base.Circuit) (t : ℕ) (cfg : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (Base.Circuit.encoding.encode c) t = some cfg) :
    stackSize cfg.stk ≤ (Base.Circuit.encoding.encode c).length +
      t * ((source F).reduction.machine.primitiveBudget +
        ((source F).targetOutput.bound.comp (source F).queryBound).eval
          (Base.Circuit.encoding.encode c).length) :=
  (source F).run_stackSize_le oracle ho c t cfg hr

/-- Original-input polynomial storage, with no separately supplied capacity.
The finite clock and answer bound are both produced by the installed source. -/
def storagePolynomial : Polynomial ℕ := (source F).sourceOutputPolynomial

theorem prefix_storage_polynomial (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Base.Native.targetEncoding F.encoding Base.Native.targetValue oracle)
    (c : Base.Circuit) (t : ℕ) (cfg : (source F).reduction.machine.Cfg)
    (ht : t ≤ (source F).reduction.time.eval (Base.Circuit.encoding.encode c).length)
    (hr : (source F).reduction.machine.run oracle (Base.Circuit.encoding.encode c) t = some cfg) :
    stackSize cfg.stk ≤ (storagePolynomial F).eval (Base.Circuit.encoding.encode c).length := by
  have hs := prefix_storage F oracle ho c t cfg hr
  have hm := Nat.mul_le_mul_right
    ((source F).reduction.machine.primitiveBudget +
      ((source F).targetOutput.bound.comp (source F).queryBound).eval
        (Base.Circuit.encoding.encode c).length) ht
  simp only [storagePolynomial, LengthControlledOracleReduction.sourceOutputPolynomial,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  omega

/-- Every executed elementary instruction is charged by the same installed
table. The caller's full time polynomial includes the decoder and inliner. -/
theorem prefix_primitive (oracle : List Bool → List Bool) (c : Base.Circuit) (t : ℕ)
    (ht : t ≤ (source F).reduction.time.eval (Base.Circuit.encoding.encode c).length) :
    OracleBatch.primitiveCount (source F).reduction.machine oracle
      ((source F).reduction.machine.init (Base.Circuit.encoding.encode c)) t ≤
        (source F).reduction.machine.primitiveBudget *
          (source F).reduction.time.eval (Base.Circuit.encoding.encode c).length :=
  (OracleBatch.primitiveCount_le _ _ _ _).trans (Nat.mul_le_mul_left _ ht)

end
end Holant.LocalDrafts.MainChain.NativeMatchingCountCodec
