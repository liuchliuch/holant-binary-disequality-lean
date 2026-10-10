import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Proofs.Algorithms.CountingCircuitAdapter
import Holant.Proofs.Algorithms.NativeMatchingCountCodec
import Holant.Proofs.Counting.CompilerSize
import Holant.Proofs.CountingMachines.OracleControl.Storage


namespace Holant.LocalDrafts.MainChain.CBSpecializedNativeHardness
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.LocalDrafts.MainChain
noncomputable section

abbrev Circuit := Holant.LocalDrafts.CountingHardness.CircuitInstance
namespace Circuit
export Holant.LocalDrafts.CountingHardness.CircuitInstance (encoding value outputBound)
end Circuit
namespace Native
export Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.OriginalFieldMap
  (TargetInput targetEncoding targetValue)
end Native

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
variable {L : Type} [Field L] [Algebra ℚ L] {d : ℕ}

/-- The count correction changes only the output specification. The physical
one-query table, clock, target answer bound and query invariant are retained. -/
def caller (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool Circuit.encoding encodingNatBool
      f Circuit.value := by
  let r := controlledOneQuery (CountingCircuitAdapter.queryComputes w)
    (identityComputes encodingNatBool) Circuit.outputBound
  exact {
    reduction := {
      machine := r.reduction.machine
      time := r.reduction.time
      correct oracle ho x := by
        simpa only [Function.comp_apply, id_eq, CountingCircuitAdapter.query_value] using
          r.reduction.correct oracle ho x }
    targetOutput := r.targetOutput
    queryBound := r.queryBound
    safeQuery := r.safeQuery }

theorem caller_machine (w : SharpPWitness ea f) :
    (caller w).reduction.machine = OracleOneQuery.machine
      (CountingCircuitAdapter.queryComputes w).machine
      (identityComputes encodingNatBool).machine := rfl

theorem caller_time (w : SharpPWitness ea f) :
    (caller w).reduction.time =
      (OracleOneQuery.reduction (CountingCircuitAdapter.queryComputes w)
        (identityComputes encodingNatBool) Circuit.outputBound).time := rfl

theorem caller_queryBound (w : SharpPWitness ea f) :
    (caller w).queryBound = (CountingCircuitAdapter.queryComputes w).outputBound.bound := rfl

def query_outputs (w : SharpPWitness ea f) (x : α) :
    TM2OutputsInTime (CountingCircuitAdapter.queryComputes w).machine.computer (ea.encode x)
      (some (Circuit.encoding.encode (CountingCircuitAdapter.query w x)))
      ((CountingCircuitAdapter.queryComputes w).time.eval (ea.encode x).length) :=
  (CountingCircuitAdapter.queryComputes w).outputs x

/-- The one outer circuit call receives precisely this source verifier's
emitted circuit, not a separately selected circuit of the same count. -/
theorem caller_query_configuration (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool) (x : α) (t : ℕ)
    (cfg : (caller w).reduction.machine.Cfg)
    (hr : (caller w).reduction.machine.run oracle (ea.encode x) t = some cfg)
    (hq : (caller w).reduction.machine.IsQuery cfg) :
    cfg = OracleOneQuery.leftCfg (CountingCircuitAdapter.queryComputes w).machine
      (identityComputes encodingNatBool).machine
      (haltList (CountingCircuitAdapter.queryComputes w).machine.computer
        (Circuit.encoding.encode (CountingCircuitAdapter.query w x))) :=
  OneQueryControl.query_configuration _ _ oracle _ _
    ((CountingCircuitAdapter.queryComputes w).outputs x).steps t cfg
    ((CountingCircuitAdapter.queryComputes w).outputs x).evals_in_steps hr hq

theorem caller_query_word (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool) (x : α) (t : ℕ)
    (cfg : (caller w).reduction.machine.Cfg)
    (hr : (caller w).reduction.machine.run oracle (ea.encode x) t = some cfg)
    (hq : (caller w).reduction.machine.IsQuery cfg) :
    cfg.stk (caller w).reduction.machine.queryStack =
      Circuit.encoding.encode (CountingCircuitAdapter.query w x) := by
  rw [caller_query_configuration w oracle x t cfg hr hq, OracleOneQuery.left_halt]
  exact wordTape_at ((CountingCircuitAdapter.queryComputes w).machine.sourceKey
    (identityComputes encodingNatBool).machine) (Circuit.encoding.encode (CountingCircuitAdapter.query w x))

/-- Unique closed entry. Both operands are concrete controlled producers;
the native callee includes interpolation, padding and scalar correction. -/
def source (F : FixedField L d) (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool Native.targetEncoding F.encoding
      f (Native.targetValue (L := L)) :=
  (caller w).composeControlled (NativeMatchingCountCodec.source F)

theorem source_machine (F : FixedField L d) (w : SharpPWitness ea f) :
    (source F w).reduction.machine =
      OracleCompose.machine (NativeMatchingCountCodec.source F).reduction.machine
        (caller w).reduction.machine := rfl

theorem source_time (F : FixedField L d) (w : SharpPWitness ea f) :
    (source F w).reduction.time =
      (caller w).compositionTimePolynomial (NativeMatchingCountCodec.source F).reduction := rfl

theorem source_queryBound (F : FixedField L d) (w : SharpPWitness ea f) :
    (source F w).queryBound =
      (NativeMatchingCountCodec.source F).queryBound.comp (caller w).queryBound := rfl

theorem source_targetOutput (F : FixedField L d) (w : SharpPWitness ea f) :
    (source F w).targetOutput = (NativeMatchingCountCodec.source F).targetOutput := rfl

def outputs (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) :
    (source F w).reduction.machine.OutputsInTime oracle (ea.encode x)
      (encodingNatBool.encode (f x)) ((source F w).reduction.time.eval (ea.encode x).length) :=
  (source F w).reduction.correct oracle ho x

/-- A real external callback is an actual callee prefix on a valid outer
circuit query, with the actual saved caller frame. -/
theorem internal_query_origin (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ) (cfg : (source F w).reduction.machine.Cfg)
    (hr : (source F w).reduction.machine.run oracle (ea.encode x) t = some cfg)
    (hq : (source F w).reduction.machine.IsQuery cfg) :
    LengthControlledOracleReduction.CompositionQueryOrigin
      (caller w) (NativeMatchingCountCodec.source F) oracle x cfg :=
  (caller w).composeControlled_query_origin (NativeMatchingCountCodec.source F)
    oracle ho x t cfg hr hq

/-- Strengthen the inliner receipt to the SAME emitted circuit of the actual
returned verifier frontend, including the saved frame and real callee run. -/
theorem compiled_circuit_query_origin (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ) (cfg : (source F w).reduction.machine.Cfg)
    (hr : (source F w).reduction.machine.run oracle (ea.encode x) t = some cfg)
    (hq : (source F w).reduction.machine.IsQuery cfg) :
    ∃ outerTime outerCfg innerTime innerCfg memory,
      (caller w).reduction.machine.run
        (encodedOracle Circuit.encoding encodingNatBool Circuit.value) (ea.encode x) outerTime = some outerCfg ∧
      (caller w).reduction.machine.IsQuery outerCfg ∧
      outerCfg.stk (caller w).reduction.machine.queryStack =
        Circuit.encoding.encode (CountingCircuitAdapter.query w x) ∧
      (Circuit.encoding.encode (CountingCircuitAdapter.query w x)).length ≤
        (caller w).queryBound.eval (ea.encode x).length ∧
      (NativeMatchingCountCodec.source F).reduction.machine.run oracle
        (Circuit.encoding.encode (CountingCircuitAdapter.query w x)) innerTime = some innerCfg ∧
      (NativeMatchingCountCodec.source F).reduction.machine.IsQuery innerCfg ∧
      cfg = OracleInline.calleeCfg (NativeMatchingCountCodec.source F).reduction.machine
        innerCfg memory outerCfg.stk := by
  obtain ⟨outerTime, outerCfg, q, innerTime, innerCfg, memory,
    houter, houterQuery, hword, hlength, hinner, hinnerQuery, hcfg⟩ :=
    internal_query_origin F w oracle ho x t cfg hr hq
  have hexact := caller_query_word w
    (encodedOracle Circuit.encoding encodingNatBool Circuit.value) x outerTime outerCfg houter houterQuery
  have heq : q = CountingCircuitAdapter.query w x :=
    Circuit.encoding.encode_injective (hword.symm.trans hexact)
  subst q
  exact ⟨outerTime, outerCfg, innerTime, innerCfg, memory,
    houter, houterQuery, hword, hlength, hinner, hinnerQuery, hcfg⟩

/-- Exact legal native query bytes and same installed-field answer bytes. -/
theorem query_answer_bytes (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ) (cfg : (source F w).reduction.machine.Cfg)
    (hr : (source F w).reduction.machine.run oracle (ea.encode x) t = some cfg)
    (hq : (source F w).reduction.machine.IsQuery cfg) :
    ∃ q : Native.TargetInput,
      cfg.stk (source F w).reduction.machine.queryStack = Native.targetEncoding.encode q ∧
      Native.targetEncoding.decode (cfg.stk (source F w).reduction.machine.queryStack) = some q ∧
      oracle (cfg.stk (source F w).reduction.machine.queryStack) =
        F.encoding.encode (Native.targetValue (L := L) q) ∧
      (cfg.stk (source F w).reduction.machine.queryStack).length ≤
        (source F w).queryBound.eval (ea.encode x).length := by
  obtain ⟨q, hword, hlength⟩ := (source F w).safeQuery oracle ho x t cfg hr hq
  refine ⟨q, hword, ?_, ?_, hlength⟩
  · rw [hword]
    exact Native.targetEncoding.decode_encode q
  · rw [hword]
    exact ho q

theorem answer_length (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ) (cfg : (source F w).reduction.machine.Cfg)
    (hr : (source F w).reduction.machine.run oracle (ea.encode x) t = some cfg)
    (hq : (source F w).reduction.machine.IsQuery cfg) :
    (oracle (cfg.stk (source F w).reduction.machine.queryStack)).length ≤
      ((source F w).targetOutput.bound.comp (source F w).queryBound).eval (ea.encode x).length :=
  (source F w).answer_length_le oracle ho x t cfg hr hq

/-- Whole-program storage, including received field answers and all inliner
scratch, at every actual prefix; capacity is not a caller parameter. -/
theorem prefix_storage (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ) (cfg : (source F w).reduction.machine.Cfg)
    (hr : (source F w).reduction.machine.run oracle (ea.encode x) t = some cfg) :
    stackSize cfg.stk ≤ (ea.encode x).length + t *
      ((source F w).reduction.machine.primitiveBudget +
        ((source F w).targetOutput.bound.comp (source F w).queryBound).eval (ea.encode x).length) :=
  (source F w).run_stackSize_le oracle ho x t cfg hr

theorem prefix_storage_polynomial (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ) (cfg : (source F w).reduction.machine.Cfg)
    (ht : t ≤ (source F w).reduction.time.eval (ea.encode x).length)
    (hr : (source F w).reduction.machine.run oracle (ea.encode x) t = some cfg) :
    stackSize cfg.stk ≤ (source F w).sourceOutputPolynomial.eval (ea.encode x).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.storage_le
    (source F w) oracle ho x t ht cfg hr

theorem prefix_primitive (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool) (x : α) (t : ℕ)
    (ht : t ≤ (source F w).reduction.time.eval (ea.encode x).length) :
    OracleBatch.primitiveCount (source F w).reduction.machine oracle
      ((source F w).reduction.machine.init (ea.encode x)) t ≤
        (source F w).reduction.machine.primitiveBudget *
          (source F w).reduction.time.eval (ea.encode x).length :=
  (OracleBatch.primitiveCount_le _ _ _ _).trans (Nat.mul_le_mul_left _ ht)

/-- The measured fee includes actual ordinary syntax, each invocation and the
complete query and returned answer words of this SAME installed program. -/
theorem prefix_fees (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ) (ht : t ≤ (source F w).reduction.time.eval (ea.encode x).length) :
    Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee
      (source F w).reduction.machine oracle (ea.encode x) t ≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.feePolynomial
        (source F w)).eval (ea.encode x).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee_le
    (source F w) oracle ho x t ht

theorem prefix_coded_storage (F : FixedField L d) (w : SharpPWitness ea f)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ) (cfg : (source F w).reduction.machine.Cfg)
    (ht : t ≤ (source F w).reduction.time.eval (ea.encode x).length)
    (hr : (source F w).reduction.machine.run oracle (ea.encode x) t = some cfg) :
    (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.configurationWord
      (source F w).reduction.machine cfg).length ≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.codedStoragePolynomial
        (source F w)).eval (ea.encode x).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.coded_storage_le
    (source F w) oracle ho x t ht cfg hr

end
end Holant.LocalDrafts.MainChain.CBSpecializedNativeHardness
