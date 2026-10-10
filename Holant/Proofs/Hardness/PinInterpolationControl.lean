import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.Source
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-! Controlled original-M pin interpolation on the literal doubling branch.
The reduction is exactly the existing Pin programme and clock. Query safety
comes from its actual completed RunsTrace, including all reached query states;
query lengths come from the actual original-M batch writer. No safe-query,
realization, interpolation success, or desired reduction is supplied by callers.
The coefficient entry constructs the checked doubling hypothesis internally.
This is a conditional coefficient-branch reduction, not universal hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PinInterpolationControl
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines OracleBatch
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
namespace Old
export Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.Source
  (queries queriesComputes pre preprocessing doubling doubling_correct doubling_coefficients)
end Old
namespace OldPin
export Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.Source.Pin
  (machine timePolynomial execution reduction exact_calls_and_primitive)
end OldPin
namespace Costs
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (runFee feePolynomial runFee_le storage_le configurationWord codedStoragePolynomial coded_storage_le)
end Costs

variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀ t,IsAlgebraic ℚ (M t))
local instance originalFieldAlgebra : Algebra ℚ (Original.field M) := (Original.field M).algebra'

/-- Bound for the SAME original singleton-M oracle and coefficient codec. -/
def targetOutput : PolynomialOutputBound Original.targetEncoding (F M halg).encoding
    (Original.targetValue M halg) :=
  (Original.tables M halg).outputBound (F M halg)

/-- Attach proven original-query control to the existing physical programme.
This does not create or choose a different reduction with the same value. -/
def source (hM : EvenSupport M) (hbranch : Old.doubling M halg=true) :
    LengthControlledOracleReduction inputEncoding (F M halg).encoding
      Original.targetEncoding (F M halg).encoding
      (targetPinValue M halg) (Original.targetValue M halg) where
  reduction := OldPin.reduction M halg hM hbranch
  targetOutput := targetOutput M halg
  queryBound := (Old.pre M halg).outputBound.bound
  safeQuery oracle ho r t c hr hq := by
    obtain ⟨n,_,htrace⟩ := OldPin.execution M halg hM hbranch oracle ho r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member htrace t c hr hq
    obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
    refine ⟨q,he.symm,?_⟩
    exact (member_length_le _ _ hm).trans (query_context_length_le (Old.pre M halg) r).1

/-- The real coefficient condition constructs the successful tested branch;
no desired output, saved Ready, pure core or supplied pin programme appears. -/
def sourceOfCoefficients (hM : EvenSupport M) (hs : SparseCase M)
    (hv : sparseV (entries M)≠0) (hu : sparseU (entries M)=2*sparseV (entries M)) :
    LengthControlledOracleReduction inputEncoding (F M halg).encoding
      Original.targetEncoding (F M halg).encoding
      (targetPinValue M halg) (Original.targetValue M halg) :=
  source M halg hM ((Old.doubling_coefficients M halg hM).mpr ⟨hs,hv,hu⟩)

variable (hM : EvenSupport M) (hbranch : Old.doubling M halg=true)

theorem same_reduction : (source M halg hM hbranch).reduction=OldPin.reduction M halg hM hbranch := rfl
theorem same_machine : (source M halg hM hbranch).reduction.machine=OldPin.machine M halg := rfl
theorem same_clock : (source M halg hM hbranch).reduction.time=OldPin.timePolynomial M halg := rfl
theorem same_query_bound : (source M halg hM hbranch).queryBound=(Old.pre M halg).outputBound.bound := rfl

/-- Every actual query is one of the precise original-M samples produced by
the same byte writer. This includes an alleged query after the clean halt. -/
theorem query_origin (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (r : Input M halg) (t : ℕ) (c : (source M halg hM hbranch).reduction.machine.Cfg)
    (hr : (source M halg hM hbranch).reduction.machine.run oracle (inputEncoding.encode r) t=some c)
    (hq : (source M halg hM hbranch).reduction.machine.IsQuery c) :
    ∃ q∈Old.queries M halg r,
      c.stk (source M halg hM hbranch).reduction.machine.queryStack=Original.targetEncoding.encode q := by
  obtain ⟨n,_,htrace⟩ := OldPin.execution M halg hM hbranch oracle ho r
  have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member htrace t c hr hq
  obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
  exact ⟨q,hmem,he.symm⟩

/-- Actual machine execution returns the inherited original-field pin value. -/
def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (r : Input M halg) :
    (source M halg hM hbranch).reduction.machine.OutputsInTime oracle (inputEncoding.encode r)
      ((F M halg).encoding.encode (targetPinValue M halg r))
      ((source M halg hM hbranch).reduction.time.eval (inputEncoding.encode r).length) :=
  (source M halg hM hbranch).reduction.correct oracle ho r

theorem query_answer_bytes (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (r : Input M halg) (t : ℕ) (c : (source M halg hM hbranch).reduction.machine.Cfg)
    (hr : (source M halg hM hbranch).reduction.machine.run oracle (inputEncoding.encode r) t=some c)
    (hq : (source M halg hM hbranch).reduction.machine.IsQuery c) :
    ∃ q : Original.TargetInput,
      c.stk (source M halg hM hbranch).reduction.machine.queryStack=Original.targetEncoding.encode q ∧
      Original.targetEncoding.decode (c.stk (source M halg hM hbranch).reduction.machine.queryStack)=some q ∧
      oracle (c.stk (source M halg hM hbranch).reduction.machine.queryStack)=
        (F M halg).encoding.encode (Original.targetValue M halg q) ∧
      (c.stk (source M halg hM hbranch).reduction.machine.queryStack).length≤
        (source M halg hM hbranch).queryBound.eval (inputEncoding.encode r).length := by
  obtain ⟨q,hword,hlen⟩ := (source M halg hM hbranch).safeQuery oracle ho r t c hr hq
  refine ⟨q,hword,?_,?_,hlen⟩
  · rw [hword]; exact Original.targetEncoding.decode_encode q
  · rw [hword]; exact ho q

theorem answer_length (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (r : Input M halg) (t : ℕ) (c : (source M halg hM hbranch).reduction.machine.Cfg)
    (hr : (source M halg hM hbranch).reduction.machine.run oracle (inputEncoding.encode r) t=some c)
    (hq : (source M halg hM hbranch).reduction.machine.IsQuery c) :
    (oracle (c.stk (source M halg hM hbranch).reduction.machine.queryStack)).length≤
      ((source M halg hM hbranch).targetOutput.bound.comp
        (source M halg hM hbranch).queryBound).eval (inputEncoding.encode r).length :=
  (source M halg hM hbranch).answer_length_le oracle ho r t c hr hq

theorem prefix_primitive (oracle : List Bool → List Bool)
    (r : Input M halg) (t : ℕ)
    (ht : t≤(source M halg hM hbranch).reduction.time.eval (inputEncoding.encode r).length) :
    OracleBatch.primitiveCount (source M halg hM hbranch).reduction.machine oracle
      ((source M halg hM hbranch).reduction.machine.init (inputEncoding.encode r)) t≤
      (source M halg hM hbranch).reduction.machine.primitiveBudget*
        (source M halg hM hbranch).reduction.time.eval (inputEncoding.encode r).length :=
  (OracleBatch.primitiveCount_le _ _ _ _).trans
    (Nat.mul_le_mul_left (source M halg hM hbranch).reduction.machine.primitiveBudget ht)

theorem prefix_fees (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (r : Input M halg) (t : ℕ)
    (ht : t≤(source M halg hM hbranch).reduction.time.eval (inputEncoding.encode r).length) :
    Costs.runFee (source M halg hM hbranch).reduction.machine oracle (inputEncoding.encode r) t≤
      (Costs.feePolynomial (source M halg hM hbranch)).eval (inputEncoding.encode r).length :=
  Costs.runFee_le (source M halg hM hbranch) oracle ho r t ht

theorem prefix_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (r : Input M halg) (t : ℕ)
    (ht : t≤(source M halg hM hbranch).reduction.time.eval (inputEncoding.encode r).length)
    (c : (source M halg hM hbranch).reduction.machine.Cfg)
    (hr : (source M halg hM hbranch).reduction.machine.run oracle (inputEncoding.encode r) t=some c) :
    stackSize c.stk≤(source M halg hM hbranch).sourceOutputPolynomial.eval (inputEncoding.encode r).length :=
  Costs.storage_le (source M halg hM hbranch) oracle ho r t ht c hr

theorem prefix_coded_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (r : Input M halg) (t : ℕ)
    (ht : t≤(source M halg hM hbranch).reduction.time.eval (inputEncoding.encode r).length)
    (c : (source M halg hM hbranch).reduction.machine.Cfg)
    (hr : (source M halg hM hbranch).reduction.machine.run oracle (inputEncoding.encode r) t=some c) :
    (Costs.configurationWord (source M halg hM hbranch).reduction.machine c).length≤
      (Costs.codedStoragePolynomial (source M halg hM hbranch)).eval (inputEncoding.encode r).length :=
  Costs.coded_storage_le (source M halg hM hbranch) oracle ho r t ht c hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PinInterpolationControl
