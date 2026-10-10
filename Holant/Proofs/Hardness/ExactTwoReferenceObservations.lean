import Holant.Proofs.Hardness.ExactTwoReferenceControlled
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-! Literal ring query, actual correction runs and charged
programme receipts for computational global pinning. No independent compiler,
query-length hypothesis or semantic oracle implementation is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceControlled
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
namespace Costs
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (runFee feePolynomial runFee_le configurationWord codedStoragePolynomial coded_storage_le)
end Costs
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d : ℕ}
variable (F : FixedField K d)
attribute [local irreducible] preprocess correctionComputes

theorem source_machine : (source F).reduction.machine=
    OracleOneQuery.Context.machine preprocess.machine (correctionComputes F).machine := by
  unfold source
  exact Cap.controlledContextOfEq_machine _ _ _ _ _

theorem source_clock : (source F).reduction.time=
    (OracleOneQuery.Context.reduction preprocess (correctionComputes F) (targetOutput F)).time := by
  unfold source
  exact Cap.controlledContextOfEq_time _ _ _ _ _

theorem atMostOne : UniversalPairReduction.ThreeQuery.AtMostQueries (source F).reduction.machine 1 := by
  rw [source_machine]
  exact UniversalPairReduction.SmoothingCompiler.ContextCount.atMostOne _ _

/-- Query identification works for every arbitrary oracle and every prefix. -/
theorem query_origin (oracle : List Bool→List Bool) (r : C.Input) (t : ℕ)
    (c : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (sourceEncoding.encode r) t=some c)
    (hq : (source F).reduction.machine.IsQuery c) :
    c.stk (source F).reduction.machine.queryStack=targetEncoding.encode (C.query r) := by
  revert c
  rw [source_machine]
  intro c hr hq
  have hc := Holant.LocalDrafts.Hardness.ContextControl.query_configuration
    preprocess.machine (correctionComputes F).machine oracle (sourceEncoding.encode r)
    (targetEncoding.encode (C.query r)) (contextEncoding.encode (R.count r.val))
    (preprocess.outputs r).steps t c (preprocess.outputs r).evals_in_steps hr hq
  subst c
  simp [Holant.LocalDrafts.Hardness.ContextControl.queryCfg,
    OracleOneQuery.Context.machine,StackProtocol.cfg,StackProtocol.tapes3,
    Machine.sourceKey,Machine.destinationKey,Machine.temporaryKey]

attribute [local irreducible] source

/-- Decoder output bytes for the actual ring oracle answer and original count. -/
def correct_answer (r : C.Input) : TM2OutputsInTime (correctionComputes F).machine.computer
    ((answerContextEncoding F).encode (P.sourceValue (C.query r),R.count r.val))
    (some (F.encoding.encode (sourceValue (K:=K) r)))
    ((correctionComputes F).time.eval
      ((answerContextEncoding F).encode (P.sourceValue (C.query r),R.count r.val)).length) := by
  rw [recovery r]
  exact (correctionComputes F).outputs _

theorem query_answer_bytes (oracle : List Bool→List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding P.sourceValue oracle)
    (r : C.Input) (t : ℕ) (c : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (sourceEncoding.encode r) t=some c)
    (hq : (source F).reduction.machine.IsQuery c) :
    c.stk (source F).reduction.machine.queryStack=targetEncoding.encode (C.query r) ∧
      targetEncoding.decode (c.stk (source F).reduction.machine.queryStack)=some (C.query r) ∧
      oracle (c.stk (source F).reduction.machine.queryStack)=F.encoding.encode (P.sourceValue (C.query r)) ∧
      (c.stk (source F).reduction.machine.queryStack).length≤
        (source F).queryBound.eval (sourceEncoding.encode r).length := by
  have hw := query_origin F oracle r t c hr hq
  obtain ⟨q,hqword,hlen⟩ := (source F).safeQuery oracle ho r t c hr hq
  refine ⟨hw,?_,?_,hlen⟩
  · rw [hw]; exact targetEncoding.decode_encode _
  · rw [hw]; exact ho _

theorem prefix_fees (oracle : List Bool→List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding P.sourceValue oracle)
    (r : C.Input) (t : ℕ)
    (ht : t≤(source F).reduction.time.eval (sourceEncoding.encode r).length) :
    Costs.runFee (source F).reduction.machine oracle (sourceEncoding.encode r) t≤
      (Costs.feePolynomial (source F)).eval (sourceEncoding.encode r).length :=
  Costs.runFee_le (source F) oracle ho r t ht

theorem prefix_coded_storage (oracle : List Bool→List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding P.sourceValue oracle)
    (r : C.Input) (t : ℕ)
    (ht : t≤(source F).reduction.time.eval (sourceEncoding.encode r).length)
    (c : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (sourceEncoding.encode r) t=some c) :
    (Costs.configurationWord (source F).reduction.machine c).length≤
      (Costs.codedStoragePolynomial (source F)).eval (sourceEncoding.encode r).length :=
  Costs.coded_storage_le (source F) oracle ho r t ht c hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceControlled
