import Holant.Proofs.Hardness.GeneralEOPairedCSPNative
import Holant.Proofs.Hardness.GeneralEOPairedCSPValidation

/-! Total raw-record oracle programme. Actual validation precedes graph
queries. Malformed arity/address records return zero and generate no oracle
query; valid records compute the original compressed CSP exactly. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPTotal
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GeneralEOPairedCSPRaw
namespace N
export GeneralEOPairedCSPNative (targetEncoding TargetInput targetValue tables post query_value)
end N
namespace U
export GeneralEOPairedCSPUnused (unused unusedComputes)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K d) (G : (i : Fin s)→Signature K (arity i.val))
variable (label : Fin s) (p : OrientedPerfectPairing (arity label.val))

def value (r : Raw) : K := if r.WellFormed p.count then
  GeneralEOPairedCSPRaw.value p (GeneralEOPairedCSPCycles.compress p (G label)) r else 0

def preprocessing (r : Raw) : List (N.TargetInput (s:=s) (arity:=arity))×ℕ :=
  (GeneralEOPairedCSPValidation.queries label p r,U.unused r)

def pre : Computes encoding
    (OracleBatch.contextEncoding (N.targetEncoding (s:=s) (arity:=arity)) unary)
    (preprocessing label p) :=
  pairComputes (GeneralEOPairedCSPValidation.queriesComputes label p) U.unusedComputes

/-- End-to-end correctness and query/answer length control hold on every raw
record, including invalid records; validation is part of the programme. -/
def controlled (hf : GeneralEOPairedCSPCycles.Covers p (G label)) :
    LengthControlledOracleReduction encoding F.encoding
      (N.targetEncoding (s:=s) (arity:=arity)) F.encoding (value G label p) (N.targetValue F G) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
    (pre label p) (N.post F) ((N.tables F G).outputBound F)
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho r
  have h := reduction.reduction.correct oracle ho r
  by_cases hr : r.WellFormed p.count
  · have hv := N.query_value F G label p hf ⟨r,hr⟩
    change GeneralEOPairedCSPRaw.value p (GeneralEOPairedCSPCycles.compress p (G label)) r=_ at hv
    rw [value,ite_eq_left hr,hv]
    simpa only [preprocessing,GeneralEOPairedCSPValidation.queries,dite_eq_left hr,
      OracleBatch.answers,List.map_cons,List.map_nil,List.getD_cons_zero,N.targetValue] using h
  · simpa [value,preprocessing,GeneralEOPairedCSPValidation.queries,hr,OracleBatch.answers] using h

omit [Algebra ℚ K] in
theorem invalid_value (r : Raw) (hr : ¬r.WellFormed p.count) : value G label p r=0 := by
  simp [value,hr]

/-- Every reachable execution prefix contains at most one query for a valid
record, and zero queries for an invalid record, including after clean halt. -/
theorem prefix_query_bound (hf : GeneralEOPairedCSPCycles.Covers p (G label))
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (N.targetEncoding (s:=s) (arity:=arity)) F.encoding
      (N.targetValue F G) oracle) (r : Raw) (t : ℕ) :
    UniversalPairReduction.ThreeQuery.queryCount (controlled F G label p hf).reduction.machine oracle
      ((controlled F G label p hf).reduction.machine.init (encoding.encode r)) t≤
      if r.WellFormed p.count then 1 else 0 := by
  have h := OracleBatch.reduction_prefix_count (pre label p) (N.post F)
    ((N.tables F G).outputBound F) oracle ho r t
  by_cases hr : r.WellFormed p.count
  · simpa only [controlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      preprocessing,GeneralEOPairedCSPValidation.queries,dite_eq_left hr,
      ite_eq_left hr,List.length_singleton] using h
  · simpa only [controlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      preprocessing,GeneralEOPairedCSPValidation.queries,dite_eq_right hr,
      ite_eq_right hr,List.length_nil] using h

/-- Exact actual oracle count, with the certified total execution clock. -/
theorem query_count (hf : GeneralEOPairedCSPCycles.Covers p (G label))
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (N.targetEncoding (s:=s) (arity:=arity)) F.encoding
      (N.targetValue F G) oracle) (r : Raw) :
    ∃t≤(controlled F G label p hf).reduction.time.eval (encoding.encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount (controlled F G label p hf).reduction.machine oracle
        ((controlled F G label p hf).reduction.machine.init (encoding.encode r)) t=
        if r.WellFormed p.count then 1 else 0 := by
  obtain ⟨t,ht,_,hq,_⟩ := OracleBatch.reduction_query_count (pre label p) (N.post F)
    ((N.tables F G).outputBound F) oracle ho r
  refine ⟨t,ht,?_⟩
  by_cases hr : r.WellFormed p.count
  · simpa only [controlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      preprocessing,GeneralEOPairedCSPValidation.queries,dite_eq_left hr,
      ite_eq_left hr,List.length_singleton] using hq
  · simpa only [controlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      preprocessing,GeneralEOPairedCSPValidation.queries,dite_eq_right hr,
      ite_eq_right hr,List.length_nil] using hq

/-- The same completed oracle execution pays its actual primitive-operation
fees from a polynomial in the original encoded raw-record length. -/
theorem primitive_bound (hf : GeneralEOPairedCSPCycles.Covers p (G label))
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (N.targetEncoding (s:=s) (arity:=arity)) F.encoding
      (N.targetValue F G) oracle) (r : Raw) :
    ∃t≤(controlled F G label p hf).reduction.time.eval (encoding.encode r).length,
      (controlled F G label p hf).reduction.machine.run oracle (encoding.encode r) t=
        some ((controlled F G label p hf).reduction.machine.output (F.encoding.encode (value G label p r))) ∧
      OracleBatch.primitiveCount (controlled F G label p hf).reduction.machine oracle
        ((controlled F G label p hf).reduction.machine.init (encoding.encode r)) t≤
        (Polynomial.C (controlled F G label p hf).reduction.machine.primitiveBudget*
          (controlled F G label p hf).reduction.time).eval (encoding.encode r).length := by
  let h := (controlled F G label p hf).reduction.correct oracle ho r
  refine ⟨h.steps,h.steps_le_m,h.evals_in_steps,?_⟩
  apply (OracleBatch.primitiveCount_le _ _ _ _).trans
  simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.mul_le_mul_left (controlled F G label p hf).reduction.machine.primitiveBudget h.steps_le_m

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPTotal
