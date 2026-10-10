import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyUnused
import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyValidation
import Holant.Proofs.Hardness.GeneralEOPairedCSPNative

/-! Actual mixed-family original-label/native-X oracle programme. Every label
uses its own covering pairing and arity. Validation, physical graph writing,
unused-variable correction, and answer arithmetic have concrete machines. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyNative
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GeneralEOPairedCSPFamilyRaw
namespace W
export GeneralEOPairedCSPFamilyValidated (query queryComputes incidence_eq)
end W
namespace U
export GeneralEOPairedCSPFamilyUnused (unused unusedComputes unused_eq)
end U
namespace N
export GeneralEOPairedCSPNative (TargetInput targetEncoding tables targetValue target_semantics post)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K d) (G : (i : Fin s)→Signature K (arity i.val))
variable (P : (i : Fin s)→OrientedPerfectPairing (arity i.val))

theorem value_scope (g : (i : Fin s)→Signature K (P i).count)
    (r : Raw s) (hr : r.WellFormed P) :
    value P g r=GeneralEOPairedCSPFamilyCycles.value P r.labelsFn g (scope P r hr) := by
  unfold value GeneralEOPairedCSPFamilyCycles.value
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext j
  rw [←W.incidence_eq P r v j,←scope_val P r hr,GeneralEOPairedCSPRaw.read_at]

def sourceValue (r : Input P) : K :=
  value P (fun i=>GeneralEOPairedCSPCycles.compress (P i) (G i)) r.val

theorem query_value (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) (r : Input P) :
    sourceValue G P r=N.targetValue F G (W.query P r)*(2:K)^U.unused r.val := by
  rw [sourceValue,value_scope P _ r.val r.property,
    GeneralEOPairedCSPFamilyCycles.query_value P r.val.labelsFn G hf,N.target_semantics,U.unused_eq P r]
  exact mul_comm _ _

def unusedComputes : Computes (inputEncoding P) unary (fun r=>U.unused r.val) :=
  recode U.unusedComputes Subtype.val (fun _=>rfl) (fun _=>rfl)

def preprocessing (r : Input P) : List (N.TargetInput (s:=s) (arity:=arity))×ℕ :=
  ([W.query P r],U.unused r.val)

def pre : Computes (inputEncoding P)
    (OracleBatch.contextEncoding (N.targetEncoding (s:=s) (arity:=arity)) unary)
    (preprocessing P) :=
  pairComputes (Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.list₁
    (N.targetEncoding (s:=s) (arity:=arity)) (W.queryComputes P)) (unusedComputes P)

def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (inputEncoding P) F.encoding
      (N.targetEncoding (s:=s) (arity:=arity)) F.encoding
      (sourceValue G P) (N.targetValue F G) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
    (pre P) (N.post F) ((N.tables F G).outputBound F)
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho r
  rw [query_value F G P hf r]
  simpa only [preprocessing,OracleBatch.answers,List.map_cons,List.map_nil,
    List.getD_cons_zero,N.targetValue] using reduction.reduction.correct oracle ho r

def totalValue (r : Raw s) : K := if r.WellFormed P then
  value P (fun i=>GeneralEOPairedCSPCycles.compress (P i) (G i)) r else 0

def totalPreprocessing (r : Raw s) : List (N.TargetInput (s:=s) (arity:=arity))×ℕ :=
  (GeneralEOPairedCSPFamilyValidation.queries P r,U.unused r)

def totalPre : Computes (encoding s)
    (OracleBatch.contextEncoding (N.targetEncoding (s:=s) (arity:=arity)) unary)
    (totalPreprocessing P) :=
  pairComputes (GeneralEOPairedCSPFamilyValidation.queriesComputes P) U.unusedComputes

def totalControlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (encoding s) F.encoding
      (N.targetEncoding (s:=s) (arity:=arity)) F.encoding (totalValue G P) (N.targetValue F G) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
    (totalPre P) (N.post F) ((N.tables F G).outputBound F)
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
  by_cases hr : r.WellFormed P
  · have hv := query_value F G P hf ⟨r,hr⟩
    change value P (fun i=>GeneralEOPairedCSPCycles.compress (P i) (G i)) r=_ at hv
    rw [totalValue,ite_eq_left hr,hv]
    simpa only [totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_left hr,
      OracleBatch.answers,List.map_cons,List.map_nil,List.getD_cons_zero,N.targetValue] using h
  · simpa [totalValue,totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,hr,OracleBatch.answers] using h

omit [Algebra ℚ K] in
theorem invalid_value (r : Raw s) (hr : ¬r.WellFormed P) : totalValue G P r=0 := by
  simp [totalValue,hr]

/-- Every execution prefix uses at most one query on valid records and no
query on malformed records, even after the programme has halted. -/
theorem prefix_query_bound (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i))
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (N.targetEncoding (s:=s) (arity:=arity)) F.encoding
      (N.targetValue F G) oracle) (r : Raw s) (t : ℕ) :
    UniversalPairReduction.ThreeQuery.queryCount (totalControlled F G P hf).reduction.machine oracle
      ((totalControlled F G P hf).reduction.machine.init ((encoding s).encode r)) t≤
      if r.WellFormed P then 1 else 0 := by
  have h := OracleBatch.reduction_prefix_count (totalPre P) (N.post F)
    ((N.tables F G).outputBound F) oracle ho r t
  by_cases hr : r.WellFormed P
  · simpa only [totalControlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_left hr,
      ite_eq_left hr,List.length_singleton] using h
  · simpa only [totalControlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_right hr,
      ite_eq_right hr,List.length_nil] using h

/-- Exact actual oracle count at a polynomially bounded completed execution. -/
theorem query_count (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i))
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (N.targetEncoding (s:=s) (arity:=arity)) F.encoding
      (N.targetValue F G) oracle) (r : Raw s) :
    ∃t≤(totalControlled F G P hf).reduction.time.eval ((encoding s).encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount (totalControlled F G P hf).reduction.machine oracle
        ((totalControlled F G P hf).reduction.machine.init ((encoding s).encode r)) t=
        if r.WellFormed P then 1 else 0 := by
  obtain ⟨t,ht,_,hq,_⟩ := OracleBatch.reduction_query_count (totalPre P) (N.post F)
    ((N.tables F G).outputBound F) oracle ho r
  refine ⟨t,ht,?_⟩
  by_cases hr : r.WellFormed P
  · simpa only [totalControlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_left hr,
      ite_eq_left hr,List.length_singleton] using hq
  · simpa only [totalControlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_right hr,
      ite_eq_right hr,List.length_nil] using hq

theorem primitive_bound (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i))
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (N.targetEncoding (s:=s) (arity:=arity)) F.encoding
      (N.targetValue F G) oracle) (r : Raw s) :
    ∃t≤(totalControlled F G P hf).reduction.time.eval ((encoding s).encode r).length,
      (totalControlled F G P hf).reduction.machine.run oracle ((encoding s).encode r) t=
        some ((totalControlled F G P hf).reduction.machine.output (F.encoding.encode (totalValue G P r))) ∧
      OracleBatch.primitiveCount (totalControlled F G P hf).reduction.machine oracle
        ((totalControlled F G P hf).reduction.machine.init ((encoding s).encode r)) t≤
        (Polynomial.C (totalControlled F G P hf).reduction.machine.primitiveBudget*
          (totalControlled F G P hf).reduction.time).eval ((encoding s).encode r).length := by
  let h := (totalControlled F G P hf).reduction.correct oracle ho r
  refine ⟨h.steps,h.steps_le_m,h.evals_in_steps,?_⟩
  apply (OracleBatch.primitiveCount_le _ _ _ _).trans
  simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.mul_le_mul_left (totalControlled F G P hf).reduction.machine.primitiveBudget h.steps_le_m

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyNative
