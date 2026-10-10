import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyFieldClosed
import Holant.Proofs.Hardness.GeneralEOPairedCSPOriginalField

/-! The actual mixed-family programme queries the literal existing original
oracle, with GeneralOriginalTarget.originalPresentation/originalValue. Its
answers are physically converted to the working field before correction.
Different coefficient presentations are never identified by a type alias. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyOriginal
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GeneralEOPairedCSPFamilyRaw
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue)
end O
namespace A
export GeneralEOPairedCSPOriginalField (presentation targetValue embedding answerComputes target_value post)
end A
namespace N
export GeneralEOPairedCSPFamilyNative (pre preprocessing totalPre totalPreprocessing)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
variable (P : (i : Fin s)→OrientedPerfectPairing (arity i.val))

local instance fieldAlgebra : Algebra ℚ (GeneralEOPairedCSPField.field G) :=
  (GeneralEOPairedCSPField.field G).algebra'

abbrev sourceValue := GeneralEOPairedCSPFamilyField.sourceValue G P
abbrev value := GeneralEOPairedCSPFamilyNative.totalValue (GeneralEOPairedCSPField.signatures G) P
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 arity

theorem query_value (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) (r : Input P) :
    sourceValue G P r=A.embedding G
      (O.originalValue G (GeneralEOPairedCSPFamilyValidated.query P r))*
        (2:GeneralEOPairedCSPField.field G)^GeneralEOPairedCSPFamilyUnused.unused r.val := by
  have h := GeneralEOPairedCSPFamilyNative.query_value (A.presentation G)
    (GeneralEOPairedCSPField.signatures G) P
    (fun i=>GeneralEOPairedCSPField.covers G i (P i) (hf i)) r
  change sourceValue G P r=A.targetValue G (GeneralEOPairedCSPFamilyValidated.query P r)*
    (2:GeneralEOPairedCSPField.field G)^GeneralEOPairedCSPFamilyUnused.unused r.val at h
  rw [A.target_value] at h
  exact h

def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (inputEncoding P) (A.presentation G).encoding
      (targetEncoding (s:=s) (arity:=arity)) (O.originalPresentation G).encoding
      (sourceValue G P) (O.originalValue G) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
    (N.pre P) (A.post G) ((O.originalTables G).outputBound (O.originalPresentation G))
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho r
  rw [query_value G P hf r]
  simpa only [N.preprocessing,OracleBatch.answers,List.map_cons,List.map_nil,
    List.getD_cons_zero,O.originalValue] using reduction.reduction.correct oracle ho r

/-- Actual validation and row writing with precisely the pre-existing
original-family oracle value and answer codec. -/
def totalControlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (encoding s) (A.presentation G).encoding
      (targetEncoding (s:=s) (arity:=arity)) (O.originalPresentation G).encoding
      (value G P) (O.originalValue G) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
    (N.totalPre P) (A.post G) ((O.originalTables G).outputBound (O.originalPresentation G))
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
  · have hv := query_value G P hf ⟨r,hr⟩
    change GeneralEOPairedCSPFamilyRaw.value P
      (fun i=>GeneralEOPairedCSPCycles.compress (P i) (GeneralEOPairedCSPField.signatures G i)) r=_ at hv
    rw [value,GeneralEOPairedCSPFamilyNative.totalValue,ite_eq_left hr,hv]
    simpa only [N.totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_left hr,
      OracleBatch.answers,List.map_cons,List.map_nil,List.getD_cons_zero,O.originalValue] using h
  · simpa [value,GeneralEOPairedCSPFamilyNative.totalValue,N.totalPreprocessing,
      GeneralEOPairedCSPFamilyValidation.queries,hr,OracleBatch.answers] using h

theorem prefix_query_bound (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i))
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (arity:=arity)) (O.originalPresentation G).encoding
      (O.originalValue G) oracle) (r : Raw s) (t : ℕ) :
    UniversalPairReduction.ThreeQuery.queryCount (totalControlled G P hf).reduction.machine oracle
      ((totalControlled G P hf).reduction.machine.init ((encoding s).encode r)) t≤
      if r.WellFormed P then 1 else 0 := by
  have h := OracleBatch.reduction_prefix_count (N.totalPre P) (A.post G)
    ((O.originalTables G).outputBound (O.originalPresentation G)) oracle ho r t
  by_cases hr : r.WellFormed P
  · simpa only [totalControlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      N.totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_left hr,
      ite_eq_left hr,List.length_singleton] using h
  · simpa only [totalControlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      N.totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_right hr,
      ite_eq_right hr,List.length_nil] using h

theorem query_count (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i))
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (arity:=arity)) (O.originalPresentation G).encoding
      (O.originalValue G) oracle) (r : Raw s) :
    ∃t≤(totalControlled G P hf).reduction.time.eval ((encoding s).encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount (totalControlled G P hf).reduction.machine oracle
        ((totalControlled G P hf).reduction.machine.init ((encoding s).encode r)) t=
        if r.WellFormed P then 1 else 0 := by
  obtain ⟨t,ht,_,hq,_⟩ := OracleBatch.reduction_query_count (N.totalPre P) (A.post G)
    ((O.originalTables G).outputBound (O.originalPresentation G)) oracle ho r
  refine ⟨t,ht,?_⟩
  by_cases hr : r.WellFormed P
  · simpa only [totalControlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      N.totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_left hr,
      ite_eq_left hr,List.length_singleton] using hq
  · simpa only [totalControlled,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
      N.totalPreprocessing,GeneralEOPairedCSPFamilyValidation.queries,dite_eq_right hr,
      ite_eq_right hr,List.length_nil] using hq

theorem primitive_bound (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i))
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (arity:=arity)) (O.originalPresentation G).encoding
      (O.originalValue G) oracle) (r : Raw s) :
    ∃t≤(totalControlled G P hf).reduction.time.eval ((encoding s).encode r).length,
      (totalControlled G P hf).reduction.machine.run oracle ((encoding s).encode r) t=
        some ((totalControlled G P hf).reduction.machine.output
          ((A.presentation G).encoding.encode (value G P r))) ∧
      OracleBatch.primitiveCount (totalControlled G P hf).reduction.machine oracle
        ((totalControlled G P hf).reduction.machine.init ((encoding s).encode r)) t≤
        (Polynomial.C (totalControlled G P hf).reduction.machine.primitiveBudget*
          (totalControlled G P hf).reduction.time).eval ((encoding s).encode r).length := by
  let h := (totalControlled G P hf).reduction.correct oracle ho r
  refine ⟨h.steps,h.steps_le_m,h.evals_in_steps,?_⟩
  apply (OracleBatch.primitiveCount_le _ _ _ _).trans
  simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.mul_le_mul_left (totalControlled G P hf).reduction.machine.primitiveBudget h.steps_le_m

variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))

/-- Every pairing is derived internally from the original closed support,
and the final oracle remains literally the existing original-family oracle. -/
def closedControlled :
    LengthControlledOracleReduction (encoding s) (A.presentation G).encoding
      (targetEncoding (s:=s) (arity:=arity)) (O.originalPresentation G).encoding
      (value G (GeneralEOPairedCSPFamilyFieldClosed.pairing G he hn hc)) (O.originalValue G) :=
  totalControlled G (GeneralEOPairedCSPFamilyFieldClosed.pairing G he hn hc)
    (GeneralEOPairedCSPFamilyFieldClosed.covers G he hn hc)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyOriginal
