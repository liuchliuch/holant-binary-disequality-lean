import Holant.Proofs.Hardness.ExactTwoChainPolynomial
import Holant.Proofs.Hardness.ExactTwoChainMachine
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-! Actual same-field controlled interpolation from [q,E] to original q.
All four-port queries, denominator arithmetic, scalar corrections and runtime
bounds are generated internally. The caller supplies only the fixed field
presentation, with no correct evaluator, desired reduction or Ready premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainControlled
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines OracleBatch BinaryInterpolation
namespace Q
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding queries)
end Q
namespace P
export ExactTwoChainPolynomial (sourceValue targetValue targetSignatures kernels quotient_correct denominator_nonzero)
end P
namespace M
export ExactTwoChainMachine (Data values resultPair interpolatedValue pre machine timePolynomial execution reduction)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d : ℕ}
variable (F : FixedField K d)

def targetTables : ExactSignatureTables d 1 1 Q.arity where
  vertex i x:=F.decode.symm (P.targetSignatures i x)
  edge i x y:=F.decode.symm (P.kernels i x y)

theorem target_evaluate (r : Q.TargetInput) : (targetTables F).evaluate F r=P.targetValue r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

def data : M.Data F (targetTables F) where
  gamma:=2
  rho:=(2 : K)⁻¹
  geometric:=true

theorem values_eq (r : Q.Input) (i : Fin (FixedGadgetSubstitution.occurrences 1 r.val+1)) :
    M.values (data F) r i=ExactTwoChainPolynomial.values r i := target_evaluate F _

theorem value_correct (r : Q.Input) : M.interpolatedValue (data F) r=P.sourceValue r := by
  have hv : M.values (data F) r=ExactTwoChainPolynomial.values r := funext (values_eq F r)
  change commonNumerator _ (M.values (data F) r)/BinaryInterpolation.commonDenominator _=P.sourceValue r
  rw [hv]
  exact P.quotient_correct r

def targetOutput : PolynomialOutputBound Q.targetEncoding F.encoding (P.targetValue (K:=K)) where
  bound:=(targetTables F).outputBound F |>.bound
  length_le r:=by
    rw [←target_evaluate F r]
    exact ((targetTables F).outputBound F).length_le r

/-- Same machine and clock as the actual four-port answered-transcript
interpreter. Safe queries follow from its full completed RunsTrace. -/
def source : LengthControlledOracleReduction Q.sourceEncoding F.encoding
    Q.targetEncoding F.encoding (P.sourceValue (K:=K)) (P.targetValue (K:=K)) where
  reduction := {
    machine:=M.machine (data F)
    time:=M.timePolynomial (data F)
    correct oracle ho r:=by
      have ho' : RepresentsOracle Q.targetEncoding F.encoding ((targetTables F).evaluate F) oracle := by
        intro q
        rw [target_evaluate]
        exact ho q
      rw [←value_correct F r]
      exact (M.reduction (data F)).correct oracle ho' r }
  targetOutput:=targetOutput F
  queryBound:=(M.pre (data F)).outputBound.bound
  safeQuery oracle ho r t c hr hq:=by
    have ho' : RepresentsOracle Q.targetEncoding F.encoding ((targetTables F).evaluate F) oracle := by
      intro q
      rw [target_evaluate]
      exact ho q
    obtain ⟨n,_,ht⟩ := M.execution (data F) oracle ho' r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t c hr hq
    obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
    exact ⟨q,he.symm,(member_length_le _ _ hm).trans (query_context_length_le (M.pre (data F)) r).1⟩

theorem same_machine : (source F).reduction.machine=M.machine (data F) := rfl
theorem same_clock : (source F).reduction.time=M.timePolynomial (data F) := rfl

theorem query_origin (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (P.targetValue (K:=K)) oracle)
    (r : Q.Input) (t : ℕ) (c : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (Q.sourceEncoding.encode r) t=some c)
    (hq : (source F).reduction.machine.IsQuery c) :
    ∃q∈Q.queries r,c.stk (source F).reduction.machine.queryStack=Q.targetEncoding.encode q := by
  have ho' : RepresentsOracle Q.targetEncoding F.encoding ((targetTables F).evaluate F) oracle := by
    intro q
    rw [target_evaluate]
    exact ho q
  obtain ⟨n,_,ht⟩ := M.execution (data F) oracle ho' r
  have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t c hr hq
  obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
  exact ⟨q,hmem,he.symm⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainControlled
