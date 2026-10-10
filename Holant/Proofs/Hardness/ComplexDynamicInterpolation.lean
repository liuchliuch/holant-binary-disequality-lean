import Holant.Proofs.Hardness.PositiveDynamicMachine
import Holant.Proofs.Hardness.ComplexDynamicGraphFilter
import Holant.Proofs.Algorithms.TraceQueryControl

/-! Same-field literal [q,E] to original q dynamic interpolation. The original
marked count drives n=C*(m+1), both root arithmetic and fully inlined graph
queries. The finite machine and actual emitted field programmes are internal;
complex norm-cone data prove the denominator nonzero. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicInterpolation
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding)
export PositiveDynamicQueries (value)
end Q
namespace G
export ThreeModeGraphEvaluation (sourceValue targetValue targetSignatures kernels)
end G
namespace M
export PositiveDynamicMachine (Data interpolatedValue value_formula machine timePolynomial pre
  execution reduction values)
end M
namespace GF
export ComplexDynamicGraphFilter (queryValue recovery)
end GF
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d : ℕ}
variable (a b c : K) (F : FixedField K d) (params : ComplexDynamicParameters.Data)

def targetTables : ExactSignatureTables d 1 1 Q.arity where
  vertex i x := F.decode.symm (G.targetSignatures a b c i x)
  edge i x y := F.decode.symm (G.kernels i x y)

omit [CharZero K] in
theorem target_evaluate (r : Q.TargetInput) :
    (targetTables a b c F).evaluate F r=G.targetValue a b c r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

def data : M.Data F (targetTables a b c F) where
  a := a
  b := b
  c := c
  params := params.realParams

omit [CharZero K] in
theorem values_eq (r : Q.Input) : M.values (data a b c F params) r=GF.queryValue a b c params r :=
  funext (fun k=>target_evaluate a b c F (Q.value params.realParams (k,r)))

variable (σ : K→+*ℂ) (ha : σ a=params.a) (hb : σ b=params.b) (hc : σ c=params.c)

include ha hb hc in
theorem value_correct (r : Q.Input) :
    M.interpolatedValue (data a b c F params) r=G.sourceValue a b c r := by
  rw [M.value_formula,values_eq]
  exact GF.recovery a b c params σ ha hb hc r

def targetOutput : PolynomialOutputBound Q.targetEncoding F.encoding (G.targetValue a b c) where
  bound := ((targetTables a b c F).outputBound F).bound
  length_le r := by
    rw [←target_evaluate a b c F r]
    exact ((targetTables a b c F).outputBound F).length_le r

/-- Actual finite programme from the literal E oracle to the original q oracle. -/
def source : LengthControlledOracleReduction Q.sourceEncoding F.encoding Q.targetEncoding F.encoding
    (G.sourceValue a b c) (G.targetValue a b c) where
  reduction := {
    machine := M.machine (data a b c F params)
    time := M.timePolynomial (data a b c F params)
    correct oracle ho r := by
      have ho' : RepresentsOracle Q.targetEncoding F.encoding
          ((targetTables a b c F).evaluate F) oracle := by
        intro q
        rw [target_evaluate]
        exact ho q
      rw [←value_correct a b c F params σ ha hb hc r]
      exact (M.reduction (data a b c F params)).correct oracle ho' r }
  targetOutput := targetOutput a b c F
  queryBound := (M.pre (data a b c F params)).outputBound.bound
  safeQuery oracle ho r t cfg hr hq := by
    have ho' : RepresentsOracle Q.targetEncoding F.encoding
        ((targetTables a b c F).evaluate F) oracle := by
      intro q
      rw [target_evaluate]
      exact ho q
    obtain ⟨n,_,ht⟩ := M.execution (data a b c F params) oracle ho' r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t cfg hr hq
    obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
    exact ⟨q,he.symm,(OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (M.pre (data a b c F params)) r).1⟩

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (G.targetValue a b c) oracle) (r : Q.Input) :=
  (source a b c F params σ ha hb hc).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicInterpolation
