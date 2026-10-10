import Holant.Proofs.Hardness.ThreeModeMachine
import Holant.Proofs.Hardness.ThreeModeGraphFilter
import Holant.Proofs.Hardness.EqualModulusThreeModeLocal
import Holant.Proofs.Algorithms.TraceQueryControl

/-! The unchanged actual three-mode annihilator programme, exposed for the
finite original-field equality test. The closed public source supplies every
normalization denominator from that test and the secondary modulus gap. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeInterpolation
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding value)
end Q
namespace G
export ThreeModeGraphEvaluation (sourceValue targetValue targetSignatures kernels queryValue)
end G
namespace M
export ThreeModeMachine (Data interpolatedValue value_formula machine timePolynomial pre
  execution reduction values)
end M
namespace A
export ThreeModeAnnihilator (denominator)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d : ℕ}
variable (a b c : K) (F : FixedField K d)

def targetTables : ExactSignatureTables d 1 1 Q.arity where
  vertex i x := F.decode.symm (G.targetSignatures a b c i x)
  edge i x y := F.decode.symm (G.kernels i x y)

omit [CharZero K] in
theorem target_evaluate (r : Q.TargetInput) :
    (targetTables a b c F).evaluate F r=G.targetValue a b c r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

def data : M.Data F (targetTables a b c F) where
  lam := c
  mu := a+b
  nu := b-a

omit [CharZero K] in
theorem values_eq (r : Q.Input) : M.values (data a b c F) r=G.queryValue a b c r :=
  funext (fun k=>target_evaluate a b c F (Q.value (k,r)))

variable (hd : ∀m : ℕ, A.denominator m c (a+b) (b-a)≠0)

include hd in
theorem value_correct (r : Q.Input) :
    M.interpolatedValue (data a b c F) r=G.sourceValue a b c r := by
  rw [M.value_formula,values_eq]
  exact ThreeModeGraphFilter.recovery a b c r (hd _)

def targetOutput : PolynomialOutputBound Q.targetEncoding F.encoding (G.targetValue a b c) where
  bound := ((targetTables a b c F).outputBound F).bound
  length_le r := by
    rw [←target_evaluate a b c F r]
    exact ((targetTables a b c F).outputBound F).length_le r

/-- Real finite programme from the literal E oracle to the original q oracle. -/
def source : LengthControlledOracleReduction Q.sourceEncoding F.encoding Q.targetEncoding F.encoding
    (G.sourceValue a b c) (G.targetValue a b c) where
  reduction := {
    machine := M.machine (data a b c F)
    time := M.timePolynomial (data a b c F)
    correct oracle ho r := by
      have ho' : RepresentsOracle Q.targetEncoding F.encoding
          ((targetTables a b c F).evaluate F) oracle := by
        intro q
        rw [target_evaluate]
        exact ho q
      rw [←value_correct a b c F hd r]
      exact (M.reduction (data a b c F)).correct oracle ho' r }
  targetOutput := targetOutput a b c F
  queryBound := (M.pre (data a b c F)).outputBound.bound
  safeQuery oracle ho r t cfg hr hq := by
    have ho' : RepresentsOracle Q.targetEncoding F.encoding
        ((targetTables a b c F).evaluate F) oracle := by
      intro q
      rw [target_evaluate]
      exact ho q
    obtain ⟨n,_,ht⟩ := M.execution (data a b c F) oracle ho' r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t cfg hr hq
    obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
    exact ⟨q,he.symm,(OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (M.pre (data a b c F)) r).1⟩

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (G.targetValue a b c) oracle) (r : Q.Input) :=
  (source a b c F hd).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeInterpolation
