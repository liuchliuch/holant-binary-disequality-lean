import Holant.Proofs.Hardness.BinaryThreeSupportStarProgrammeCorrectness
import Holant.Proofs.Hardness.BinaryCSPProgrammeValidated
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-! Valid signed raw CSPs reduce to the unsigned NAND table by the actual
star/interpolation programme. Oracle correctness is used only on the emitted
well-formed queries. The original codec and declared variable slots remain. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeSigned
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace M
export BinaryThreeSupportStarMachine (machine timePolynomial interpolatedValue targetValue
  execution_agree interpolatedValue_eq pre outputBound)
end M
namespace Q
export BinaryCSPProgrammeStars (queries query_valid)
end Q
namespace R
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (runFee feePolynomial runFee_le configurationWord codedStoragePolynomial coded_storage_le)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d)

def targetValue (r : P.Input) : K := M.targetValue r.val
def sourceValue (r : P.Input) : K := BinaryThreeSupportGraph.value r.val

def targetOutput : PolynomialOutputBound P.inputEncoding F.encoding (targetValue (K:=K)) where
  bound := (M.outputBound F).bound
  length_le r := (M.outputBound F).length_le r.val

theorem execution (oracle : List Bool→List Bool)
    (ho : RepresentsOracle P.inputEncoding F.encoding (targetValue (K:=K)) oracle) (r : P.Input) :
    ∃t≤(M.timePolynomial F).eval (P.inputEncoding.encode r).length,
      OracleBatch.RunsTrace (M.machine F) oracle ((M.machine F).init (P.inputEncoding.encode r))
        ((M.machine F).output (F.encoding.encode (M.interpolatedValue r.val))) t
        ((Q.queries r.val).map encoding.encode) :=
  M.execution_agree F oracle r.val (fun q hq=>ho ⟨q,Q.query_valid r.val r.property q hq⟩)

def controlled : LengthControlledOracleReduction P.inputEncoding F.encoding P.inputEncoding F.encoding
    (sourceValue (K:=K)) (targetValue (K:=K)) where
  reduction := {
    machine := M.machine F
    time := M.timePolynomial F
    correct oracle ho r := by
      have he : sourceValue r=M.interpolatedValue (K:=K) r.val :=
        (M.interpolatedValue_eq r.val r.property).symm
      rw [he]
      let h := execution F oracle ho r
      exact {steps:=h.choose,steps_le_m:=h.choose_spec.1,evals_in_steps:=h.choose_spec.2.run} }
  targetOutput := targetOutput F
  queryBound := M.pre.outputBound.bound
  safeQuery oracle ho r t cfg hr hq := by
    obtain ⟨n,_,ht⟩ := execution F oracle ho r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t cfg hr hq
    obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
    refine ⟨⟨q,Q.query_valid r.val r.property q hmem⟩,he.symm,?_⟩
    exact (OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le M.pre r.val).1

theorem every_prefix_fees (oracle : List Bool→List Bool)
    (ho : RepresentsOracle P.inputEncoding F.encoding (targetValue (K:=K)) oracle)
    (r : P.Input) (t : ℕ)
    (ht : t≤(M.timePolynomial F).eval (P.inputEncoding.encode r).length) :
    R.runFee (M.machine F) oracle (P.inputEncoding.encode r) t≤
      (R.feePolynomial (controlled F)).eval (P.inputEncoding.encode r).length :=
  R.runFee_le (controlled F) oracle ho r t ht

theorem every_prefix_storage (oracle : List Bool→List Bool)
    (ho : RepresentsOracle P.inputEncoding F.encoding (targetValue (K:=K)) oracle)
    (r : P.Input) (t : ℕ)
    (ht : t≤(M.timePolynomial F).eval (P.inputEncoding.encode r).length)
    (cfg : (M.machine F).Cfg)
    (hr : (M.machine F).run oracle (P.inputEncoding.encode r) t=some cfg) :
    (R.configurationWord (M.machine F) cfg).length≤
      (R.codedStoragePolynomial (controlled F)).eval (P.inputEncoding.encode r).length :=
  R.coded_storage_le (controlled F) oracle ho r t ht cfg hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeSigned
