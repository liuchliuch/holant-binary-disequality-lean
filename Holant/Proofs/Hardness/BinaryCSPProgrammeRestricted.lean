import Holant.Proofs.Hardness.BinaryCSPProgrammeCorrectness
import Holant.Proofs.Hardness.BinaryCSPProgrammeValidated

/-! Actual valid-input restriction of the positive-power oracle programme.
Correctness uses agreement on the exact finite query transcript. No oracle
extension, malformed-input evaluator or fabricated codec identity is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeRestricted
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace M
export BinaryCSPProgrammeMachine (machine timePolynomial interpolatedValue support support_correct execution_agree pre)
end M
namespace V
export BinaryCSPProgrammeValue (value targetOutput)
end V
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b c : K) (f : Bool→Bool→K)

def targetValue (r : P.Input) : K := V.value f r.val
def sourceValue (r : P.Input) : K := M.support f r.val

def targetOutput : PolynomialOutputBound P.inputEncoding F.encoding (targetValue f) where
  bound := (V.targetOutput F a b c f).bound
  length_le r := (V.targetOutput F a b c f).length_le r.val

theorem execution (oracle : List Bool→List Bool)
    (ho : RepresentsOracle P.inputEncoding F.encoding (targetValue f) oracle) (r : P.Input) :
    ∃t≤(M.timePolynomial F a b c f).eval (P.inputEncoding.encode r).length,
      OracleBatch.RunsTrace (M.machine F a b c) oracle ((M.machine F a b c).init (P.inputEncoding.encode r))
        ((M.machine F a b c).output (F.encoding.encode (M.interpolatedValue F a b c f r.val))) t
        ((BinaryCSPProgrammeRepeat.queries r.val).map encoding.encode) :=
  M.execution_agree F a b c f oracle r.val (fun q hq =>
    ho ⟨q,BinaryCSPProgrammeRepeat.query_valid r.val r.property q hq⟩)

def supportControlled (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hf : ∀ x y,f x y=0 ∨ f x y=a ∨ f x y=b ∨ f x y=c) :
    LengthControlledOracleReduction P.inputEncoding F.encoding P.inputEncoding F.encoding
      (sourceValue f) (targetValue f) where
  reduction := {
    machine := M.machine F a b c
    time := M.timePolynomial F a b c f
    correct oracle ho r := by
      have he : sourceValue f r=M.interpolatedValue F a b c f r.val :=
        (M.support_correct F a b c f ha hb hc hf r.val).symm
      rw [he]
      let h := execution F a b c f oracle ho r
      exact {steps:=h.choose,steps_le_m:=h.choose_spec.1,evals_in_steps:=h.choose_spec.2.run} }
  targetOutput := targetOutput F a b c f
  queryBound := (M.pre F a b c).outputBound.bound
  safeQuery oracle ho r t cfg hr hq := by
    obtain ⟨n,_,ht⟩ := execution F a b c f oracle ho r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t cfg hr hq
    obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
    refine ⟨⟨q,BinaryCSPProgrammeRepeat.query_valid r.val r.property q hmem⟩,he.symm,?_⟩
    exact (OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (M.pre F a b c) r.val).1

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeRestricted
