import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeMachine
import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeNetwork
import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeSemantics

/-! Actual polynomial-time elimination of a conjugated full-support binary
label. All physical queries use the original table and original field K.
Only answered-transcript arithmetic takes place in the explicitly embedded
common star-field L. No evaluator, backend, target clock, codec equality,
root-distinctness or conjugation-closure premise is supplied by the caller. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgramme
open Turing Computability Holant Holant.Algebraic Holant.Complexity
namespace Q
export EOBinaryConjugateProgrammeQueries (Input inputEncoding originalValue count queries)
end Q
namespace C
export ExactTwoChainQueries (TargetInput targetEncoding value)
end C
namespace P
export EOBinaryConjugateProgrammePairs (roots roots_conjugate)
end P
namespace B
export EOBinaryConjugateProgrammeBase (coefficients state answers)
end B
namespace N
export EOBinaryPlaneConjugateNetwork (value base marked row selected mixed_value)
end N
namespace H
export EOBinaryConjugateProgrammeNetwork (roots_nonzero marked_mem answers_moments)
end H
namespace M
export EOBinaryConjugateProgrammeMachine (machine timePolynomial interpolatedValue controlled query_origin)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] [StarRing L]
variable {d e : ℕ} (F : FixedField K d) (G : FixedField L e) (into : K→ₐ[ℚ] L) (f : Signature K 2)
local instance : CharZero L := algebraRat.charZero L

def value (r : Q.Input) : L :=
  N.value (fun z=>into (f z)) (fun z=>star (into (f z))) r

/-- The exact result of the physically executed arithmetic loop. -/
theorem interpolated_correct (hf : ∀z,f z≠0) (r : Q.Input) :
    M.interpolatedValue G into f r=value into f r := by
  change EOBinaryConjugateProgrammeLoop.result G
    (EOBinaryConjugateProgrammeState.initial
      (P.roots (B.coefficients into f) r.val.vertices.length) ((B.answers f r).map into))=_
  rw [H.answers_moments]
  have h:=EOBinaryConjugateProgrammeSemantics.physical_reconstruct G
    (P.roots (B.coefficients into f) r.val.vertices.length)
    (fun a : Fin r.val.edges.length→Bool=>into (N.base f r a))
    (fun a=>into (N.marked f (N.selected r) (N.row r a)))
    (H.roots_nonzero into f hf r.val.vertices.length)
    (P.roots_conjugate (B.coefficients into f) r.val.vertices.length)
    (H.marked_mem into f r)
  exact h.trans (N.mixed_value into.toRingHom f r).symm

/-- The complete source-to-original-field controlled reduction. -/
def controlled (hf : ∀z,f z≠0) :
    LengthControlledOracleReduction Q.inputEncoding G.encoding C.targetEncoding F.encoding
      (value into f) (Q.originalValue f) where
  reduction := {
    machine:=(M.controlled F G into f).reduction.machine
    time:=(M.controlled F G into f).reduction.time
    correct oracle ho r:=by
      rw [←interpolated_correct G into f hf r]
      exact (M.controlled F G into f).reduction.correct oracle ho r }
  targetOutput:=(M.controlled F G into f).targetOutput
  queryBound:=(M.controlled F G into f).queryBound
  safeQuery:=(M.controlled F G into f).safeQuery

theorem same_machine (hf : ∀z,f z≠0) :
    (controlled F G into f hf).reduction.machine=M.machine F G into f := rfl

theorem same_clock (hf : ∀z,f z≠0) :
    (controlled F G into f hf).reduction.time=M.timePolynomial F G into f := rfl

/-- Every oracle call is a positive original-table moment within the quartic grid. -/
theorem query_origin (hf : ∀z,f z≠0) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle C.targetEncoding F.encoding (Q.originalValue f) oracle)
    (r : Q.Input) (t : ℕ) (cfg : (controlled F G into f hf).reduction.machine.Cfg)
    (hr : (controlled F G into f hf).reduction.machine.run oracle (Q.inputEncoding.encode r) t=some cfg)
    (hq : (controlled F G into f hf).reduction.machine.IsQuery cfg) :
    ∃k,0<k+1 ∧ k+1≤(r.val.vertices.length+1)^4 ∧
      cfg.stk (controlled F G into f hf).reduction.machine.queryStack=C.targetEncoding.encode (C.value (k,r)) := by
  obtain ⟨k,hk,hk'⟩:=M.query_origin F G into f oracle ho r t cfg hr hq
  exact ⟨k,Nat.zero_lt_succ _,by unfold Q.count at hk; omega,hk'⟩

theorem every_prefix_fees (hf : ∀z,f z≠0) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle C.targetEncoding F.encoding (Q.originalValue f) oracle) (r : Q.Input) (t : ℕ)
    (ht : t≤(M.timePolynomial F G into f).eval (Q.inputEncoding.encode r).length) :
    Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee
      (M.machine F G into f) oracle (Q.inputEncoding.encode r) t≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.feePolynomial
        (controlled F G into f hf)).eval (Q.inputEncoding.encode r).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee_le
    (controlled F G into f hf) oracle ho r t ht

theorem every_prefix_storage (hf : ∀z,f z≠0) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle C.targetEncoding F.encoding (Q.originalValue f) oracle) (r : Q.Input) (t : ℕ)
    (ht : t≤(M.timePolynomial F G into f).eval (Q.inputEncoding.encode r).length)
    (cfg : (M.machine F G into f).Cfg)
    (hr : (M.machine F G into f).run oracle (Q.inputEncoding.encode r) t=some cfg) :
    (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.configurationWord (M.machine F G into f) cfg).length≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.codedStoragePolynomial
        (controlled F G into f hf)).eval (Q.inputEncoding.encode r).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.coded_storage_le
    (controlled F G into f hf) oracle ho r t ht cfg hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgramme
