import Holant.Proofs.Hardness.BinaryIsingNand
import Holant.Proofs.Hardness.BinaryIsingRows
import Holant.Proofs.Hardness.BinaryCSPProgrammeApex
import Holant.Proofs.Platonic.PhysicalCostComposition

/-! The complete unpinned Ising source: the actual unsigned NAND-count programme
calls only original quaternary vertices and native disequality edges. All root
arithmetic, unused-bit correction, the global factor 1/2, and answer bytes use
the original supplied fixed-field presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingSource
open Turing Computability Holant Holant.Algebraic Holant.Complexity
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace I
export BinaryIsingProgramme (validQueryEncoding validQueryValue)
end I
namespace A
export BinaryCSPProgrammeApex (expand controlled)
end A
namespace N
export BinaryCSPProgrammeNative (targetValue tables)
end N
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (TargetInput targetEncoding)
end O
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace R
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (runFee feePolynomial runFee_le configurationWord codedStoragePolynomial coded_storage_le)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (p q : K)

omit [Algebra ℚ K] in
theorem query_semantics (a : BinaryIsingProgramme.ValidQuery) :
    I.validQueryValue p q a=
      BinaryCSPProgrammeMixed.mixedValue (BinaryIsingWeights.table p q) (A.expand a) :=
  BinaryIsingRows.value_eq_mixed p q a.1.val a.1.property a.2

def queryControlled (hm : M=EOBinaryPlaneCore.lift (BinaryIsingWeights.table p q)) :
    LengthControlledOracleReduction I.validQueryEncoding F.encoding O.targetEncoding F.encoding
      (I.validQueryValue p q) (N.targetValue F M) where
  reduction := {
    machine := (A.controlled F M (BinaryIsingWeights.table p q) hm).reduction.machine
    time := (A.controlled F M (BinaryIsingWeights.table p q) hm).reduction.time
    correct oracle ho a := by
      rw [query_semantics]
      exact (A.controlled F M (BinaryIsingWeights.table p q) hm).reduction.correct oracle ho a }
  targetOutput := (A.controlled F M (BinaryIsingWeights.table p q) hm).targetOutput
  queryBound := (A.controlled F M (BinaryIsingWeights.table p q) hm).queryBound
  safeQuery := (A.controlled F M (BinaryIsingWeights.table p q) hm).safeQuery

def controlled (hm : M=EOBinaryPlaneCore.lift (BinaryIsingWeights.table p q))
    (hp : p≠0) (hq : q≠0) (hr : ∀j,0<j→(q/p)^(2*j)≠1) :
    LengthControlledOracleReduction P.inputEncoding F.encoding O.targetEncoding F.encoding
      (BinaryCSPProgrammeSigned.targetValue (K:=K)) (N.targetValue F M) :=
  C.composeControlled (BinaryIsingNand.controlled F p q hp hq hr) (queryControlled F M p q hm)

/-- A positive real nonunit image proves the denominator conditions only. No
embedding, inverse embedding, or enlarged answer codec is used by the machine. -/
def positiveControlled (hm : M=EOBinaryPlaneCore.lift (BinaryIsingWeights.table p q))
    (hp : p≠0) (hq : q≠0) (ι : K→+*ℂ) (r : ℝ) (hr : 0<r) (hne : r≠1)
    (hi : ι (q/p)=(r : ℂ)) :
    LengthControlledOracleReduction P.inputEncoding F.encoding O.targetEncoding F.encoding
      (BinaryCSPProgrammeSigned.targetValue (K:=K)) (N.targetValue F M) :=
  controlled F M p q hm hp hq (BinaryIsingFilter.positive_image_ne_one (q/p) ι r hr hne hi)

variable (hm : M=EOBinaryPlaneCore.lift (BinaryIsingWeights.table p q))
  (hp : p≠0) (hq : q≠0) (hr : ∀j,0<j→(q/p)^(2*j)≠1)

def exact_answer (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle) (r : P.Input) :
    (controlled F M p q hm hp hq hr).reduction.machine.OutputsInTime oracle
      (P.inputEncoding.encode r) (F.encoding.encode (BinaryCSPProgrammeSigned.targetValue r))
      ((controlled F M p q hm hp hq hr).reduction.time.eval (P.inputEncoding.encode r).length) :=
  (controlled F M p q hm hp hq hr).reduction.correct oracle ho r

theorem every_prefix_fees (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle)
    (r : P.Input) (t : ℕ)
    (ht : t≤(controlled F M p q hm hp hq hr).reduction.time.eval (P.inputEncoding.encode r).length) :
    R.runFee (controlled F M p q hm hp hq hr).reduction.machine oracle (P.inputEncoding.encode r) t≤
      (R.feePolynomial (controlled F M p q hm hp hq hr)).eval (P.inputEncoding.encode r).length :=
  R.runFee_le (controlled F M p q hm hp hq hr) oracle ho r t ht

theorem every_prefix_storage (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle)
    (r : P.Input) (t : ℕ)
    (ht : t≤(controlled F M p q hm hp hq hr).reduction.time.eval (P.inputEncoding.encode r).length)
    (cfg : (controlled F M p q hm hp hq hr).reduction.machine.Cfg)
    (hc : (controlled F M p q hm hp hq hr).reduction.machine.run oracle (P.inputEncoding.encode r) t=some cfg) :
    (R.configurationWord (controlled F M p q hm hp hq hr).reduction.machine cfg).length≤
      (R.codedStoragePolynomial (controlled F M p q hm hp hq hr)).eval (P.inputEncoding.encode r).length :=
  R.coded_storage_le (controlled F M p q hm hp hq hr) oracle ho r t ht cfg hc

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingSource
