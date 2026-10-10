import Holant.Proofs.Hardness.BinaryCSPCountingSource
import Holant.Proofs.Hardness.BinaryIsingQueryOrigin
import Holant.Proofs.CountingMachines.StandardMachine.Source
import Holant.Proofs.Counting.Hardness

/-! Natural and conventional accepting-path counting into the original Ising
quaternary/native-X oracle. The counting frontend, signed-star interpolation,
positive Ising filter, exact scalar corrections, and natural answer decoder
are all concrete programmes composed here. Every oracle answer uses the
supplied original fixed coefficient presentation; the source result is decoded
into the canonical natural-number answer encoding. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingCountingSource
open Turing Computability Holant Holant.Algebraic Holant.Complexity
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (targetEncoding)
end O
namespace N
export BinaryCSPProgrammeNative (targetValue)
end N
namespace R
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (runFee feePolynomial runFee_le configurationWord codedStoragePolynomial coded_storage_le)
end R
namespace Standard
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine (Model)
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Source (standard_to_witness)
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.InputRecoding (injectedEncoding)
end Standard
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (p q : K)
variable (hm : M=EOBinaryPlaneCore.lift (BinaryIsingWeights.table p q))
  (hp : p≠0) (hq : q≠0) (hs : ∀j,0<j→(q/p)^(2*j)≠1)
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding F.encoding f (N.targetValue F M) :=
  C.composeControlled
    (C.composeControlled (BinaryCSPCountingSource.source F w) (BinaryCSPProgrammeSigned.controlled F))
    (BinaryIsingSource.controlled F M p q hm hp hq hs)

def positiveSource (ι : K→+*ℂ) (r : ℝ) (hr : 0<r) (hne : r≠1)
    (hi : ι (q/p)=(r : ℂ)) (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool O.targetEncoding F.encoding f (N.targetValue F M) :=
  source F M p q hm hp hq (BinaryIsingFilter.positive_image_ne_one (q/p) ι r hr hne hi) w

include hm hp hq hs in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    O.targetEncoding F.encoding (N.targetValue F M) := by
  intro α ea f w
  exact ⟨(source F M p q hm hp hq hs w).reduction⟩

variable (w : SharpPWitness ea f)
attribute [local irreducible] source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle) (x : α) :
    (source F M p q hm hp hq hs w).reduction.machine.OutputsInTime oracle (ea.encode x)
      (encodingNatBool.encode (f x))
      ((source F M p q hm hp hq hs w).reduction.time.eval (ea.encode x).length) :=
  (source F M p q hm hp hq hs w).reduction.correct oracle ho x

theorem query_answer_bytes (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle)
    (x : α) (t : ℕ) (cfg : (source F M p q hm hp hq hs w).reduction.machine.Cfg)
    (hr : (source F M p q hm hp hq hs w).reduction.machine.run oracle (ea.encode x) t=some cfg)
    (hc : (source F M p q hm hp hq hs w).reduction.machine.IsQuery cfg) :
    ∃query,
      cfg.stk (source F M p q hm hp hq hs w).reduction.machine.queryStack=O.targetEncoding.encode query ∧
      O.targetEncoding.decode (cfg.stk (source F M p q hm hp hq hs w).reduction.machine.queryStack)=some query ∧
      oracle (cfg.stk (source F M p q hm hp hq hs w).reduction.machine.queryStack)=
        F.encoding.encode (N.targetValue F M query) := by
  obtain ⟨query,he,_⟩ := (source F M p q hm hp hq hs w).safeQuery oracle ho x t cfg hr hc
  exact ⟨query,he,by rw [he]; exact O.targetEncoding.decode_encode query,by rw [he]; exact ho query⟩

theorem every_prefix_fees (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle)
    (x : α) (t : ℕ)
    (ht : t≤(source F M p q hm hp hq hs w).reduction.time.eval (ea.encode x).length) :
    R.runFee (source F M p q hm hp hq hs w).reduction.machine oracle (ea.encode x) t≤
      (R.feePolynomial (source F M p q hm hp hq hs w)).eval (ea.encode x).length :=
  R.runFee_le (source F M p q hm hp hq hs w) oracle ho x t ht

theorem every_prefix_storage (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle)
    (x : α) (t : ℕ)
    (ht : t≤(source F M p q hm hp hq hs w).reduction.time.eval (ea.encode x).length)
    (cfg : (source F M p q hm hp hq hs w).reduction.machine.Cfg)
    (hr : (source F M p q hm hp hq hs w).reduction.machine.run oracle (ea.encode x) t=some cfg) :
    (R.configurationWord (source F M p q hm hp hq hs w).reduction.machine cfg).length≤
      (R.codedStoragePolynomial (source F M p q hm hp hq hs w)).eval (ea.encode x).length :=
  R.coded_storage_le (source F M p q hm hp hq hs w) oracle ho x t ht cfg hr

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool O.targetEncoding F.encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (N.targetValue F M) :=
  source F M p q hm hp hq hs (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

def positiveStandardSource (ι : K→+*ℂ) (r : ℝ) (hr : 0<r) (hne : r≠1)
    (hi : ι (q/p)=(r : ℂ)) : LengthControlledOracleReduction ea encodingNatBool O.targetEncoding F.encoding
      (m.physicalCount (Standard.injectedEncoding ea input hinj)) (N.targetValue F M) :=
  standardSource F M p q hm hp hq (BinaryIsingFilter.positive_image_ne_one (q/p) ι r hr hne hi)
    m input hinj clock htime

attribute [local irreducible] standardSource

def standard_outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle) (x : α) :
    (standardSource (ea:=ea) F M p q hm hp hq hs m input hinj clock htime).reduction.machine.OutputsInTime
      oracle (ea.encode x)
      (encodingNatBool.encode (m.physicalCount (Standard.injectedEncoding ea input hinj) x))
      ((standardSource (ea:=ea) F M p q hm hp hq hs m input hinj clock htime).reduction.time.eval (ea.encode x).length) :=
  (standardSource (ea:=ea) F M p q hm hp hq hs m input hinj clock htime).reduction.correct oracle ho x

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingCountingSource
