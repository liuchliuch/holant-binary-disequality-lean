import Holant.Proofs.Algorithms.CBSpecializedNativeHardness
import Holant.Proofs.CountingMachines.StandardMachine.Source


noncomputable section
namespace Holant.LocalDrafts.MainChain.CBStandardNativeHardness
open Computability Holant Holant.Algebraic Holant.Complexity
namespace Standard
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine (Model)
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Source (standard_to_witness)
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.InputRecoding (injectedEncoding)
end Standard
namespace Native
export CBSpecializedNativeHardness.Native (TargetInput targetEncoding targetValue)
end Native
namespace Cost
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (runFee feePolynomial runFee_le configurationWord codedStoragePolynomial coded_storage_le)
end Cost

variable {α Δ Q L : Type} {ea : Encoding α Bool}
variable [Fintype Δ] [Fintype Q] [Field L] [Algebra ℚ L] {d : ℕ}
variable (m : Standard.Model Δ Q) (input : Bool → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock) (F : FixedField L d)

abbrev count : α → ℕ := m.physicalCount (Standard.injectedEncoding ea input hinj)

def source : LengthControlledOracleReduction ea encodingNatBool Native.targetEncoding F.encoding
    (count (ea := ea) m input hinj) (Native.targetValue (L := L)) :=
  CBSpecializedNativeHardness.source F
    (Standard.standard_to_witness (ea := ea) m input hinj clock htime)

def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) :
    (source (ea := ea) m input hinj clock htime F).reduction.machine.OutputsInTime
      oracle (ea.encode x) (encodingNatBool.encode (count (ea := ea) m input hinj x))
      ((source (ea := ea) m input hinj clock htime F).reduction.time.eval (ea.encode x).length) :=
  (source (ea := ea) m input hinj clock htime F).reduction.correct oracle ho x

theorem query_answer_bytes (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ) (c : (source (ea := ea) m input hinj clock htime F).reduction.machine.Cfg)
    (hr : (source (ea := ea) m input hinj clock htime F).reduction.machine.run oracle (ea.encode x) t=some c)
    (hq : (source (ea := ea) m input hinj clock htime F).reduction.machine.IsQuery c) :
    ∃ q : Native.TargetInput,
      c.stk (source (ea := ea) m input hinj clock htime F).reduction.machine.queryStack=Native.targetEncoding.encode q ∧
      Native.targetEncoding.decode (c.stk (source (ea := ea) m input hinj clock htime F).reduction.machine.queryStack)=some q ∧
      oracle (c.stk (source (ea := ea) m input hinj clock htime F).reduction.machine.queryStack)=
        F.encoding.encode (Native.targetValue (L := L) q) := by
  obtain ⟨q,hq,_⟩ := (source (ea := ea) m input hinj clock htime F).safeQuery oracle ho x t c hr hq
  exact ⟨q,hq,by rw [hq]; exact Native.targetEncoding.decode_encode q,by rw [hq]; exact ho q⟩

theorem prefix_fees (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ)
    (ht : t≤(source (ea := ea) m input hinj clock htime F).reduction.time.eval (ea.encode x).length) :
    Cost.runFee (source (ea := ea) m input hinj clock htime F).reduction.machine oracle (ea.encode x) t≤
      (Cost.feePolynomial (source (ea := ea) m input hinj clock htime F)).eval (ea.encode x).length :=
  Cost.runFee_le (source (ea := ea) m input hinj clock htime F) oracle ho x t ht

theorem prefix_coded_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding (Native.targetValue (L := L)) oracle)
    (x : α) (t : ℕ)
    (ht : t≤(source (ea := ea) m input hinj clock htime F).reduction.time.eval (ea.encode x).length)
    (c : (source (ea := ea) m input hinj clock htime F).reduction.machine.Cfg)
    (hr : (source (ea := ea) m input hinj clock htime F).reduction.machine.run oracle (ea.encode x) t=some c) :
    (Cost.configurationWord (source (ea := ea) m input hinj clock htime F).reduction.machine c).length≤
      (Cost.codedStoragePolynomial (source (ea := ea) m input hinj clock htime F)).eval (ea.encode x).length :=
  Cost.coded_storage_le (source (ea := ea) m input hinj clock htime F) oracle ho x t ht c hr

end Holant.LocalDrafts.MainChain.CBStandardNativeHardness
