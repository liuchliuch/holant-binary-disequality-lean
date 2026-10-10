import Holant.Proofs.Hardness.BinaryCSPProgrammeCircuit
import Holant.Proofs.Hardness.BinaryCSPProgrammeValidated

/-! The accepted circuit byte writer lands in the proved well-formed raw-CSP
subtype. Its encoded output is literally the previously verified byte stream;
the logical validity proof adds no runtime field or auxiliary input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeFront
open Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.CountingBridge
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

def compile (c : CircuitInstance) : P.Input :=
  ⟨BinaryThreeSupportGraph.compile c,BinaryThreeSupportGraph.compile_wellFormed c⟩

def computes : Computes CircuitInstance.encoding P.inputEncoding compile :=
  recode BinaryCSPProgrammeCircuit.computes id (fun _=>rfl) (fun _=>rfl)

def polyTime : PolyTime CircuitInstance.encoding P.inputEncoding compile := computes.toPolyTime

theorem value_eq {K : Type} [CommRing K] (c : CircuitInstance) :
    BinaryThreeSupportGraph.value (K:=K) (compile c).val=(c.value : K) :=
  BinaryThreeSupportGraph.compile_value c

theorem every_prefix_fees (c : CircuitInstance) (t : ℕ)
    (ht : t≤computes.time.eval (CircuitInstance.encoding.encode c).length) :
    primitiveCost computes.machine t
      (some (Turing.initList computes.machine.computer (CircuitInstance.encoding.encode c)))≤
      (primitivePolynomial computes).eval (CircuitInstance.encoding.encode c).length :=
  BinaryCSPProgrammeCore.prefix_primitive_bound computes c t ht

theorem every_prefix_storage (c : CircuitInstance) (t : ℕ) (cfg : computes.machine.Config)
    (hr : (fun q=>q.bind computes.machine.computer.step)^[t]
      (some (Turing.initList computes.machine.computer (CircuitInstance.encoding.encode c)))=some cfg)
    (ht : t≤computes.time.eval (CircuitInstance.encoding.encode c).length) :
    stackSize cfg.stk≤computes.outputBound.bound.eval (CircuitInstance.encoding.encode c).length :=
  BinaryCSPProgrammeCore.prefix_storage_bound computes c t cfg hr ht

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeFront
