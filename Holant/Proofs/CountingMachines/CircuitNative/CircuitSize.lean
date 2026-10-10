import Holant.Proofs.CountingMachines.CircuitNative.Circuit
import Holant.Complexity.OutputSize

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.CircuitInstance

open Computability Holant.Complexity

theorem value_le (c : CircuitInstance) : c.value ≤ 2 ^ c.inputs := by
  simpa [value] using countAccepted_le c.circuit.eval

theorem output_length_le (c : CircuitInstance) :
    (encodingNatBool.encode c.value).length ≤ (encoding.encode c).length + 1 := by
  have hc : (encodingNatBool.encode c.value).length ≤ c.inputs + 1 := by
    change (encodeNat c.value).length ≤ _
    rw [Holant.Algebraic.encodeNat_length]
    exact le_trans (Nat.size_le_size (value_le c)) Nat.size_pow.le
  exact le_trans hc (Nat.add_le_add_right c.inputs_le_encoded_length 1)

noncomputable def outputBound : PolynomialOutputBound encoding encodingNatBool value where
  bound := Polynomial.X + 1
  length_le c := by simpa using output_length_le c

end Holant.LocalDrafts.RemoteWork.CountingBridge.CircuitInstance
