import Holant.Complexity.GraphPreprocessing.UnaryBinary
import Holant.Complexity.FixedFieldMachines.LeftMap
import Holant.Complexity.ClosedNetworkEncoding

/-! Physical unary-edge query materialization through the actual binary carry
machine and actual framing loops. No natural-to-word callback runs on a tape. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointQuery
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines

/-- The edge counter is framed; the literal original-end bit is the remaining suffix. -/
def inputEncoding : Encoding RawEndpoint Bool := pairEncoding UnaryBinary.unaryEncoding encodingBoolBool

abbrev machine : BinaryCompose.Machine := LeftMap.machine UnaryBinary.machine

def ticks (edge : ℕ) : ℕ := UnaryBinary.ticks [] edge + 2 * edge + 2 * (encodeNat edge).length + 7

/-- Exact execution includes framing, every carry and restoration step, and halt. -/
theorem exact_run (edge : ℕ) (side : Bool) :
    RunsExactly machine.computer.step
      (initList machine.computer (inputEncoding.encode (edge,side)))
      (haltList machine.computer (RawClosedNetwork.endpointEncoding.encode (edge,side))) (ticks edge) := by
  have first := UnaryBinary.convert_exact (List.replicate edge true) 0
  change UnaryBinary.Runs (UnaryBinary.config 0 (List.replicate edge true) [] [])
    (UnaryBinary.config 3 [] (encodeNat (0 + (List.replicate edge true).length)) []) _ at first
  simp only [List.length_replicate, Nat.zero_add, UnaryBinary.initial_eq] at first
  have source := first.trans (UnaryBinary.Runs.one (UnaryBinary.halt_step (encodeNat edge)))
  have run := LeftMap.exact_run UnaryBinary.machine _ _ (encodingBoolBool.encode side) _ source
  have ht : ticks edge = 2 * (List.replicate edge true).length +
      (1 + UnaryBinary.ticks (encodeNat 0) edge) + 2 * (encodeNat edge).length + 6 := by
    change UnaryBinary.ticks [] edge + 2 * edge + 2 * (encodeNat edge).length + 7 =
      2 * (List.replicate edge true).length + (1 + UnaryBinary.ticks [] edge) + 2 * (encodeNat edge).length + 6
    simp only [List.length_replicate]
    omega
  rw [ht]
  exact run

/-- A genuine polynomial-time query serializer, retaining the original endpoint meaning. -/
noncomputable def computes : BinaryCompose.Computes inputEncoding RawClosedNetwork.endpointEncoding id :=
  recode (leftMapComputes encodingBoolBool UnaryBinary.computes) id (fun _ => rfl) (fun _ => rfl)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointQuery
