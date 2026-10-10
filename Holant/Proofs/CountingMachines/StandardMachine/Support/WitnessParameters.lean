import Holant.Proofs.CountingMachines.VerifierCircuit.Support.Polynomial
import Holant.Proofs.CountingMachines.StandardMachine.Support.Foundation

set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.WitnessParameters
open Computability Holant.Complexity
open Holant.LocalDrafts.CountingHardness
export Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters (unary polynomialComputes parameterComputes)
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)
noncomputable def witnessComputes := parameterComputes ea w.witnessLength
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.WitnessParameters
