import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetSharpWitnessCore
import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Source

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetSharpWitness
open Turing Computability Holant.Complexity
variable (m : BinaryMachine) (T : Polynomial ℕ) (acceptControl : m.core.σ → Bool)
local instance (key : m.core.K) : Fintype (m.core.Γ key) := m.alphabets key
variable {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀))

/-- Optional literal Boolean encoding bridge, applied ONLY after the original
Γ witness and its actual verifier/count have been produced above. Its physical
old-length counter and unique false suffix are the delivered producers. -/
def booleanSource : SharpPWitness (BooleanInputWitness.inputEncoding (source m T acceptControl ea))
    (boundedCount m T acceptControl ea) :=
  BooleanInputWitness.Source.source (source m T acceptControl ea)

theorem boolean_same_count (a : α) :
    boundedCount m T acceptControl ea a =
      witnessCount ((booleanSource m T acceptControl ea).witnessLength.eval
        ((BooleanInputWitness.inputEncoding (source m T acceptControl ea)).encode a).length)
        (fun bits => (booleanSource m T acceptControl ea).accept (a,bits)) :=
  (booleanSource m T acceptControl ea).counts a
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetSharpWitness
