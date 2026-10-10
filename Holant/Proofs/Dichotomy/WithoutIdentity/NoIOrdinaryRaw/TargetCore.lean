import Holant.Complexity.OracleQueryBounds
import Holant.Complexity.WitnessCounting

/-! An exact oracle destination and its actual counted-verifier hardness
predicate, independent of source-selection programmes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw
open Computability Holant Holant.Complexity
structure Target : Type 1 where
  Input : Type
  Output : Type
  inputEncoding : Encoding Input Bool
  outputEncoding : Encoding Output Bool
  value : Input→Output

def Target.Hard (T : Target) : Prop:=∀(A : Type) (encoding : Encoding A Bool) (count : A→ℕ),
  SharpPWitness encoding count→Nonempty (LengthControlledOracleReduction encoding encodingNatBool
    T.inputEncoding T.outputEncoding count T.value)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw
end
