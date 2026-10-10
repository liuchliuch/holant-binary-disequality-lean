import Holant.Complexity.WitnessCounting
import Holant.Complexity.OracleMachine
import Holant.Proofs.Counting.Circuit


namespace Holant.LocalDrafts.CountingHardness

open Computability Holant.Complexity

/-- Universal polynomial-time oracle hardness for all actual finite verifiers
on faithfully Boolean-encoded inputs. -/
def WitnessCountingHard {β δ : Type} (eb : Encoding β Bool) (ed : Encoding δ Bool)
    (g : β → δ) : Prop :=
  ∀ (α : Type) (ea : Encoding α Bool) (f : α → ℕ),
    ∀ _w : SharpPWitness ea f,
      Nonempty (PolyTimeOracleReduction ea encodingNatBool eb ed f g)

/-- Naming the target obligation is not a proof of it. -/
def CircuitCountingHard : Prop :=
  WitnessCountingHard CircuitInstance.encoding encodingNatBool CircuitInstance.value

end Holant.LocalDrafts.CountingHardness
