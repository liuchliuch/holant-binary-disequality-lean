import Holant.Proofs.Closure.ClosureMarkedPlatonicSubgroup
import Holant.Proofs.Closure.ClosureMarkedHistoryReceipts

/-! NEW_POST_RECOVERY; pending fresh check. Resolve the actual source model
at the SAME returned physical marking, preserving every old receipt and edge.
Actual Platonic model data does not provide its basis/gadget/rigidity/complexity
consumer. No model or future compiler is an input to the public producer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedActualReceipts
open Holant Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

structure Result (P : Palette G) (torsion : ResidualTorsion P.family) : Type 1 where
  physical : ClosureMarkedHistoryReceipts.Result G P torsion
  actual : ClosureMarkedPlatonicSubgroup.Source.ActualFor
    (algebraicEmbedding G) P.family torsion physical.marking

def produce (P : Palette G) (torsion : ResidualTorsion P.family) : Result G P torsion :=
  let R := ClosureMarkedHistoryReceipts.produce G P torsion
  ⟨R,ClosureMarkedPlatonicSubgroup.Source.refine (algebraicEmbedding G) P.family torsion R.marking⟩

@[simp] theorem same_physical (P : Palette G) (torsion : ResidualTorsion P.family) :
    (produce G P torsion).physical = ClosureMarkedHistoryReceipts.produce G P torsion := rfl

theorem same_marking (P : Palette G) (torsion : ResidualTorsion P.family) :
    (produce G P torsion).physical.marking =
      ClosureMarkedSourceRouting.produce (algebraicEmbedding G) P.family torsion P.equality :=
  (produce G P torsion).physical.markingIdentity

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedActualReceipts
end
