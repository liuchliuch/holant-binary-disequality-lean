import Holant.Proofs.Counting.VerifierRun

/-! Canonical bounded-cell representation used by the structural compiler.
These two definitions are adapted literally from the reference BoundedTableau.
No finite enumeration of whole configurations or tableaux is introduced. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.BoundedTableau
open Holant.LocalDrafts.CountingHardness
open Turing

/-- Missing cells have the unique `none` padding value. -/
def pad {A : Type} (capacity : ℕ) (xs : List A) : Fin capacity → Option A :=
  fun i => xs[i.val]?

/-- Label, finite control state, and fixed-width heterogeneous stack cells. -/
abbrev Packed (tm : FinTM2) (capacity : ℕ) :=
  Option tm.Λ × (tm.σ × ((k : tm.K) → Fin capacity → Option (tm.Γ k)))

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.BoundedTableau
