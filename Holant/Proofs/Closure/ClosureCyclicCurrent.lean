import Holant.Proofs.Closure.ClosureCyclicCurrentCatalogue
import Holant.Proofs.Closure.ClosureCyclicCurrentEndpoint
import Holant.Proofs.Closure.ClosureCyclicCurrentContinuation
import Holant.Proofs.Closure.ClosureCyclicCurrentOutside
import Holant.Proofs.Closure.ClosureCyclicCurrentUnary

/-! Closed CURRENT cyclic q4 boundary: actual phase resources and all physical
cards are produced from the same source group and regenerated raw deck. Every
frozen endpoint/outside/doubled alternative carries constructed original-G
access and old-tree-preserving saturation, with no complexity classification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

/-- The square is actual and saturated; its descended exact factor has its
own charged power-extraction boundary and computed group-external transfer. -/
structure DoubledReceipt (m : ℕ) where
  doubled : CyclicBoundary.NonsquareExit.DoubledOutside
    (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) m

def DoubledReceipt.output {m : ℕ} (r : DoubledReceipt G P m) := (doubledOutput G P r.doubled).output
def DoubledReceipt.squarePalette {m : ℕ} (r : DoubledReceipt G P m) := doubledPalette G P r.doubled
def DoubledReceipt.palette {m : ℕ} (r : DoubledReceipt G P m) := installedPalette G P r.doubled
abbrev DoubledReceipt.factor {m : ℕ} (r : DoubledReceipt G P m) := (doubleFactors G P r.doubled).left
abbrev DoubledReceipt.factorToOriginal {m : ℕ} (r : DoubledReceipt G P m) := doubleFactorToOriginal G P r.doubled
abbrev DoubledReceipt.toOriginal {m : ℕ} (r : DoubledReceipt G P m) := (DoubledReceipt.palette G P r).toOriginal
abbrev DoubledReceipt.factorFromOriginal {m : ℕ} (r : DoubledReceipt G P m) := doubleFactorFromOriginal G P r.doubled
abbrev DoubledReceipt.fromOriginal {m : ℕ} (r : DoubledReceipt G P m) := (DoubledReceipt.palette G P r).fromOriginal

theorem DoubledReceipt.outside {m : ℕ} (r : DoubledReceipt G P m) :
    ¬CP.IsPhase m (CyclicBoundary.ActualCards.walshTransfer
      (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) r.factor)) :=
  doubleFactor_outside G P r.doubled

inductive Result (m : ℕ) : Type 1
  | endpoint (receipt : EndpointReceipt G P)
  | outside (receipt : OutsideReceipt G P m) (domain : OutsideDomain G P receipt)
  | doubled (receipt : DoubledReceipt G P m)

variable (τ : ResidualTorsion P.family) (q : Signature (OI.K G) 4)
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
variable (stable : ∀ g ∈ rawDeck P.family τ q, MatchingOrZero (actualTransfers P.family) g)
variable (cyclic : IsCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
variable (range : 3 ≤ Nat.card (D.group (ClosureSourceRows.embedding G) P.family τ))

theorem selected_at_least_four : 4 ≤ (selected G P τ cyclic range).m := by
  have even := selected_even G P τ cyclic range
  obtain ⟨k,hk⟩ := even
  have lower := (selected G P τ cyclic range).range
  omega

include q core hcore stable in
/-- All three actual frozen alternatives are transformed into real source data.
No successful branch, output graph or endpoint compiler is a caller argument. -/
theorem result_exists : Nonempty (Result G P (selected G P τ cyclic range).m) := by
  rcases source_dispatch G P τ q core hcore stable cyclic range with endpoint | outside | doubled
  · exact ⟨.endpoint (endpointReceipt G P endpoint)⟩
  · obtain ⟨card⟩ := outside
    let receipt := outsideReceipt G P card
    exact ⟨.outside receipt (outsideDomain G P receipt)⟩
  · obtain ⟨d⟩ := doubled
    exact ⟨.doubled ⟨d⟩⟩

/-- Offline fixed-family construction. This does not claim a uniform input-time
signature classifier or relabel the source endpoint Hard, Tract or Close. -/
def run : Result G P (selected G P τ cyclic range).m :=
  Classical.choice (result_exists G P τ q core hcore stable cyclic range)

/-- Dependent real continuation for THIS exact source dispatch alternative. -/
def ForResult (R : Result G P (selected G P τ cyclic range).m) : Type 1 :=
  match R with
  | .endpoint _ => PUnit.{2}
  | .outside o _ => UnaryReceipt G P o
  | .doubled r => DoubledContinuation G P τ (selected G P τ cyclic range) r.doubled

/-- The outside card supplies a genuine unary, while the installed doubled
factor triggers actual structural inspection or strict complete-group growth. -/
def forResult (R : Result G P (selected G P τ cyclic range).m) : ForResult G P τ cyclic range R :=
  match R with
  | .endpoint _ => PUnit.unit
  | .outside o _ => outsideUnary G P τ (selected G P τ cyclic range) o
  | .doubled r => doubledContinuation G P τ (selected G P τ cyclic range) r.doubled

structure Completion : Type 1 where
  branch : Result G P (selected G P τ cyclic range).m
  branchFactory : branch = run G P τ q core hcore stable cyclic range
  continuation : ForResult G P τ cyclic range branch

/-- Closed CURRENT cyclic boundary AND actual post-installation continuation.
All input guards concern the real current source; none selects a desired output. -/
def complete : Completion G P τ q core hcore stable cyclic range :=
  let R := run G P τ q core hcore stable cyclic range
  ⟨R,rfl,forResult G P τ cyclic range R⟩

@[simp] theorem run_factory : run G P τ q core hcore stable cyclic range =
    Classical.choice (result_exists G P τ q core hcore stable cyclic range) := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
