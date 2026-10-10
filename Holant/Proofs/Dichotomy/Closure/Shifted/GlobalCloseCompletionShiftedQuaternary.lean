import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedMarking
import Holant.Proofs.Closure.HistorySectorNormalizedEndpoint
import Holant.Proofs.Closure.HistorySectorNormalizedMarking

/-! Consume an actual prepared shifted prime q4 into the same weighted graph,
with nonzero complementary endpoints and its existing original-G open return.
The reflection, source keys, edge multiplier, and current labels are retained;
there is no changed-coordinate Palette or ordinary-wire assertion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedQuaternary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export GlobalCloseCompletionShiftedMarking (Native)
end D
namespace H
export HistorySectorNormalized (RootDeck rootDeck endpointGraph endpointReturn endpointSource
  endpointGraph_zero_nonzero endpointGraph_one_nonzero endpointGraph_edge endpointReturn_original)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (native : D.Native G P torsion)

abbrev basis := native.reflection.basis
abbrev selected := native.reflection.selected native.axis native.notTwo native.notFour
abbrev parameters := native.reflection.parameters P.equality native.axis native.notTwo native.notFour native.noZ

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

def deck : H.RootDeck G P torsion (basis G P torsion native)
    (selected G P torsion native) (parameters G P torsion native) rfl q :=
  H.rootDeck G P torsion (basis G P torsion native) (selected G P torsion native)
    (parameters G P torsion native) rfl q (by trivial) core literal stable

def graph : Network AlgebraicComplex 4 :=
  H.endpointGraph G P torsion (basis G P torsion native) (selected G P torsion native)
    (parameters G P torsion native) rfl q core literal (deck G P torsion native q core literal stable)

def original : Signature (OI.K G) 4 :=
  H.endpointSource G P torsion (basis G P torsion native) (selected G P torsion native)
    (parameters G P torsion native) rfl q core literal (deck G P torsion native q core literal stable)

def access : ClosurePhysicalBridge.HolographicOpenAccess G P
    (basis G P torsion native).symm (graph G P torsion native q core literal stable) :=
  H.endpointReturn G P torsion (basis G P torsion native) (selected G P torsion native)
    (parameters G P torsion native) rfl q core literal (deck G P torsion native q core literal stable)

theorem original_exact : (access G P torsion native q core literal stable).output=
    original G P torsion native q core literal stable :=
  H.endpointReturn_original G P torsion (basis G P torsion native) (selected G P torsion native)
    (parameters G P torsion native) rfl q core literal (deck G P torsion native q core literal stable)

theorem edge_exact (e : Fin (graph G P torsion native q core literal stable).shape.edges) :
    (graph G P torsion native q core literal stable).edge e=
      sectorEdge (basis G P torsion native) :=
  H.endpointGraph_edge G P torsion (basis G P torsion native) (selected G P torsion native)
    (parameters G P torsion native) rfl q core literal (deck G P torsion native q core literal stable) e

theorem zero_nonzero : (graph G P torsion native q core literal stable).denote (fun _=>false)≠0 :=
  H.endpointGraph_zero_nonzero G P torsion (basis G P torsion native) (selected G P torsion native)
    (parameters G P torsion native) rfl q core literal (deck G P torsion native q core literal stable)

theorem one_nonzero : (graph G P torsion native q core literal stable).denote (fun _=>true)≠0 :=
  H.endpointGraph_one_nonzero G P torsion (basis G P torsion native) (selected G P torsion native)
    (parameters G P torsion native) rfl q core literal (deck G P torsion native q core literal stable)

/-- All physical information is tied to one deterministic construction. -/
structure Receipt : Type 1 where
  network : Network AlgebraicComplex 4
  networkIdentity : network=graph G P torsion native q core literal stable
  original : Signature (OI.K G) 4
  originalIdentity : original=GlobalCloseCompletionShiftedQuaternary.original G P torsion native q core literal stable
  access : ClosurePhysicalBridge.HolographicOpenAccess G P (basis G P torsion native).symm network
  outputIdentity : access.output=original
  edges : ∀e,network.edge e=sectorEdge (basis G P torsion native)
  zero : network.denote (fun _=>false)≠0
  one : network.denote (fun _=>true)≠0

def produce : Receipt G P torsion native q core literal stable where
  network := graph G P torsion native q core literal stable
  networkIdentity := rfl
  original := original G P torsion native q core literal stable
  originalIdentity := rfl
  access := access G P torsion native q core literal stable
  outputIdentity := original_exact G P torsion native q core literal stable
  edges := edge_exact G P torsion native q core literal stable
  zero := zero_nonzero G P torsion native q core literal stable
  one := one_nonzero G P torsion native q core literal stable

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedQuaternary
end
