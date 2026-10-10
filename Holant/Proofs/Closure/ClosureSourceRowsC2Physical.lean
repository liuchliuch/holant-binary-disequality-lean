import Holant.Proofs.Closure.ClosureSourceRowsC2Deck
import Holant.Proofs.Closure.ClosurePhysicalBridgeNetwork

/-! The concrete C2 source certificate and its SAME ordinary graph are
descended to the original coefficient field and physically compiled. The
finite actual-group order-two test is internal; a missing C2 branch is an
explicit routing result, not a successful global closure certificate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4)
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

structure C2PhysicalBoundary where
  copies : ℕ
  atMostTwo : copies ≤ 2
  network : Network AlgebraicComplex 4
  coreLabels : EqualityQuaternary.Boundary.CoreLabels
    (RingHomRealization.mapSignature (embedding G) q) network
  native : EqualityQuaternary.Boundary.Native network
  exactCopies : EqualityQuaternary.Counted.copies network = copies
  endpoint : Holant.EightVertex.ProductAnchor.EndpointEven network.denote
  outside : ¬ EqualityQuaternary.GroupMatching
    (EqualityQuaternary.SourceGroup .c2) network.denote
  uses : EqualityQuaternary.Boundary.Uses
    (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num))) network
  access : ClosurePhysicalBridge.NetworkGraphAccess G
    (retainedPalette G P torsion q core hcore (by norm_num)) (embedding G) network uses

def c2PhysicalBoundary
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)
    (cardTwo : Nat.card (completeGroup P.family torsion) = 2) :
    C2PhysicalBoundary G P torsion q core hcore := by
  let cert := (c2_source_interface G P torsion q core hcore stableDeck cardTwo).1
  let n := Classical.choose cert
  have hn := Classical.choose_spec cert
  let N := Classical.choose hn.2
  have hN := Classical.choose_spec hn.2
  exact ⟨n,hn.1,N,hN.1,hN.2.1,hN.2.2.1,hN.2.2.2.1,hN.2.2.2.2.1,
    hN.2.2.2.2.2.2,ClosurePhysicalBridge.fromNetwork G
      (retainedPalette G P torsion q core hcore (by norm_num)) (embedding G) N
      hN.2.2.2.2.2.2 hN.2.1⟩

theorem c2PhysicalBoundary_network
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)
    (cardTwo : Nat.card (completeGroup P.family torsion) = 2) :
    (c2PhysicalBoundary G P torsion q core hcore stableDeck cardTwo).network =
      Classical.choose ((Classical.choose_spec
        ((c2_source_interface G P torsion q core hcore stableDeck cardTwo).1)).2) := rfl

theorem c2PhysicalBoundary_access
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)
    (cardTwo : Nat.card (completeGroup P.family torsion) = 2) :
    let d := c2PhysicalBoundary G P torsion q core hcore stableDeck cardTwo
    d.access = ClosurePhysicalBridge.fromNetwork G
      (retainedPalette G P torsion q core hcore (by norm_num)) (embedding G)
      d.network d.uses d.native := rfl

abbrev C2PhysicalBoundary.originalOutput
    (d : C2PhysicalBoundary G P torsion q core hcore) : Signature (OI.K G) 4 := d.access.output
abbrev C2PhysicalBoundary.toOriginal (d : C2PhysicalBoundary G P torsion q core hcore) :=
  d.access.toOriginal
abbrev C2PhysicalBoundary.fromOriginal (d : C2PhysicalBoundary G P torsion q core hcore) :=
  d.access.fromOriginal

theorem C2PhysicalBoundary.originalOutput_exact (d : C2PhysicalBoundary G P torsion q core hcore) :
    RingHomRealization.mapSignature (embedding G) (d.originalOutput G P torsion q core hcore) =
      d.network.denote := d.access.mappedOutput

theorem C2PhysicalBoundary.same_network (d : C2PhysicalBoundary G P torsion q core hcore) :
    d.access.source.map (embedding G) = d.network := d.access.mappedNetwork

theorem C2PhysicalBoundary.toOriginal_controlled (d : C2PhysicalBoundary G P torsion q core hcore) :
    (d.toOriginal G P torsion q core hcore).controlled =
      RetainedBranch.controlledToOriginal G
        (retainedPalette G P torsion q core hcore (by norm_num))
        ⟨4,d.originalOutput G P torsion q core hcore⟩ d.access.access.power :=
  d.access.access.toOriginal_controlled G _ (embedding G) _ _

theorem C2PhysicalBoundary.fromOriginal_controlled (d : C2PhysicalBoundary G P torsion q core hcore) :
    (d.fromOriginal G P torsion q core hcore).controlled =
      RetainedBranch.controlledFromOriginal G
        (retainedPalette G P torsion q core hcore (by norm_num))
        ⟨4,d.originalOutput G P torsion q core hcore⟩ :=
  d.access.access.fromOriginal_controlled G _ (embedding G) _ _

/-- The actual finite-group test does not require a caller-selected row. -/
inductive C2Attempt where
  | detected (cardTwo : Nat.card (completeGroup P.family torsion) = 2)
      (boundary : C2PhysicalBoundary G P torsion q core hcore)
  | otherGroup (cardNotTwo : Nat.card (completeGroup P.family torsion) ≠ 2)

def attemptC2
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    C2Attempt G P torsion q core hcore := by
  classical
  by_cases h : Nat.card (completeGroup P.family torsion) = 2
  · exact .detected h (c2PhysicalBoundary G P torsion q core hcore stableDeck h)
  · exact .otherGroup h

/-- An actual quaternary stable exit exposes the internally tested C2 route.
Other exits/arity domains carry no invented C2 obligation. -/
def ForExit (E : StructuralExit G P) : Type 1 := match E with
  | .stable 2 f _ _ hτ minimum literal _ _ _ => C2Attempt G P hτ f minimum literal
  | _ => PUnit.{2}

def forStructuralExit (E : StructuralExit G P) : ForExit G P E := match E with
  | .unary _ _ _ => PUnit.unit
  | .infinite _ _ _ => PUnit.unit
  | .odd _ _ _ _ _ => PUnit.unit
  | .stable 0 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 1 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 2 f _ _ hτ minimum literal _ _ stableDeck =>
      attemptC2 G P hτ f minimum literal stableDeck
  | .stable (Nat.succ (Nat.succ (Nat.succ _))) _ _ _ _ _ _ _ _ _ => PUnit.unit

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
