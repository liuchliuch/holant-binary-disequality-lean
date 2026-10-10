import Holant.Proofs.Closure.HistorySectorNormalizedDeck
import Holant.Proofs.Closure.ClosureSourceRowsMonomialDeck

/-! Closed SAME-marking q4 normalization. Literal M reuses the checked
original-field native-X row bridge; B/A construct the actual changed-edge
weighted hypotheses. Cyclic/A0/small/Platonic and higher-arity obligations keep
their exact preceding payloads, without being relabelled as a q4 sector deck. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (hcore : core.signature = ⟨4,q⟩)

structure NativeRootDeck (N : ClosureMarkedDihedral.NativeM
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)) : Type 1 where
  indices : ∀ p t, ClosureSourceRows.MonomialIndex G P torsion N p t
  indicesIdentity : ∀ p t, indices p t = ClosureSourceRows.monomialIndex G P torsion N p t
  edge : sectorEdge InvertibleKernel.identity = Signature.disequality
  deck : Holant.Certificates.EqualityQuaternary.SourceDeck (.monomial N.m)
    (ClosureSourceRows.monomialRepresentatives G P torsion N q core hcore)
    (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q)

def nativeRootDeck
    (N : ClosureMarkedDihedral.NativeM
      (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))
    (stable : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    NativeRootDeck G P torsion q core hcore N where
  indices := ClosureSourceRows.monomialIndex G P torsion N
  indicesIdentity _ _ := rfl
  edge := edgeM
  deck := ClosureSourceRows.monomial_sourceDeck G P torsion N q core hcore stable

/-- The actual returned M branch has the literal identity basis. This gate
justifies native-X reuse; it says nothing about a nontrivial normalized basis. -/
theorem monomial_same_basis
    (N : ClosureMarkedDihedral.NativeM
      (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)) :
    (ClosureMarkedSourceRouting.Marking.monomial N).basis = some InvertibleKernel.identity := rfl

def NormalizedFor
    (M : ClosureMarkedSourceRouting.Marking (algebraicEmbedding G) P.family torsion) : Type 1 :=
  match M with
  | .monomial N => NativeRootDeck G P torsion q core hcore N
  | .bilinear N => RootDeck G P torsion basisB N.selected N.parameters rfl q
  | .shifted axis _ notTwo notFour noZ R _ =>
      RootDeck G P torsion R.basis (R.selected axis notTwo notFour)
        (R.parameters P.equality axis notTwo notFour noZ) rfl q
  | .smallTwo .. => PUnit.{2}
  | .smallFour .. => PUnit.{2}
  | .cyclic .. => PUnit.{2}
  | .unshifted .. => PUnit.{2}
  | .platonic .. => PUnit.{2}

def normalizeMarking
    (stable : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)
    (M : ClosureMarkedSourceRouting.Marking (algebraicEmbedding G) P.family torsion) :
    NormalizedFor G P torsion q core hcore M :=
  match M with
  | .monomial N => nativeRootDeck G P torsion q core hcore N stable
  | .bilinear N => rootDeck G P torsion basisB N.selected N.parameters rfl q
      (show nonstandard N.parameters from True.intro) core hcore stable
  | .shifted axis _ notTwo notFour noZ R _ =>
      rootDeck G P torsion R.basis (R.selected axis notTwo notFour)
        (R.parameters P.equality axis notTwo notFour noZ) rfl q
        (show nonstandard (R.parameters P.equality axis notTwo notFour noZ) from True.intro)
        core hcore stable
  | .smallTwo .. => PUnit.unit
  | .smallFour .. => PUnit.unit
  | .cyclic .. => PUnit.unit
  | .unshifted .. => PUnit.unit
  | .platonic .. => PUnit.unit

variable (stable : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)

structure Result : Type 1 where
  cards : HistorySectorCardsReceipts.Result G P torsion q
  cardsIdentity : cards = HistorySectorCardsReceipts.produce G P torsion q core hcore
    stable
  normalized : NormalizedFor G P torsion q core hcore cards.marking.physical.marking

/-- All standard model, phase, basis and normalized-deck data is constructed
from the actual previously produced CURRENT stable exit. -/
def produce : Result G P torsion q core hcore stable :=
  let C := HistorySectorCardsReceipts.produce G P torsion q core hcore stable
  ⟨C,rfl,normalizeMarking G P torsion q core hcore stable C.marking.physical.marking⟩

theorem same_marking : (produce G P torsion q core hcore stable).cards.marking =
    ClosureMarkedActualReceipts.produce G P torsion :=
  (produce G P torsion q core hcore stable).cards.markingIdentity

def ForExit (E : StructuralExit G P) : Type 1 :=
  match E with
  | .stable 2 q _ _ torsion core hcore _ _ stable => Result G P torsion q core hcore stable
  | .stable 0 _ _ _ _ _ _ _ _ _ => PUnit.{2}
  | .stable 1 _ _ _ _ _ _ _ _ _ => PUnit.{2}
  | .stable (Nat.succ (Nat.succ (Nat.succ _))) _ _ _ _ _ _ _ _ _ => PUnit.{2}
  | .unary .. => PUnit.{2}
  | .infinite .. => PUnit.{2}
  | .odd .. => PUnit.{2}

def forExit (E : StructuralExit G P) : ForExit G P E :=
  match E with
  | .stable 2 q _ _ torsion core hcore _ _ stable => produce G P torsion q core hcore stable
  | .stable 0 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 1 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable (Nat.succ (Nat.succ (Nat.succ _))) _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .unary .. => PUnit.unit
  | .infinite .. => PUnit.unit
  | .odd .. => PUnit.unit

def original (torsion : ResidualTorsion (OI.family G)) (core : MinimumCore (OI.family G))
    (proper : 4 ≤ core.signature.1) (even : Even core.signature.1) :
    ForExit G (HistoryPalette.original G torsion core proper even).palette
      (HistoryPalette.original G torsion core proper even).sourceResult.exit :=
  forExit G (HistoryPalette.original G torsion core proper even).palette
    (HistoryPalette.original G torsion core proper even).sourceResult.exit

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
end
