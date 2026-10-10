import Holant.Proofs.Closure.HistorySectorCardsMatching
import Holant.Proofs.Closure.ClosureMarkedActualReceipts

/-! Closed actual-history adapter: a stable CURRENT exit internally produces
its marking ONCE, and each basis-bearing branch receives that SAME basis's
whole literal card deck, original-field physical access, scalar/ordered matching
receipts and actual inverse-holographic return. Genuine other exits and marking
branches retain their original payloads. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCardsReceipts
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
open HistorySectorCards
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) {m : ℕ}
variable (f : Signature (OI.K G) (m+2)) (U : InvertibleKernel)

structure Receipt : Type 1 where
  current : RegeneratedDeckAccess G P torsion f
  cardIdentity : ∀ key : RawCardKey m (completeGroup P.family torsion),
    card (algebraicEmbedding G) U P.family torsion f key =
      U.symm.action (HistorySectorCards.RH.mapSignature (algebraicEmbedding G)
        (rawCard P.family torsion f key))
  zeroIdentity : ∀ key : RawCardKey m (completeGroup P.family torsion),
    card (algebraicEmbedding G) U P.family torsion f key = 0 ↔ rawCard P.family torsion f key = 0
  deckIdentity : deck (algebraicEmbedding G) U P.family torsion f =
    (fun g => U.symm.action (HistorySectorCards.RH.mapSignature (algebraicEmbedding G) g)) ''
      rawDeck P.family torsion f
  matching : ∀ g ∈ deck (algebraicEmbedding G) U P.family torsion f,
    MatchingInSector (algebraicEmbedding G) U P.family g
  sector : ClosureMarkedHistoryReceipts.SectorReceipt G P U

def receipt (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g) :
    Receipt G P torsion f U where
  current := regeneratedDeckAccess G P torsion f core hcore
  cardIdentity key := (card_transport (algebraicEmbedding G) U P.family torsion f key).symm
  zeroIdentity := card_zero_iff (algebraicEmbedding G) U P.family torsion f
  deckIdentity := deck_exact (algebraicEmbedding G) U P.family torsion f
  matching := current_deck_matching (algebraicEmbedding G) U P.family torsion f stable
  sector := ClosureMarkedHistoryReceipts.sectorReceipt G P U

theorem current_identity (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g) :
    (receipt G P torsion f U core hcore stable).current =
      regeneratedDeckAccess G P torsion f core hcore := rfl

theorem same_edge (R : Receipt G P torsion f U) : R.sector.edge = sectorEdge U :=
  R.sector.edgeIdentity

def ForMarking
    (M : ClosureMarkedActualReceipts.Result G P torsion) : Type 1 :=
  match M.physical.marking.basis with
  | none => PUnit.{2}
  | some U => Receipt G P torsion f U

structure Result : Type 1 where
  marking : ClosureMarkedActualReceipts.Result G P torsion
  markingIdentity : marking = ClosureMarkedActualReceipts.produce G P torsion
  cards : ForMarking G P torsion f marking

/-- The caller supplies the actual stable-exit's existing proof data; basis,
marking, physical source programmes and all card coverage are constructed. -/
def produce (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g) :
    Result G P torsion f := by
  let M := ClosureMarkedActualReceipts.produce G P torsion
  refine ⟨M,rfl,?_⟩
  unfold ForMarking
  cases hb : M.physical.marking.basis with
  | none => exact PUnit.unit
  | some U => exact receipt G P torsion f U core hcore stable

def ForExit (E : StructuralExit G P) : Type 1 :=
  match E with
  | .stable _ f _ _ torsion _ _ _ _ _ => Result G P torsion f
  | .unary .. => PUnit.{2}
  | .infinite .. => PUnit.{2}
  | .odd .. => PUnit.{2}

/-- No stable deck, model, phase, basis, coverage or compiler is an input
beyond the actual returned StructuralExit itself. -/
def forExit (E : StructuralExit G P) : ForExit G P E :=
  match E with
  | .stable _ f _ _ torsion core hcore _ _ stable => produce G P torsion f core hcore stable
  | .unary .. => PUnit.unit
  | .infinite .. => PUnit.unit
  | .odd .. => PUnit.unit

def forHistory {C : StabilizationMathematical.State (OI.K G)}
    (R : HistoryPalette.Result G C) : ForExit G R.palette R.sourceResult.exit :=
  forExit G R.palette R.sourceResult.exit

def original (torsion : ResidualTorsion (OI.family G)) (core : MinimumCore (OI.family G))
    (proper : 4 ≤ core.signature.1) (even : Even core.signature.1) :
    ForExit G (HistoryPalette.original G torsion core proper even).palette
      (HistoryPalette.original G torsion core proper even).sourceResult.exit :=
  forHistory G (HistoryPalette.original G torsion core proper even)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCardsReceipts
end
