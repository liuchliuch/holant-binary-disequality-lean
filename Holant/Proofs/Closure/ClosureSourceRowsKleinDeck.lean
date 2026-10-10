import Holant.Proofs.Closure.ClosureSourceRowsKleinScalars
import Holant.Proofs.Closure.ClosurePhysicalBridgeBoundary
import Holant.Proofs.Closure.ClosureSourceRowsC2Deck

/-! CURRENT raw-deck to actual standard/exotic Klein SourceDeck transport.
Row resources and original-field card multipliers are constructed from the
literal actual catalogue; A.8 uses no supplied deck or endpoint certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
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
variable (kind : EqualityQuaternary.Klein.Kind) (coverage : KleinCoverage G P torsion kind)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

theorem klein_sourceDeck
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    EqualityQuaternary.Klein.PhysicalDeck (kleinRepresentatives G P torsion kind q core hcore coverage)
      (RingHomRealization.mapSignature (embedding G) q) := by
  intro e k
  let j := (kleinIndex G P torsion kind coverage k).key
  let B := actualRepresentative P.family torsion j
  change Holant.Marked.SupportAtlas.physicalCard (RingHomRealization.mapSignature (embedding G) q) e
    (B.map (embedding G)) = 0 ∨ ∃ i c, c ≠ 0 ∧
      Holant.Marked.SupportAtlas.physicalCard (RingHomRealization.mapSignature (embedding G) q) e
        (B.map (embedding G)) = Holant.Marked.scale c
          ((kleinRepresentatives G P torsion kind q core hcore coverage).matrix i)
  rcases actualCard_actual_or_zero G P torsion q stableDeck core hcore e B
    (actualRepresentative_actual P.family torsion j) with hz | ha
  · left
    rw [sourceCard_actual,hz]
    funext a b
    simp [binaryMatrix,Matrix.map_apply]
  · let R := kleinLineSource G P torsion kind coverage (binaryMatrix (originalOrderedCard q e B)) ha
    refine Or.inr ⟨R.index,embedding G R.coefficient,(map_ne_zero (embedding G)).mpr R.nonzero,?_⟩
    rw [sourceCard_actual]
    exact kleinLineSource_mapped G P torsion kind coverage q core hcore _ R

def kleinRow : EqualityQuaternary.Klein.Kind → EqualityQuaternary.SourceRow
  | .standard => .standardKlein
  | .exotic => .exoticKlein

def kleinSourceRepresentatives : EqualityQuaternary.SourceRepresentatives
    (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num))) (kleinRow kind) := by
  cases kind
  · exact kleinRepresentatives G P torsion .standard q core hcore coverage
  · exact kleinRepresentatives G P torsion .exotic q core hcore coverage

theorem kleinSource_retained : EqualityQuaternary.SourceRetained (kleinRow kind)
    (kleinSourceRepresentatives G P torsion kind coverage q core hcore) := by
  cases kind
  · exact klein_retained G P torsion .standard q core hcore coverage
  · exact klein_retained G P torsion .exotic q core hcore coverage

theorem kleinSource_deck
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    EqualityQuaternary.SourceDeck (kleinRow kind)
      (kleinSourceRepresentatives G P torsion kind coverage q core hcore)
      (RingHomRealization.mapSignature (embedding G) q) := by
  cases kind
  · exact klein_sourceDeck G P torsion .standard coverage q core hcore stableDeck
  · exact klein_sourceDeck G P torsion .exotic coverage q core hcore stableDeck

theorem klein_source_interface
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    EqualityQuaternary.BoundaryCertificate
      (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num)))
      (RingHomRealization.mapSignature (embedding G) q) (EqualityQuaternary.SourceGroup (kleinRow kind)) ∧
    EqualityQuaternary.SourceDetail
      (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num)))
      (RingHomRealization.mapSignature (embedding G) q) (kleinRow kind)
      (kleinSourceRepresentatives G P torsion kind coverage q core hcore) :=
  EqualityQuaternary.source_equality_accessible_quaternary_interface _ (kleinRow kind)
    (by cases kind <;> trivial) (kleinSourceRepresentatives G P torsion kind coverage q core hcore)
    (kleinSource_retained G P torsion kind coverage q core hcore) _
    (core_ambient_prime G P q core hcore) (core_ambient_retained G P torsion q core hcore)
    (identity_ambient_retained G P torsion q core hcore (by norm_num))
    (kleinSource_deck G P torsion kind coverage q core hcore stableDeck)

def kleinPhysical
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    ClosurePhysicalBridge.BoundaryAccess G (retainedPalette G P torsion q core hcore (by norm_num))
      (RingHomRealization.mapSignature (embedding G) q) (EqualityQuaternary.SourceGroup (kleinRow kind))
      (klein_source_interface G P torsion kind coverage q core hcore stableDeck).1 :=
  ClosurePhysicalBridge.fromBoundary G (retainedPalette G P torsion q core hcore (by norm_num))
    (RingHomRealization.mapSignature (embedding G) q) _
    (klein_source_interface G P torsion kind coverage q core hcore stableDeck).1

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
