import Holant.Proofs.Closure.ClosureSourceRowsMonomialScalars
import Holant.Proofs.Closure.ClosurePhysicalBridgeBoundary

/-! The constructed native-M row consumes the real CURRENT q4 stable deck.
Every phase representative and output-card unit has a literal source-field
receipt. A.8 and both original-G programmes are then generated internally.
This is one actual Z-centralizer branch, not a classification of all groups. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Marked Holant.Marked.SupportAtlas
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM (ClosureMarkedDihedral.Source.group (embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

theorem monomial_sourceDeck
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    EqualityQuaternary.SourceDeck (.monomial N.m)
      (monomialRepresentatives G P torsion N q core hcore)
      (RingHomRealization.mapSignature (embedding G) q) := by
  intro e p t
  let j := (monomialIndex G P torsion N p t).key
  let B := actualRepresentative P.family torsion j
  change Holant.Marked.SupportAtlas.physicalCard (RingHomRealization.mapSignature (embedding G) q) e
    (B.map (embedding G)) = 0 ∨
      EqualityQuaternary.ActualMonomialLine (monomialRepresentatives G P torsion N q core hcore)
        (Holant.Marked.SupportAtlas.physicalCard (RingHomRealization.mapSignature (embedding G) q) e
          (B.map (embedding G)))
  rcases actualCard_actual_or_zero G P torsion q stableDeck core hcore e B
    (actualRepresentative_actual P.family torsion j) with hz | ha
  · left
    rw [sourceCard_actual,hz]
    funext a b
    simp [binaryMatrix,Matrix.map_apply]
  · let R := monomialLineSource G P torsion N q core hcore
      (binaryMatrix (originalOrderedCard q e B)) ha
    refine Or.inr ⟨R.orientation,R.phase,embedding G R.coefficient,
      (map_ne_zero (embedding G)).mpr R.nonzero,?_⟩
    rw [sourceCard_actual]
    exact monomialLineSource_mapped G P torsion N q core hcore _ R

theorem monomial_source_interface
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    EqualityQuaternary.BoundaryCertificate
      (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num)))
      (RingHomRealization.mapSignature (embedding G) q) (EqualityQuaternary.SourceGroup (.monomial N.m)) ∧
    EqualityQuaternary.SourceDetail
      (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num)))
      (RingHomRealization.mapSignature (embedding G) q) (.monomial N.m)
      (monomialRepresentatives G P torsion N q core hcore) :=
  EqualityQuaternary.source_equality_accessible_quaternary_interface _ (.monomial N.m) N.range
    (monomialRepresentatives G P torsion N q core hcore)
    (monomial_retained G P torsion N q core hcore) _
    (core_ambient_prime G P q core hcore)
    (core_ambient_retained G P torsion q core hcore)
    (identity_ambient_retained G P torsion q core hcore (by norm_num))
    (monomial_sourceDeck G P torsion N q core hcore stableDeck)

def nativeMonomialModel
    (inZCentralizer : ClosureMarkedDihedral.Source.group (embedding G) P.family torsion ≤
      Subgroup.centralizer ({ClosureMarkedDihedral.PC.zClass} : Set (PGL2 ℂ)))
    (notTwo : Nat.card (ClosureMarkedDihedral.Source.group (embedding G) P.family torsion) ≠ 2)
    (notFour : Nat.card (ClosureMarkedDihedral.Source.group (embedding G) P.family torsion) ≠ 4) :
    ClosureMarkedDihedral.NativeM (ClosureMarkedDihedral.Source.group (embedding G) P.family torsion) :=
  ClosureMarkedDihedral.Source.nativeM (embedding G) P.family torsion P.equality
    inZCentralizer notTwo notFour

variable
    (inZCentralizer : ClosureMarkedDihedral.Source.group (embedding G) P.family torsion ≤
      Subgroup.centralizer ({ClosureMarkedDihedral.PC.zClass} : Set (PGL2 ℂ)))
    (notTwo : Nat.card (ClosureMarkedDihedral.Source.group (embedding G) P.family torsion) ≠ 2)
    (notFour : Nat.card (ClosureMarkedDihedral.Source.group (embedding G) P.family torsion) ≠ 4)
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)

/-- The model, actual row representatives and SourceDeck are constructed in
this producer. Only the concrete actual-group branch guard is a hypothesis. -/
def nativeMonomialCertificate : EqualityQuaternary.BoundaryCertificate
    (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num)))
    (RingHomRealization.mapSignature (embedding G) q)
    (EqualityQuaternary.SourceGroup
      (.monomial (nativeMonomialModel G P torsion inZCentralizer notTwo notFour).m)) :=
  (monomial_source_interface G P torsion
    (nativeMonomialModel G P torsion inZCentralizer notTwo notFour) q core hcore stableDeck).1

def nativeMonomialPhysical : ClosurePhysicalBridge.BoundaryAccess G
    (retainedPalette G P torsion q core hcore (by norm_num))
    (RingHomRealization.mapSignature (embedding G) q)
    (EqualityQuaternary.SourceGroup
      (.monomial (nativeMonomialModel G P torsion inZCentralizer notTwo notFour).m))
    (nativeMonomialCertificate G P torsion q core hcore inZCentralizer notTwo notFour stableDeck) :=
  ClosurePhysicalBridge.fromBoundary G (retainedPalette G P torsion q core hcore (by norm_num))
    (RingHomRealization.mapSignature (embedding G) q) _
    (nativeMonomialCertificate G P torsion q core hcore inZCentralizer notTwo notFour stableDeck)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
