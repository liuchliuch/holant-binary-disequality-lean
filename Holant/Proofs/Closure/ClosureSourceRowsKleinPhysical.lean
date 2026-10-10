import Holant.Proofs.Closure.ClosureSourceRowsKleinDeck
import Holant.Proofs.Closure.ClosureSourceRowsC2Frontier

/-! NEW UNVERIFIED source-row work after executor recovery. The finite actual
representative catalogue is inspected in both directions. A detected literal
standard/exotic row constructs its original-field resources, current SourceDeck,
actual A.8 network and original-G physical programmes internally. Failed guards
remain explicit; proving the guards on the whole noncyclic order-four domain is
still the separate actual group-shape producer's obligation. -/
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
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

abbrev KleinPhysicalType (kind : EqualityQuaternary.Klein.Kind)
    (coverage : KleinCoverage G P torsion kind)
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :=
  ClosurePhysicalBridge.BoundaryAccess G (retainedPalette G P torsion q core hcore (by norm_num))
    (RingHomRealization.mapSignature (embedding G) q) (EqualityQuaternary.SourceGroup (kleinRow kind))
    (klein_source_interface G P torsion kind coverage q core hcore stableDeck).1

inductive KleinAttempt
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) : Type 1 where
  | detected (kind : EqualityQuaternary.Klein.Kind) (coverage : KleinCoverage G P torsion kind)
      (physical : KleinPhysicalType G P torsion q core hcore kind coverage stableDeck)
      (physicalIdentity : physical = kleinPhysical G P torsion kind coverage q core hcore stableDeck)
  | unmatched (notStandard : ¬ KleinCoverage G P torsion .standard)
      (notExotic : ¬ KleinCoverage G P torsion .exotic)

/-- The caller supplies the already established CURRENT stable deck only.
No row, coverage proof, SourceDeck, certificate, compiler or success branch is
caller input. Each accepted guard is the actual finite source catalogue test. -/
def attemptKlein
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    KleinAttempt G P torsion q core hcore stableDeck := by
  classical
  by_cases standard : KleinCoverage G P torsion .standard
  · exact .detected .standard standard
      (kleinPhysical G P torsion .standard standard q core hcore stableDeck) rfl
  · by_cases exotic : KleinCoverage G P torsion .exotic
    · exact .detected .exotic exotic
        (kleinPhysical G P torsion .exotic exotic q core hcore stableDeck) rfl
    · exact .unmatched standard exotic

/-- A literal coverage result from the actual group-shape producer rules out
exactly the unmatched domain. It is not assumed by the attempt factory. -/
theorem attemptKlein_not_unmatched
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)
    (someCoverage : ∃ kind, KleinCoverage G P torsion kind) :
    ¬ ∃ notStandard notExotic,
      attemptKlein G P torsion q core hcore stableDeck = .unmatched notStandard notExotic := by
  rintro ⟨notStandard,notExotic,_⟩
  obtain ⟨kind,hkind⟩ := someCoverage
  cases kind
  · exact notStandard hkind
  · exact notExotic hkind

/-- The full detector is indexed by the genuine SAME current stable exit;
higher even minima and other exit constructors are not coerced into q4 rows. -/
def ForKleinExit (E : StructuralExit G P) : Type 1 := match E with
  | .stable 2 f _ _ torsion minimum literal _ _ stableDeck =>
      KleinAttempt G P torsion f minimum literal stableDeck
  | _ => PUnit.{2}

def forKleinStructuralExit (E : StructuralExit G P) : ForKleinExit G P E := match E with
  | .unary _ _ _ => PUnit.unit
  | .infinite _ _ _ => PUnit.unit
  | .odd _ _ _ _ _ => PUnit.unit
  | .stable 0 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 1 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 2 f _ _ torsion minimum literal _ _ stableDeck =>
      attemptKlein G P torsion f minimum literal stableDeck
  | .stable (Nat.succ (Nat.succ (Nat.succ _))) _ _ _ _ _ _ _ _ _ => PUnit.unit

/-- This per-occurrence continuation consumes the exact regenerated exit
already obtained by that occurrence's own batch. It never runs another q4 batch. -/
def C2Frontier.StableReceipt.klein
    {stable : StabilizationMathematical.Stable (C2Frontier.state G P torsion q core hcore)}
    (R : C2Frontier.StableReceipt G P torsion q core hcore stable) :
    ForKleinExit G (C2Frontier.batch G P torsion q core hcore).palette R.exit :=
  forKleinStructuralExit G _ R.exit

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
