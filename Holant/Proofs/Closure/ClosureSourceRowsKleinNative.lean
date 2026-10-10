import Holant.Proofs.Closure.ClosureSourceRowsKleinPhysical
import Holant.Proofs.Closure.ClosureKleinShapeCoverage

/-! NEW UNVERIFIED native continuation consumer. The ACTUAL
noncyclic order-four source group internally constructs literal Klein coverage,
source-field representatives, the CURRENT SourceDeck, A.8 network and original-G
physical programmes. Cyclic order four stays an explicit separate domain.
No classifier, FourSource, row, coverage or compiler is caller input.
The whole-domain actual group producer has freshly passed separately; this
consumer awaits its own strict check and full actual-origin audit. -/
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
variable (cardinal : Nat.card (completeGroup P.family torsion) = 4)
variable (noncyclic : ¬ IsCyclic (completeGroup P.family torsion))

include cardinal noncyclic in
/-- Exact original-current-key coverage, using the actual group producer. -/
theorem nativeKleinCoverage : ∃ kind, KleinCoverage G P torsion kind := by
  obtain ⟨kind,coverage⟩ := ClosureKleinShape.nativeRepresentativeCoverage
    (embedding G) P.family torsion (P.retainsIdentity G) cardinal noncyclic
  refine ⟨kind,?_,?_⟩
  · intro j
    obtain ⟨k,c,hc,he⟩ := coverage.forward j
    exact ⟨k,embedding G c,(map_ne_zero (embedding G)).mpr hc,he⟩
  · intro k
    obtain ⟨j,c,hc,he⟩ := coverage.backward k
    exact ⟨j,embedding G c,(map_ne_zero (embedding G)).mpr hc,he⟩

def nativeKleinKind := Classical.choose (nativeKleinCoverage G P torsion cardinal noncyclic)
def nativeKleinResources : KleinCoverage G P torsion
    (nativeKleinKind G P torsion cardinal noncyclic) :=
  Classical.choose_spec (nativeKleinCoverage G P torsion cardinal noncyclic)

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
variable (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)

abbrev NativeKleinPhysicalType := KleinPhysicalType G P torsion q core hcore
  (nativeKleinKind G P torsion cardinal noncyclic)
  (nativeKleinResources G P torsion cardinal noncyclic) stableDeck

def nativeKleinPhysical : NativeKleinPhysicalType G P torsion cardinal noncyclic q core hcore stableDeck :=
  kleinPhysical G P torsion (nativeKleinKind G P torsion cardinal noncyclic)
    (nativeKleinResources G P torsion cardinal noncyclic) q core hcore stableDeck

include cardinal noncyclic in
/-- On this genuine actual group domain, the generic guard detector cannot
return its unmatched branch. The coverage premise is derived internally. -/
theorem nativeKlein_guard_detected : ¬ ∃ notStandard notExotic,
    attemptKlein G P torsion q core hcore stableDeck = .unmatched notStandard notExotic :=
  attemptKlein_not_unmatched G P torsion q core hcore stableDeck
    (nativeKleinCoverage G P torsion cardinal noncyclic)

inductive NativeKleinAttempt : Type 1 where
  | detected (cardinal : Nat.card (completeGroup P.family torsion) = 4)
      (noncyclic : ¬ IsCyclic (completeGroup P.family torsion))
      (physical : NativeKleinPhysicalType G P torsion cardinal noncyclic q core hcore stableDeck)
      (physicalIdentity : physical = nativeKleinPhysical G P torsion cardinal noncyclic q core hcore stableDeck)
  | otherOrder (notFour : Nat.card (completeGroup P.family torsion) ≠ 4)
  | cyclicFour (cardinal : Nat.card (completeGroup P.family torsion) = 4)
      (cyclic : IsCyclic (completeGroup P.family torsion))

/-- Internally tests the actual current group, with explicit remaining domains. -/
def attemptNativeKlein : NativeKleinAttempt G P torsion q core hcore stableDeck := by
  classical
  by_cases cardinal : Nat.card (completeGroup P.family torsion) = 4
  · by_cases cyclic : IsCyclic (completeGroup P.family torsion)
    · exact .cyclicFour cardinal cyclic
    · exact .detected cardinal cyclic
        (nativeKleinPhysical G P torsion cardinal cyclic q core hcore stableDeck) rfl
  · exact .otherOrder cardinal

/-- The actual noncyclic order-four domain is routed to the internally
constructed physical factory, including its exact chosen original-G programme. -/
theorem attemptNativeKlein_of_native
    (cardinal : Nat.card (completeGroup P.family torsion) = 4)
    (noncyclic : ¬ IsCyclic (completeGroup P.family torsion)) :
    attemptNativeKlein G P torsion q core hcore stableDeck =
      .detected cardinal noncyclic
        (nativeKleinPhysical G P torsion cardinal noncyclic q core hcore stableDeck) rfl := by
  classical
  simp only [attemptNativeKlein,dif_pos cardinal,dif_neg noncyclic]

/-- The same actual stable CURRENT q4 exit provides all mathematical input. -/
def ForNativeKleinExit (E : StructuralExit G P) : Type 1 := match E with
  | .stable 2 q _ _ torsion minimum literal _ _ stableDeck =>
      NativeKleinAttempt G P torsion q minimum literal stableDeck
  | _ => PUnit.{2}

def forNativeKleinStructuralExit (E : StructuralExit G P) : ForNativeKleinExit G P E := match E with
  | .unary _ _ _ => PUnit.unit
  | .infinite _ _ _ => PUnit.unit
  | .odd _ _ _ _ _ => PUnit.unit
  | .stable 0 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 1 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 2 q _ _ torsion minimum literal _ _ stableDeck =>
      attemptNativeKlein G P torsion q minimum literal stableDeck
  | .stable (Nat.succ (Nat.succ (Nat.succ _))) _ _ _ _ _ _ _ _ _ => PUnit.unit

/-- Exact per-occurrence continuation, without a second preparation batch. -/
def C2Frontier.StableReceipt.nativeKlein
    {stable : StabilizationMathematical.Stable (C2Frontier.state G P torsion q core hcore)}
    (R : C2Frontier.StableReceipt G P torsion q core hcore stable) :
    ForNativeKleinExit G (C2Frontier.batch G P torsion q core hcore).palette R.exit :=
  forNativeKleinStructuralExit G _ R.exit

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
