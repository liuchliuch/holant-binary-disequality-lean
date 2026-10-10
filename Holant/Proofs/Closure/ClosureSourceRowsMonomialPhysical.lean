import Holant.Proofs.Closure.ClosureSourceRowsMonomialDeck
import Holant.Proofs.Closure.ClosureSourceRowsC2Frontier

/-! Closed native-M guard routing for actual structural exits. A failed
centralizer or small-order test is an explicit pending row domain, never a
successful generic residual. Every detected endpoint is internally produced
from the current q4 deck and its exact original-field source resources. -/
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

abbrev InNativeM := ClosureMarkedDihedral.Source.group (embedding G) P.family torsion ≤
  Subgroup.centralizer ({ClosureMarkedDihedral.PC.zClass} : Set (PGL2 ℂ))
abbrev AmbientCard := Nat.card (ClosureMarkedDihedral.Source.group (embedding G) P.family torsion)

abbrev NativeMPhysicalType (inZ : InNativeM G P torsion)
    (notTwo : AmbientCard G P torsion ≠ 2) (notFour : AmbientCard G P torsion ≠ 4)
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :=
  ClosurePhysicalBridge.BoundaryAccess G (retainedPalette G P torsion q core hcore (by norm_num))
    (RingHomRealization.mapSignature (embedding G) q)
    (EqualityQuaternary.SourceGroup (.monomial (nativeMonomialModel G P torsion inZ notTwo notFour).m))
    (nativeMonomialCertificate G P torsion q core hcore inZ notTwo notFour stableDeck)

inductive NativeMAttempt
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) : Type 1 where
  | detected (inZ : InNativeM G P torsion)
      (notTwo : AmbientCard G P torsion ≠ 2) (notFour : AmbientCard G P torsion ≠ 4)
      (physical : NativeMPhysicalType G P torsion q core hcore inZ notTwo notFour stableDeck)
  | otherSector (notInZ : ¬ InNativeM G P torsion)
  | smallGroup (small : AmbientCard G P torsion = 2 ∨ AmbientCard G P torsion = 4)

/-- No model, row representatives, SourceDeck or certificate is an input. -/
def attemptNativeM
    (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    NativeMAttempt G P torsion q core hcore stableDeck := by
  classical
  by_cases hZ : InNativeM G P torsion
  · by_cases h2 : AmbientCard G P torsion = 2
    · exact .smallGroup (Or.inl h2)
    · by_cases h4 : AmbientCard G P torsion = 4
      · exact .smallGroup (Or.inr h4)
      · exact .detected hZ h2 h4
          (nativeMonomialPhysical G P torsion q core hcore hZ h2 h4 stableDeck)
  · exact .otherSector hZ

def ForNativeMExit (E : StructuralExit G P) : Type 1 := match E with
  | .stable 2 f _ _ hτ minimum literal _ _ stableDeck =>
      NativeMAttempt G P hτ f minimum literal stableDeck
  | _ => PUnit.{2}

def forNativeMStructuralExit (E : StructuralExit G P) : ForNativeMExit G P E := match E with
  | .unary _ _ _ => PUnit.unit
  | .infinite _ _ _ => PUnit.unit
  | .odd _ _ _ _ _ => PUnit.unit
  | .stable 0 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 1 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 2 f _ _ hτ minimum literal _ _ stableDeck =>
      attemptNativeM G P hτ f minimum literal stableDeck
  | .stable (Nat.succ (Nat.succ (Nat.succ _))) _ _ _ _ _ _ _ _ _ => PUnit.unit

/-- The unchanged branch of EACH actual q4 occurrence uses its own generated
CURRENT exit. The M guard and physical endpoint require no caller branch proof. -/
def C2Frontier.StableReceipt.monomial
    {stable : StabilizationMathematical.Stable (C2Frontier.state G P torsion q core hcore)}
    (R : C2Frontier.StableReceipt G P torsion q core hcore stable) :
    ForNativeMExit G (C2Frontier.batch G P torsion q core hcore).palette R.exit :=
  forNativeMStructuralExit G _ R.exit

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
