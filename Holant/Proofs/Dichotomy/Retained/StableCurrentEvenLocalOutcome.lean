import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenEOTransport
import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenEOHardness

/-! Source-backed native-M minimum-core outcomes. The sparse branch either
has the proved Product membership or produces an actual EO graph. Failure of
that exact row's singleton EOTract predicate gives original-G counting hardness.
Singleton tractability remains a whole-family closure obligation, and full
parity support remains a separate dense residual. Every other marking is kept. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenLocalOutcome
open Holant Holant.Tractable Holant.Complexity
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Certificates.EqualityQuaternary
open FrontierCommonPresentation StableCurrentEvenEOTransport
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

abbrev OriginalHard : Prop := Holant.LocalDrafts.CountingHardness.WitnessCountingHard
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature = ⟨4,q⟩)

def eoRow (d : SparseOutput G P q core literal) : Signature AlgebraicComplex 4 :=
  StableCurrentEvenEOHardness.mappedOutput G P (Flip.network (embedded G q) d.mask)
    (graph_uses G P q core literal d.mask) d.access

theorem eoRow_exact (d : SparseOutput G P q core literal) :
    eoRow G P q core literal d = Flip.value (embedded G q) d.mask :=
  d.mapped_output G P q core literal

theorem eoRow_support (d : SparseOutput G P q core literal) :
    DenseEOUnitLocal.EOSupport (eoRow G P q core literal d) := by
  rw [eoRow_exact]
  exact d.eo

/-- The graph's actual saved programme substitutes every generated EO row
and performs the exact coefficient decoding back to the original G oracle. -/
theorem negative_eo_original_hard (d : SparseOutput G P q core literal)
    (negative : ¬ EOTract {⟨4,eoRow G P q core literal d⟩}) : OriginalHard G :=
  StableCurrentEvenEOHardness.witnessCountingHard G P
    (Flip.network (embedded G q) d.mask) (graph_uses G P q core literal d.mask)
    d.access (eoRow_support G P q core literal d) negative

inductive CoreOutcome : Type 1 where
  | product (membership : leafPredicate G productClass InvertibleKernel.identity
      (⟨4,q⟩ : AnySignature (OI.K G)))
  | eoHard (row : SparseOutput G P q core literal)
      (negative : ¬ EOTract {⟨4,eoRow G P q core literal row⟩})
      (hard : OriginalHard G)
  | eoTractablePending (row : SparseOutput G P q core literal)
      (singletonTractable : EOTract {⟨4,eoRow G P q core literal row⟩})
  | denseParityPending (parity : Bool) (full : FullParity G q parity)

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (stable : ∀ g ∈ rawDeck P.family torsion q,
  MatchingOrZero (actualTransfers P.family) g)

include torsion N stable in
/-- No successful spectral, support, hardness or tractability branch is an
input. The two pending constructors intentionally assert no common-family
tractability, shared affine basis, or transformed-edge membership. -/
theorem core_outcome_exists : Nonempty (CoreOutcome G P q core literal) := by
  classical
  by_cases small : ((Finset.univ : Finset (Fin 4 → Bool)).filter fun x => q x ≠ 0).card ≤ 2
  · exact ⟨.product (StableCurrentEvenNativeM.current_four_product_of_small
      G P torsion N q core literal stable small)⟩
  rcases sparse_or_full G P torsion N q core literal stable with full | sparse
  · obtain ⟨p,full⟩ := full
    exact ⟨.denseParityPending p full⟩
  · obtain ⟨row⟩ := sparse
    by_cases tract : EOTract {⟨4,eoRow G P q core literal row⟩}
    · exact ⟨.eoTractablePending row tract⟩
    · exact ⟨.eoHard row tract (negative_eo_original_hard G P q core literal row tract)⟩

def coreOutcome : CoreOutcome G P q core literal :=
  Classical.choice (core_outcome_exists G P q core literal torsion N stable)

structure NativeOutcome (core : MinimumCore P.family) : Type 1 where
  table : Signature (OI.K G) 4
  literal : core.signature = ⟨4,table⟩
  result : CoreOutcome G P table core literal

/-- The actual stable all-even prime core is reduced to arity four by the
retained native-M rigidity theorem before the local outcome is produced. -/
def fromStable {m : ℕ} (f : Signature (OI.K G) (m+2)) (proper : 2 ≤ m)
    (even : Even (m+2)) (core : MinimumCore P.family)
    (literal : core.signature = ⟨m+2,f⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion f,
      MatchingOrZero (actualTransfers P.family) g) : NativeOutcome G P core := by
  have prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)) :=
    (congrArg Holant.LocalDrafts.FinitePGL2.Stabilization.Prime literal).mp core.prime
  have residual := ClosureNativeMCore.stable_prime_residual_eq_two G P torsion N f proper even prime stable
  subst m
  exact ⟨f,literal,coreOutcome G P f core literal torsion N stable⟩

def ForMarking (core : MinimumCore P.family)
    (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G) P.family torsion) : Type 1 :=
  match M with
  | .monomial _ => NativeOutcome G P core
  | .smallTwo .. => PUnit.{2}
  | .smallFour .. => PUnit.{2}
  | .cyclic .. => PUnit.{2}
  | .bilinear .. => PUnit.{2}
  | .unshifted .. => PUnit.{2}
  | .shifted .. => PUnit.{2}
  | .platonic .. => PUnit.{2}

def forMarking {m : ℕ} (f : Signature (OI.K G) (m+2)) (proper : 2 ≤ m)
    (even : Even (m+2)) (core : MinimumCore P.family)
    (literal : core.signature = ⟨m+2,f⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion f,
      MatchingOrZero (actualTransfers P.family) g)
    (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G) P.family torsion) :
    ForMarking G P torsion core M := by
  cases M with
  | monomial N => exact fromStable G P torsion N f proper even core literal stable
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | bilinear => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

structure MarkedReceipt (core : MinimumCore P.family) : Type 1 where
  marking : ClosureMarkedActualReceipts.Result G P torsion
  markingIdentity : marking = ClosureMarkedActualReceipts.produce G P torsion
  localOutcome : ForMarking G P torsion core marking.physical.marking

def markedReceipt {m : ℕ} (f : Signature (OI.K G) (m+2)) (proper : 2 ≤ m)
    (even : Even (m+2)) (core : MinimumCore P.family)
    (literal : core.signature = ⟨m+2,f⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion f,
      MatchingOrZero (actualTransfers P.family) g) : MarkedReceipt G P torsion core :=
  let marking := ClosureMarkedActualReceipts.produce G P torsion
  ⟨marking,rfl,forMarking G P torsion f proper even core literal stable marking.physical.marking⟩

def ForExit (E : StructuralExit G P) : Type 1 :=
  match E with
  | .stable _ _ _ _ tau core _ _ _ _ => MarkedReceipt G P tau core
  | .unary .. => PUnit.{2}
  | .infinite .. => PUnit.{2}
  | .odd .. => PUnit.{2}

def forExit (E : StructuralExit G P) : ForExit G P E :=
  match E with
  | .stable _ f proper even tau core literal _ _ stable =>
      markedReceipt G P tau f proper even core literal stable
  | .unary .. => PUnit.unit
  | .infinite .. => PUnit.unit
  | .odd .. => PUnit.unit

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenLocalOutcome
end
