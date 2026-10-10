import Holant.Proofs.Closure.ClosureSourceRowsC2FrontierFacts
import Holant.Proofs.Closure.QueueTaggedJoint

/-! A selected current q4 occurrence runs its OWN closed full batch. Actual
unary/infinite exits remain real; group growth carries a genuine sourceOmega
continuation. The unchanged branch uses this occurrence's regenerated CURRENT
deck before internally testing the C2 source endpoint. No old selected-f deck,
desired branch, successor programme or normalization oracle is supplied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows.C2Frontier
open Holant Holant.Algebraic Holant.Tractable
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4)
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

def batch : DeckBatchResult G P torsion q := QueueBatch.result G P torsion q core hcore (by norm_num)

theorem batch_family : (batch G P torsion q core hcore).palette.family =
    (state G P torsion q core hcore).augmented :=
  ProgrammeRetained.palette_family G P torsion q core hcore (by norm_num)

structure GroupReceipt (outer : StabilizationMathematical.Outer (state G P torsion q core hcore)) : Type 1 where
  successor : StabilizationMathematical.State (OI.K G)
  successorIdentity : successor = outer.target
  successorFamily : (batch G P torsion q core hcore).palette.family = successor.family
  step : Node.Step successor.node (state G P torsion q core hcore).node
  decreases : Node.RankLT successor.node.sourceOmega
    (state G P torsion q core hcore).node.sourceOmega

def groupReceipt (outer : StabilizationMathematical.Outer (state G P torsion q core hcore)) :
    GroupReceipt G P torsion q core hcore outer :=
  ⟨outer.target,rfl,(batch_family G P torsion q core hcore).trans outer.target_family.symm,
    outer.step,outer.source_decreases⟩

structure StableReceipt (stable : StabilizationMathematical.Stable (state G P torsion q core hcore)) where
  exit : StructuralExit G (batch G P torsion q core hcore).palette
  exitIdentity : exit = HistoryPalette.exit G (state G P torsion q core hcore)
    (batch G P torsion q core hcore).palette (batch_family G P torsion q core hcore) (.stable stable)
  regeneratedAccess : RetainedFinalAccess.Access G (batch G P torsion q core hcore).palette exit
  c2 : ClosureSourceRows.ForExit G (batch G P torsion q core hcore).palette exit

def stableReceipt (stable : StabilizationMathematical.Stable (state G P torsion q core hcore)) :
    StableReceipt G P torsion q core hcore stable :=
  let E := HistoryPalette.exit G (state G P torsion q core hcore)
    (batch G P torsion q core hcore).palette (batch_family G P torsion q core hcore) (.stable stable)
  ⟨E,rfl,RetainedFinalAccess.forStructuralExit G _ E,ClosureSourceRows.forStructuralExit G _ E⟩

/-- The receipt type is indexed by the actual mathematical constructor.
Odd and arity-descent alternatives are impossible for this q4-only batch. -/
def Meaning :
    StabilizationMathematical.Terminal (state G P torsion q core hcore) ⊕
      StabilizationMathematical.Outer (state G P torsion q core hcore) → Type 1
  | .inl (.unary u retained nonzero) =>
      RetainedFinalAccess.Access G (batch G P torsion q core hcore).palette
        (HistoryPalette.exit G (state G P torsion q core hcore)
          (batch G P torsion q core hcore).palette (batch_family G P torsion q core hcore)
          (.unary u retained nonzero))
  | .inl (.infinite B actual infiniteOrder) =>
      RetainedFinalAccess.Access G (batch G P torsion q core hcore).palette
        (HistoryPalette.exit G (state G P torsion q core hcore)
          (batch G P torsion q core hcore).palette (batch_family G P torsion q core hcore)
          (.infinite B actual infiniteOrder))
  | .inl (.odd _ _ _ _ _) => PEmpty.{2}
  | .inl (.stable S) => StableReceipt G P torsion q core hcore S
  | .inr (.group hτ noOdd strict) => GroupReceipt G P torsion q core hcore (.group hτ noOdd strict)
  | .inr (.arity _ _ _ _) => PEmpty.{2}

def meaning (noOdd : ∀ g ∈ P.family, Prime g → 3 ≤ g.1 → Even g.1)
    (branch : StabilizationMathematical.Terminal (state G P torsion q core hcore) ⊕
      StabilizationMathematical.Outer (state G P torsion q core hcore)) :
    Meaning G P torsion q core hcore branch := by
  cases branch with
  | inl terminal =>
      cases terminal with
      | unary u retained nonzero =>
          exact RetainedFinalAccess.forStructuralExit G
            (batch G P torsion q core hcore).palette
            (HistoryPalette.exit G (state G P torsion q core hcore)
              (batch G P torsion q core hcore).palette (batch_family G P torsion q core hcore)
              (.unary u retained nonzero))
      | infinite B actual infiniteOrder =>
          exact RetainedFinalAccess.forStructuralExit G
            (batch G P torsion q core hcore).palette
            (HistoryPalette.exit G (state G P torsion q core hcore)
              (batch G P torsion q core hcore).palette (batch_family G P torsion q core hcore)
              (.infinite B actual infiniteOrder))
      | odd f retained prime nonbinary oddArity =>
          exact False.elim ((Nat.not_even_iff_odd.mpr oddArity)
            (augmented_noOdd G P torsion q core hcore noOdd f retained prime nonbinary))
      | stable S => exact stableReceipt G P torsion q core hcore S
  | inr outer =>
      cases outer with
      | group hτ noOdd strict => exact groupReceipt G P torsion q core hcore (.group hτ noOdd strict)
      | arity hτ noOdd sameGroup smaller =>
          have hm := minimum_arity G P torsion q core hcore
          have hc : (state G P torsion q core hcore).core.signature.1 = 4 :=
            congrArg Sigma.fst hcore
          exact False.elim (by omega)

/-- Every stored field belongs to the same internally produced batch and
the exact dispatch constructor; no successful-state witness is caller input. -/
structure Result where
  physicalBatch : DeckBatchResult G P torsion q
  batchIdentity : physicalBatch = batch G P torsion q core hcore
  nativeJoint : FullQueue.TaggedJointTrace G P torsion q core hcore (by norm_num) true
    (FullQueue.taggedExecution G P torsion q).trace
  ambientJoint : HistoryPalette.Saved.TraceReceipt G (state G P torsion q core hcore) P rfl
  branch : StabilizationMathematical.Terminal (state G P torsion q core hcore) ⊕
    StabilizationMathematical.Outer (state G P torsion q core hcore)
  branchIdentity : branch = StabilizationMathematical.dispatch (state G P torsion q core hcore)
  receipt : Meaning G P torsion q core hcore branch

def run (noOdd : ∀ g ∈ P.family, Prime g → 3 ≤ g.1 → Even g.1) : Result G P torsion q core hcore :=
  ⟨batch G P torsion q core hcore,rfl,
    FullQueue.savedTaggedJoint G P torsion q core hcore (by norm_num),
    HistoryPalette.Saved.traceReceipt G (state G P torsion q core hcore) P rfl,
    StabilizationMathematical.dispatch (state G P torsion q core hcore),rfl,
    meaning G P torsion q core hcore noOdd (StabilizationMathematical.dispatch (state G P torsion q core hcore))⟩

/-- All actual current saved q4 occurrences are accepted. The source core
is internally proved minimum, and this occurrence supplies its own exact q. -/
def forOccurrence (o : CurrentOccurrences.Id G P)
    (arity : (CurrentOccurrences.savedLeaf G P o).1.1 = 4)
    (noOdd : ∀ g ∈ P.family, Prime g → 3 ≤ g.1 → Even g.1) :=
  let d := FrontierQ4.domain G P o arity noOdd
  let q := FrontierQ4.tableFour (CurrentOccurrences.savedLeaf G P o).1 arity
  let literal := d.literal.trans (FrontierQ4.tableFour_exact (CurrentOccurrences.savedLeaf G P o).1 arity).symm
  run G P torsion q d.minimum literal noOdd

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows.C2Frontier
