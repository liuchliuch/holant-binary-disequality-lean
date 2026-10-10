import Holant.Proofs.Closure.ClosureCyclicRestartKernel

/-! A real cyclic installation followed by the closed CURRENT-group producer.
The strict original-field group growth survives every actual preparation batch.
The next stable deck is regenerated from that producer's own final ledger. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
attribute [local irreducible] ClosureCyclicCurrent.selected ClosureCyclicCurrent.run
  ClosureCyclicCurrent.installedPalette GeneratedGroupWorklist.result
abbrev SourceGroup (S : Node G) :=
  ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) S.palette.family S.torsion

structure Growth (S : Node G) : Type 1 where
  cyclic : IsCyclic (SourceGroup G S)
  range : 3 ≤ Nat.card (SourceGroup G S)
  doubled : CyclicBoundary.NonsquareExit.DoubledOutside
    (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) S.palette.family)
    (ClosureCyclicCurrent.selected G S.palette S.torsion cyclic range).m
  branchSame : (ClosureCyclicCurrent.Result.doubled ⟨doubled⟩ :
    ClosureCyclicCurrent.Result G S.palette
      (ClosureCyclicCurrent.selected G S.palette S.torsion cyclic range).m) =
    ClosureCyclicCurrent.run G S.palette S.torsion S.q S.core S.literal S.matching cyclic range
  ready : OccurrenceWorklist.Ready G (ClosureCyclicCurrent.installedPalette G S.palette doubled)
  strict : completeGroup S.palette.family S.torsion <
    completeGroup (ClosureCyclicCurrent.installedPalette G S.palette doubled).family ready.torsion

namespace Growth
variable {G} {S : Node G} (g : Growth G S)
abbrev installed : Palette G := ClosureCyclicCurrent.installedPalette G S.palette g.doubled

def installedCopy : Copy G S.palette g.installed :=
  ⟨ClosureCyclicCurrent.installedOldLabel G S.palette g.doubled,
    ClosureCyclicCurrent.installedOldLabel_injective G S.palette g.doubled,
    ClosureCyclicCurrent.installed_old_saved G S.palette g.doubled⟩

/-- No caller's future worklist or successful preparation is accepted. -/
def preparation : GeneratedGroupWorklist.Result G g.installed :=
  GeneratedGroupWorklist.result G g.installed

theorem preparation_factory : g.preparation = GeneratedGroupWorklist.result G g.installed := rfl

abbrev finalSource := (g.preparation).finalSource G g.installed
abbrev finalPalette : Palette G := g.finalSource.palette

def preparedCopy : Copy G g.installed g.finalPalette :=
  ⟨g.finalSource.rootLabel,g.finalSource.rootInjective,g.finalSource.rootSaved⟩

def copy : Copy G S.palette g.finalPalette := g.installedCopy.comp g.preparedCopy

theorem final_minimum_arity_le_four (core : MinimumCore g.finalPalette.family) : core.signature.1 ≤ 4 := by
  have bound := MinimumCore.arity_nonincrease g.copy.retains S.core core
  have sourceArity := congrArg Sigma.fst S.literal
  change S.core.signature.1 = 4 at sourceArity
  omega

theorem final_stable_residual_eq_two {m : ℕ} (q : Signature (OI.K G) (m+2))
    (proper : 2 ≤ m) (core : MinimumCore g.finalPalette.family)
    (literal : core.signature = ⟨m+2,q⟩) : m = 2 := by
  have bound := g.final_minimum_arity_le_four core
  have arity := congrArg Sigma.fst literal
  change core.signature.1 = m+2 at arity
  omega

theorem installed_nonbinary : ∃ f ∈ g.installed.family, Holant.LocalDrafts.FinitePGL2.Stabilization.Prime f ∧ 3 ≤ f.1 := by
  obtain ⟨f,retained,prime,arity⟩ := S.nonbinary G
  exact ⟨f,g.installedCopy.retains retained,prime,arity⟩

/-- This is the actual fresh final-group exit, not the predecessor's stable deck. -/
def exit : StructuralExit G g.finalPalette :=
  GroupPreparedStability.resultExit G g.installed g.preparation g.installed_nonbinary

theorem exit_factory : g.exit =
    GroupPreparedStability.resultExit G g.installed g.preparation g.installed_nonbinary := rfl

/-- Charged access to this exact fresh exit, including every current raw key. -/
def exitAccess : RetainedFinalAccess.Access G g.finalPalette g.exit :=
  RetainedFinalAccess.forStructuralExit G g.finalPalette g.exit

theorem exitAccess_factory : g.exitAccess =
    RetainedFinalAccess.forStructuralExit G g.finalPalette g.exit := rfl

theorem strict_final (torsion : ResidualTorsion g.finalPalette.family) :
    completeGroup S.palette.family S.torsion < completeGroup g.finalPalette.family torsion :=
  lt_of_lt_of_le g.strict (completeGroup_mono g.preparedCopy.retains g.ready.torsion torsion)

theorem rank_lt (torsion : ResidualTorsion g.finalPalette.family) :
    sourceGroupDefect g.finalPalette.family torsion < S.rank G :=
  sourceGroupDefect_lt_of_strict S.torsion torsion (g.strict_final torsion)

end Growth

/-- Every repeated node is the literal q4 constructor of this fresh exit. -/
inductive Step (S : Node G) : Node G → Type 1
  | next (growth : Growth G S) (torsion : ResidualTorsion growth.finalPalette.family)
      (q : Signature (OI.K G) 4) (core : MinimumCore growth.finalPalette.family)
      (literal : core.signature = ⟨4,q⟩)
      (noUnary : ¬ RetainedUnary growth.finalPalette.family)
      (noOdd : StabilizationMathematical.NoOdd growth.finalPalette.family)
      (matching : ∀ f ∈ rawDeck growth.finalPalette.family torsion q,
        MatchingOrZero (actualTransfers growth.finalPalette.family) f)
      (sameExit : growth.exit = .stable 2 q (by decide) (by decide) torsion core literal noUnary noOdd matching) :
      Step S ⟨growth.finalPalette,torsion,q,core,literal,noUnary,noOdd,matching⟩

def Step.copy {S T : Node G} (e : Step G S T) : Copy G S.palette T.palette := by
  cases e with
  | next growth _ _ _ _ _ _ _ _ => exact growth.copy

theorem Step.decreases {S T : Node G} (e : Step G S T) : Earlier G T S := by
  cases e with
  | next growth torsion _ _ _ _ _ _ _ => exact growth.rank_lt torsion

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
end
