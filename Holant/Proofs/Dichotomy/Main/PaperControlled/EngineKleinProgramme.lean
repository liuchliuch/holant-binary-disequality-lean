import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineTransitions
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineKleinTransitions
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineKleinFrontier
import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedPredicateRestart

/-! A generic actual-output restart consumes its full saved factor batch and
the real generated-group worklist. Any changed group gives the global engine's
strict defect decrease; the same-group branch retains the exact exhausted
receipt and exact final palette for predicate-minimum descent. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.EngineKleinProgramme
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace R
export GlobalCloseCompletionRetainedPredicateRestart (installed preparation finalPalette finalSource retains_old)
end R
namespace T
export PaperControlled.EngineTransitions (Step CurrentTract Hard current_mono)
end T
namespace K
export PaperControlled.EngineKleinFrontier (Higher exhausted)
end K
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
attribute [local irreducible] GeneratedGroupWorklist.result
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : AnySignature (OI.K G)) (nonzero : q.2≠0) (positive : 0<q.1)
variable (actual : Gadget.Realizes P.family .disequality q.2)

structure Same where
  active : GeneratedGroupWorklist.Active G (R.installed G P q nonzero positive actual)
  run : GeneratedGroupWorklist.Exhausted G (R.installed G P q nonzero positive actual) active
  noPrior : active.source.done=∅
  palette_eq : R.finalPalette G P q nonzero positive actual=run.final.source.palette
  old : P.family⊆run.final.source.palette.family
  group_eq : completeGroup run.final.source.palette.family run.final.ready.torsion=completeGroup P.family torsion

theorem restart : Nonempty (T.Step G P torsion) ∨ Nonempty (Same G P torsion q nonzero positive actual) := by
  have installedOld : P.family⊆(R.installed G P q nonzero positive actual).family :=
    ProgrammeSaturation.retains_old G P q nonzero positive actual
  cases equation : R.preparation G P q nonzero positive actual with
  | initialStop stop trace => exact Or.inl ⟨.stopped (R.installed G P q nonzero positive actual) installedOld stop⟩
  | prepared ready trace result =>
    cases result with
    | inl stopped =>
      exact Or.inl ⟨.stopped stopped.finalSource.palette
        (installedOld.trans (GroupPreparedStability.source_retains G (R.installed G P q nonzero positive actual) stopped.finalSource))
        stopped.stop⟩
    | inr run =>
      have samePalette : R.finalPalette G P q nonzero positive actual=run.final.source.palette := by
        unfold R.finalPalette R.finalSource
        rw [equation]
        rfl
      have old : P.family⊆run.final.source.palette.family :=
        installedOld.trans (GroupPreparedStability.source_retains G (R.installed G P q nonzero positive actual) run.final.source)
      by_cases same : completeGroup run.final.source.palette.family run.final.ready.torsion=completeGroup P.family torsion
      · exact Or.inr ⟨⟨_,run,rfl,samePalette,old,same⟩⟩
      · exact Or.inl ⟨.next (R.installed G P q nonzero positive actual) _ run rfl old
          (sourceGroupDefect_lt_of_strict torsion run.final.ready.torsion
            (lt_of_le_of_ne (completeGroup_mono old torsion run.final.ready.torsion) (fun eq=>same eq.symm)))⟩

theorem Same.frontier (S : Same G P torsion q nonzero positive actual)
    (cardinal : Nat.card (completeGroup P.family torsion)=4)
    (noncyclic : ¬IsCyclic (completeGroup P.family torsion)) :
    Nonempty (T.Step G P torsion) ∨
      Nonempty (K.Higher G (R.installed G P q nonzero positive actual) S.run) := by
  have four : Nat.card (completeGroup S.run.final.source.palette.family S.run.final.ready.torsion)=4 := by
    rw [S.group_eq]
    exact cardinal
  have nc : ¬IsCyclic (completeGroup S.run.final.source.palette.family S.run.final.ready.torsion) := by
    rw [S.group_eq]
    exact noncyclic
  have fourSource : Nat.card (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
      S.run.final.source.palette.family S.run.final.ready.torsion)=4 := by
    rw [ClosureMarkedDihedral.Source.source_cardinal]
    exact four
  have ncSource : ¬IsCyclic (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
      S.run.final.source.palette.family S.run.final.ready.torsion) := by
    exact fun h=>nc ((ClosureFieldBridgeEquiv.source_isCyclic_iff (ClosureSourceRows.embedding G)
      S.run.final.source.palette.family S.run.final.ready.torsion).mpr h)
  rcases K.exhausted G (R.installed G P q nonzero positive actual) S.run S.noPrior fourSource ncSource with tract|hard|higher
  · exact Or.inl ⟨.tract (T.current_mono G P S.run.final.source.palette S.old tract)⟩
  · exact Or.inl ⟨.hard hard⟩
  · exact Or.inr higher


def restrict_same (Q : Palette G) (newTorsion : ResidualTorsion Q.family)
    (old : P.family⊆Q.family) (same : completeGroup Q.family newTorsion=completeGroup P.family torsion)
    (step : T.Step G Q newTorsion) : T.Step G P torsion := by
  have rank : sourceGroupDefect Q.family newTorsion=sourceGroupDefect P.family torsion := by
    simp only [sourceGroupDefect,same]
  cases step with
  | tract criterion => exact .tract (T.current_mono G P Q old criterion)
  | hard proof => exact .hard proof
  | stopped target kept stop => exact .stopped target (old.trans kept) stop
  | next base active run noPrior kept decreases =>
    exact .next base active run noPrior (old.trans kept) (decreases.trans_eq rank)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.EngineKleinProgramme
end
