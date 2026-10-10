import Holant.Proofs.Dichotomy.Closure.Engine.GlobalCloseCompletionEngineTransitions
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinQuaternaryContinuation

/-! Consume a genuine nonmatching Klein quaternary through its actual
programme saturation and generated-group run. Unchanged groups close by the
completed quaternary theorem; changed groups strictly decrease the same
original-field defect used by the global engine. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEngineKleinTransitions
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace R
export GlobalCloseCompletionKleinQuaternaryRestart
  (installed preparation finalPalette finalSource nonzero root)
end R
namespace T
export GlobalCloseCompletionEngineTransitions (Step current_mono)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
attribute [local irreducible] GeneratedGroupWorklist.result
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))

include cardinal noncyclic in
theorem restart_step (d : GlobalCloseCompletionKleinQuaternaryRestart.D.Output G P) :
    Nonempty (T.Step G P torsion) := by
  have installedOld : P.family⊆(R.installed G P d).family :=
    ProgrammeSaturation.retains_old G P (R.root G P d) (R.nonzero G P d) (by change 0<4; decide) d.actual
  cases equation : R.preparation G P d with
  | initialStop stop trace => exact ⟨.stopped (R.installed G P d) installedOld stop⟩
  | prepared ready trace result =>
    cases result with
    | inl stopped =>
      exact ⟨.stopped stopped.finalSource.palette
        (installedOld.trans (GroupPreparedStability.source_retains G (R.installed G P d) stopped.finalSource))
        stopped.stop⟩
    | inr run =>
      have samePalette : R.finalPalette G P d=run.final.source.palette := by
        unfold R.finalPalette R.finalSource
        rw [equation]
        rfl
      have old : P.family⊆run.final.source.palette.family :=
        installedOld.trans (GroupPreparedStability.source_retains G (R.installed G P d) run.final.source)
      cases GlobalCloseCompletionStopArityTwo.complete G run.final.source.palette with
      | small empty _ =>
        exact ⟨.tract (T.current_mono G P run.final.source.palette old
          (FrontierSmallArity.small_native_tractX G run.final.source.palette empty))⟩
      | higher data =>
        have high := GlobalCloseCompletionStopArityTwo.large_retained G run.final.source.palette data
        obtain ⟨core⟩ := exists_minimumCore run.final.source.palette.family ⟨_,high⟩
        obtain ⟨m,f,proper,even,literal,stable⟩ :=
          GroupPreparedStability.forExhausted G (R.installed G P d) run rfl core
        have continuation := GlobalCloseCompletionKleinQuaternaryContinuation.stable_classified_or_growth
          G P torsion d cardinal noncyclic
        rw [samePalette] at continuation
        rcases continuation run.final.ready.torsion f proper even core literal run.final.ready.noUnary stable with
          tract|hard|growth
        · exact ⟨.tract tract⟩
        · exact ⟨.hard hard⟩
        · exact ⟨.next (R.installed G P d) _ run rfl old
            (sourceGroupDefect_lt_of_strict torsion run.final.ready.torsion growth)⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEngineKleinTransitions
end
