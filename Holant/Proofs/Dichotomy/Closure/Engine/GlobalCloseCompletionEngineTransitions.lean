import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RestartResolution
import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicResolvedSource
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryEq4Complete

/-! Actual C2 and cyclic continuation, with every ordinary Eq4 exit consumed.
The only continuing constructor contains the real exhausted engine receipt,
whole-source inclusion, and a strict decrease of the original-field group
defect. Structural stops are preserved as actual stops, not classified here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEngineTransitions
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace O
export GlobalCloseCompletionStopOrdinarySource (family tract_iff_current)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
abbrev CurrentTract (P : Palette G) :=
  TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P))
abbrev Hard := NoXWeightedAntiResourcesOriginal.Hard G

theorem current_mono (P Q : Palette G) (old : P.family⊆Q.family)
    (criterion : CurrentTract G Q) : CurrentTract G P :=
  (O.tract_iff_current G P).mp (((O.tract_iff_current G Q).mpr criterion).mono_family
    (GlobalCloseCompletionCyclicResolvedSource.ordinary_mono G P Q old))

inductive Step (P : Palette G) (torsion : ResidualTorsion P.family) : Type 1 where
  | tract (criterion : CurrentTract G P)
  | hard (proof : Hard G)
  | stopped (Q : Palette G) (old : P.family⊆Q.family) (stop : OccurrenceWorklist.Stop G Q)
  | next (base : Palette G) (A : GeneratedGroupWorklist.Active G base)
      (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
      (old : P.family⊆run.final.source.palette.family)
      (decreases : sourceGroupDefect run.final.source.palette.family run.final.ready.torsion <
        sourceGroupDefect P.family torsion)

theorem c2_extension_decreases (P : Palette G) (torsion : ResidualTorsion P.family)
    (two : Nat.card (completeGroup P.family torsion)=2)
    (Q : Palette G) (newTorsion : ResidualTorsion Q.family)
    (old : P.family⊆Q.family) (notTwo : Nat.card (completeGroup Q.family newTorsion)≠2) :
    sourceGroupDefect Q.family newTorsion<sourceGroupDefect P.family torsion := by
  apply sourceGroupDefect_lt_of_strict torsion newTorsion
  apply lt_of_le_of_ne (completeGroup_mono old torsion newTorsion)
  intro same
  exact notTwo (same ▸ two)

theorem c2_install (P : Palette G) (torsion : ResidualTorsion P.family)
    (two : Nat.card (completeGroup P.family torsion)=2)
    (endpoint : GlobalCloseCompletionC2RestartResolution.Endpoint G P) :
    Nonempty (Step G P torsion) := by
  cases endpoint with
  | tract Q old criterion =>
    exact ⟨.tract ((O.tract_iff_current G P).mp (criterion.mono_family
      (GlobalCloseCompletionCyclicResolvedSource.ordinary_mono G P Q old)))⟩
  | hard proof => exact ⟨.hard proof⟩
  | anchor Q old anchor =>
    rcases GlobalCloseCompletionOrdinaryEq4Complete.current_classified G Q anchor with tract|hard
    · exact ⟨.tract (current_mono G P Q old tract)⟩
    · exact ⟨.hard hard⟩
  | stopped Q old stop => exact ⟨.stopped Q old stop⟩
  | other base A run noPrior old notTwo =>
    exact ⟨.next base A run noPrior old (c2_extension_decreases G P torsion two
      run.final.source.palette run.final.ready.torsion old notTwo)⟩

variable (base : Palette G) {A : GeneratedGroupWorklist.Active G base}
variable (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)

include noPrior in
theorem c2_exhausted (two : Nat.card (completeGroup run.final.source.palette.family
    run.final.ready.torsion)=2) :
    Nonempty (Step G run.final.source.palette run.final.ready.torsion) := by
  rcases GlobalCloseCompletionC2PreparedFrontier.exhausted G base run noPrior two with
    tract|hard|anchor|⟨minimum,restart⟩
  · exact ⟨.tract ((O.tract_iff_current G run.final.source.palette).mp tract)⟩
  · exact ⟨.hard hard⟩
  · rcases GlobalCloseCompletionOrdinaryEq4Complete.current_classified G run.final.source.palette anchor with tract|hard
    · exact ⟨.tract tract⟩
    · exact ⟨.hard hard⟩
  · obtain ⟨restart⟩ := restart
    obtain ⟨endpoint⟩ := GlobalCloseCompletionC2RestartResolution.restart_terminates G
      run.final.source.palette minimum.signature.1 run.final.source.palette minimum rfl
      (Set.Subset.refl _) restart
    exact c2_install G run.final.source.palette run.final.ready.torsion two endpoint

include noPrior in
theorem cyclic_exhausted (native : ClosureMarkedCyclic.NativeCyclic
    (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
      run.final.source.palette.family run.final.ready.torsion)) :
    Nonempty (Step G run.final.source.palette run.final.ready.torsion) := by
  have cyclic : IsCyclic (completeGroup run.final.source.palette.family run.final.ready.torsion) :=
    (ClosureFieldBridgeEquiv.source_isCyclic_iff (ClosureSourceRows.embedding G)
      run.final.source.palette.family run.final.ready.torsion).mpr
        (GlobalCloseCompletionCyclicPreparedResolution.native_cyclic _ native)
  cases GlobalCloseCompletionCyclicResolvedSource.complete G base run noPrior native with
  | tract criterion => exact ⟨.tract criterion⟩
  | hard proof => exact ⟨.hard proof⟩
  | ordinary data =>
    exact ⟨.hard (NoXGeneralComplete.countingHard G data.source data.zLabel data.zLiteral data.negative)⟩
  | stopped Q old stop => exact ⟨.stopped Q old stop⟩
  | other target active next noPrior old noncyclic =>
    exact ⟨.next target active next noPrior old
      (GlobalCloseCompletionCyclicResolvedSource.noncyclic_extension_decreases G
        run.final.source.palette run.final.ready.torsion cyclic next.final.source.palette
        next.final.ready.torsion old noncyclic)⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEngineTransitions
end
