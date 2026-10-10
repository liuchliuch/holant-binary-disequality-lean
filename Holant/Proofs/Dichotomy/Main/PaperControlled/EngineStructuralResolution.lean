import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinCurrentSource
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineTransitions
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineKleinFrontier
import Holant.Proofs.Dichotomy.Main.PaperControlled.NativeMComplete
import Holant.Proofs.Dichotomy.Main.PaperControlled.BComplete
import Holant.Proofs.Dichotomy.Main.PaperControlled.A0Complete
import Holant.Proofs.Dichotomy.Main.PaperControlled.ShiftedComplete
import Holant.Proofs.Dichotomy.Main.PaperControlled.PlatonicComplete

/-! The full exhausted engine consumes all eight markings, including the
proved standard real-Klein family continuation. Strong induction uses actual
source-group defect and retains the full original alphabet. Only genuine
structural stops remain; this endpoint does not assume a stop classifier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.EngineStructuralResolution
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace T
export PaperControlled.EngineTransitions (CurrentTract Hard current_mono Step)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

inductive Endpoint (origin : Palette G) : Type 1 where
  | tract (criterion : T.CurrentTract G origin)
  | hard (proof : T.Hard G)
  | stopped (Q : Palette G) (old : origin.family⊆Q.family) (stop : OccurrenceWorklist.Stop G Q)

def Endpoint.restrict (P Q : Palette G) (old : P.family⊆Q.family)
    (endpoint : Endpoint G Q) : Endpoint G P := by
  cases endpoint with
  | tract criterion => exact .tract (T.current_mono G P Q old criterion)
  | hard proof => exact .hard proof
  | stopped target kept stop => exact .stopped target (old.trans kept) stop

/-- Strong induction consumes every actual C2/cyclic transition, including
changes between those markings. No theorem-producing callback is an input. -/
theorem exhausted_terminates : ∀k : ℕ,∀base : Palette G,
    ∀A : GeneratedGroupWorklist.Active G base,
    ∀run : GeneratedGroupWorklist.Exhausted G base A, A.source.done=∅→
    sourceGroupDefect run.final.source.palette.family run.final.ready.torsion=k→
    Nonempty (Endpoint G run.final.source.palette) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro base A run noPrior rank
    have proceed (step : T.Step G run.final.source.palette run.final.ready.torsion) :
        Nonempty (Endpoint G run.final.source.palette) := by
      cases step with
      | tract criterion => exact ⟨.tract criterion⟩
      | hard proof => exact ⟨.hard proof⟩
      | stopped Q old stop => exact ⟨.stopped Q old stop⟩
      | next target active next fresh old decreases =>
        obtain ⟨endpoint⟩ := ih
          (sourceGroupDefect next.final.source.palette.family next.final.ready.torsion)
          (decreases.trans_eq rank) target active next fresh rfl
        exact ⟨Endpoint.restrict G run.final.source.palette next.final.source.palette old endpoint⟩
    cases (ClosureMarkedActualReceipts.produce G run.final.source.palette
      run.final.ready.torsion).physical.marking with
    | smallTwo two =>
      have originalTwo : Nat.card (completeGroup run.final.source.palette.family
          run.final.ready.torsion)=2 := by
        rw [←ClosureMarkedDihedral.Source.source_cardinal (ClosureSourceRows.embedding G)
          run.final.source.palette.family run.final.ready.torsion]
        exact two
      obtain ⟨step⟩ := PaperControlled.EngineTransitions.c2_exhausted G base run noPrior originalTwo
      exact proceed step
    | cyclic native =>
      obtain ⟨step⟩ := PaperControlled.EngineTransitions.cyclic_exhausted G base run noPrior native
      exact proceed step
    | smallFour four noncyclic =>
      rcases PaperControlled.EngineKleinFrontier.exhausted G base run noPrior four noncyclic with
        tract|hard|higher
      · exact ⟨.tract tract⟩
      · exact ⟨.hard hard⟩
      · obtain ⟨higher⟩ := higher
        obtain ⟨step⟩:=PaperControlled.KleinCurrentSource.source G base run noPrior higher
        exact proceed step
    | monomial native =>
      rcases PaperControlled.NativeMComplete.classified G base run noPrior native with tract|hard
      · exact ⟨.tract tract⟩
      · exact ⟨.hard hard⟩
    | bilinear native =>
      rcases PaperControlled.BComplete.classified G base run noPrior native with tract|hard
      · exact ⟨.tract tract⟩
      · exact ⟨.hard hard⟩
    | unshifted z native y =>
      rcases PaperControlled.A0Complete.classified G base run noPrior native z y with tract|hard
      · exact ⟨.tract tract⟩
      · exact ⟨.hard hard⟩
    | shifted axis noncyclic notTwo notFour noZ reflection same =>
      rcases PaperControlled.ShiftedComplete.classified G base run noPrior
        ⟨axis,noncyclic,notTwo,notFour,noZ,reflection,same⟩ with tract|hard
      · exact ⟨.tract tract⟩
      · exact ⟨.hard hard⟩
    | platonic model semantic =>
      rcases PaperControlled.PlatonicComplete.classified G base run noPrior model semantic with tract|hard
      · exact ⟨.tract tract⟩
      · exact ⟨.hard hard⟩

variable (base : Palette G)

theorem result_endpoint (result : GeneratedGroupWorklist.Result G base) :
    Nonempty (Endpoint G base) := by
  cases result with
  | initialStop stop _ => exact ⟨.stopped base (Set.Subset.refl _) stop⟩
  | prepared ready trace result =>
    cases result with
    | inl stopped =>
      exact ⟨.stopped stopped.finalSource.palette
        (GroupPreparedStability.source_retains G base stopped.finalSource) stopped.stop⟩
    | inr run =>
      obtain ⟨endpoint⟩ := exhausted_terminates G _ base _ run rfl rfl
      exact ⟨Endpoint.restrict G base run.final.source.palette
        (GroupPreparedStability.source_retains G base run.final.source) endpoint⟩

def complete : Endpoint G base :=
  (result_endpoint G base (GeneratedGroupWorklist.result G base)).some

/-- G is the only input. Every unchanged exhausted marking is consumed.
The remaining endpoint contains an actual structural stop and the exact
whole-family inclusion needed by its universal source consumer. -/
def original_current_structural_resolution : Endpoint G (Initial.palette G) :=
  complete G (Initial.palette G)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.EngineStructuralResolution
end
