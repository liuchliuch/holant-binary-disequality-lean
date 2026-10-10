import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicEvenCurrent
import Holant.Proofs.Closure.ClosureCyclicRestartExecution

/-! Every repeated cyclic four-port continuation is consumed internally.
The proved finite group-defect iteration ends at a genuine whole-family
ordinary anchor, tractable/hard source, structural stop, or an actual freshly
exhausted noncyclic source. No endpoint, future deck, or callback is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicQ4Resolution
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace O
export GlobalCloseCompletionStopOrdinarySource (table family)
end O
namespace E
export GlobalCloseCompletionC2OrdinaryPairOutcome (HasEq4)
end E
namespace R
export ClosureCyclicRestart (Node SourceGroup Terminal Completion finish)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option Elab.async false
attribute [local irreducible] GeneratedGroupWorklist.result
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (origin : Palette G)

inductive Endpoint : Type 1 where
  | anchor (Q : Palette G) (old : origin.family⊆Q.family) (eq4 : E.HasEq4 (O.table G Q))
  | tract (Q : Palette G) (old : origin.family⊆Q.family) (criterion : Tract (O.family G Q))
  | hard (proof : NoXWeightedAntiSquares.Hard G)
  | stopped (Q : Palette G) (old : origin.family⊆Q.family) (stop : OccurrenceWorklist.Stop G Q)
  | other (base : Palette G) (A : GeneratedGroupWorklist.Active G base)
      (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
      (old : origin.family⊆run.final.source.palette.family)
      (noncyclic : ¬IsCyclic (completeGroup run.final.source.palette.family run.final.ready.torsion))

theorem from_even (P : Palette G) (old : origin.family⊆P.family)
    (out : GlobalCloseCompletionCyclicEvenCurrent.Outcome G P) : Nonempty (Endpoint G origin) := by
  cases out with
  | anchor Q kept anchor => exact ⟨.anchor Q (old.trans kept) anchor⟩
  | tract Q kept criterion => exact ⟨.tract Q (old.trans kept) criterion⟩
  | hard proof => exact ⟨.hard proof⟩
  | unary Q kept unary =>
    obtain ⟨u,retained,nonzero⟩ := unary
    exact ⟨.stopped Q (old.trans kept) (.unary u retained nonzero)⟩

theorem prepare_other (P : Palette G) (old : origin.family⊆P.family)
    (torsion : ResidualTorsion P.family) (noncyclic : ¬IsCyclic (completeGroup P.family torsion)) :
    Nonempty (Endpoint G origin) := by
  cases GeneratedGroupWorklist.result G P with
  | initialStop stop _ => exact ⟨.stopped P old stop⟩
  | prepared ready recomputed result =>
    cases result with
    | inl stopped => exact ⟨.stopped stopped.finalSource.palette
        (old.trans (GroupPreparedStability.source_retains G P stopped.finalSource)) stopped.stop⟩
    | inr run =>
      have kept : P.family⊆run.final.source.palette.family :=
        GroupPreparedStability.source_retains G P run.final.source
      have guard : ¬IsCyclic (completeGroup run.final.source.palette.family run.final.ready.torsion) := by
        intro cyclic
        letI := cyclic
        exact noncyclic (Subgroup.isCyclic_of_le (completeGroup_mono kept torsion run.final.ready.torsion))
      exact ⟨.other P _ run rfl (old.trans kept) guard⟩

variable (S : R.Node G) (range : 3≤Nat.card (R.SourceGroup G S))

include range in
theorem range_retained (T : R.Node G) (old : S.palette.family⊆T.palette.family) :
    3≤Nat.card (R.SourceGroup G T) := by
  letI := completeGroup_finite T.palette.family T.torsion
  have inclusion := completeGroup_mono old S.torsion T.torsion
  have cardinal := Nat.card_le_card_of_injective (Subgroup.inclusion inclusion) (Subgroup.inclusion_injective inclusion)
  have oldRange : 3≤Nat.card (completeGroup S.palette.family S.torsion) := by
    simpa only [R.SourceGroup,ClosureMarkedDihedral.Source.source_cardinal] using range
  simpa only [R.SourceGroup,ClosureMarkedDihedral.Source.source_cardinal] using oldRange.trans cardinal

include range in
theorem terminal_consumed (T : R.Node G) (old : S.palette.family⊆T.palette.family)
    (terminal : R.Terminal G T) : Nonempty (Endpoint G S.palette) := by
  cases terminal with
  | noncyclic guard =>
    exact prepare_other G S.palette T.palette old T.torsion
      (ClosureFieldBridgeEquiv.source_not_isCyclic (ClosureSourceRows.embedding G) T.palette.family T.torsion guard)
  | small cyclic guard => exact False.elim (guard (range_retained G S range T old))
  | endpoint cyclic size receipt same =>
    obtain ⟨out⟩ := GlobalCloseCompletionCyclicEvenCurrent.actual_classified G T.palette T.torsion cyclic
      (ClosureCyclicCurrent.EndpointReceipt.output G T.palette receipt)
      (ClosureCyclicCurrent.ProjectiveOutput.source_actual G T.palette receipt.target receipt.access)
      (ClosureCyclicCurrent.EndpointReceipt.source_prime G T.palette receipt)
      (ClosureCyclicCurrent.EndpointReceipt.source_even G T.palette receipt)
    exact from_even G S.palette T.palette old out
  | unary cyclic size receipt domain unary same =>
    have kept := (ClosureCyclicRestart.projectiveCopy G T.palette receipt.card.signature receipt.access
      (by norm_num) receipt.card.nonzero).retains
    exact ⟨.stopped (ClosureCyclicCurrent.OutsideReceipt.palette G T.palette receipt) (old.trans kept)
      (.unary unary.output unary.retained unary.nonzero)⟩
  | installedStop cyclic size receipt same stop physical =>
    have kept : T.palette.family⊆(ClosureCyclicCurrent.installedPalette G T.palette receipt.doubled).family := by
      rintro f ⟨i,rfl⟩
      exact ⟨ClosureCyclicCurrent.installedOldLabel G T.palette receipt.doubled i,
        congrArg Sigma.fst (ClosureCyclicCurrent.installed_old_saved G T.palette receipt.doubled i)⟩
    exact ⟨.stopped _ (old.trans kept) stop⟩
  | preparedOther growth other =>
    have kept := old.trans growth.copy.retains
    cases equation : growth.exit with
    | unary u retained nonzero => exact ⟨.stopped growth.finalPalette kept (.unary u retained nonzero)⟩
    | infinite B actual infiniteOrder => exact ⟨.stopped growth.finalPalette kept (.infinite B actual infiniteOrder)⟩
    | odd f retained prime nonbinary odd => exact ⟨.stopped growth.finalPalette kept (.odd f retained prime nonbinary odd)⟩
    | stable m q proper even torsion core literal noUnary noOdd matching =>
      have size := growth.final_stable_residual_eq_two q proper core literal
      subst m
      exact False.elim (other (by rw [equation];rfl))

include range in
theorem resolved : Nonempty (Endpoint G S.palette) := by
  let result := R.finish G S
  exact terminal_consumed G S range result.last (result.trace.copy G).retains result.terminal

def complete : Endpoint G S.palette := (resolved G S range).some


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicQ4Resolution
end
