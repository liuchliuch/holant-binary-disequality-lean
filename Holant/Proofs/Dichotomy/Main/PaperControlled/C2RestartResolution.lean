import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryPairOutcome
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2PreparedFrontier

/-! Finite consumption of every repeated C2 bad-minimum restart. Each step
installs a genuine graph and its complete factor catalogue, runs the real
GeneratedGroupWorklist, and preserves the entire source. A renewed C2 branch
strictly decreases the retained bad-prime arity. The final source is tractable,
hard, Eq4-anchored, structurally stopped, or genuinely outside C2 with its
actual exhausted-run receipt. No future classifier callback is an input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2RestartResolution
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace O
export GlobalCloseCompletionStopOrdinarySource (family table)
end O
namespace F
export GlobalCloseCompletionRetainedFlatLeaf (Predicate split_closed)
end F
namespace B
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end B
namespace R
export GlobalCloseCompletionC2FlatRestart (Output)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option Elab.async false
attribute [local irreducible] GeneratedGroupWorklist.result
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (origin : Palette G)

inductive Endpoint : Type 1 where
  | tract (Q : Palette G) (old : origin.family⊆Q.family) (criterion : Tract (O.family G Q))
  | hard (proof : PaperControlledHardness.Original G)
  | anchor (Q : Palette G) (old : origin.family⊆Q.family)
      (eq4 : PaperControlled.C2OrdinaryPairOutcome.HasEq4 (O.table G Q))
  | stopped (Q : Palette G) (old : origin.family⊆Q.family) (stop : OccurrenceWorklist.Stop G Q)
  | other (base : Palette G) (A : GeneratedGroupWorklist.Active G base)
      (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
      (old : origin.family⊆run.final.source.palette.family)
      (notTwo : Nat.card (completeGroup run.final.source.palette.family run.final.ready.torsion)≠2)

theorem restart_terminates : ∀k : ℕ,∀P : Palette G,∀M : B.Minimum G P (F.Predicate G),
    M.signature.1=k→ origin.family⊆P.family→R.Output G P M→Nonempty (Endpoint G origin) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro P M size old D
    let installed := ProgrammeSaturation.palette G P D.signature D.nonzero D.positive D.actual
    have included : P.family⊆installed.family := ProgrammeSaturation.retains_old G P _ _ _ _
    have root : D.signature∈installed.family := by
      exact ⟨RetainedFactorCatalogue.rootLabel G P _ _,
        congrArg Sigma.fst (ProgrammeSaturation.root_saved G P _ _ _ _)⟩
    cases GeneratedGroupWorklist.result G installed with
    | initialStop stop _ => exact ⟨.stopped installed (old.trans included) stop⟩
    | prepared ready recomputed result =>
      cases result with
      | inl stopped =>
        exact ⟨.stopped stopped.finalSource.palette
          (old.trans (included.trans (GroupPreparedStability.source_retains G installed stopped.finalSource))) stopped.stop⟩
      | inr run =>
        let Q := run.final.source.palette
        have saved : installed.family⊆Q.family := GroupPreparedStability.source_retains G installed run.final.source
        have oldQ : origin.family⊆Q.family := old.trans (included.trans saved)
        by_cases two : Nat.card (completeGroup Q.family run.final.ready.torsion)=2
        · rcases PaperControlled.C2PreparedFrontier.exhausted G installed run rfl two with
            tract|hard|anchor|⟨next,nextD⟩
          · exact ⟨.tract Q oldQ tract⟩
          · exact ⟨.hard hard⟩
          · exact ⟨.anchor Q oldQ anchor⟩
          · obtain ⟨nextD⟩ := nextD
            have smaller : next.signature.1<k :=
              (next.arity_le_retained G Q (F.Predicate G) (F.split_closed G) D.signature (saved root) D.bad).trans_lt
                (D.smaller.trans_eq size)
            exact ih next.signature.1 smaller Q next rfl oldQ nextD
        · exact ⟨.other installed _ run rfl oldQ two⟩

variable (base : Palette G)

theorem result_endpoint (result : GeneratedGroupWorklist.Result G base) : Nonempty (Endpoint G base) := by
  cases result with
  | initialStop stop _ => exact ⟨.stopped base (Set.Subset.refl _) stop⟩
  | prepared ready recomputed result =>
    cases result with
    | inl stopped => exact ⟨.stopped stopped.finalSource.palette
        (GroupPreparedStability.source_retains G base stopped.finalSource) stopped.stop⟩
    | inr run =>
      let Q := run.final.source.palette
      have old : base.family⊆Q.family := GroupPreparedStability.source_retains G base run.final.source
      by_cases two : Nat.card (completeGroup Q.family run.final.ready.torsion)=2
      · rcases PaperControlled.C2PreparedFrontier.exhausted G base run rfl two with
          tract|hard|anchor|⟨M,D⟩
        · exact ⟨.tract Q old tract⟩
        · exact ⟨.hard hard⟩
        · exact ⟨.anchor Q old anchor⟩
        · obtain ⟨D⟩ := D
          exact restart_terminates G base M.signature.1 Q M rfl old D
      · exact ⟨.other base _ run rfl old two⟩

def complete : Endpoint G base := (result_endpoint G base (GeneratedGroupWorklist.result G base)).some

def original_current_c2_resolution : Endpoint G (Initial.palette G) := complete G (Initial.palette G)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2RestartResolution
end
