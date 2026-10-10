import Holant.Proofs.Closure.GroupPreparedStabilityKernel
import Holant.Proofs.Closure.GeneratedGroupWorklistRetention

/-! A fresh structural stable exit at the SAME fully generated final palette.
Every FINAL minimum is an actual prepared occurrence at the FINAL group. Its
old saved proper-card trees therefore consist of final-retained binary leaves,
and genuine representative transport proves its regenerated CURRENT deck.
No earlier stable exit is transplanted to a changed family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GroupPreparedStability
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

structure PreparedDeck (Q : Palette G) (torsion : ResidualTorsion Q.family)
    (core : MinimumCore Q.family) where
  m : ℕ
  signature : Signature (OI.K G) (m+2)
  proper : 2 ≤ m
  even : Even (m+2)
  literal : core.signature = ⟨m+2,signature⟩
  matching : ∀ g ∈ rawDeck Q.family torsion signature,
    MatchingOrZero (actualTransfers Q.family) g

def preparationTorsion {S T : GeneratedOccurrenceWorklist.State G base}
    (e : GeneratedOccurrenceWorklist.Transition G base S T) : ResidualTorsion S.palette.family := by
  cases e with
  | binary o pending ready recomputed arity => exact ready.torsion
  | higher o pending ready recomputed input => exact ready.torsion

/-- FINAL minimum and actual group provenance are enough even if the visit's
batch used only retained membership, rather than then-minimality. -/
def fromPreparation {S T : GeneratedOccurrenceWorklist.State G base}
    (e : GeneratedOccurrenceWorklist.Transition G base S T)
    (Q : Palette G) (torsion : ResidualTorsion Q.family) (core : MinimumCore Q.family)
    (selected : core.signature = (CurrentOccurrences.savedLeaf G S.palette (e.selected G base)).1)
    (saved : T.palette.family ⊆ Q.family)
    (sameGroup : completeGroup Q.family torsion =
      completeGroup S.palette.family (preparationTorsion G base e))
    (noUnary : ¬ RetainedUnary Q.family) : PreparedDeck G Q torsion core := by
  cases e with
  | binary o pending ready recomputed arity =>
      have hc := congrArg Sigma.fst selected
      have hn := core.nonbinary
      change core.signature.1 = (CurrentOccurrences.savedLeaf G S.palette o).1.1 at hc
      change (CurrentOccurrences.savedLeaf G S.palette o).1.1 = 2 at arity
      omega
  | higher o pending ready recomputed input =>
      have literal : core.signature = ⟨input.m+2,input.signature⟩ := selected.trans input.literal.symm
      refine ⟨input.m,input.signature,input.proper,input.evenArity,literal,?_⟩
      have retainedCurrent :
          (⟨input.m+2,input.signature⟩ : AnySignature (OI.K G)) ∈ S.palette.family := input.retained
      apply regenerated_batch_matching_in_final input.proper S.palette.family ready.torsion
        input.signature Q.family ?_ torsion sameGroup core ?_ noUnary
      · intro f hf
        apply saved
        change f ∈ (OccurrenceBatch.palette G S.palette ready.torsion input.signature
          retainedCurrent input.proper).family
        rw [OccurrenceBatch.family_exact]
        exact hf
      · rw [literal]

def fromReceipt {S T : GeneratedGroupWorklist.Active G base}
    {h : GeneratedGroupWorklist.Trace G base S T}
    {q : CurrentOccurrences.Id G T.source.palette}
    (r : GeneratedGroupWorklist.PreparationReceipt G base h q)
    (core : MinimumCore T.source.palette.family)
    (literal : core.signature = (CurrentOccurrences.savedLeaf G T.source.palette q).1) :
    PreparedDeck G T.source.palette T.ready.torsion core :=
  fromPreparation G base (r.event.preparation G base) T.source.palette T.ready.torsion core
    (literal.trans (congrArg Sigma.fst r.leafExact)) (r.batchRetained G base)
    r.currentGroup T.ready.noUnary

/-- This factory works for EVERY actual FINAL minimum, not merely the prime
selected by the earlier minimum-core stabilization history. -/
def forExhausted {S : GeneratedGroupWorklist.Active G base}
    (R : GeneratedGroupWorklist.Exhausted G base S) (noPrior : S.source.done = ∅)
    (core : MinimumCore R.final.source.palette.family) :
    PreparedDeck G R.final.source.palette R.final.ready.torsion core := by
  let h := current_prime_occurrence G R.final.source.palette core.signature core.retained core.prime
  let q := Classical.choose h
  have hq := Classical.choose_spec h
  exact fromReceipt G base (R.preparationReceipt G base noPrior q) core hq.symm

def PreparedDeck.exit (Q : Palette G) (torsion : ResidualTorsion Q.family)
    (core : MinimumCore Q.family) (deck : PreparedDeck G Q torsion core)
    (noUnary : ¬ RetainedUnary Q.family) (noOdd : StabilizationMathematical.NoOdd Q.family) :
    StructuralExit G Q :=
  .stable deck.m deck.signature deck.proper deck.even torsion core deck.literal noUnary noOdd deck.matching

/-- Exact copied-root receipts preserve the whole base family through every
real batch and every strict-growth status reset. -/
theorem source_retains (S : GeneratedOccurrenceWorklist.State G base) : base.family ⊆ S.palette.family := by
  rintro q ⟨i,rfl⟩
  exact ⟨S.rootLabel i,congrArg Sigma.fst (S.rootSaved i)⟩

/-- A closed actual generated-group result plus a genuine base nonbinary
prime yields a fresh structural exit at exactly its final source palette. -/
def resultExit (R : GeneratedGroupWorklist.Result G base)
    (nonbinary : ∃ f ∈ base.family, Prime f ∧ 3 ≤ f.1) :
    StructuralExit G (R.finalSource G base).palette := by
  cases R with
  | initialStop stop recomputed => exact stop.structural G
  | prepared ready recomputed completion =>
      cases completion with
      | inl stopped => exact stopped.stop.structural G
      | inr exhausted =>
          have hn : ∃ f ∈ exhausted.final.source.palette.family, Prime f ∧ 3 ≤ f.1 := by
            obtain ⟨f,hf,hp,h3⟩ := nonbinary
            exact ⟨f,source_retains G base exhausted.final.source hf,hp,h3⟩
          let core := Classical.choice (exists_minimumCore exhausted.final.source.palette.family hn)
          let deck := forExhausted G base exhausted rfl core
          exact PreparedDeck.exit G exhausted.final.source.palette exhausted.final.ready.torsion core deck
            exhausted.final.ready.noUnary exhausted.final.ready.noOdd

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GroupPreparedStability
end
