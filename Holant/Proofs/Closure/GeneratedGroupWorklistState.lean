import Holant.Proofs.Closure.GeneratedOccurrenceWorklistLedger
import Holant.Proofs.FiniteGroups.Stabilization.ExactGroupBound

/-! Actual current-group occurrence preparation. Unchanged-group events use
strict multiset arity replacement. A genuinely larger complete group resets
preparation to the exact CURRENT saved-address universe and strictly decreases
the original-field group deficit. No minimum-core switching descent is claimed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
abbrev Source := GeneratedOccurrenceWorklist.State G base

structure Active : Type 1 where
  source : Source G base
  ready : OccurrenceWorklist.Ready G source.palette
  recomputed : OccurrenceWorklist.inspect G source.palette = .inr ready

def restart (S : Source G base) : Source G base :=
  { S with todo := Finset.univ, done := ∅, disjoint := by simp, partition := by simp }

abbrev Rank := ℕ × Multiset ℕ
abbrev RankLT : Rank → Rank → Prop := Prod.Lex (· < ·) Multiset.IsDershowitzMannaLT

def Active.rank (S : Active G base) : Rank :=
  (sourceGroupDefect S.source.palette.family S.ready.torsion,S.source.rank G base)

def Earlier (T S : Active G base) : Prop := RankLT (T.rank G base) (S.rank G base)

theorem rank_wellFounded : WellFounded RankLT :=
  Nat.lt_wfRel.wf.prod_lex Multiset.wellFounded_isDershowitzMannaLT

theorem earlier_wellFounded : WellFounded (Earlier G base) :=
  InvImage.wf (fun S : Active G base => S.rank G base) rank_wellFounded

theorem retains {S T : Source G base} (e : GeneratedOccurrenceWorklist.Transition G base S T) :
    S.palette.family ⊆ T.palette.family := by
  cases e with
  | binary => exact fun _ h => h
  | higher o hp ready hr b =>
    have retained : (⟨b.m+2,b.signature⟩ : AnySignature (OI.K G)) ∈ S.palette.family := by
      simpa only [OccurrenceWorklist.initial] using b.retained
    change S.palette.family ⊆ (OccurrenceBatch.palette G S.palette ready.torsion b.signature retained b.proper).family
    rw [OccurrenceBatch.family_exact]
    exact fullRetainedDeck_retains _ _ _

/-- Each step stores the real preparation event/work. Strict growth alone
allows reopening current preparation IDs; same-group steps preserve done. -/
inductive Transition : Active G base → Active G base → Type 1
  | same (S : Active G base) (raw : Source G base)
      (event : GeneratedOccurrenceWorklist.Transition G base S.source raw)
      (work : GeneratedOccurrenceWorklist.EventWork G base event)
      (ready : OccurrenceWorklist.Ready G raw.palette)
      (recomputed : OccurrenceWorklist.inspect G raw.palette = .inr ready)
      (sameGroup : completeGroup raw.palette.family ready.torsion = completeGroup S.source.palette.family S.ready.torsion) :
      Transition S ⟨raw,ready,recomputed⟩
  | growth (S : Active G base) (raw : Source G base)
      (event : GeneratedOccurrenceWorklist.Transition G base S.source raw)
      (work : GeneratedOccurrenceWorklist.EventWork G base event)
      (ready : OccurrenceWorklist.Ready G raw.palette)
      (recomputed : OccurrenceWorklist.inspect G raw.palette = .inr ready)
      (strict : completeGroup S.source.palette.family S.ready.torsion < completeGroup raw.palette.family ready.torsion) :
      Transition S ⟨restart G base raw,ready,recomputed⟩

theorem Transition.decreases {S T : Active G base} (e : Transition G base S T) : Earlier G base T S := by
  cases e with
  | same raw event work ready recomputed sameGroup =>
    have hd : sourceGroupDefect raw.palette.family ready.torsion =
        sourceGroupDefect S.source.palette.family S.ready.torsion := by
      unfold sourceGroupDefect
      rw [sameGroup]
    change RankLT (sourceGroupDefect raw.palette.family ready.torsion,raw.rank G base) _
    rw [hd]
    exact Prod.Lex.right _ (event.decreases G base)
  | growth raw event work ready recomputed strict =>
    exact Prod.Lex.left _ _ (sourceGroupDefect_lt_of_strict S.ready.torsion ready.torsion strict)

/-- Explicit restart receipt: same physically returned palette/root trees,
all CURRENT addresses pending, no done resource, and actual strict group growth. -/
structure RestartReceipt (S : Active G base) (raw : Source G base)
    (ready : OccurrenceWorklist.Ready G raw.palette) : Type 1 where
  strict : completeGroup S.source.palette.family S.ready.torsion < completeGroup raw.palette.family ready.torsion
  paletteIdentity : (restart G base raw).palette = raw.palette
  todoIdentity : (restart G base raw).todo = Finset.univ
  doneIdentity : (restart G base raw).done = ∅
  rootsIdentity : (restart G base raw).rootLabel = raw.rootLabel
  deficitDecrease : sourceGroupDefect raw.palette.family ready.torsion <
    sourceGroupDefect S.source.palette.family S.ready.torsion

def restartReceipt (S : Active G base) (raw : Source G base) (ready : OccurrenceWorklist.Ready G raw.palette)
    (strict : completeGroup S.source.palette.family S.ready.torsion < completeGroup raw.palette.family ready.torsion) :
    RestartReceipt G base S raw ready :=
  ⟨strict,rfl,rfl,rfl,rfl,sourceGroupDefect_lt_of_strict S.ready.torsion ready.torsion strict⟩

inductive Dispatch (S : Active G base) : Type 1
  | exhausted (empty : S.source.todo = ∅)
  | structural (raw : Source G base) (event : GeneratedOccurrenceWorklist.Transition G base S.source raw)
      (work : GeneratedOccurrenceWorklist.EventWork G base event) (stop : OccurrenceWorklist.Stop G raw.palette)
      (recomputed : OccurrenceWorklist.inspect G raw.palette = .inl stop)
  | next (T : Active G base) (event : Transition G base S T)

def dispatch (S : Active G base) : Dispatch G base S := by
  by_cases hn : S.source.todo.Nonempty
  · let e := GeneratedOccurrenceWorklist.next G base S.source S.ready S.recomputed hn
    let w := GeneratedOccurrenceWorklist.eventWork G base e.2
    cases hi : OccurrenceWorklist.inspect G e.1.palette with
    | inl stop => exact .structural e.1 e.2 w stop hi
    | inr ready =>
      by_cases he : completeGroup e.1.palette.family ready.torsion = completeGroup S.source.palette.family S.ready.torsion
      · exact .next ⟨e.1,ready,hi⟩ (.same S e.1 e.2 w ready hi he)
      · have strict := lt_of_le_of_ne (completeGroup_mono (retains G base e.2) S.ready.torsion ready.torsion)
          (fun h => he h.symm)
        exact .next ⟨restart G base e.1,ready,hi⟩ (.growth S e.1 e.2 w ready hi strict)
  · exact .exhausted (Finset.not_nonempty_iff_eq_empty.mp hn)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupWorklist
