import Holant.Proofs.Closure.Interface
import Holant.Proofs.Closure.StabilizationMathematical
import Holant.Proofs.Closure.QueueBatch
import Holant.Proofs.Closure.InitialPalette
import Holant.Proofs.Closure.QueueTaggedAmbient
import Holant.Proofs.Closure.RetainedFinalAccess

/-! RECONSTRUCTED AFTER WORKSPACE REPLACEMENT; fresh kernel verification is required.
Based on the retained pre-fix source seed and explicit remembered final repairs.
Actual physical-palette realization of the all-arity saved history.
Each batch is the closed QueueBatch factory at the SAME current palette.
Its original-G machines, exact old/root trees and initial-to-final queue are
retained in the history. No successor palette or history is caller input.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistoryPalette
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
attribute [local instance] Classical.propDecidable
local instance : DecidableEq (HistoryCatalogue.Key (OI.K G)) := Classical.decEq _

theorem palette_saturated (P : Palette G) : FactorSaturated P.family := by
  intro f hf _
  obtain ⟨i, rfl⟩ := hf
  exact ⟨P.trees i, P.leavesRetained i⟩

def state (P : Palette G) (hτ : ResidualTorsion P.family) (core : MinimumCore P.family)
    (hfour : 4 ≤ core.signature.1) (heven : Even core.signature.1) :
    StabilizationMathematical.State (OI.K G) :=
  StabilizationMathematical.ofMinimum P.family (Set.finite_range _) P.equality
    (palette_saturated G P) hτ core hfour heven

@[simp] theorem state_family (P : Palette G) (hτ : ResidualTorsion P.family)
    (core : MinimumCore P.family) (hfour : 4 ≤ core.signature.1)
    (heven : Even core.signature.1) : (state G P hτ core hfour heven).family = P.family := rfl

@[simp] theorem minimum_transport_signature {L : Type*} [Field L]
    {F H : SignatureFamily L} (he : F = H) (core : MinimumCore F) :
    (he ▸ core).signature = core.signature := by
  cases he
  rfl

theorem rawDeck_family_transport {L : Type*} [Field L] {F H : SignatureFamily L}
    (he : F = H) (hτ : ResidualTorsion F) {m : ℕ} (f : Signature L (m+2)) :
    rawDeck F hτ f = rawDeck H (he ▸ hτ) f := by
  cases he
  rfl

theorem retainedDeck_family_transport {L : Type*} [Field L] [NumberField L]
    {F H : SignatureFamily L} (he : F = H) (hτ : ResidualTorsion F)
    {m : ℕ} (f : Signature L (m+2)) :
    fullRetainedDeck F hτ f = fullRetainedDeck H (he ▸ hτ) f := by
  cases he
  rfl

/-- A source exit can be installed only at a Palette whose actual family is
the exact saved terminal augmentation. No arbitrary successor is substituted. -/
def exit (C : StabilizationMathematical.State (OI.K G)) (P : Palette G)
    (hfamily : P.family = C.augmented) (T : StabilizationMathematical.Terminal C) :
    StructuralExit G P := by
  cases T with
  | unary u hr hn => exact .unary u (by simpa only [hfamily] using hr) hn
  | infinite B ha hi => exact .infinite B (by simpa only [hfamily] using ha) hi
  | odd f hr hp hn ho => exact .odd f (by simpa only [hfamily] using hr) hp hn ho
  | stable S =>
      let hτ : ResidualTorsion P.family := hfamily.symm ▸ S.torsion
      let core : MinimumCore P.family := hfamily.symm ▸ C.retainedCore S.sameArity
      refine .stable C.m C.signature C.proper C.evenArity hτ core ?_ ?_ ?_ ?_
      · change (hfamily.symm ▸ C.retainedCore S.sameArity).signature = _
        rw [minimum_transport_signature]
        exact C.coreLiteral
      · simpa only [hfamily] using S.noUnary
      · simpa only [hfamily, StabilizationMathematical.NoOdd] using S.noOdd
      · intro g hg
        have hdeck : rawDeck P.family hτ C.signature = rawDeck C.augmented S.torsion C.signature :=
          rawDeck_family_transport hfamily hτ C.signature
        rw [hdeck] at hg
        simpa only [hfamily] using S.regenerated g hg

namespace Saved
variable (C : StabilizationMathematical.State (OI.K G)) (P : Palette G)
variable (hfamily : P.family = C.family)

def torsion : ResidualTorsion P.family := hfamily.symm ▸ C.torsion
def core : MinimumCore P.family := hfamily.symm ▸ C.core

theorem coreLiteral : (core G C P hfamily).signature = ⟨C.m+2,C.signature⟩ := by
  rw [core, minimum_transport_signature]
  exact C.coreLiteral

/-- The full physical batch is produced at each reached palette; its
programme endpoints and tree choices cannot be independently substituted. -/
def batch : DeckBatchResult G P (torsion G C P hfamily) C.signature :=
  QueueBatch.result G P (torsion G C P hfamily) C.signature
    (core G C P hfamily) (coreLiteral G C P hfamily) C.proper

theorem batch_family : (batch G C P hfamily).palette.family = C.augmented := by
  rw [batch, QueueBatch.result_palette, ProgrammeRetained.palette_family]
  exact retainedDeck_family_transport hfamily (torsion G C P hfamily) C.signature

def batchLabel (i : Fin P.count) : Fin (batch G C P hfamily).palette.count :=
  RetainedCatalogue.oldLabel G P (torsion G C P hfamily) C.signature i

@[simp] theorem batchLabel_val (i : Fin P.count) :
    (batchLabel G C P hfamily i).val = i.val := rfl

theorem batchSavedAt (i : Fin P.count) :
    (⟨⟨(batch G C P hfamily).palette.arity (batchLabel G C P hfamily i).val,
      (batch G C P hfamily).palette.table (batchLabel G C P hfamily i)⟩,
      (batch G C P hfamily).palette.trees (batchLabel G C P hfamily i)⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩ :=
  RetainedCatalogue.old_saved G P (torsion G C P hfamily) C.signature i

def successorFamily (O : StabilizationMathematical.Outer C) :
    (batch G C P hfamily).palette.family = O.target.family :=
  (batch_family G C P hfamily).trans O.target_family.symm

theorem exhaust_transport {L : Type*} [Field L] [NumberField L]
    {F H : SignatureFamily L} (he : F = H) (hτ : ResidualTorsion F)
    {m : ℕ} (f : Signature L (m+2)) :
    HEq (HistoryCatalogue.exhaust F hτ f) (HistoryCatalogue.exhaust H (he ▸ hτ) f) := by
  cases he
  rfl

/-- Both queues are the same factory with exactly transported family/torsion
arguments. This is not an equality of separately chosen native/ambient runs. -/
theorem queueIdentity :
    HEq (HistoryCatalogue.exhaust P.family (torsion G C P hfamily) C.signature)
      (HistoryCatalogue.exhaust C.family C.torsion C.signature) :=
  exhaust_transport hfamily (torsion G C P hfamily) C.signature

structure TraceReceipt : Type 1 where
  queue : HistoryCatalogue.Exhausted P.family (torsion G C P hfamily) C.signature
  queueIdentity : queue = HistoryCatalogue.exhaust P.family (torsion G C P hfamily) C.signature
  mathematicalIdentity : HEq queue (HistoryCatalogue.exhaust C.family C.torsion C.signature)
  joint : AmbientQueue.JointTrace G P (torsion G C P hfamily) C.signature
    (core G C P hfamily) (coreLiteral G C P hfamily) C.proper true queue.trace
  taggedJoint : AmbientQueue.TaggedJointTrace G P (torsion G C P hfamily) C.signature
    (core G C P hfamily) (coreLiteral G C P hfamily) C.proper true queue.tagged.trace

def traceReceipt : TraceReceipt G C P hfamily :=
  ⟨HistoryCatalogue.exhaust P.family (torsion G C P hfamily) C.signature, rfl,
    queueIdentity G C P hfamily,
    AmbientQueue.savedJoint G P (torsion G C P hfamily) C.signature
      (core G C P hfamily) (coreLiteral G C P hfamily) C.proper,
    AmbientQueue.savedTaggedJoint G P (torsion G C P hfamily) C.signature
      (core G C P hfamily) (coreLiteral G C P hfamily) C.proper⟩

/-- The constructors save exact before-palette, branch, full physical batch,
and successor identity through their dependent indices. Intermediate palettes
are the literal factories above, rather than existential replacement tables. -/
inductive Execution : (C : StabilizationMathematical.State (OI.K G)) →
    (P : Palette G) → P.family = C.family → Type 1
  | stop {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
      {hfamily : P.family = C.family} (terminal : StabilizationMathematical.Terminal C) :
      Execution C P hfamily
  | next {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
      {hfamily : P.family = C.family} (outer : StabilizationMathematical.Outer C)
      (rest : Execution outer.target (batch G C P hfamily).palette
        (successorFamily G C P hfamily outer)) : Execution C P hfamily

/-- Every reached before/after palette has joint physical receipts for its
exact constructor-indexed ambient trace, including terminal stable states. -/
def Execution.Receipts {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
    {hfamily : P.family = C.family} : Execution G C P hfamily → Type 1
  | .stop _ => TraceReceipt G C P hfamily
  | .next _ rest => TraceReceipt G C P hfamily × rest.Receipts

def Execution.receipts {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
    {hfamily : P.family = C.family} (E : Execution G C P hfamily) : E.Receipts :=
  match E with
  | .stop _ => traceReceipt G C P hfamily
  | .next _ rest => (traceReceipt G C P hfamily, rest.receipts)

def finish (C : StabilizationMathematical.State (OI.K G)) (P : Palette G)
    (hfamily : P.family = C.family) : Execution G C P hfamily := by
  let M : StabilizationMathematical.State (OI.K G) → Type 1 := fun D =>
    ∀ (Q : Palette G) (hQ : Q.family = D.family), Execution G D Q hQ
  let step : ∀ D, (∀ E, StabilizationMathematical.Earlier E D → M E) → M D :=
    fun D recurse Q hQ => match StabilizationMathematical.dispatch D with
      | .inl terminal => .stop terminal
      | .inr outer => .next outer
          (recurse outer.target outer.source_decreases (batch G D Q hQ).palette
            (successorFamily G D Q hQ outer))
  exact ((StabilizationMathematical.earlier_wellFounded (L:=OI.K G)).fix step C) P hfamily

theorem finish_unfold (C : StabilizationMathematical.State (OI.K G)) (P : Palette G)
    (hfamily : P.family = C.family) :
    finish G C P hfamily = match StabilizationMathematical.dispatch C with
      | .inl terminal => .stop terminal
      | .inr outer => .next outer (finish G outer.target (batch G C P hfamily).palette
          (successorFamily G C P hfamily outer)) := by
  unfold finish
  dsimp only
  rw [WellFounded.fix_eq]

def Execution.history {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
    {hfamily : P.family = C.family} : Execution G C P hfamily → StabilizationMathematical.Execution C
  | .stop terminal => .stop terminal
  | .next outer rest => .next outer rest.history

def Execution.palette {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
    {hfamily : P.family = C.family} : Execution G C P hfamily → Palette G
  | .stop _ => (batch G C P hfamily).palette
  | .next _ rest => rest.palette

/-- Distinct initial label indices remain distinct physical labels, even
when their signature values and entire saved trees are equal. -/
def Execution.initialLabel {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
    {hfamily : P.family = C.family} (E : Execution G C P hfamily) :
    Fin P.count → Fin E.palette.count :=
  match E with
  | .stop _ => batchLabel G C P hfamily
  | .next _ rest => fun i => initialLabel rest (batchLabel G C P hfamily i)

@[simp] theorem Execution.initialLabel_val {C : StabilizationMathematical.State (OI.K G)}
    {P : Palette G} {hfamily : P.family = C.family} (E : Execution G C P hfamily)
    (i : Fin P.count) : (Execution.initialLabel G E i).val = i.val := by
  induction E with
  | stop terminal => rfl
  | @next C P hfamily outer rest ih => exact ih (batchLabel G C P hfamily i)

theorem Execution.initialLabel_injective {C : StabilizationMathematical.State (OI.K G)}
    {P : Palette G} {hfamily : P.family = C.family} (E : Execution G C P hfamily) :
    Function.Injective (Execution.initialLabel G E) := by
  intro i j he
  apply Fin.ext
  simpa only [Execution.initialLabel_val G E] using congrArg Fin.val he

theorem Execution.initialSavedAt {C : StabilizationMathematical.State (OI.K G)}
    {P : Palette G} {hfamily : P.family = C.family} (E : Execution G C P hfamily)
    (i : Fin P.count) :
    (⟨⟨E.palette.arity (Execution.initialLabel G E i).val,E.palette.table (Execution.initialLabel G E i)⟩,
      E.palette.trees (Execution.initialLabel G E i)⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩ := by
  induction E with
  | @stop C P hfamily terminal => exact batchSavedAt G C P hfamily i
  | @next C P hfamily outer rest ih =>
      change (⟨⟨rest.palette.arity (Execution.initialLabel G rest (batchLabel G C P hfamily i)).val,
        rest.palette.table (Execution.initialLabel G rest (batchLabel G C P hfamily i))⟩,
        rest.palette.trees (Execution.initialLabel G rest (batchLabel G C P hfamily i))⟩ : TreeOccurrence (OI.K G)) = _
      exact (ih (batchLabel G C P hfamily i)).trans (batchSavedAt G C P hfamily i)


theorem Execution.finalFamily {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
    {hfamily : P.family = C.family} (E : Execution G C P hfamily) :
    E.palette.family = E.history.final.augmented := by
  induction E with
  | @stop C P hfamily terminal => exact batch_family G C P hfamily
  | next outer rest ih => exact ih

def Execution.Produced {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
    {hfamily : P.family = C.family} : Execution G C P hfamily → Prop
  | .stop terminal => StabilizationMathematical.dispatch C = .inl terminal
  | .next outer rest => StabilizationMathematical.dispatch C = .inr outer ∧ rest.Produced

theorem finish_produced (C : StabilizationMathematical.State (OI.K G)) (P : Palette G)
    (hfamily : P.family = C.family) : (finish G C P hfamily).Produced := by
  refine (StabilizationMathematical.earlier_wellFounded (L:=OI.K G)).induction C
    (C := fun C => ∀ (P : Palette G) (hfamily : P.family = C.family),
      (finish G C P hfamily).Produced) ?_ P hfamily
  intro C ih P hfamily
  rw [finish_unfold]
  cases hd : StabilizationMathematical.dispatch C with
  | inl terminal => exact hd
  | inr outer => exact ⟨hd, ih outer.target outer.source_decreases _ _⟩

theorem Execution.history_produced {C : StabilizationMathematical.State (OI.K G)} {P : Palette G}
    {hfamily : P.family = C.family} (E : Execution G C P hfamily) (h : E.Produced) :
    E.history.Produced := by
  induction E with
  | stop terminal => exact h
  | next outer rest ih => exact ⟨h.1, ih h.2⟩

theorem finish_history (C : StabilizationMathematical.State (OI.K G)) (P : Palette G)
    (hfamily : P.family = C.family) :
    (finish G C P hfamily).history = StabilizationMathematical.finish C := by
  refine (StabilizationMathematical.earlier_wellFounded (L:=OI.K G)).induction C
    (C := fun C => ∀ (P : Palette G) (hfamily : P.family = C.family),
      (finish G C P hfamily).history = StabilizationMathematical.finish C) ?_ P hfamily
  intro C ih P hfamily
  rw [finish_unfold, StabilizationMathematical.finish_unfold]
  cases StabilizationMathematical.dispatch C with
  | inl terminal => rfl
  | inr outer =>
      change StabilizationMathematical.Execution.next outer _ =
        StabilizationMathematical.Execution.next outer _
      exact congrArg (StabilizationMathematical.Execution.next outer)
        (ih outer.target outer.source_decreases _ _)

end Saved

structure Result (C : StabilizationMathematical.State (OI.K G)) : Type 1 where
  initial : Palette G
  initialFamily : initial.family = C.family
  execution : Saved.Execution G C initial initialFamily

def Result.history {C : StabilizationMathematical.State (OI.K G)} (R : Result G C) :
    StabilizationMathematical.Execution C := R.execution.history

def Result.palette {C : StabilizationMathematical.State (OI.K G)} (R : Result G C) : Palette G :=
  R.execution.palette

theorem Result.finalFamily {C : StabilizationMathematical.State (OI.K G)} (R : Result G C) :
    R.palette.family = R.history.final.augmented := R.execution.finalFamily

def Result.receipts {C : StabilizationMathematical.State (OI.K G)} (R : Result G C) :
    R.execution.Receipts := R.execution.receipts

def Result.initialLabel {C : StabilizationMathematical.State (OI.K G)} (R : Result G C) :
    Fin R.initial.count → Fin R.palette.count := Saved.Execution.initialLabel G R.execution

theorem Result.initialLabel_injective {C : StabilizationMathematical.State (OI.K G)}
    (R : Result G C) : Function.Injective (Result.initialLabel G R) := Saved.Execution.initialLabel_injective G R.execution

@[simp] theorem Result.initialLabel_val {C : StabilizationMathematical.State (OI.K G)}
    (R : Result G C) (i : Fin R.initial.count) : (Result.initialLabel G R i).val = i.val :=
  Saved.Execution.initialLabel_val G R.execution i

theorem Result.initialSavedAt {C : StabilizationMathematical.State (OI.K G)}
    (R : Result G C) (i : Fin R.initial.count) :
    (⟨⟨R.palette.arity (Result.initialLabel G R i).val,R.palette.table (Result.initialLabel G R i)⟩,
      R.palette.trees (Result.initialLabel G R i)⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨R.initial.arity i.val,R.initial.table i⟩,R.initial.trees i⟩ := Saved.Execution.initialSavedAt G R.execution i

def Result.sourceResult {C : StabilizationMathematical.State (OI.K G)} (R : Result G C) :
    StabilizationResult G :=
  ⟨R.palette, exit G R.history.final R.palette R.finalFamily R.history.terminal⟩

/-- Separately charged actual access for the genuine FINAL regenerated deck.
Freshly chosen current trees are accessed with their own saved identities;
they are not asserted to be literal pre-existing final alphabet labels. -/
def Result.regeneratedAccess {C : StabilizationMathematical.State (OI.K G)} (R : Result G C) :
    RetainedFinalAccess.Access G R.palette R.sourceResult.exit :=
  RetainedFinalAccess.forStructuralExit G R.palette R.sourceResult.exit

/-- Closed physical-history producer at an already source-established palette.
All subsequent palettes and programmes are internally built. -/
def produce (C : StabilizationMathematical.State (OI.K G)) (P : Palette G)
    (hfamily : P.family = C.family) : Result G C :=
  ⟨P, hfamily, Saved.finish G C P hfamily⟩

def originalState (hτ : ResidualTorsion (OI.family G)) (core : MinimumCore (OI.family G))
    (hfour : 4 ≤ core.signature.1) (heven : Even core.signature.1) :
    StabilizationMathematical.State (OI.K G) :=
  StabilizationMathematical.ofMinimum (OI.family G)
    ((Initial.family_exact G) ▸ Set.finite_range
      (fun i : Fin (Initial.palette G).count =>
        (⟨(Initial.palette G).arity i.val,(Initial.palette G).table i⟩ : AnySignature (OI.K G))))
    ((Initial.family_exact G) ▸ (Initial.palette G).equality)
    ((Initial.family_exact G) ▸ palette_saturated G (Initial.palette G)) hτ core hfour heven

@[simp] theorem originalState_family (hτ : ResidualTorsion (OI.family G))
    (core : MinimumCore (OI.family G)) (hfour : 4 ≤ core.signature.1)
    (heven : Even core.signature.1) : (originalState G hτ core hfour heven).family = OI.family G := rfl

/-- Public original-G entry: exact original field, family, initial trees and
both physical programmes are chosen before any continuation is interpreted. -/
def original (hτ : ResidualTorsion (OI.family G)) (core : MinimumCore (OI.family G))
    (hfour : 4 ≤ core.signature.1) (heven : Even core.signature.1) :
    Result G (originalState G hτ core hfour heven) :=
  produce G (originalState G hτ core hfour heven) (Initial.palette G) (Initial.family_exact G)

def originalLabel (hτ : ResidualTorsion (OI.family G)) (core : MinimumCore (OI.family G))
    (hfour : 4 ≤ core.signature.1) (heven : Even core.signature.1) :
    Fin (OI.count G) → Fin (original G hτ core hfour heven).palette.count :=
  Result.initialLabel G (original G hτ core hfour heven)

@[simp] theorem originalLabel_val (hτ : ResidualTorsion (OI.family G))
    (core : MinimumCore (OI.family G)) (hfour : 4 ≤ core.signature.1)
    (heven : Even core.signature.1) (i : Fin (OI.count G)) :
    (originalLabel G hτ core hfour heven i).val = i.val :=
  Result.initialLabel_val G (original G hτ core hfour heven) i

theorem originalLabel_injective (hτ : ResidualTorsion (OI.family G))
    (core : MinimumCore (OI.family G)) (hfour : 4 ≤ core.signature.1)
    (heven : Even core.signature.1) : Function.Injective (originalLabel G hτ core hfour heven) :=
  Result.initialLabel_injective G (original G hτ core hfour heven)

theorem originalSavedAt (hτ : ResidualTorsion (OI.family G)) (core : MinimumCore (OI.family G))
    (hfour : 4 ≤ core.signature.1) (heven : Even core.signature.1) (i : Fin (OI.count G)) :
    let R := original G hτ core hfour heven
    (⟨⟨R.palette.arity (originalLabel G hτ core hfour heven i).val,
      R.palette.table (originalLabel G hτ core hfour heven i)⟩,
      R.palette.trees (originalLabel G hτ core hfour heven i)⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨OI.arity G i.val,OI.publicTable G i⟩,OI.storedTrees G i⟩ :=
  Result.initialSavedAt G (original G hτ core hfour heven) i

@[simp] theorem original_initial (hτ : ResidualTorsion (OI.family G))
    (core : MinimumCore (OI.family G)) (hfour : 4 ≤ core.signature.1)
    (heven : Even core.signature.1) :
    (original G hτ core hfour heven).initial = Initial.palette G := rfl

theorem original_produced (hτ : ResidualTorsion (OI.family G)) (core : MinimumCore (OI.family G))
    (hfour : 4 ≤ core.signature.1) (heven : Even core.signature.1) :
    (original G hτ core hfour heven).execution.Produced :=
  Saved.finish_produced G _ _ _

theorem original_history (hτ : ResidualTorsion (OI.family G))
    (core : MinimumCore (OI.family G)) (hfour : 4 ≤ core.signature.1)
    (heven : Even core.signature.1) :
    (original G hτ core hfour heven).history =
      StabilizationMathematical.finish (originalState G hτ core hfour heven) :=
  Saved.finish_history G _ _ _

theorem original_stabilization : OriginalStabilizationGoal := by
  intro s a G hτ core hfour heven
  exact ⟨(original G hτ core hfour heven).sourceResult⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistoryPalette
end
