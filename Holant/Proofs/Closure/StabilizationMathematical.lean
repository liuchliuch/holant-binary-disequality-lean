import Holant.Proofs.Closure.ContinuationTransport
import Holant.Proofs.Closure.HistoryCatalogue
import Holant.Proofs.Closure.ContinuationCatalogue
import Holant.Proofs.FiniteGroups.Stabilization.ResolvingExecution.RetainedBranches

/-! RECONSTRUCTED AFTER WORKSPACE REPLACEMENT; fresh kernel verification is
required. Every all-arity successor recomputes the actual retained family,
complete group and minimum. Genuine outer Step precedes original-field rank
descent. The unchanged branch keeps the old literal core and frozen queue,
while the CURRENT regenerated deck is transported with explicit source scalars.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.StabilizationMathematical
open Holant Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {L : Type*} [Field L] [NumberField L]
attribute [local instance] Classical.propDecidable
local instance : DecidableEq (HistoryCatalogue.Key L) := Classical.decEq _

structure State (L : Type*) [Field L] [NumberField L] where
  family : SignatureFamily L
  finite : family.Finite
  equality : (⟨2,binarySignature Signature.equality⟩ : AnySignature L) ∈ family
  saturated : FactorSaturated family
  torsion : ResidualTorsion family
  core : MinimumCore family
  m : ℕ
  signature : Signature L (m+2)
  coreLiteral : core.signature = ⟨m+2,signature⟩
  proper : 2 ≤ m
  evenArity : Even (m+2)

namespace State
variable (C : State L)

def node : Node L (HistoryCatalogue.Key L) where
  family := C.family
  finite := C.finite
  equality := C.equality
  torsion := C.torsion
  core := C.core
  frozen := HistoryCatalogue.keyUniverse C.family C.torsion C.signature
  queue := FrozenQueue.initial (HistoryCatalogue.keyUniverse C.family C.torsion C.signature)
    (HistoryCatalogue.root C.family C.torsion C.signature)

def augmented : SignatureFamily L := fullRetainedDeck C.family C.torsion C.signature

theorem retains : C.family ⊆ C.augmented := fullRetainedDeck_retains C.family C.torsion C.signature

def minimum : MinimumCore C.augmented :=
  Classical.choice (exists_minimumCore C.augmented
    ⟨C.core.signature,C.retains C.core.retained,C.core.prime,C.core.nonbinary⟩)

theorem minimum_nonincrease : C.minimum.signature.1 ≤ C.core.signature.1 :=
  MinimumCore.arity_nonincrease C.retains C.core C.minimum

end State

theorem signature_cast_eq (f : AnySignature L) {n : ℕ} (hn : f.1 = n) :
    f = (⟨n,hn ▸ f.2⟩ : AnySignature L) := by
  cases f
  cases hn
  rfl

def ofMinimum (F : SignatureFamily L) (hf : F.Finite)
    (hI : (⟨2,binarySignature Signature.equality⟩ : AnySignature L) ∈ F)
    (hs : FactorSaturated F) (hτ : ResidualTorsion F) (core : MinimumCore F)
    (hfour : 4 ≤ core.signature.1) (heven : Even core.signature.1) : State L := by
  let m := core.signature.1 - 2
  have hn : core.signature.1 = m+2 := by dsimp [m]; omega
  let f : Signature L (m+2) := hn ▸ core.signature.2
  exact ⟨F,hf,hI,hs,hτ,core,m,f,signature_cast_eq core.signature hn,
    by dsimp [m]; omega,by simpa only [← hn] using heven⟩

def NoOdd (F : SignatureFamily L) : Prop := ∀ g ∈ F, Prime g → 3 ≤ g.1 → Even g.1

theorem noOdd_of_absent {F : SignatureFamily L}
    (ho : ¬ ∃ g ∈ F, Prime g ∧ 3 ≤ g.1 ∧ Odd g.1) : NoOdd F := by
  intro g hg hp hn
  rcases Nat.even_or_odd g.1 with he | he
  · exact he
  · exact False.elim (ho ⟨g,hg,hp,hn,he⟩)

namespace State
variable (C : State L)

def restart (hτ : ResidualTorsion C.augmented) (ho : NoOdd C.augmented) : State L := by
  have he : Even C.minimum.signature.1 :=
    ho C.minimum.signature C.minimum.retained C.minimum.prime C.minimum.nonbinary
  have hf : 4 ≤ C.minimum.signature.1 := by
    have hn := C.minimum.nonbinary
    obtain ⟨k,hk⟩ := he
    omega
  exact ofMinimum C.augmented (fullRetainedDeck_finite C.family C.finite C.torsion C.signature)
    (C.retains C.equality) (fullRetainedDeck_saturated C.family C.saturated C.torsion C.signature)
    hτ C.minimum hf he

/-- Same arity does not license choosing a different active core. The old
retained prime itself is a current minimum, with its literal signature intact. -/
def retainedCore (ha : C.minimum.signature.1 = C.core.signature.1) : MinimumCore C.augmented where
  signature := C.core.signature
  retained := C.retains C.core.retained
  prime := C.core.prime
  nonbinary := C.core.nonbinary
  minimum g hg hp hn := by
    have h := C.minimum.minimum g hg hp hn
    rwa [ha] at h

end State

structure Stable (C : State L) where
  torsion : ResidualTorsion C.augmented
  sameGroup : completeGroup C.augmented torsion = completeGroup C.family C.torsion
  sameArity : C.minimum.signature.1 = C.core.signature.1
  noUnary : ¬ RetainedUnary C.augmented
  noOdd : NoOdd C.augmented
  regenerated : ∀ g ∈ rawDeck C.augmented torsion C.signature,
    MatchingOrZero (actualTransfers C.augmented) g
  queue : HistoryCatalogue.Exhausted C.family C.torsion C.signature
  queueIdentity : queue = HistoryCatalogue.exhaust C.family C.torsion C.signature
  regeneratedKeySet : HistoryCatalogue.keyUniverse C.augmented torsion C.signature = C.node.frozen

inductive Terminal (C : State L) : Type _
  | unary (u : Signature L 1) (retained : (⟨1,u⟩ : AnySignature L) ∈ C.augmented) (nonzero : u ≠ 0)
  | infinite (B : Binary (K:=L)) (actual : ActualNonsingular C.augmented B)
      (infiniteOrder : ¬ ProjectivelyFinite (transfer B))
  | odd (f : AnySignature L) (retained : f ∈ C.augmented) (prime : Prime f)
      (nonbinary : 3 ≤ f.1) (oddArity : Odd f.1)
  | stable (stable : Stable C)

inductive Outer (C : State L) : Type _
  | group (torsion : ResidualTorsion C.augmented) (noOdd : NoOdd C.augmented)
      (strict : completeGroup C.family C.torsion < completeGroup C.augmented torsion)
  | arity (torsion : ResidualTorsion C.augmented) (noOdd : NoOdd C.augmented)
      (sameGroup : completeGroup C.augmented torsion = completeGroup C.family C.torsion)
      (smaller : C.minimum.signature.1 < C.core.signature.1)

namespace Outer
variable {C : State L}

def target : Outer C → State L
  | .group hτ ho _ => C.restart hτ ho
  | .arity hτ ho _ _ => C.restart hτ ho

@[simp] theorem target_family (O : Outer C) : O.target.family = C.augmented := by
  cases O <;> rfl

theorem catalogue_reset (O : Outer C) : O.target.node.frozen =
    HistoryCatalogue.keyUniverse O.target.family O.target.torsion O.target.signature := rfl

/-- Construct the actual continuing relation before using its descent. -/
theorem step (O : Outer C) : Node.Step O.target.node C.node := by
  cases O with
  | group hτ ho hs => exact .group C.node _ C.retains hs
  | arity hτ ho he ha => exact .arity C.node _ C.retains he ha

theorem source_decreases (O : Outer C) : Node.RankLT O.target.node.sourceOmega C.node.sourceOmega :=
  Node.source_step_decreases O.step

end Outer

/-- Actual all-arity dispatcher. Its witnesses and every next State are
internally selected from the real retained family; no successful branch or
future executor is input. -/
def dispatch (C : State L) : Terminal C ⊕ Outer C := by
  classical
  by_cases hu : RetainedUnary C.augmented
  · exact .inl (.unary (Classical.choose hu) (Classical.choose_spec hu).1 (Classical.choose_spec hu).2)
  by_cases hτ : ResidualTorsion C.augmented
  · by_cases ho : ∃ f ∈ C.augmented, Prime f ∧ 3 ≤ f.1 ∧ Odd f.1
    · exact .inl (.odd (Classical.choose ho) (Classical.choose_spec ho).1
        (Classical.choose_spec ho).2.1 (Classical.choose_spec ho).2.2.1 (Classical.choose_spec ho).2.2.2)
    · have noOdd := noOdd_of_absent ho
      by_cases hg : completeGroup C.augmented hτ = completeGroup C.family C.torsion
      · by_cases ha : C.minimum.signature.1 < C.core.signature.1
        · exact .inr (.arity hτ noOdd hg ha)
        have ha : C.minimum.signature.1 = C.core.signature.1 :=
          le_antisymm C.minimum_nonincrease (Nat.le_of_not_gt ha)
        have hmin : C.m+2 ≤ C.minimum.signature.1 := by
          have hn := congrArg Sigma.fst C.coreLiteral
          change C.core.signature.1 = C.m+2 at hn
          omega
        exact .inl (.stable ⟨hτ,hg,ha,hu,noOdd,
          ContinuationTransport.fullRetainedDeck_regenerated_matching C.proper C.family C.torsion
            C.signature C.minimum hmin hτ hg hu,
          HistoryCatalogue.exhaust C.family C.torsion C.signature,rfl,
          ContinuationCatalogue.keyUniverse_unchanged C.retains C.torsion hτ hg C.signature⟩)
      · exact .inr (.group hτ noOdd
          (lt_of_le_of_ne (completeGroup_mono C.retains C.torsion hτ) (fun he => hg he.symm)))
  · let h := (residual_or_actual_infinite C.augmented).resolve_left hτ
    exact .inl (.infinite (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2)

def Earlier (C D : State L) : Prop := Node.RankLT C.node.sourceOmega D.node.sourceOmega

theorem earlier_wellFounded : WellFounded (Earlier (L:=L)) :=
  InvImage.wf (fun C : State L => C.node.sourceOmega) Node.rank_wellFounded

inductive Execution : State L → Type _
  | stop {C : State L} (terminal : Terminal C) : Execution C
  | next {C : State L} (outer : Outer C) (rest : Execution outer.target) : Execution C

def finish (C : State L) : Execution C :=
  earlier_wellFounded.fix (C := fun C => Execution C) (fun C recurse =>
    match dispatch C with
    | .inl terminal => .stop terminal
    | .inr outer => .next outer (recurse outer.target outer.source_decreases)) C

theorem finish_unfold (C : State L) : finish C = match dispatch C with
    | .inl terminal => .stop terminal
    | .inr outer => .next outer (finish outer.target) := by
  unfold finish
  rw [WellFounded.fix_eq]

namespace Execution
variable {C : State L}

def final : {C : State L} → Execution C → State L
  | C, .stop _ => C
  | _, .next _ rest => final rest

def terminal : {C : State L} → (E : Execution C) → Terminal E.final
  | _, .stop terminal => terminal
  | _, .next _ rest => terminal rest

def depth : {C : State L} → Execution C → ℕ
  | _, .stop _ => 0
  | _, .next _ rest => depth rest+1

theorem retains (E : Execution C) : C.family ⊆ E.final.augmented := by
  induction E with
  | @stop C terminal => exact C.retains
  | @next C outer rest ih =>
      have ht : C.augmented ⊆ rest.final.augmented := by
        simpa only [outer.target_family] using ih
      exact C.retains.trans ht

def Produced : {C : State L} → Execution C → Prop
  | C, .stop terminal => dispatch C = .inl terminal
  | C, .next outer rest => dispatch C = .inr outer ∧ Produced rest

end Execution

theorem finish_produced (C : State L) : (finish C).Produced := by
  refine earlier_wellFounded.induction C (C := fun D => (finish D).Produced) ?_
  intro C ih
  rw [finish_unfold]
  cases hd : dispatch C with
  | inl terminal => exact hd
  | inr outer => exact ⟨hd,ih outer.target outer.source_decreases⟩

theorem rank_original_bound (C : State L) : C.node.sourceOmega.1 =
    sourceGroupBound (Module.finrank ℚ L) - Nat.card (completeGroup C.family C.torsion) := rfl

namespace State
variable (C : State L)

/-- Same-stratum augmentation retains the SAME core, catalogue and actual
queue. Mere family growth does not constitute a local progress step. -/
def augmentedNode (hτ : ResidualTorsion C.augmented)
    (ha : C.minimum.signature.1 = C.core.signature.1)
    (q : FrozenQueue L C.node.frozen) : Node L (HistoryCatalogue.Key L) where
  family := C.augmented
  finite := fullRetainedDeck_finite C.family C.finite C.torsion C.signature
  equality := C.retains C.equality
  torsion := hτ
  core := C.retainedCore ha
  frozen := C.node.frozen
  queue := q

theorem augmented_core_identity (hτ : ResidualTorsion C.augmented)
    (ha : C.minimum.signature.1 = C.core.signature.1) (q : FrozenQueue L C.node.frozen) :
    (C.augmentedNode hτ ha q).core.signature = C.core.signature := rfl

theorem augmented_catalogue_identity (hτ : ResidualTorsion C.augmented)
    (ha : C.minimum.signature.1 = C.core.signature.1) (q : FrozenQueue L C.node.frozen) :
    (C.augmentedNode hτ ha q).frozen = C.node.frozen := rfl

end State

theorem same_stratum_step (C : State L) (hτ : ResidualTorsion C.augmented)
    (hg : completeGroup C.augmented hτ = completeGroup C.family C.torsion)
    (ha : C.minimum.signature.1 = C.core.signature.1)
    (q : FrozenQueue L C.node.frozen) (hq : FrozenQueue.Step q C.node.queue) :
    Node.Step (C.augmentedNode hτ ha q) C.node :=
  .retainedLocal C.node _ C.retains hg rfl rfl hq

theorem same_stratum_source_decreases (C : State L) (hτ : ResidualTorsion C.augmented)
    (hg : completeGroup C.augmented hτ = completeGroup C.family C.torsion)
    (ha : C.minimum.signature.1 = C.core.signature.1)
    (q : FrozenQueue L C.node.frozen) (hq : FrozenQueue.Step q C.node.queue) :
    Node.RankLT (C.augmentedNode hτ ha q).sourceOmega C.node.sourceOmega :=
  Node.source_step_decreases (same_stratum_step C hτ hg ha q hq)

abbrev NodeRuns (S T : Node L (HistoryCatalogue.Key L)) : Prop := Node.Runs S T

/-- Lift the SAME saved queue run after its genuine first retained-local
edge. The nil alternative is excluded by an actual pending initial key. -/
theorem augmented_queue_trace (C : State L) (hτ : ResidualTorsion C.augmented)
    (hg : completeGroup C.augmented hτ = completeGroup C.family C.torsion)
    (ha : C.minimum.signature.1 = C.core.signature.1)
    (q : FrozenQueue L C.node.frozen)
    (run : FrozenQueue.Runs C.node.queue q) (empty : q.todo = ∅) :
    NodeRuns C.node (C.augmentedNode hτ ha q) := by
  rcases run.cases_head with he | ⟨first,hs,rest⟩
  · have hi := HistoryCatalogue.key_covered C.family C.torsion C.signature (Sum.inl 1)
    have hz : C.node.queue.todo = ∅ := by rw [he,empty]
    change HistoryCatalogue.embed C.family C.torsion C.signature (Sum.inl 1) ∈
      C.node.queue.todo at hi
    rw [hz] at hi
    exact False.elim (Finset.notMem_empty _ hi)
  · have hfirst : NodeRuns C.node (C.augmentedNode hτ ha first) :=
      Relation.ReflTransGen.single (same_stratum_step C hτ hg ha first hs)
    have hrest := Node.lift_queue_run (C.augmentedNode hτ ha first) rest
    exact hfirst.trans hrest

theorem stable_node_run (C : State L) (S : Stable C) :
    NodeRuns C.node (C.augmentedNode S.torsion S.sameArity S.queue.final) :=
  augmented_queue_trace C S.torsion S.sameGroup S.sameArity S.queue.final S.queue.run S.queue.empty

end Holant.LocalDrafts.RemoteWork.StableClosureV2.StabilizationMathematical
end
