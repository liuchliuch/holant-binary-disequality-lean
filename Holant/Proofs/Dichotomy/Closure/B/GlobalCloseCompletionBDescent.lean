import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentCoverage
import Holant.Proofs.Closure.ClosureBStableCore
import Holant.Proofs.Closure.ClosureMarkedActualReceipts

/-! Universal B-coordinate higher-current descent through exact prepared card
occurrences. Higher primes do not acquire matching raw decks merely by queue
exhaustion. Rather, each has a nonmatching card with a strictly smaller even
prime in its own copied saved tree; the finite arity descent reaches q4. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDescent
open Holant Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open StableHigherCurrentCoverage
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {S T : GeneratedGroupWorklist.Active G base}
variable {h : GeneratedGroupWorklist.Trace G base S T}
variable {o : CurrentOccurrences.Id G T.source.palette}
variable (r : GeneratedGroupWorklist.PreparationReceipt G base h o)
variable (proper : 4 ≤ (CurrentOccurrences.savedLeaf G T.source.palette o).1.1)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion))

include N in
/-- This is the obstruction to the proposed all-arity matching invariant:
every genuinely higher current B-coordinate prime has an actual nonmatching key. -/
theorem higher_has_nonmatching_key
    (higher : 4 < (CurrentOccurrences.savedLeaf G T.source.palette o).1.1) :
    ∃ k : Key G base r proper,
      ¬ MatchingOrZero (actualTransfers T.source.palette.family) (current G base r proper k) := by
  classical
  by_contra absent
  push Not at absent
  have stable : ∀ g ∈ rawDeck T.source.palette.family T.ready.torsion
      (input G base r proper).signature,
      MatchingOrZero (actualTransfers T.source.palette.family) g := by
    intro g member
    rcases member with zero | ⟨key,rfl⟩
    · exact .inl zero
    · exact absent key
  have literal := r.selectedSignatureFinal G base proper
  have prime : Prime (⟨(input G base r proper).m+2,
      (input G base r proper).signature⟩ : AnySignature (OI.K G)) := by
    rw [literal]
    exact CurrentOccurrences.savedLeaf_prime G T.source.palette o
  have bound := ClosureBStableCore.stable_prime_residual_eq_two G T.source.palette
    T.ready.torsion N (input G base r proper).signature (input G base r proper).proper
    (input G base r proper).evenArity prime stable
  have arity := congrArg Sigma.fst literal
  change (input G base r proper).m + 2 = _ at arity
  omega

include N in
/-- The entire current deck cannot be declared matching-stable when the
addressed B-coordinate prime has arity greater than four. -/
theorem higher_not_matching_deck
    (higher : 4 < (CurrentOccurrences.savedLeaf G T.source.palette o).1.1) :
    ¬ (∀ g ∈ rawDeck T.source.palette.family T.ready.torsion
      (input G base r proper).signature,
      MatchingOrZero (actualTransfers T.source.palette.family) g) := by
  obtain ⟨key,bad⟩ := higher_has_nonmatching_key G base r proper N higher
  intro stable
  exact bad (stable _ (.inr ⟨key,rfl⟩))

variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done = ∅)

/-- A descent edge carries this parent's actual preparation event, one actual
current-group raw key, and one address in its copied saved old card tree. -/
structure Step (o : CurrentOccurrences.Id G R.final.source.palette) : Type 1 where
  proper : 4 ≤ (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1
  key : Key G base (R.preparationReceipt G base noPrior o) proper
  nonmatching : ¬ MatchingOrZero (actualTransfers R.final.source.palette.family)
    (current G base (R.preparationReceipt G base noPrior o) proper key)
  nonzero : current G base (R.preparationReceipt G base noPrior o) proper key ≠ 0
  address : Occurrences.Address
    (oldRoot G base (R.preparationReceipt G base noPrior o) proper key nonzero).2
  lower : 4 ≤ (CurrentOccurrences.savedLeaf G R.final.source.palette
    (cardLeaf G base (R.preparationReceipt G base noPrior o) proper key nonzero address)).1.1

namespace Step
variable {R noPrior} {o : CurrentOccurrences.Id G R.final.source.palette}
variable (e : Step G base R noPrior o)
abbrev target : CurrentOccurrences.Id G R.final.source.palette :=
  cardLeaf G base (R.preparationReceipt G base noPrior o) e.proper e.key e.nonzero e.address

theorem decreases :
    (CurrentOccurrences.savedLeaf G R.final.source.palette (e.target G base)).1.1 <
      (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 :=
  cardLeaf_arity_lt G base (R.preparationReceipt G base noPrior o) e.proper e.key e.nonzero e.address

/-- Both graph substitution and coefficient decoding are those actually
constructed for the same current raw key in the original field. -/
def access := cardAccess G base (R.preparationReceipt G base noPrior o) e.proper e.key

theorem saved : CurrentOccurrences.savedLeaf G R.final.source.palette (e.target G base) =
    Occurrences.leaf (oldRoot G base (R.preparationReceipt G base noPrior o)
      e.proper e.key e.nonzero).2 e.address :=
  cardLeaf_saved G base (R.preparationReceipt G base noPrior o) e.proper e.key e.nonzero e.address
end Step

variable (native : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    R.final.source.palette.family R.final.ready.torsion))

include native in
theorem step_nonempty (o : CurrentOccurrences.Id G R.final.source.palette)
    (higher : 4 < (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1) :
    Nonempty (Step G base R noPrior o) := by
  let proper : 4 ≤ (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 := higher.le
  let receipt := R.preparationReceipt G base noPrior o
  obtain ⟨key,bad⟩ := higher_has_nonmatching_key G base receipt proper native higher
  obtain ⟨nonzero,address,lower,_even,_decreases⟩ :=
    nonmatching_has_lower_leaf G base receipt proper key bad
  exact ⟨⟨proper,key,bad,nonzero,address,lower⟩⟩

/-- An actual finite chain of prepared raw-card / saved-factor events at the
same final palette. No engine termination hypothesis is introduced here. -/
inductive Path : CurrentOccurrences.Id G R.final.source.palette →
    CurrentOccurrences.Id G R.final.source.palette → Type 1
  | refl (o : CurrentOccurrences.Id G R.final.source.palette) : Path o o
  | cons {o q : CurrentOccurrences.Id G R.final.source.palette} (step : Step G base R noPrior o)
      (rest : Path (step.target G base) q) : Path o q

include native in
/-- Every even nonbinary final occurrence reaches an actual addressed q4 via
its own prepared contractions. The conclusion preserves the entire path. -/
theorem quaternary_path_exists (o : CurrentOccurrences.Id G R.final.source.palette)
    (proper : 4 ≤ (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1) :
    ∃ q : CurrentOccurrences.Id G R.final.source.palette,
      Nonempty (Path G base R noPrior o q) ∧
      (CurrentOccurrences.savedLeaf G R.final.source.palette q).1.1 = 4 := by
  classical
  have inductionClaim : ∀ n : ℕ, ∀ o : CurrentOccurrences.Id G R.final.source.palette,
      (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 = n → 4 ≤ n →
      ∃ q : CurrentOccurrences.Id G R.final.source.palette,
        Nonempty (Path G base R noPrior o q) ∧
        (CurrentOccurrences.savedLeaf G R.final.source.palette q).1.1 = 4 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro o arity proper
      by_cases four : n = 4
      · exact ⟨o,⟨.refl o⟩,arity.trans four⟩
      · have higher : 4 < (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 := by omega
        obtain ⟨step⟩ := step_nonempty G base R noPrior native o higher
        obtain ⟨q,⟨path⟩,qfour⟩ := ih
          (CurrentOccurrences.savedLeaf G R.final.source.palette (step.target G base)).1.1
          (by simpa only [arity] using step.decreases G base)
          (step.target G base) rfl step.lower
        exact ⟨q,⟨.cons step path⟩,qfour⟩
  exact inductionClaim _ o rfl proper

structure Descent (o : CurrentOccurrences.Id G R.final.source.palette) : Type 1 where
  endpoint : CurrentOccurrences.Id G R.final.source.palette
  path : Path G base R noPrior o endpoint
  four : (CurrentOccurrences.savedLeaf G R.final.source.palette endpoint).1.1 = 4

def descent (o : CurrentOccurrences.Id G R.final.source.palette)
    (proper : 4 ≤ (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1) :
    Descent G base R noPrior o := by
  let witness := quaternary_path_exists G base R noPrior native o proper
  let endpoint := Classical.choose witness
  have result := Classical.choose_spec witness
  exact ⟨endpoint,Classical.choice result.1,result.2⟩

/-- The selected native model comes from the SAME actual final marking. All
other markings keep their own local obligations. -/
def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    R.final.source.palette.family R.final.ready.torsion) : Type 1 :=
  match M with
  | .bilinear _ => ∀ o : CurrentOccurrences.Id G R.final.source.palette,
      4 ≤ (CurrentOccurrences.savedLeaf G R.final.source.palette o).1.1 →
        Descent G base R noPrior o
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    R.final.source.palette.family R.final.ready.torsion) : ForMarking G base R noPrior M := by
  cases M with
  | bilinear N => exact fun o proper => descent G base R noPrior N o proper
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | monomial => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 :=
  match result with
  | .initialStop .. => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted rfl
        (ClosureMarkedActualReceipts.produce G exhausted.final.source.palette
          exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) =>
      forMarking G base exhausted rfl
        (ClosureMarkedActualReceipts.produce G exhausted.final.source.palette
          exhausted.final.ready.torsion).physical.marking

/-- Unconditional original-G producer. Its B-coordinate branch covers every final
nonbinary saved occurrence, including genuinely higher ones and duplicates. -/
def original_higher_current_descent : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDescent
end
