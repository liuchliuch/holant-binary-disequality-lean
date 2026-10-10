import Holant.Proofs.Closure.Occurrences
import Holant.Proofs.Closure.OccurrenceScalarScope
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-! Source-bound finite outer-occurrence frontier.
Visiting means recording the exact occurrence and its pending local domain;
it never means resolving that domain. The outer measure is the number of
unvisited saved occurrences, independently of the minimum-core sourceOmega.
All returned entries retain the CURRENT palette and its original-G machines. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.Frontier
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Occurrences

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- Exact arity domains for separate local consumers. An even higher-arity
entry is not assumed to be a minimum core or a stabilized prime. -/
inductive LocalKind (f : AnySignature (OI.K G)) : Type
  | unary (arity : f.1 = 1)
  | binary (arity : f.1 = 2)
  | oddNonbinary (nonbinary : 3 ≤ f.1) (odd : Odd f.1)
  | evenNonbinary (proper : 4 ≤ f.1) (even : Even f.1)

def classify (f : AnySignature (OI.K G)) (hpos : 0 < f.1) : LocalKind G f := by
  by_cases h1 : f.1 = 1
  · exact .unary h1
  by_cases h2 : f.1 = 2
  · exact .binary h2
  have h3 : 3 ≤ f.1 := by omega
  by_cases he : Even f.1
  · exact .evenNonbinary (by rcases he with ⟨k, hk⟩; omega) he
  · exact .oddNonbinary h3 ((Nat.even_or_odd f.1).resolve_left he)

def localKind (o : Id G) : LocalKind G (originalLeaf G o).1 :=
  classify G (originalLeaf G o).1 (originalLeaf_positive G o)

def paletteRoot (P : Palette G) (i : Fin P.count) : TreeOccurrence (OI.K G) :=
  ⟨⟨P.arity i.val, P.table i⟩, P.trees i⟩

def occurrenceLeaves (t : TreeOccurrence (OI.K G)) : Multiset (AnySignature (OI.K G)) :=
  t.2.leaves

/-- Pending occurrences are not prepared minima merely because their arity
is even. A genuine minimum receipt supplies both the actual CURRENT core and
literal signature equality; it still supplies no local classification theorem. -/
inductive Preparation (P : Palette G) (f : AnySignature (OI.K G)) : Type
  | pending
  | actualMinimum (minimum : MinimumCore P.family) (literal : minimum.signature = f)

/-- A pending local leaf carries the full current source state, its original
field and both physical original-G programmes, an exact original saved root
binding, the actual retained literal leaf label, and its unproved leaf domain. -/
structure CurrentDomain (P : Palette G) (o : Id G) where
  savedRootLabel : Fin P.count
  savedRootExact : paletteRoot G P savedRootLabel = originalRoot G o
  currentLeafLabel : Fin P.count
  currentLeafExact : (⟨P.arity currentLeafLabel.val, P.table currentLeafLabel⟩ :
    AnySignature (OI.K G)) = (originalLeaf G o).1
  kind : LocalKind G (originalLeaf G o).1
  preparation : Preparation G P (originalLeaf G o).1

abbrev CurrentDomain.toOriginal {P : Palette G} {o : Id G}
    (_domain : CurrentDomain G P o) := P.toOriginal

abbrev CurrentDomain.fromOriginal {P : Palette G} {o : Id G}
    (_domain : CurrentDomain G P o) := P.fromOriginal

/-- Construct the local domain solely from P's existing exact saved bindings.
No current leaf theorem or whole-family coverage certificate is requested. -/
def currentDomain (P : Palette G) (o : Id G) : CurrentDomain G P o := by
  let j := Classical.choose (P.originalSaved o.1)
  have hj' : paletteRoot G P j = originalRoot G o := Classical.choose_spec (P.originalSaved o.1)
  have hm : (originalLeaf G o).1 ∈ (P.trees j).leaves := by
    change (originalLeaf G o).1 ∈ occurrenceLeaves G (paletteRoot G P j)
    rw [hj']
    exact leaf_mem (OI.storedTrees G o.1) o.2
  have hlabels : ∃ k : Fin P.count,
      (⟨P.arity k.val, P.table k⟩ : AnySignature (OI.K G)) = (originalLeaf G o).1 :=
    P.leavesRetained j _ hm
  let k := Classical.choose hlabels
  exact ⟨j, hj', k, Classical.choose_spec hlabels, localKind G o, .pending⟩

def CurrentDomain.withMinimum {P : Palette G} {o : Id G} (d : CurrentDomain G P o)
    (minimum : MinimumCore P.family) (literal : minimum.signature = (originalLeaf G o).1) :
    CurrentDomain G P o := { d with preparation := .actualMinimum minimum literal }

theorem currentDomain_unprepared (P : Palette G) (o : Id G) :
    (currentDomain G P o).preparation = Preparation.pending := rfl

/-- No arity filter and no deduplication by table values. -/
def records (P : Palette G) : List ((o : Id G) × CurrentDomain G P o) :=
  (enumeration G).map (fun o => ⟨o, currentDomain G P o⟩)

theorem records_complete (P : Palette G) (o : Id G) :
    (⟨o, currentDomain G P o⟩ : (o : Id G) × CurrentDomain G P o) ∈ records G P := by
  exact List.mem_map.mpr ⟨o, enumeration_complete G o, rfl⟩

theorem records_ids (P : Palette G) : (records G P).map Sigma.fst = enumeration G := by
  simp [records, List.map_map, Function.comp_def]

theorem records_length (P : Palette G) : (records G P).length = Fintype.card (Id G) := by
  simp only [records, List.length_map, enumeration_length]

/-- One saved-address catalogue visit. Its associated receipt is `currentDomain` for
this exact selected address and this exact P. It does not mark the leaf solved. -/
inductive Visit (P : Palette G) : Finset (Id G) → Finset (Id G) → Prop
  | erase (before : Finset (Id G)) (selected : Id G) (pending : selected ∈ before) :
      Visit P before (before.erase selected)

theorem Visit.selection {P : Palette G} {before after : Finset (Id G)}
    (h : Visit G P before after) :
    ∃ selected : Id G, selected ∈ before ∧ after = before.erase selected := by
  cases h with
  | erase o ho => exact ⟨o, ho, rfl⟩

def Visit.selected {P : Palette G} {before after : Finset (Id G)}
    (h : Visit G P before after) : Id G := Classical.choose (Visit.selection G h)

theorem Visit.selected_pending {P : Palette G} {before after : Finset (Id G)}
    (h : Visit G P before after) : Visit.selected G h ∈ before :=
  (Classical.choose_spec (Visit.selection G h)).1

theorem Visit.selected_after {P : Palette G} {before after : Finset (Id G)}
    (h : Visit G P before after) : after = before.erase (Visit.selected G h) :=
  (Classical.choose_spec (Visit.selection G h)).2

/-- Classical extraction recovers the very address erased by that step. -/
theorem Visit.erase_selected (P : Palette G) (before : Finset (Id G))
    (o : Id G) (ho : o ∈ before) :
    Visit.selected G (Visit.erase (P := P) before o ho) = o := by
  by_contra hne
  have hm : o ∈ before.erase (Visit.selected G (Visit.erase (P := P) before o ho)) :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, ho⟩
  rw [← Visit.selected_after G (Visit.erase (P := P) before o ho)] at hm
  exact Finset.notMem_erase o before hm

def Visit.receipt {P : Palette G} {before after : Finset (Id G)}
    (h : Visit G P before after) : CurrentDomain G P (Visit.selected G h) :=
  currentDomain G P (Visit.selected G h)

theorem visit_decreases {P : Palette G} {before after : Finset (Id G)}
    (h : Visit G P before after) : after.card < before.card := by
  cases h with
  | erase o ho => exact Finset.card_erase_lt_of_mem ho

/-- Separate well-founded outer occurrence measure. Changing active primes
of equal arity is not a sourceOmega decrease. -/
theorem visit_wellFounded (P : Palette G) :
    WellFounded (fun after before => Visit G P before after) :=
  Subrelation.wf (fun h => visit_decreases G h) (measure Finset.card).wf

abbrev Runs (P : Palette G) := Relation.ReflTransGen (Visit G P)

/-- Internally produced finite exhaustive visit run; no run is caller input. -/
theorem exhausts (P : Palette G) (before : Finset (Id G)) : Runs G P before ∅ := by
  induction before using Finset.induction_on with
  | empty => exact .refl
  | @insert o todo ho ih =>
      have step : Visit G P (insert o todo) todo := by
        simpa [ho] using Visit.erase (P := P) (insert o todo) o (Finset.mem_insert_self o todo)
      exact (Relation.ReflTransGen.single step).trans ih

theorem visit_no_reopen {P : Palette G} {before after : Finset (Id G)}
    (h : Visit G P before after) : after ⊆ before := by
  cases h with
  | erase o ho => exact Finset.erase_subset o before

theorem runs_no_reopen {P : Palette G} {before after : Finset (Id G)}
    (h : Runs G P before after) : after ⊆ before := by
  induction h with
  | refl => exact fun _ h => h
  | tail h step ih => exact (visit_no_reopen G step).trans ih

/-- Final frontier remains pending even after every catalogue entry is visited.
All entries are explicitly represented at the same current source palette. -/
structure Result (P : Palette G) where
  pending : List ((o : Id G) × CurrentDomain G P o)
  pendingExact : pending = records G P
  finalTodo : Finset (Id G)
  visitRun : Runs G P Finset.univ finalTodo
  exhausted : finalTodo = ∅

/-- Finite address-ledger traversal and full unresolved frontier factory.
This is not a physical batch-preparation or local-classification producer. -/
def build (P : Palette G) : Result G P :=
  ⟨records G P, rfl, ∅, exhausts G P Finset.univ, rfl⟩

theorem build_coverage (P : Palette G) (o : Id G) :
    (⟨o, currentDomain G P o⟩ : (o : Id G) × CurrentDomain G P o) ∈ (build G P).pending :=
  records_complete G P o

/-- Apply the same frontier factory to the exact returned source palette.
The structural exit is retained by its enclosing result; visiting its other
original occurrences supplies no additional resolved leaf theorem. -/
def forStabilization (result : StabilizationResult G) : Result G result.palette :=
  build G result.palette

theorem forStabilization_coverage (result : StabilizationResult G) (o : Id G) :
    (⟨o, currentDomain G result.palette o⟩ :
      (o : Id G) × CurrentDomain G result.palette o) ∈
      (forStabilization G result).pending :=
  build_coverage G result.palette o

/-- Direct frozen-interface consequence of the scalar-scope obstruction:
no finite returned Palette literally retains every unit multiple of any of
its actual nonzero retained table labels. -/
theorem palette_table_not_scalar_universal (P : Palette G) (j : Fin P.count) :
    ¬ ∀ c : (OI.K G)ˣ,
      (⟨P.arity j.val, ((c : OI.K G) • P.table j : Signature (OI.K G) (P.arity j.val))⟩ : AnySignature (OI.K G)) ∈ P.family :=
  OccurrenceScalarScope.finite_family_cannot_retain_all_unit_scalars
    P.family (Set.finite_range _) (P.table j) (P.nonzero j)

/-- Both source programmes are literally those of the retained CURRENT P. -/
theorem domain_toOriginal_machine (P : Palette G) (o : Id G) :
    (CurrentDomain.toOriginal G (currentDomain G P o)).controlled.reduction.machine =
      P.toOriginal.controlled.reduction.machine := rfl

theorem domain_fromOriginal_machine (P : Palette G) (o : Id G) :
    (CurrentDomain.fromOriginal G (currentDomain G P o)).controlled.reduction.machine =
      P.fromOriginal.controlled.reduction.machine := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.Frontier
end
